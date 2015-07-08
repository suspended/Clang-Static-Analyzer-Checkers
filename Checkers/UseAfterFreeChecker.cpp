//===-- UseAfterFreeChecker.cpp -----------------------------------------*- C++ -*--//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Defines a checker to flag cases of use-after-free.
//   - If a memory block has been freed with free, then its value should
//	 no long be valid.
//
//===----------------------------------------------------------------------===//

/*	HIGH LEVEL PSEUDOCODE

	checkPreStmt -	Before statement executes, we see if the return value is a 
					reference to a symbol

	checkPreCall -	Before making a call to a function, check if the function 
					is free(). 

					If so, check the parameter being passed to see if it is a 
					valid symbol.

					If valid, check if symbol has been freed and flag double 
					free (see if core checker does this)

					If the free is supposed to be executed, generate (move to)
					the next transition, in which the value corresponding to 
					the symbol in the AllocationMap is updated to Freed

	checkPostCall -	After making a call to a function, check if the function
					is malloc(). Note that calloc is a wrapper for malloc.
					
					If so, get the symbol from the return value.

					Generate the next transition, adding an edge in our
					AllocationMap, where its value to the key is InUse.
*/

#include "ClangSACheckers.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"

using namespace clang;
using namespace ento;

namespace {
	
	struct AllocState {
		private:
			enum Kind { Allocated, Freed } K;
			AllocState(Kind InK) { K = InK; };

		public:
			bool isAllocated() const { return K == Allocated; }
			bool isFreed() const { return K == Freed; }

			static AllocState getAllocated() { 
				return AllocState(Allocated); 
			}
			static AllocState getFreed() { 
				return AllocState(Freed); 
			}
			bool operator==(const AllocState &X) const {
				return K == X.K;
			}
			// not sure what this is for; apparently it overrides hash function
			void Profile(llvm::FoldingSetNodeID &ID) const {
				ID.AddInteger(K);
			}
	};

	class UseAfterFreeChecker : public Checker<	check::PostCall,
												check::PreStmt<ReturnStmt>,
												check::PreCall> 
	{
		mutable IdentifierInfo *IIfmalloc, *IIffree;

		std::unique_ptr<BugType> UseAfterFreeBugType;

		void initIdentifierInfo(ASTContext &Ctx) const;

	private:
		bool checkUseAfterFree(SymbolRef Sym, CheckerContext &C, const Stmt *S) const;

		void reportUseAfterFree(CheckerContext &C, SourceRange Range,
			SymbolRef Sym) const;

		bool symIsFreed(SymbolRef Sym, CheckerContext &C) const;

	public:
		UseAfterFreeChecker();

		void checkPreStmt(const ReturnStmt *DS, CheckerContext &C) const;
		
		void checkPostCall(const CallEvent &Call, CheckerContext &C) const;

		void checkPreCall(const CallEvent &Call, CheckerContext &C) const;

	};

} // end anonymous namespace

/// The state of the checker is a map from malloc'd symbols to their
/// allocation state (in-use or freed). Let's store it in the ProgramState.
REGISTER_MAP_WITH_PROGRAMSTATE(AllocationMap, SymbolRef, AllocState)

namespace {
	class StopTrackingCallback : public SymbolVisitor {
		ProgramStateRef state;

	public:
		StopTrackingCallback(ProgramStateRef st) : state(st) {}
		ProgramStateRef getState() const { return state; }

		bool VisitSymbol(SymbolRef sym) override {
			state = state->remove<AllocationMap>(sym);
			return true;
		}
	};
} // end anonymous namespace

bool UseAfterFreeChecker::symIsFreed(SymbolRef Sym, CheckerContext &C) const {
	assert(Sym);
	const AllocState *RS = C.getState()->get<AllocationMap>(Sym);
	return (RS && RS->isFreed());
}

bool UseAfterFreeChecker::checkUseAfterFree(SymbolRef Sym, CheckerContext &C,
	const Stmt *S) const {

	if (symIsFreed(Sym, C)) {
		reportUseAfterFree(C, S->getSourceRange(), Sym);
		return true;
	}

	return false;
}


















/*
checkPreStmt - Before returning from a function, we want to see if we are 
returning a symbol.

If so, check the parameter being passed to see if it is a
valid symbol.

If valid, check if symbol has been freed and flag use-after-free error since
it has already been freed.		*/
void UseAfterFreeChecker::checkPreStmt(const ReturnStmt *S, CheckerContext &C) const {
	const Expr *E = S->getRetValue();
	if (!E)
		return;

	// Check if we are returning a symbol.
	ProgramStateRef State = C.getState();
	SVal RetVal = State->getSVal(E, C.getLocationContext());
	SymbolRef Sym = RetVal.getAsSymbol();
	if (!Sym)
		// If we are returning a field of the allocated struct or an array element,
		// the callee could still free the memory.
		if (const MemRegion *MR = RetVal.getAsRegion())
			if (isa<FieldRegion>(MR) || isa<ElementRegion>(MR))
				if (const SymbolicRegion *BMR =
					dyn_cast<SymbolicRegion>(MR->getBaseRegion()))
					Sym = BMR->getSymbol();

	// Check if we are returning freed memory.
	if (Sym)
		checkUseAfterFree(Sym, C, E);
}

/*
checkPreCall - Before making a call to a function, check if the function
is free().

If so, check the parameter being passed to see if it is a
valid symbol.

If valid, check if symbol has been freed and flag double
free(see if core checker does this)

If the free is supposed to be executed, generate(move to)
the next transition, in which the value corresponding to
the symbol in the AllocationMap is updated to Freed */
void UseAfterFreeChecker::checkPreCall(const CallEvent &Call, CheckerContext &C) const
{
	initIdentifierInfo(C.getASTContext());

	//if (Call.getCalleeIdentifier() != IIffree)
	//	return;

	if (Call.getCalleeIdentifier() == IIffree) {
		// Get the symbolic value corresponding to the variable.
		SymbolRef Sym = Call.getArgSVal(0).getAsSymbol();
		if (!Sym)
			return;

		// Check if the symbol has already been freed.
		ProgramStateRef State = C.getState();
		const AllocState *SS = State->get<AllocationMap>(Sym);
		if (SS && SS->isFreed()) {
			//reportDoubleFree(C, Call.getSourceRange(), Sym);
			return;
		}

		// Generate the next transition, in which the symbol is freed
		State = State->set<AllocationMap>(Sym, AllocState::getFreed());
		C.addTransition(State);
	}
	else {
		// Check if the callee of a method is deleted.
		if (const CXXInstanceCall *CC = dyn_cast<CXXInstanceCall>(&Call)) {
			SymbolRef Sym = CC->getCXXThisVal().getAsSymbol();
			if (!Sym || checkUseAfterFree(Sym, C, CC->getCXXThisExpr()))
				return;
		}

		// Check arguments for being used after free.
		for (unsigned I = 0, E = Call.getNumArgs(); I != E; ++I) {
			SVal ArgSVal = Call.getArgSVal(I);
			if (ArgSVal.getAs<Loc>()) {
				SymbolRef Sym = ArgSVal.getAsSymbol();
				if (!Sym)
					continue;
				if (checkUseAfterFree(Sym, C, Call.getArgExpr(I)))
					return;
			}
		}
	}

	return;
}

// If we are malloc'ing, we add it to the AllocationMap of allocated symbols
void UseAfterFreeChecker::checkPostCall(const CallEvent &Call, CheckerContext &C) const
{
	initIdentifierInfo(C.getASTContext());

	if (!Call.isGlobalCFunction())
		return;

	// Hook onto malloc calls only
	if (Call.getCalleeIdentifier() != IIfmalloc)
		return;

	// Get the symbolic value corresponding to the malloc'd variable
	SymbolRef Sym = Call.getReturnValue().getAsSymbol();
	if (!Sym)	// malloc failed; just return
		return;

	// Generate the next transition (current state of var is now allocated).
	ProgramStateRef State = C.getState();
	State = State->set<AllocationMap>(Sym, AllocState::getAllocated());
	C.addTransition(State);

	return;
}

UseAfterFreeChecker::UseAfterFreeChecker()
	: IIfmalloc(nullptr), IIffree(nullptr) 
{
	// Initialize the bug types.
	UseAfterFreeBugType.reset(
		new BugType(this, "Use after free error", "Memory Error"));
}

void UseAfterFreeChecker::reportUseAfterFree(CheckerContext &C, SourceRange Range,
	SymbolRef Sym) const {
	// We reached a bug, stop exploring the path here by generating a sink.
	ExplodedNode *ErrNode = C.generateSink();
	// If we've already reached this node on another path, return.
	if (!ErrNode)
		return;

	// Generate the report.
	auto R = llvm::make_unique<BugReport>(*UseAfterFreeBugType,
		"Use-after-free error", ErrNode);
	R->addRange(Range);
	R->markInteresting(Sym);
	C.emitReport(std::move(R));
}

/* Define the functions we are looking out from by parsing the AST context */
void UseAfterFreeChecker::initIdentifierInfo(ASTContext &Ctx) const 
{
	if (IIfmalloc && IIffree)
		return;
	IIfmalloc = &Ctx.Idents.get("malloc");
	IIffree = &Ctx.Idents.get("free");
}

/* Register the checkers in into the analyzer */
void ento::registerUseAfterFreeChecker(CheckerManager &mgr) 
{
	mgr.registerChecker<UseAfterFreeChecker>();
}

