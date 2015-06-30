//===-- DoubleFreeChecker.cpp -----------------------------------------*- C++ -*--//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Defines a checker to flag cases of double free.
//   - If a memory block has been freed with free, then it should not be
//	   freed.
//
//===----------------------------------------------------------------------===//

/*	HIGH LEVEL PSEUDOCODE

	checkPreCall -	Before making a call to a function, check if the function 
					is free(). 

					If so, check the parameter being passed to see if it is a 
					valid symbol.

					If valid, check if symbol has been freed before and flag
					double free.

					If the free is supposed to be executed, generate (move to)
					the next transition, in which the value corresponding to 
					the symbol in the AllocationMap is updated to Freed.

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

	class DoubleFreeChecker : public Checker<check::PostCall,check::PreCall> {
		mutable IdentifierInfo *IIfmalloc, *IIffree;

		std::unique_ptr<BugType> DoubleFreeBugType;

		void initIdentifierInfo(ASTContext &Ctx) const;

	private:
		bool checkDoubleFree(SymbolRef Sym, CheckerContext &C, const Stmt *S) const;

		void reportDoubleFree(CheckerContext &C, SourceRange Range,
			SymbolRef Sym) const;

		bool symIsFreed(SymbolRef Sym, CheckerContext &C) const;

	public:
		DoubleFreeChecker();

		//void checkPreStmt(const ReturnStmt *DS, CheckerContext &C) const;

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


//	checkPreStmt - Before statement executes, we see if the return value is a
//	reference to a symbol


// If we are malloc'ing, we add it to the AllocationMap of allocated symbols
void DoubleFreeChecker::checkPostCall(const CallEvent &Call, CheckerContext &C) const
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
void DoubleFreeChecker::checkPreCall(const CallEvent &Call, CheckerContext &C) const
{
	initIdentifierInfo(C.getASTContext());

	if (!Call.isGlobalCFunction())
		return;

	if (Call.getCalleeIdentifier() != IIffree)
		return;

	if (Call.getNumArgs() != 1)
		return;

	// Get the symbolic value corresponding to the variable.
	SymbolRef Sym = Call.getArgSVal(0).getAsSymbol();
	if (!Sym)
		return;

	// Check if the symbol has already been freed.
	ProgramStateRef State = C.getState();
	const AllocState *SS = State->get<AllocationMap>(Sym);
	if (SS && SS->isFreed()) {
		reportDoubleFree(C, Call.getSourceRange(), Sym);
		return;
	}

	// Generate the next transition, in which the symbol is freed
	State = State->set<AllocationMap>(Sym, AllocState::getFreed());
	C.addTransition(State);

	return;
}

DoubleFreeChecker::DoubleFreeChecker()
	: IIfmalloc(nullptr), IIffree(nullptr)
{
	// Initialize the bug types.
	DoubleFreeBugType.reset(
		new BugType(this, "Use after free error", "Memory Error"));
	// Sinks are higher importance bugs as well as calls to assert() or exit(0).
	//DoubleFreeBugType->setSuppressOnSink(true);
}


void DoubleFreeChecker::reportDoubleFree(CheckerContext &C, SourceRange Range,
	SymbolRef Sym) const {
	// We reached a bug, stop exploring the path here by generating a sink.
	ExplodedNode *ErrNode = C.generateSink();
	// If we've already reached this node on another path, return.
	if (!ErrNode)
		return;

	// Generate the report.
	auto R = llvm::make_unique<BugReport>(*DoubleFreeBugType,
		"Double free error", ErrNode);
	R->addRange(Range);
	R->markInteresting(Sym);
	C.emitReport(std::move(R));
}

bool DoubleFreeChecker::symIsFreed(SymbolRef Sym, CheckerContext &C) const {
	assert(Sym);
	const AllocState *RS = C.getState()->get<AllocationMap>(Sym);
	return (RS && RS->isFreed());
}

/* Define the functions we are looking out from by parsing the AST context */
void DoubleFreeChecker::initIdentifierInfo(ASTContext &Ctx) const
{
	if (IIfmalloc && IIffree)
		return;

	IIfmalloc = &Ctx.Idents.get("malloc");
	IIffree = &Ctx.Idents.get("free");
}

/* Register the checkers in into the analyzer */
void ento::registerDoubleFreeChecker(CheckerManager &mgr)
{
	mgr.registerChecker<DoubleFreeChecker>();
}
