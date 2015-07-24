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

/*  DoubleFreeChecker Visitors

	checkPreCall -	Before making a call to a function, check if the function 
					we are calling is free(). 

					If so, check the parameter being passed to see if there is
					a valid symbol.

					If valid, check if symbol has been freed before and flag
					double free if so.

					If the symbol is still allocated (not freed before), 
					generate (move to) to next transition, in which the value 
					corresponding to the symbol in the AllocationMap is updated
					to 'Freed'.

	checkPostCall -	After making a call to a function (to ensure it returned
					correctly , check if the function is malloc(). Note that 
					calloc is a wrapper for malloc.
					
					If so, get the malloc'd symbol from the return value.

					Generate the next transition, adding an edge in our
					AllocationMap, where its value to the key is 'Allocated'.
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
		enum Kind { Allocated, Freed } K;	// 2 states in our state diagram
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

		// not clear what this is for; apparently it overrides hash function
		// by adding the AllocState so that it is used to calculate the hash
		void Profile(llvm::FoldingSetNodeID &ID) const {
			ID.AddInteger(K);
		}
	};

	class DoubleFreeChecker : public Checker<check::PostCall, check::PreCall> {
		mutable IdentifierInfo *IIfmalloc, *IIffree;

		std::unique_ptr<BugType> DoubleFreeBugType;

		void initIdentifierInfo(ASTContext &Ctx) const;

	private:
		bool checkDoubleFree(SymbolRef Sym, CheckerContext &C, const Stmt *S) const;

		void reportDoubleFree(CheckerContext &C, SourceRange Range,
			SymbolRef Sym) const;

	public:
		DoubleFreeChecker();

		void checkPostCall(const CallEvent &Call, CheckerContext &C) const;

		void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
	};

}

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
}

// If we are malloc'ing, we add it to the AllocationMap of allocated symbols, marking
// it as Allocated. 
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
	if (!Sym)	// malloc somehow failed; just return
		return;

	// Generate the next transition (current Symbol state is now Allocated).
	ProgramStateRef State = C.getState();
	State = State->set<AllocationMap>(Sym, AllocState::getAllocated());
	C.addTransition(State);

	return;
}

// In this visitor, we are checking if we are freeing a symbol for the first
// time, or freeing it for the second time
void DoubleFreeChecker::checkPreCall(const CallEvent &Call, CheckerContext &C) const
{
	initIdentifierInfo(C.getASTContext());

	if (!Call.isGlobalCFunction())
		return;

	// Hook onto free calls only
	if (Call.getCalleeIdentifier() != IIffree)
		return;

	// free() takes in 1 parameter only - pretty much dead code
	if (Call.getNumArgs() != 1)
		return;

	// Get the symbolic value corresponding to the variable.
	SymbolRef Sym = Call.getArgSVal(0).getAsSymbol();
	if (!Sym)
		return;

	// Check if the symbol has already been freed. If we free again
	// then report DoubleFree error
	ProgramStateRef State = C.getState();
	const AllocState *SS = State->get<AllocationMap>(Sym);
	if (SS && SS->isFreed()) {
		reportDoubleFree(C, Call.getSourceRange(), Sym);
		return;
	}

	// Otherwise, this is our first time freeing it.
	// Generate the next transition, in which the symbol is freed
	State = State->set<AllocationMap>(Sym, AllocState::getFreed());
	C.addTransition(State);

	return;
}

DoubleFreeChecker::DoubleFreeChecker()
	: IIfmalloc(nullptr), IIffree(nullptr)
{
	// Initialize the DoubleFree bug type.
	DoubleFreeBugType.reset(
		new BugType(this, "Double free error", "Memory Error"));
}


void DoubleFreeChecker::reportDoubleFree(CheckerContext &C, SourceRange Range,
	SymbolRef Sym) const {
	// We reached a bug, stop exploring the path here by generating a sink.
	ExplodedNode *ErrNode = C.generateSink();

	if (!ErrNode)
		return;

	// Generate the report.
	auto R = llvm::make_unique<BugReport>(*DoubleFreeBugType,
		"Double free error", ErrNode);
	R->addRange(Range);
	R->markInteresting(Sym);
	C.emitReport(std::move(R));
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