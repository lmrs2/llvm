//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include <fstream>
#include <set>
#include <cctype>
 
using namespace llvm;
#define DEBUG_TYPE "Zerostack"

#define LEN(X) sizeof(X)/sizeof((X)[0])

namespace {

  class Zerostack : public FunctionPass {
    
	
    public:
    // variables
    static char ID; // Pass identification, replacement for typeid
    Zerostack() : FunctionPass(ID) {}

	// Use FunctionPass instead of ModulePass because it sometimes crashes when used with EP_EarlyAsPossible
	bool runOnFunction( Function & F ) override {
		
		Module & M = *F.getParent();
		errs() << "Zerostack's module!! " << M.getName()  << " for function " << F.getName() << "\n";

		//for (auto &F : M) {
		//	errs() << "F:" << F << "\n";
		//}	
		// https://homes.cs.washington.edu/~bholt/posts/llvm-quick-tricks.html
		GlobalVariable * global_annos = M.getNamedGlobal("llvm.global.annotations");
		if (global_annos) {
		
			errs() << "global_annos = " << *global_annos << "\n\n";
			
			ConstantArray * CA = cast<ConstantArray>(global_annos->getOperand(0));
			for (unsigned i=0; i<CA->getNumOperands(); i++) {
				ConstantStruct * CS = cast<ConstantStruct>(CA->getOperand(i));
				assert ( CS && "CS is null" );
				errs() << "CS[" << i << "] = " << *CS << "\n\n";
				if (Function * F = dyn_cast<Function>(CS->getOperand(0)->getOperand(0))) {
					
					//errs() << "		F:" << *F << "\n\n";
					StringRef anno = cast<ConstantDataArray>(cast<GlobalVariable>(CS->getOperand(1)->getOperand(0))->getOperand(0))->getAsCString();
					if ( !F->hasFnAttribute(anno) ) {
						errs() << "		Function " << F->getName() << " Added Anno " << anno << "\n";
						errs() << " current attr:" << F->hasFnAttribute(anno) << "\n";
						F->addFnAttr(anno); // add function annotation here. This is used by backend pass to identify sensitive functions
					}
				} 
			}
		}
		
		return true;
	}
  };
}

// clang -Xclang -load -Xclang LLVMZerostack.so file.c -o file
char Zerostack::ID = 0;

// to be able to use it in clang directly
static void registerZerostackPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new Zerostack());

}

// http://llvm.org/doxygen/classllvm_1_1PassManagerBuilder.html
// EP_EarlyAsPossible requires FunctionPass
//static RegisterStandardPasses
//        RegisterMyPass0(PassManagerBuilder::EP_EnabledOnOptLevel0, registerZerostackPass);


// Call pass for all optimization levels
static RegisterStandardPasses RegisterZerostackPass(
     PassManagerBuilder::EP_EarlyAsPossible, registerZerostackPass);

// to be able to use it with opt             
static RegisterPass<Zerostack> X("zerostack", "Zerostack Pass");

#if 0

static void registerZerostack(const PassManagerBuilder &,
						 legacy::PassManagerBase &PM) {
  PM.add(new Zerostack());
}

static RegisterStandardPasses
  RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,	
				 registerZerostack);

// to be able to use it with opt             
static RegisterPass<Zerostack> X("Zerostack", "Zerostack Pass to annotate sensitive functions");
#endif
// INITIALIZE_PASS_BEGIN(Zerostack, "zerostack",
// 				"Zerostack pass", false, false)
// //INITIALIZE_PASS_DEPENDENCY(LazyValueInfo)
// //INITIALIZE_PASS_DEPENDENCY(TargetLibraryInfoWrapperPass)
// INITIALIZE_PASS_END(Lolo, "zerostack",
// 				"Zerostack pass", false, false)

//ModulePass *llvm::createZerostackPass() { return new Zerostack(); }
// Initialization Routines
// void llvm::initializeInstCombine(PassRegistry &Registry) {
//   initializeInstructionCombiningPassPass(Registry);
// }

// void LLVMInitializeInstCombine(LLVMPassRegistryRef R) {
//   initializeInstructionCombiningPassPass(*unwrap(R));
// }

// FunctionPass *llvm::createInstructionCombiningPass() {
//   return new InstructionCombiningPass();
// }
