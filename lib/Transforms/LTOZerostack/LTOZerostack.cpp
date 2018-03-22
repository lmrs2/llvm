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

#define LTO_BUILD 1
#if LTO_BUILD
#	include "llvm/Transforms/LTOZerostack.h"
#	include "llvm/Support/CommandLine.h"
#	include "llvm/IR/InlineAsm.h"

#	define TYPE	"type_annotate_"

//static bool IsLibc = true;

#endif

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

/**
 * 
 * http://www.cs.ucr.edu/~benavidz/cs201_spring15/project.html for code
 * https://github.com/sampsyo/llvm-pass-skeleton/blob/master/skeleton/Skeleton.cpp for the registration of the pass
 * 
 * compile example code:
 * 	clang -O0 -emit-llvm -c welcome.cpp -o welcome.bc
 * 
 * compile pass:
 * 	$cmake --build . --target LLVMLTOZerostack
 * 
 * run pass:
 * 	$opt -load $LLVMLIB/LLVMLTOZerostack.so -LTOZerostack < $BENCHMARKS/welcome/welcome.bc > $BENCHMARKS/welcome/welcome.bc2
 * 
 * compile example and includes my pass
 * 	$clang -Xclang -load -Xclang $LLVMLIB/LLVMLTOZerostack.so welcome.cpp
 * 
 * run it:
 * 	$./a.out
 * 
 * check passes run with optimizations:
 * 	$llvm-as < /dev/null | opt -OX -disable-output -debug-pass=Arguments
 * 	$clang -mllvm -debug-pass=Arguments welcome.cpp 
 * 
 */
 
using namespace llvm;
#define DEBUG_TYPE "LTOZerostack"

#define LEN(X) sizeof(X)/sizeof((X)[0])

//STATISTIC(LTOZerostackCounter, "Counts number of functions greeted");
#if LTO_BUILD
	//static cl::opt<std::string> OutputFilename("zs-metafile", cl::desc("Specify output metafile name"), cl::value_desc("noname"));
	//static cl::opt<bool> OutputFilename("LTOZerostack-debug-info", cl::init(true));
	//static cl::opt<unsigned> OutputFilename(
    //"LTOZerostack-threshold", cl::init(16), cl::Hidden,
    //cl::desc("The maximum number of SCEV checks allowed."));
    //cl::opt<std::string> OutputFilename("LTOZerostack", cl::desc("Specify output filename"), cl::value_desc("filename"));
#endif

namespace {
	
  // LTOZerostack - The first implementation, without getAnalysisUsage.
  class LTOZerostack : public ModulePass {
    
    class CFGNode {
		public:
			
			typedef StringMapIterator<CFGNode*> iterator;
		
			CFGNode(StringRef R, size_t n = 16) {
				Name = R;
				isChild = false;
				isExternal = true;
				isVisited = false;
				isAnnotation = false;
				ChildMap = new StringMap<CFGNode*>(n);
				assert ( ChildMap && "Cannot allocate ChildMap" );
			}
			
			// Note: we don't delete the elements, this is done thru the hash map FunctionMap
			virtual ~CFGNode() {
				if ( ChildMap ) {
					delete ChildMap;
				}
			}
			
			bool hasChild() { return (ChildMap->size() > 0); }
			bool hasParent() { return isChild; }
			bool getVisited() { return isVisited; }
			void setVisited(bool a) { isVisited = a; }
			void setParent(bool a) { isChild = a; }
			void setExternal(bool a) { isExternal = a; }
			bool getExternal() { return isExternal; }
			void setAnnotation(bool a) { isAnnotation = a; }
			bool getAnnotation() { return isAnnotation; }
			
			void setName(StringRef N) { Name = N; }
			StringRef getName() { return Name; }
			void addChild( CFGNode * node ) {
				assert (node);
				ChildMap->insert( std::pair<StringRef, CFGNode*>(node->Name, node) );
				
			}
			
			
			CFGNode* getChild(StringRef Name) {
				if ( ChildMap ) {
					return ChildMap->lookup(Name);
				}
				return NULL; 
			}
			
			iterator begin() { return ChildMap->begin(); }
			iterator end() { return ChildMap->end(); }
			
		private:
			std::string Name;
			StringMap<CFGNode*>* ChildMap;	// this class's ownership
			bool isChild;
			bool isExternal = true;
			bool isVisited = false;	// I add this for aliases
			bool isAnnotation = false;	// I add this for annotation
	};
	
	std::set<StringRef>  AnnotationSet;	// all know annotation kept here
    StringMap<CFGNode*> FunctionMap;	// all the nodes kept here, fast access, simple deletion
    //StringMap<StringRef> AliasMap;
    
    CFGNode * newNode(StringRef N) {
		CFGNode * n = new CFGNode(N);
		assert (n && "Cannot allocate node");
		assert ( 0 == ListAllFunctions(N) );
		FunctionMap.insert( std::pair<StringRef, CFGNode*>(n->getName(), n) );
		return n;
	}
	
	void deleteNodes() {
		for ( auto & it : FunctionMap ) {
			CFGNode *n = it.getValue(); // getKey()
			errs() << "Deleting node " << n->getName() << "\n";
			delete n;
		}
		FunctionMap.clear();
	}
	
	CFGNode * ListAllFunctions( StringRef N ) {
		return FunctionMap.lookup( N );
	}
	
	
	//bool FunctionAlreadyProcessed( StringRef Name ) {
	//	return (1 == FunctionMap.count(Name) );
	//}
    
    // =================================
    
    LLVMContext *mContext = NULL;
    //Module *Mod = NULL;
    GlobalVariable *mBranchCounter = NULL;
    GlobalVariable *mTrueCounter = NULL;
    GlobalVariable *mFalseCounter = NULL;
    //GlobalVariable *BasicBlockPrintfFormatStr = NULL;
    Function *mPrintf_func = NULL;    
    // for stack zeroing
    
    public:
    // variables
    static char ID; // Pass identification, replacement for typeid
    LTOZerostack() : ModulePass(ID) {
#if LTO_BUILD
		// initializeLTOZerostackPass is defined by the MACRO INITIALIZE_PASS_BEGIN and INITIALIZE_PASS_END
		initializeLTOZerostackPass(*PassRegistry::getPassRegistry());
#endif
	}

	// https://github.com/thomaslee/llvm-demo/blob/master/main.cc
	static Function* printf_prototype(LLVMContext& ctx, Module *mod) {
		std::vector<Type*> printf_arg_types;
		printf_arg_types.push_back(Type::getInt8PtrTy(ctx));

		FunctionType* printf_type = FunctionType::get(Type::getInt32Ty(ctx), printf_arg_types, true);
		Function *func = mod->getFunction("printf");
		if(!func)
			func = Function::Create(printf_type, Function::ExternalLinkage, Twine("printf"), mod);
		func->setCallingConv(CallingConv::C);
		return func;
	}
  
	// use -analyze with opt to call this
	virtual void 	print (raw_ostream &O, const Module *M) const {
		
		outs() << "Hello outs()\n"; 
		O << "Hello O"; 
		errs() << "Hello errs()\n";
	}
	
	#if !LTO_BUILD
	//----------------------------------
    bool doInitialization(Module &M) {
		
		errs() << "\n---------Starting BasicBlockDemo---------\n";
		return false;
		mContext = &M.getContext();
		mBranchCounter 	= new GlobalVariable(M, Type::getInt32Ty(*mContext), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*mContext), 0), "mBranchCounter");
		mTrueCounter 	= new GlobalVariable(M, Type::getInt32Ty(*mContext), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*mContext), 0), "mTrueCounter");
		mFalseCounter 	= new GlobalVariable(M, Type::getInt32Ty(*mContext), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*mContext), 0), "mFalseCounter");
		
		mPrintf_func = printf_prototype(*mContext, &M);
		/*const char *finalPrintString = "BB Count: %d\n";
		Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
		BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), 
														strlen(finalPrintString)+1), true, 
														llvm::GlobalValue::PrivateLinkage, 
														format_const, "BasicBlockPrintfFormatStr");
		printf_func = printf_prototype(*Context, &M);
		Mod  = &M;
		
		
		errs() << "Module: " << M.getName() << "\n";
		*/
		return true;
    }
    
     //----------------------------------
    bool doFinalization(Module &M) {
		errs() << "-------Finished BasicBlocksDemo----------\n";
		return false;
    }
    #endif	// LTO_BUILD
    //-----------------------------------
    #if 0
    bool runOnModule( Module & M ) /*override*/ {
		
		// https://homes.cs.washington.edu/~bholt/posts/llvm-quick-tricks.html
		auto global_annos = M.getNamedGlobal("llvm.global.annotations");
		if (global_annos) {
		  auto a = cast<ConstantArray>(global_annos->getOperand(0));
		  for (int i=0; i<a->getNumOperands(); i++) {
			auto e = cast<ConstantStruct>(a->getOperand(i));

			if (auto fn = dyn_cast<Function>(e->getOperand(0)->getOperand(0))) {
			  auto anno = cast<ConstantDataArray>(cast<GlobalVariable>(e->getOperand(1)->getOperand(0))->getOperand(0))->getAsCString();
			  //outs() << "Function " << fn->getName() << " Added Anno " << anno << "\n";
			  fn->addFnAttr(anno); // <-- add function annotation here
			  
			  runOnFunction(*fn);
			}
		  }
		}
		return true;
	}
	#endif
	
	bool runOnModule( Module & M ) override {
		
		// LLVMgold plugin is loaded in function AddGoldPlugin() of file ../tools/clang/lib/Driver/Tools.cpp
		
		errs() << "LTOZerostack's module!!" << M.getName() << "\n";

		//return false;
		// https://homes.cs.washington.edu/~bholt/posts/llvm-quick-tricks.html
		#if 0
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
					errs() << "		Function " << F->getName() << " Added Anno " << anno << "\n";
					F->addFnAttr(anno); // add function annotation here. This is used by backend pass to identify sensitive functions
					AnnotationSet.insert( anno );	// I think this is not used anymore
				} 
			}
		}
		#endif
		
		//return true; //cpmpile this file aside and launch it explicitely with load like the clang plugin/ This way no need to recompile it all...
		//assert (0);
		
		/*** list ALIAS from the module
		// first, let's get the aliases
		// WARNING: cannot add these here, otherwise I will miss the function CFG in runOnFunction
		// as the function will appear as already visited
		for (auto I = M.alias_begin(), E = M.alias_end(); I != E;) {
			GlobalAlias &GV = *I++;
			const Constant * Alias = GV.getAliasee();
			Type *Atype = Alias->getType();
			if ( Atype->isPointerTy() && Atype->getPointerElementType()->isFunctionTy() ) {
				// we have a pointer to a function, get the base object
				// Note: probably we don't need to do the test aboves, and we could just try to dyn_cast
				// I still keep it for consistency; and also I think it's faster :)
				const GlobalObject * GO = GV.getBaseObject();
				if ( const Function *AF = dyn_cast<Function>(GO) ) {
					errs() << GV.getName() << " is an function alias to " << AF->getName() << "\n";
					//AliasMap.insert( std::pair<StringRef, StringRef>(GV.getName(), AF->getName()) );
				}
			}
		}
		**/
		
		//const ValueSymbolTable & VST = 	M.getValueSymbolTable ();
		//for ( auto & V : VST ) {
		//	errs() << *V.getValue() << "\n";
		//}
		
		/*
		CFGNode * node = newNode("LTOZerostack node");
		CFGNode * n1 = newNode("child 1");
		CFGNode * n2 = newNode("child 2");
		CFGNode * n3 = 0;;
		node->addChild(n1);
		node->addChild(n2);
		node->addChild(n2);
		n2->addChild(n1);
		
		for ( auto& F : M ) {
			runOnFunction(F, "");
		}
		// get a child
		if ( (n3 = node->getChild(n1->getName())) ) {
			errs() << "child " << n3->getName() << "\n";
		}
		// iterate thru all of them
		for ( auto & it : FunctionMap ) {
			CFGNode *n = it.getValue();
			errs() << "child " << n->getName() << " is there\n";
		}
		
		deleteNodes();
		*/
		//assert ("We're here" && 0);
		
		for ( auto& F : M ) {
			_runOnFunction(F);
		}

		//assert (0 && "help debug");
		// now let's print the CFG
		// reset the visited
		#define RESET_VISTED \
				for ( auto & it : FunctionMap )  {	\
					CFGNode *n = it.getValue();	\
					n->setVisited(false);			\
				}	
		
		RESET_VISTED
				
		for ( auto & it : FunctionMap ) {
			CFGNode *n = it.getValue();
			printNode( n, "" );
			//errs() << "Node " << n->getName() << " is there\n";
		}
		
		// check one function we're interested in, say "main"
		RESET_VISTED
		printNode(ListAllFunctions("main"), "");
		
		//assert ( OutputFilename.length() != 0 && "Empty --zs-metafile option. Did you pass -Xclang ?" );
		//errs() << "fn:" << OutputFilename << "\n";
		//assert(0);
		MarshallToFile("/tmp/metafile_pass");
		
		deleteNodes();
		//assert(0);
		return false;
	}
	
	void MarshallToFile(StringRef filename) {
		// f1:f2,f3,f4
		std::fstream outfs;
		int err = -1;
		do {
			err = remove( filename.str().c_str() );
		} while (err < 0 && errno == EINTR);
		// also delete the file used by the MachineFunction pass, as we cannot use a MachineModulePass
		do {
			std::string mfilename = filename;
			mfilename.append(".machine");
			err = remove( mfilename.c_str() );
		} while (err < 0 && errno == EINTR);
		
		// i trust this input file, no path validation for now :)
		outfs.open(filename.str().c_str(), std::fstream::out);
		assert ( outfs.is_open() );
		
		for ( auto & it : FunctionMap ) {
			CFGNode *n = it.getValue();
			if ( !n->getExternal() /*|| n->getAnnotation()*/ ) {
				errs() << n->getName() << ":";
				outfs << n->getName().str() << ":";
				for ( CFGNode::iterator it = n->begin(), eit = n->end(); eit != it; ++it ) {
					errs() << it->getValue()->getName() << ",";
					outfs << it->getValue()->getName().str() << ",";
				}
				errs() << "\n";
				outfs << "\n";
			} 
		}
		
		outfs.close();
	}
	
	
	// ---------------------------------
	void printNode(CFGNode * n, Twine Ident) {
		
		if ( n ) {
			
			// stop if already visited. Note that I should put this check in the for-loop to avoid an unnecessary call
			// but i put it here for printing it
			if ( n->getVisited() ) {
				errs() << Ident << "Node " << n->getName() << " ALREADY VISITED\n";
				return;
			}
			
			errs() << Ident << "Node " << n->getName() << "\n";
			
			// the the node visited
			n->setVisited( true );
			
			for ( CFGNode::iterator it = n->begin(), eit = n->end(); eit != it; ++it ) {
				// recurse only if the function is not recursive
				if ( n != it->getValue() ) {
					printNode( it->getValue()	, Ident + " " );
				}
			}
		}
	}
	
	/*bool DoesNotRecurseByDev( std::string name ) {
	
		// although doesNotRecurse return false for the below functions, I think they don't...
		// closer look is necessary for real deployment
		return (
				name.substr(0,4) == "aio_"	||
				name.substr(0,6) == "__aio_"||
				name == "submit" 			||	// submit is used by aio_read/write/etc, definition in same file
				name == "io_thread_func"	||	// used by aio_ code as a function pointer
				name.substr(0,4) == "sem_"	||
				name == "__timedwait_cp"	||
				name == "__clock_gettime"	||
				name == "__syscall_cp"		||	// Note: this function just calls __syscall
				name == "__syscall_cp_asm"	||	// Note: this function does update the stack but accesses it only upward rsp+N
				name == "__syscall"			||	// Note: this function does update the stack but accesses it only upward rsp+N
				name == "pthread_rwlock_timedrdlock"
		);		
	}*/
	
	/*	now cycle is detected in python script
	 * bool IsLibcRecursiveFunction( StringRef Fname ) {
	
		// recursive libc functions
		return  ( 
		
			// regcomp.c
			Fname.str().substr(0,15) == "tre_stack_push_" || // unsupported group of functions that push stuff on stack
			Fname == "tre_stack_push" || 	// unsupported
			Fname == "parse_atom"	||
			Fname == "tre_ast_to_tnfa" ||
			// tdestroy.c
			Fname == "tdestroy"	||
			//tsearch_avl.c
			Fname == "remove.755"	||
			Fname == "remove_rightmost"	||
			Fname == "remove_leftmost"	||
			Fname == "insert"	||
			Fname == "walk"	||
			// fmemopen.c
			Fname == "mwrite"	||
			// open_memstream.c
			Fname == "ms_write"	||
			// vswprintf.c
			Fname == "sw_write"	||
			// strptime.c
			Fname == "strptime"	||
			// glob.c
			Fname == "match_in_dir"	|| // not supported
			// ... file roughly= function name :)
			Fname == "frexpl" 	||	// not supported	
			Fname == "frexp" 	||	// not supported	
			Fname == "frexpf" 	||	// not supported	
			Fname == "mbrtoc16" ||	// not supported	
			Fname == "inet_pton" || // not supported - maybe it calls itself only once, not sure through a quick glance
			Fname == "do_nftw" ||	// not supported	
			Fname == "iconv" 	||	// not supported	
			Fname == "fflush" 	||			// at most two nested calls, so multiply stack use by 2 in python
			Fname == "getservbyport_r" || 	// at most two nested calls, so multiply stack use by 2 in python
			Fname == "evalexpr" ||			// used to parse the GNU message catalog (https://ftp.gnu.org/old-gnu/Manuals/glibc-2.2.3/html_chapter/libc_8.html)
			Fname == "evalbinop" ||			// eg files under /usr/share/locale/en_GB/LC_MESSAGES/
			Fname == "evalprim" 			// functions such as dcngettext (http://linux.die.net/man/3/dgettext) do use them
		
		);	
	}*/
	
	StringRef getCallAnnotation(const Value *V) {
	
		if (auto *I = dyn_cast<Instruction>(V)) {
			MDNode *MD = I->getMetadata("tyann");
			if (MD) {
				auto *MDS = cast<MDString>(MD->getOperand(0));
				errs() << "MD:" << MDS->getString() << "\n";
				return MDS->getString();
			}
		}
		return StringRef();
	}
	
	//----------------------------------
	bool _runOnFunction(Function &F ) {
		
		//errs() << F.getName() << " " << F.isDeclaration() << " " << F.isIntrinsic() << " " << F.doesNotRecurse() << '\n';
		
		// for now, assume none of these function  use the stack
		// TODO: check intrinsic function's use of the stack
		if ( F.isIntrinsic() ) { return false; }
		// i dont use this, coz it flags virtually all functions :)
		//if ( IsLibc ) {
		//	assert ( ( F.doesNotRecurse() || DoesNotRecurseByDev( F.getName() ) )			
		//			&& "Recursive LIBC function found" 	);
		//}
		
		//if ( F.hasFnAttribute("hash_function") ) {
		//	errs() << "F " << F.getName() << " has annotation async\n";
		//	errs() << F << "\n";
		//	//assert (0);
		//}
		
		//if ( F.getName() == "syscall" ) {
		//	errs() << F << "\n";
		//	assert (0);
		//}
		
		CFGNode * ThisNode = 0;
		DILocation *Loc = 0;
		if ( (ThisNode = ListAllFunctions( F.getName() )) == NULL ) { 
			// function never visited or called
			ThisNode = newNode( F.getName() );
		}
		
		// at this point the node should NEVER have been visited
		assert ( ThisNode && !ThisNode->getVisited() );
		
		// Note: we could just move this line to inside the for loop below
		// since it will enter it iff we have the definition of the function.
		ThisNode->setExternal( F.isDeclaration() );
		ThisNode->setVisited( true );	// now we've visited it
		// get the attribute
		// TODO: change representation to store in the same line as the function as fname[@ANNO_anno]:foo1,foo2,etc
	#if 0	// is this still relevant?
		for ( StringRef Anno : AnnotationSet ) {
			if ( F.hasFnAttribute( Anno ) ) {
				errs() << F.getName() << " has attribute " << Anno << "\n";
				CFGNode * annoNode = 0;
				StringRef annoName = "@ANNO_" + Anno.str();
				if ( !(annoNode = ListAllFunctions( annoName ) ) ) {
					annoNode = newNode( annoName );
					annoNode->setAnnotation(true);
				}
								
				assert ( annoNode && "annoNode is null" );
				// a child, for an annotation node, is simply a function that is tagged with the annotation's name
				annoNode->addChild( ThisNode );
			}
		}
	#endif			
		// once only for each function
		// errs() << Ident << F.getName() << " " << F.isDeclaration() << " " << F.isIntrinsic() << " " << F.doesNotRecurse() << '\n';
		
		for (auto& B : F) {
						
			//errs() << "BB:" << B;			
			for (auto& I : B) {
				
				// http://llvm.org/docs/SourceLevelDebugging.html
				//if (!Loc && (Loc = ((Instruction*)&I)->getDebugLoc()) ) {
				//	unsigned Line = Loc->getLine();
				//	StringRef File = Loc->getFilename();
				//	StringRef Dir = Loc->getDirectory();
				//	errs() << File << " " << Dir << " " << Line << "\n";
				//}
				//errs() << "I:" << I << "\n";
				//continue;
				if ( auto* CI = dyn_cast<CallInst>(&I) ) {					
				  
					//errs() << "*** isCallInst:" << *CI << "\n";
					//errs() << CI->isInlineAsm() << "\n";
					//errs() << *CI->getCalledValue() << "\n";
					//for ( unsigned i = 0; i< CI->getNumArgOperands() ; ++i ) {
					//	errs() << "args " << i << " is " << *CI->getArgOperand(i) << "\n";
					//}
					
					if ( CI->isInlineAsm() ) {
						//errs() << "is INLINEASM:" << *CI << "\n";
												
						// TODO: get the registers used in the Machinepass or here? i prefer machine pass
						InlineAsm * IASM = dyn_cast<InlineAsm>(CI->getCalledValue());
						std::string ASMStr = IASM->getAsmString();
						std::transform(ASMStr.begin(), ASMStr.end(), ASMStr.begin(), ::tolower); // make everything lower case
						assert (IASM && "IASM is null");
						//errs() << "IASM:" << ASMStr << "\n"; 
						//errs() << "side effects:" << IASM->hasSideEffects() << "\n";
						//errs() << "constraints:" << IASM->getConstraintString() << "\n";
					#if 0
						InlineAsm::ConstraintInfoVector CIV = InlineAsm::ParseConstraints(IASM->getConstraintString());
						for ( InlineAsm::ConstraintInfo& CInfo : CIV ) {
							//errs() << "type:" << CInfo.Type << "\n";
							if ( InlineAsm::isOutput == CInfo.Type || InlineAsm::isClobber == CInfo.Type ) {
								for ( std::string & code : CInfo.Codes ) {
									//errs() << "code:" << code << "\n";
									assert ( code.find("rsp") == std::string::npos	&&
											code.find("esp") == std::string::npos	&&
											"Handwritten assembly changes the stack");
									
									// WARNING: this does not handle all possible cases :(
									// TODO: check in x86 backend
									//assert ( ASMStr.find("push") == std::string::npos	&&
									//		 ASMStr.find("pop") == std::string::npos	&& 
									//		 "Handwritten assembly changes the stack (2)");
									
									// check for push, sub e/rsp
								}
							}
						}
					#endif
						
						// check for use of esp/rsp. Note: this will also contain reads and not just writes
						if ( !( ASMStr.find("esp") == std::string::npos && ASMStr.find("ESP") == std::string::npos &&
								ASMStr.find("rsp") == std::string::npos && ASMStr.find("RSP") == std::string::npos) ) {
								
								errs() << "F:" << F << "\n";
								errs() << "B:" << B << "\n";
								errs() << "INLINEASM:" << *IASM << "\n";
								errs() << F.getName() << "\n";
								
								// this is too broad, deference of stack pointer also cautch here... REMOVED so we can compile :)
								// just a hack for sanity check for now... we don;t support asm anyway
								//if ( ! (IsLibc && F.getName() == "cleanup") ) {
								//	assert ( 0 && "Handwritten assembly uses esp/rsp");
								//}
						}
								
						if ( !( ASMStr.find("push") == std::string::npos && ASMStr.find("PUSH") == std::string::npos ) ) {
						
								errs() << "F:" << F << "\n";
								errs() << "B:" << B << "\n";
								errs() << "INLINEASM:" << *IASM << "\n";
								errs() << F.getName() << "\n";
								
								// Note: if we find this in real code, we can conservatively assume it's 8 bytes on x86_64
								// We can add a stack size to a Node, and get the backend pass to add its value to it
								assert ( 0 && "Handwritten assembly uses push");
						
						}
						// Note: if we're here, the handwritten assembly did not
						// alter the stack
						
						// we don't want a jmp except in certain libc functions for the time being
						// list of function i've checked and jump into the "same" function, so are fine... just a hack :)
						// or call something that does not alter the stack
						// anyway, we said we don't support asm at the moment
						std::vector<std::string> ListJMPFunctionsOK = {"aes_setkey_enc", "aesni_setkey_enc", "aesni_crypt_ecb", "aes_crypt_ecb"};
						if ( ! isMuslStartFunction( F.getName() ) ) {
							
							// don't check tail call as all ASM calls are considered tail calls
							// jmp are OK so long as they jump within the function
							// http://unixwiz.net/techtips/x86-jumps.html
							std::vector<std::string> JMPList = {"JO","JNO", "JS", "JNS", "JE", "JZ", "JNE", "JZE", "JB", "JNAE", "JC", "JNB", "JAE", "JNC", "JBE", "JNA", "JA", "JNBE", 
														"JL", "JNGE", "JGE", "JNL", "JLE", "JNG", "JG", "JNLE", "JP", "JPE", "JNP", "JPO", "JCXZ", "JECXZ", "JMP"};
							for ( std::string jmp : JMPList ) {
								jmp += " ";
								std::transform(jmp.begin(), jmp.end(), jmp.begin(), ::tolower); // make everything lower case	
								
								// jmp 1f, b1 explained https://docs.oracle.com/cd/E19253-01/817-5477/6mkuavhra/
								if ( ASMStr.find(jmp) != std::string::npos && !Contains(ListJMPFunctionsOK,F.getName())  ) {
									errs() << "F:" << F << "\n";
									errs() << "B:" << B << "\n";
									errs() << "INLINEASM:" << *IASM << "\n";
									errs() << "jmp:" << jmp << "\n";
									errs() << F.getName() << "\n";
									assert ( 0 && "Found JMP instruction in handwritten assembly" );
								}
								
							}
							
						}
						
						// we don't want calls coz we must follow them
						// TODO: refine this by 1) alowing jmp assuming within function, and 2) get callee info
						//... but "call" may be from syscall ...
						// I though of looking for "call " but it may also be possible to have "syscall "
						// these function are OK, i the sense that the function (block) they call don't change the stack pointer
						std::vector<std::string> ListCALLFunctionsOK = {"aes_setkey_enc", "aesni_setkey_enc"};
						size_t pos = ASMStr.find("call", 0); // fist occurrence
						while(pos != std::string::npos) {
							if ( !( (pos >= 3 && ASMStr.substr(pos-3, 7) == "syscall" ) || Contains(ListCALLFunctionsOK,F.getName()) ) ) {
								errs() << "F:" << F << "\n";
								errs() << "B:" << B << "\n";
								errs() << "INLINEASM:" << *IASM << "\n";
								errs() << ASMStr.substr(pos-3, 7) << "\n";
								errs() << F.getName() << "\n";
								assert ( 0 && "Found not syscall" );
							}
							assert ( (pos >= 3 && ASMStr.substr(pos-3, 7) == "syscall") || Contains(ListCALLFunctionsOK,F.getName()) );
							pos = ASMStr.find("call", pos+1);
						}
						
						// get syscall, sub e/rsp, push
						//if ( ASMStr.find("mov") == 0 ) return false;
						// if there a syscall we want to keep in our tree?
						// Note: this is just to help validate the CFG, we don't use it
						// to increment the stack size
						// TODO: int 0x80
						assert ( ASMStr.find("int ") == std::string::npos );
						if ( ASMStr.find("syscall") == std::string::npos ) { continue; }
						
						// I use @INSTRUCTION_SYSCALL, coz musl does have a function called syscall
						// Note: we don't need to check for non-asm code for this name since it can only be called via asm
						std::string syscallInst = "@INSTRUCTION_SYSCALL";
						assert ( F.getName() != syscallInst && "Found recursive function in inline asm" );
						
						// create the node only if it does not exist
						CFGNode * asmNode = 0;
						if ( !(asmNode = ListAllFunctions( /*IASM->getAsmString()*/ syscallInst ) ) ) {
							asmNode = newNode( /*IASM->getAsmString()*/ syscallInst );
						} 
						
						assert ( asmNode && "asmNode is null" );
						ThisNode->addChild( asmNode );
						
						
					} else {
						
						// we don't care about tail calls. We can still compute the CFG and registers
						
						// get the callee
						Function * Callee = CI->getCalledFunction();
						if ( Callee ) {
							
							// we let them go through, but will catch them in the python script
							// TODO: detect the cycle in python code
							//if ( IsLibc && IsLibcRecursiveFunction( Callee->getName() ) ) { continue; }															
							
							// print so we know which function failed recursive test
							// if ( Callee->getName() == F.getName() ) {
							//	errs() << "F:" << F << "\n";
							//	errs() << "B:" << B << "\n";
							//	errs() << Callee->getName() << "\n";
							//}
							
							// check for recursive function - now cycle detected in python script
							// assert ( Callee->getName() != F.getName() && "Found recursive function in Callee" );
							
							CFGNode * calleeNode = 0;
							if ( !(calleeNode = ListAllFunctions( Callee->getName() ) ) ) {
								calleeNode = newNode( Callee->getName() );
							} 
							
							assert ( calleeNode && "calleeNode is null" );
							ThisNode->addChild( calleeNode );
							
						} else {
							
							
							const Value * CV = CI->getCalledValue();
							assert ( CV && "CV is null" );
							Type *Atype = CV->getType();
														
							// this may be an alias to another function, try to get it
							if ( const GlobalAlias * GA = dyn_cast<GlobalAlias>(CV) ) {
																
								const Constant * Alias = GA->getAliasee();
								
								assert (Alias && "Alias is null");
								
								Type *Atype = Alias->getType();
								
								assert ( Atype->isPointerTy() && Atype->getPointerElementType()->isFunctionTy() && "Alias not a pointer to function" );
								
								// we have a pointer to a function, get the base object
								// Note: probably we don't need to do the test aboves, and we could just try to dyn_cast
								// I still keep it for consistency; and also I think it's faster :)
								const GlobalObject * GO = GA->getBaseObject();
								
								assert (GO && "GO is null");
								
								const Function *AF = dyn_cast<Function>(GO);
								assert (AF && "AF is null");
								
								errs() << GA->getName() << " is an function alias to " << AF->getName() << "\n";
								
								// check for recursive function - now cycle detected in python script
								// assert ( GA->getName() != F.getName() && AF->getName() != F.getName() && "Found recursive function in GlobalAlias" );
								
								CFGNode * aliasNode = 0;
								if ( !(aliasNode = ListAllFunctions( AF->getName() ) ) ) {
									aliasNode = newNode( AF->getName() );
								} 
								
								assert ( aliasNode && "aliasNode is null" );
								ThisNode->addChild( aliasNode );
									
								
								
							} else if ( Atype->isPointerTy() && Atype->getPointerElementType()->isFunctionTy() ){
								// WARNING: we should still accept non-annotated poipnters/function so long
								// 			 as it's not in the CFG of sensitive functions:TODO
								//			 for this i will just mark a call to an unknown function, and check it in python script
								
								//errs() << "F:" << F << "\n";
								//errs() << "B:" << B << "\n";
								//errs() << "CI:" << *CI << "\n";
								//errs() << F.getName() << "\n";
								//assert ( 0 && "Unsupport pointer to function" );
								
								// get the annotation. First from the called value. If none, try the call instruction itself
	//errs() << "getCallAnnotation from CV:" << *CV << "\n";
								StringRef FPAnno = getCallAnnotation( CV );
								if ( FPAnno == "" ) { FPAnno = getCallAnnotation( CI ); }
//							errs() << "getCallAnnotation from CI:" << *CI << "\n";	
//errs() << "Parent:" << *CI->getParent()->getParent() << "\n";
								if ( FPAnno == "" ) {
								
									CFGNode * unknownNode = 0;
									StringRef unknownName = "@UNKNOWN_POINTER";
									if ( !(unknownNode = ListAllFunctions( unknownName ) ) ) {
										unknownNode = newNode( unknownName );
									} 
									
									assert ( unknownNode && "unknownNode is null" );
									ThisNode->addChild( unknownNode );
									
									// TODO: emit a warning
									//errs() << "F:" << F << "\n";
									//errs() << "B:" << B << "\n";
									//errs() << "CI:" << *CI << "\n";
									//errs() << F.getName() << "\n";
									//assert(0);
									
								} else {
									// TODO: has annotation
									errs() << "Got annotation:" << FPAnno << "\n";
									
									CFGNode * gpNode = 0;
									StringRef gpName = (Twine("@ANNOTATED_POINTER_") + Twine(FPAnno)).str();
									if ( !(gpNode = ListAllFunctions( gpName ) ) ) {
										gpNode = newNode( gpName );
									} 
									
									assert ( gpNode && "gpNode is null" );
									ThisNode->addChild( gpNode );
									errs() << "gpName:" << gpName << "\n";
									//assert (0); 
								}
														
								/**
								  below is what a call to a function marked with annotation str.2 looks like... the simplest form i'm looking for :)
								  * Note: if this is not as simple, then we'll have to use def-use chain somehow...?
								  %5 = call i8* @llvm.ptr.annotation.p0i8(i8* %.pre3, i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.2, i64 0, i64 0), i8* getelementptr inbounds ([11 x i8], [11 x i8]* @.str.3, i64 0, i64 0), i32 46)
								  %6 = bitcast i8* %5 to i32 (...)**
								  %7 = load i32 (...)*, i32 (...)** %6, align 8, !tbaa !5
								  %call2 = call i32 (...) %7() #5

								 */
								 
								 #if 0
								// this gets the %7 = load i32 (...)*, i32 (...)** %6, align 8, !tbaa !5
								const LoadInst *LI = dyn_cast<LoadInst>(CV);
								assert ( LI && "LI is null");	// of the struct is not annotated, this will return 0. We should allow it after testing :)
								errs() << "LI:" << *LI << "\n";
								
								// this gets the %6
								const BitCastInst * BCI = dyn_cast<BitCastInst>( LI->getPointerOperand() );
								assert (BCI && "BCI is null");
								errs() << "BCI:" << *BCI << "\n";
								
								// this gets the %5
								const CallInst * CIA = dyn_cast<CallInst>( BCI->getOperand(0) );
								assert ( CIA && "CIA is null" );
								errs() << "CIA:" << *CIA << "\n";
								
								// validate the function name
								Function * ICallee = CIA->getCalledFunction();
								assert ( ICallee && "ICallee is null" );
								assert ( ICallee->isIntrinsic() && "ICallee not intrinsic" );
								assert ( ICallee->getName() == "llvm.ptr.annotation.p0i8" );
								errs() << "ICallee:" << *ICallee << "\n";
								
								// this gets the @.str.2 which is the annotation							
								// http://lists.llvm.org/pipermail/llvm-dev/2011-January/037534.html
								std::string anno = dyn_cast<ConstantDataArray>( dyn_cast<GlobalVariable>( dyn_cast<ConstantExpr>( CIA->getOperand(1) ) ->getOperand(0) ) ->getOperand(0) ) ->getAsCString();
								errs() << "anno:" << anno << "\n";
								
								CFGNode * annoNode = 0;
								StringRef annoName = "@ANNO_" + anno;
								if ( !(annoNode = ListAllFunctions( annoName ) ) ) {
									annoNode = newNode( annoName );
									annoNode->setAnnotation(true);
								} 
								
								assert ( annoNode && "annoNode is null" );
								ThisNode->addChild( annoNode );
								#endif
								
							} else {
								assert ( 0 && "Unsupported call object" );
							}
							
						}					
						
					}
					
					//errs() << F.getName() << " -> " << Callee->getName() << "\n";
					//Type * type = Callee->getType();
					//errs() << "getType:" << *type << "\n";
					//errs() << "getValueName:" << CI->hasName() ? CI->getValueName() : "(none)"<< "\n";
					//errs() << "getName:" << Callee->getName() << "\n";

					//assert(0);
				}
			}
		
		}
		return true; 
    }
    
    // utility function to find if an item is in a vector
    template <class Container> 
	const bool Contains(Container& container, const typename Container::value_type& element) {
		return std::find(container.begin(), container.end(), element) != container.end();
	}
    
    // copy from backend pass
    bool isMuslStartFunction ( StringRef Name ) {
	  //errs() << "Name:" << Name << "\n";
	  // should check the module name too...
	if ( "_start_c" == Name	||
		 "__libc_start_main" == Name ||
		 "__dls2" == Name ||
		 "__dls3" == Name ||
		 Name == "_start" ||
		 Name == "__init_libc" ||
		 "__libc_start_init" == Name ||
		 "do_init_fini" == Name) {
		return true;
	}
	return false;
  }
    
    //----------------------------------
    bool runOnFunction(Function &F) /*override*/ {
		//errs() << "Function: " << F.getName() << '\n';

		//AttributeSet AttSet = F.getAttributes();
		//AttSet.dump();
		/*for ( unsigned Slot = 0; Slot < AttSet.getNumSlots(); ++Slot ) {
			
			std::string AttrName = AttSet.getAsString(Slot);
			errs() << F.getName()  << " Attr:" << AttrName << "\n";
			if ( "LTOZerostack" == AttrName ) {
				errs() << "Found att for function " << F.getName();
				assert (0);
			}
		}*/
		
		/*
		bool ret = false;
		for (auto& B : F) {
			
			if(F.getName().equals("main") && isa<ReturnInst>(B.getTerminator())) { // major hack?
				addFinalPrintf(B, mContext);
			}
			
			ret = runOnBasicBlock(B);
		}*/
		
		return _runOnFunction(F);
		return false; 
    }
    
    void incrementCounter(Instruction *insertPos, GlobalVariable *V) {
		
		IRBuilder<> IRB(insertPos);
		Value *loadAddr = IRB.CreateLoad(V);
		Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*mContext), 1), loadAddr);
		IRB.CreateStore(addAddr, V);		
	}
	
    //----------------------------------
    bool runOnBasicBlock(BasicBlock &B) {
		
		bool ret = false;
		
		for (auto& I : B) {
			/*if (auto* op = dyn_cast<BinaryOperator>(&I)) {
				
				// Insert at the point where the instruction `op` appears.
				IRBuilder<> builder(op);

				// Make a multiply with the same operands as `op`.
				Value* lhs = op->getOperand(0);
				Value* rhs = op->getOperand(1);
				Value* mul = builder.CreateMul(lhs, rhs);
				
				errs() << "Found op\n";
				errs() << "lhs:" << *lhs << "\n";
				errs() << "rhs:" << *rhs << "\n";

				// Everywhere the old instruction was used as an operand, use our
				// new multiply instruction instead.
				for (auto& U : op->uses()) {
					User* user = U.getUser();  // A User is anything with operands.
					user->setOperand(U.getOperandNo(), mul);
					errs() << "OpNum:" << U.getOperandNo() << "\n";
				}

				// We modified the code.
				ret = true;
			}*/
			
			if ( auto* op = dyn_cast<BranchInst>(&I) ) {					
				if ( op->isConditional() ) {
					errs() << "Found op " << *op << "\n";
					Value * v = op->getCondition();
					errs() << " cond: " << *v << "\n";
					
					incrementCounter(op, mBranchCounter);
					incrementCounter(&*op->getSuccessor(0)->getFirstInsertionPt(), mTrueCounter);
					incrementCounter(&*op->getSuccessor(1)->getFirstInsertionPt(), mFalseCounter);
					ret = true;
					
					// get the true block and add instruct
					//BasicBlock *TrueBlock = op->getSuccessor(0);
					//errs() << "   True: " << *TrueBlock << "\n";
					//BasicBlock *FalseBlock = op->getSuccessor(1);
					//errs() << "   False: " << *FalseBlock << "\n";
				}
			}
		}
		
		return ret;
    }
    
    //----------------------------------
    // Rest of this code is needed to: printf("%d\n", bbCounter); to the end of main, just BEFORE the return statement
    // For this, prepare the SCCGraph, and append to last BB?
	void addFinalPrintf(BasicBlock& BB, LLVMContext *Context) {
		
		
		IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
		Value * FmtStr = builder.CreateGlobalStringPtr("\nresult:\ntotal:%u\ntrue:%u\nfalse:%u\n", Twine("fmt"));
		Value *bCounter = builder.CreateLoad(mBranchCounter);
		Value *tCounter = builder.CreateLoad(mTrueCounter);
		Value *fCounter = builder.CreateLoad(mFalseCounter);
		Value *Args[] = {FmtStr, bCounter, tCounter, fCounter};
		// makeArrayRef(Args)
		CallInst *call = builder.CreateCall(mPrintf_func, Args);
		call->setTailCall(false);	
		
    }
	
    // We don't modify the program, so we preserve all analyses.
    /*void getAnalysisUsage(AnalysisUsage &AU) const override {
		// there are function about requireed passes to run before, eg addRequired<LoopInfoWrapperPass>()
		AU.setPreservesAll(); // there are other cunction to preserve only specific passes, eg etPreservesCFG
    }*/

	
  };
}


char LTOZerostack::ID = 0;
#if LTO_BUILD
	// to use in LTO - these macro create the initializeLTOZerostackPass() function 
	INITIALIZE_PASS_BEGIN(LTOZerostack, "LTOZerostack",
					"LTOZerostack pass", false, false)
	//INITIALIZE_PASS_DEPENDENCY(LazyValueInfo)
	//INITIALIZE_PASS_DEPENDENCY(TargetLibraryInfoWrapperPass)
	INITIALIZE_PASS_END(LTOZerostack, "LTOZerostack",
					"LTOZerostack pass", false, false)
	// Public interface to the LTOZerostack pass
	ModulePass *llvm::createLTOZerostackPass() { return new LTOZerostack(); }

#else

	// to be able to use it in clang directly
	static void registerLTOZerostack(const PassManagerBuilder &,
							 legacy::PassManagerBase &PM) {
	  PM.add(new LTOZerostack());
	}

	static RegisterStandardPasses
	  RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,	// for LTO, this does not matter
					 registerLTOZerostack);

	// to be able to use it with opt             
	static RegisterPass<LTOZerostack> X("LTOZerostack", "LTOZerostack World Pass");

#endif
