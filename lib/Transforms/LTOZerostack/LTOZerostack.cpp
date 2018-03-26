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


#include "llvm/Transforms/LTOZerostack.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/InlineAsm.h"
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

/*
This code retrieves the callees of each function, and stored them in a file META_FILE. This is used for 
the callgraph-based solution.
This file is then used by the backend. The backend augments it with stack/register information.
Then the python script uses this information to compute the maximum stack usage.
*/
 
using namespace llvm;

#define DEBUG_TYPE "LTOZerostack"
#define LEN(X) sizeof(X)/sizeof((X)[0])

// metafiles used by CG solution
const char * META_FILE = "/tmp/metafile_pass";
// type annotation prefix
#define TYPE	"type_annotate_"

namespace {
	
  	// LTOZerostack 
  	class LTOZerostack : public ModulePass {
    
    	class CGNode {
		public:
			
			typedef StringMapIterator<CGNode*> iterator;
		
			CGNode(StringRef R, size_t n = 16) {
				Name = R;
				isChild = false;
				isExternal = true;
				isVisited = false;
				isAnnotation = false;
				ChildMap = new StringMap<CGNode*>(n);
				assert ( ChildMap && "Cannot allocate ChildMap" );
			}
			
			// Note: we don't delete the elements, this is done thru the hash map FunctionMap
			virtual ~CGNode() {
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
			void addChild( CGNode * node ) {
				assert (node);
				ChildMap->insert( std::pair<StringRef, CGNode*>(node->Name, node) );
				
			}
			
			
			CGNode* getChild(StringRef Name) {
				if ( ChildMap ) {
					return ChildMap->lookup(Name);
				}
				return NULL; 
			}
			
			iterator begin() { return ChildMap->begin(); }
			iterator end() { return ChildMap->end(); }
			
		private:
			std::string Name;
			StringMap<CGNode*>* ChildMap;	// this class's ownership
			bool isChild;
			bool isExternal = true;
			bool isVisited = false;	// I add this for aliases
			bool isAnnotation = false;	// I add this for annotation
		
		};
	
		std::set<StringRef>  AnnotationSet;	// all know annotation kept here
	    StringMap<CGNode*> FunctionMap;	// all the nodes kept here, fast access, simple deletion
	    //StringMap<StringRef> AliasMap;
    
	    CGNode * newNode(StringRef N) {
			CGNode * n = new CGNode(N);
			assert (n && "Cannot allocate node");
			assert ( 0 == ListAllFunctions(N) );
			FunctionMap.insert( std::pair<StringRef, CGNode*>(n->getName(), n) );
			return n;
		}
	
		void deleteNodes() {
			for ( auto & it : FunctionMap ) {
				CGNode *n = it.getValue(); // getKey()
				//errs() << "Deleting node " << n->getName() << "\n";
				delete n;
			}
			FunctionMap.clear();
		}
	
		CGNode * ListAllFunctions( StringRef N ) {
			return FunctionMap.lookup( N );
		}
	
	    
	    LLVMContext *mContext = NULL;
	    
    
    	public:

	    // variables
	    static char ID; // Pass identification, replacement for typeid
    
	    LTOZerostack() : ModulePass(ID) {
			// initializeLTOZerostackPass is defined by the MACRO INITIALIZE_PASS_BEGIN and INITIALIZE_PASS_END
			initializeLTOZerostackPass(*PassRegistry::getPassRegistry());
		}
	
	
		bool runOnModule( Module & M ) override {
			
			// LLVMgold plugin is loaded in function AddGoldPlugin() of file ../tools/clang/lib/Driver/Tools.cpp
			//errs() << "LTOZerostack's module!!" << M.getName() << "\n";

			
			for ( auto& F : M ) {
				_runOnFunction(F);
			}

		
		#if 0 // set this to one to print debug info 
			// now let's print the CFG
			// reset the visited node
			#define RESET_VISTED \
					for ( auto & it : FunctionMap )  {	\
						CGNode *n = it.getValue();	\
						n->setVisited(false);			\
					}	
			
			RESET_VISTED
			// this prints all nodes	
			for ( auto & it : FunctionMap ) {
				CGNode *n = it.getValue();
				printNode( n, "" );
			}
			
			// this prints one function we're interested in, eg "main" in this case
			RESET_VISTED
			printNode(ListAllFunctions("main"), "");
		#endif
			
			MarshallToFile(META_FILE);
			
			deleteNodes();
			
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
				CGNode *n = it.getValue();
				if ( !n->getExternal() /*|| n->getAnnotation()*/ ) {
					//errs() << n->getName() << ":";
					outfs << n->getName().str() << ":";
					for ( CGNode::iterator it = n->begin(), eit = n->end(); eit != it; ++it ) {
						//errs() << it->getValue()->getName() << ",";
						outfs << it->getValue()->getName().str() << ",";
					}
					//errs() << "\n";
					outfs << "\n";
				} 
			}
			
			outfs.close();
		}
	
	
		// ---------------------------------
		void printNode(CGNode * n, Twine Ident) {
			
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
				
				for ( CGNode::iterator it = n->begin(), eit = n->end(); eit != it; ++it ) {
					// recurse only if the function is not recursive
					if ( n != it->getValue() ) {
						printNode( it->getValue()	, Ident + " " );
					}
				}
			}
		}
	
	
		StringRef getCallAnnotation(const Value *V) {
		
			if (auto *I = dyn_cast<Instruction>(V)) {
				MDNode *MD = I->getMetadata("tyann");
				if (MD) {
					auto *MDS = cast<MDString>(MD->getOperand(0));
					//errs() << "MD:" << MDS->getString() << "\n";
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
			
			CGNode * ThisNode = 0;
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
			
			for (auto& B : F) {
							
				for (auto& I : B) {
					
					if ( auto* CI = dyn_cast<CallInst>(&I) ) {					
					  
					  	// Note: ASM is *not* supported. But I still perform a bunch of validation checks
					  	// to see if we can figure if ASM uses the stack. These checks are naive and not 
					  	// exhaustive
						if ( CI->isInlineAsm() ) {
							
							InlineAsm * IASM = dyn_cast<InlineAsm>(CI->getCalledValue());
							std::string ASMStr = IASM->getAsmString();
							std::transform(ASMStr.begin(), ASMStr.end(), ASMStr.begin(), ::tolower); // make everything lower case
							assert (IASM && "IASM is null");
													
							// check for use of esp/rsp. Note: this will also contain reads and not just writes
							// The check below is too naive: deference of stack pointer also gets caught here... 
							// so I comment it out.
							#if 0
							if ( !( ASMStr.find("esp") == std::string::npos && ASMStr.find("ESP") == std::string::npos &&
									ASMStr.find("rsp") == std::string::npos && ASMStr.find("RSP") == std::string::npos) ) {
									
									errs() << "F:" << F << "\n";
									errs() << "B:" << B << "\n";
									errs() << "INLINEASM:" << *IASM << "\n";
									errs() << F.getName() << "\n";
									
									assert ( 0 && "Handwritten assembly uses esp/rsp");
							}
							#endif
									
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
							// alter the stack.
							
							// we don't want a jmp except in certain libc functions for the time being
							// a jmp within the same function is fine. A jmp outside is not, because we must follow it
							// to compute the call graph
							// The check below has a list of function used when testing mbedTLS. I manually verified
							// these jmp within the same function so we are fine. For other libs/function, it's not supported
							// since ASM is *not* supported anyway
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
							
							// we don't want calls because we must follow them
							// I thought of looking for "call " but it may also be possible to have "syscall "
							// these function are OK, i the sense that the function (block) they call does not change the stack pointer
							// this was use when testing mbedTLS. ASM is *not* supported in general
							std::vector<std::string> ListCALLFunctionsOK = {"aes_setkey_enc", "aesni_setkey_enc"};
							size_t pos = ASMStr.find("call", 0); // fist occurrence
							while(pos != std::string::npos) {
								if ( !( (pos >= 3 && ASMStr.substr(pos-3, 7) == "syscall" ) || Contains(ListCALLFunctionsOK,F.getName()) ) ) {
									//errs() << "F:" << F << "\n";
									//errs() << "B:" << B << "\n";
									//errs() << "INLINEASM:" << *IASM << "\n";
									errs() << ASMStr.substr(pos-3, 7) << "\n";
									//errs() << F.getName() << "\n";
									assert ( 0 && "Found not syscall" );
								}
								assert ( (pos >= 3 && ASMStr.substr(pos-3, 7) == "syscall") || Contains(ListCALLFunctionsOK,F.getName()) );
								pos = ASMStr.find("call", pos+1);
							}
							
							// Note: this is just to help troubleshoot the CFG, we don't use syscall during call graph computation
							// TODO: int 0x80
							assert ( ASMStr.find("int ") == std::string::npos );
							if ( ASMStr.find("syscall") == std::string::npos ) { continue; }
							
							// I use @INSTRUCTION_SYSCALL, because musl does have a function called syscall
							// Note: we don't need to check for non-asm code for this name since it can only be called via asm
							std::string syscallInst = "@INSTRUCTION_SYSCALL";
							assert ( F.getName() != syscallInst && "Found recursive function in inline asm" );
							
							// create the node only if it does not exist
							CGNode * asmNode = 0;
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
								
								// check for recursive function - now cycle detected in python script
								// assert ( Callee->getName() != F.getName() && "Found recursive function in Callee" );
								
								CGNode * calleeNode = 0;
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
									
									//errs() << GA->getName() << " is an function alias to " << AF->getName() << "\n";
									
									// check for recursive function - now cycle detected in python script
									// assert ( GA->getName() != F.getName() && AF->getName() != F.getName() && "Found recursive function in GlobalAlias" );
									
									CGNode * aliasNode = 0;
									if ( !(aliasNode = ListAllFunctions( AF->getName() ) ) ) {
										aliasNode = newNode( AF->getName() );
									} 
									
									assert ( aliasNode && "aliasNode is null" );
									ThisNode->addChild( aliasNode );
										
									
									
								} else if ( Atype->isPointerTy() && Atype->getPointerElementType()->isFunctionTy() ){
																	
									// get the annotation. First from the called value. If none, try the call instruction itself
									StringRef FPAnno = getCallAnnotation( CV );
									if ( FPAnno == "" ) { FPAnno = getCallAnnotation( CI ); }
									if ( FPAnno == "" ) {
									
										CGNode * unknownNode = 0;
										StringRef unknownName = "@UNKNOWN_POINTER";
										if ( !(unknownNode = ListAllFunctions( unknownName ) ) ) {
											unknownNode = newNode( unknownName );
										} 
										
										assert ( unknownNode && "unknownNode is null" );
										ThisNode->addChild( unknownNode );
										
										
									} else {
										
										//errs() << "Got annotation:" << FPAnno << "\n";
										
										CGNode * gpNode = 0;
										StringRef gpName = (Twine("@ANNOTATED_POINTER_") + Twine(FPAnno)).str();
										if ( !(gpNode = ListAllFunctions( gpName ) ) ) {
											gpNode = newNode( gpName );
										} 
										
										assert ( gpNode && "gpNode is null" );
										ThisNode->addChild( gpNode );
										//errs() << "gpName:" << gpName << "\n";
										
									}
															
									
									
								} else {
									assert ( 0 && "Unsupported call object" );
								}
								
							}					
							
						}
						
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
    
	    // Just a hack to try to validate *some* ASM
	    // ASM is not supported in general
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
 
  };
}


char LTOZerostack::ID = 0;

// to use in LTO - these macro create the initializeLTOZerostackPass() function 
INITIALIZE_PASS_BEGIN(LTOZerostack, "LTOZerostack",
				"LTOZerostack pass", false, false)
//INITIALIZE_PASS_DEPENDENCY(LazyValueInfo)
//INITIALIZE_PASS_DEPENDENCY(TargetLibraryInfoWrapperPass)
INITIALIZE_PASS_END(LTOZerostack, "LTOZerostack",
				"LTOZerostack pass", false, false)
// Public interface to the LTOZerostack pass
ModulePass *llvm::createLTOZerostackPass() { return new LTOZerostack(); }


