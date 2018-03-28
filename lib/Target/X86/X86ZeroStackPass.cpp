#include "X86.h"
#include "X86TargetMachine.h"
#include "X86MachineFunctionInfo.h"
#include "MCTargetDesc/X86MCTargetDesc.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/Passes.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetInstrInfo.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"

// for demangle
#include <cxxabi.h>
#include <libgen.h>

// for stream
#include <fstream>

// for map
#include <map>

using namespace llvm;


#define DEBUG_TYPE "X86Zerostack"
#define UNUSED(V)	(void*)(V)

/*
This code does:
	- in runOnMachineFunctionBeforePEI()
		- collects all RET instructions
		- computes the stack usage (variable FunctionStackOffset) due to function call (see function runOnMachineBasicBlockBeforePEI())
	- in runOnMachineFunctionAfterPEI()
		- computes stack usage (variable Offset) in function runOnMachineFunctionAfterPEI() using getStackSize() and estimateStackSize()
			I am not sure FunctionStackOffset is needed at all, but I've added anyway.
		- erase stack used and registers

What we need for production code:
	- more documentation
	- split the 3 implementations in different files
	- remove MACRO to select between implementations, and use compiler option instead

*/

// =================================================================
//
//	config parameters. In a production build, these would be
//	passed as compiler flags
//
// =================================================================

// http://llvm.org/docs/CommandLine.html#boolean-arguments
#define DISABLE_PASS 0
static bool IsLibc = false;

static const char * STACKPOINT_VAR = "__StackPoint";
// file and foledr where GV is created in musl libc
static const char * STACKPOINT_FILE_DEF = "__GV.c";	
static const char * LIBC_STACKPOINT_DECL_MOD_FOLDER = "ldso";

// Function-based solution
#define ZERO_EACH_FUNCTION 1			// requires -fno-optimize-sibling-calls
#define ZERO_EACH_FUNCTION_WITH_SIGNAL 1

// Stack-based solution
#define ZERO_WITH_STACKPOINT 0			// requires -fno-optimize-sibling-calls - signal handling is accounted for:TODO: make it optional, and also VDSO
#define ZERO_WITH_STACKPOINT_BULK_REG 0	// erase all register in sensitive function once only

// Call-Graph-based solution (CG)
#define ZERO_WITH_CG_BULK_REG	0		// erase register at the end of each function or in bulk ? per function requires -fno-optimize-sibling-calls
#define ZERO_WITH_CG	0		// WARNING: make sure linker is gold: ln -s /usr/bin/ld.gold /use/bin/ld

#define SENSITIVE_ATTRIBUTE	"SENSITIVE"
#define TYPE_ATTRIBUTE	"type_annotate_"

// list of registers used by any of the VDSO functions. 
// I disassembled them for my OS. This would be passed as compiler flag in product build.
unsigned VDSO_UsedRegs[] = {X86::RBP, X86::RDI, X86::RSI, X86::RAX, X86::R12, X86::RBX, X86::R8, X86::RDX, X86::RCX, X86::R12};

// Offset that must be added for the redzone, vdso calls (provided by kernel), and cpu state saving during signal handling
// signal/interrupts with process CPU state saved on user stack http://users.cms.caltech.edu/~donnie/cs124/CS124Lec17.pdf
// do_signal() -> get_signal()
//			   -> handle_signal() -> setup_rt_frame() -> *_setup_rt_frame() which saves cpu state
#define OFFSET_VDSO_CALLS		40	// bytes - did manually for my OS
#define _OFFSET_REDZONE			128	// bytes
#define _OFFSET_SIGNAL_CPU_STATE	(3072/8)	// bytes used to store CPU state during signal handling. This value is approximate. TODO:get the exact value
#define OFFSET_SIGNAL_HANDLING	(_OFFSET_REDZONE + _OFFSET_SIGNAL_CPU_STATE)

// metafiles used by CG solution
const char * META_FILE = "/tmp/metafile_pass";
const char * META_MACHINE_FILE = "/tmp/metafile_pass.machine";



// All lists of function below would be declared thru a compiler flag
// in production build. 
// libc functions called only at the start are allowed to not return
// these functions will not be instrumented, since they don't return...
const char * MUSL_SAFE_START_NON_RETURN[] = { "_start_c", "__libc_start_main", 
										"__dls2", "__dls3", "_start", "__init_libc", 
										"__libc_start_init", "do_init_fini" }; 
// other libc functions allowed to not return
const char * MUSL_SAFE_NON_RETURN[] = { "_exit", "_Exit", "abort", "__assert_fail", "exec", "__exec", "execl", "execle", "execlp", "__execvpe" };

const char * COMPILER_RT_NON_RETURN[] = {"compilerrt_abort_impl", "__eprintf" /*used in all version of assert()*/};

const char * EXIT_NON_RETURN[] = {"_exit", "_Exit", "exit"};
const char * EXEC_NON_RETURN[] = {"exec", "__exec"};
const char * VDSO_FUNCTIONS[] = {"clock_gettime", "gettimeofday", "time"}; 

#define MAX(x, y) (((x) > (y)) ? (x) : (y))
#define LEN(X) sizeof(X)/sizeof((X)[0])

// Allow calls to exit()/exec*() functions in non-libc code?
#define ALLOW_EXIT_CALLS	0


#define ZEROVALUE	(0)

STATISTIC(FunctionStackOffset, "Function Stack Offset");
STATISTIC(FunctionIsLeaf, "Function Leave or not");	// this is a boolean for us
STATISTIC(FunctionUseVDSO, "function calls a vdso function or not");	// this is a boolean for us

namespace {
class ZeroStackPass : public MachineFunctionPass {
  //const X86InstrInfo *InstrInfo = NULL;
  //const TargetInstrInfo *TII = NULL;
private:
	
  SmallVector<MachineInstr *, 16> StackStores;
  SmallVector<MachineInstr *, 4> Returns;
  SmallVector<unsigned, 32> RegList;
  SmallVector<unsigned, 4> RetRegList;
   
  const TargetInstrInfo	* TTI;
  bool IsPEI;
	const TargetInstrInfo& getTargetInstrInfo(MachineBasicBlock &MBB) const {
	
		MachineFunction &MF = *MBB.getParent();	
		return getTargetInstrInfo(MF);
	}
	
	const TargetInstrInfo& getTargetInstrInfo(MachineFunction &MF) const {
	
		return *MF.getSubtarget().getInstrInfo();
	}
	
	const TargetRegisterInfo& getTargetRegisterInfo(MachineBasicBlock &MBB) const {
	
		MachineFunction &MF = *MBB.getParent();	
		return getTargetRegisterInfo(MF);
	}
	
	const TargetRegisterInfo& getTargetRegisterInfo(MachineFunction &MF) const {
	
		return *MF.getSubtarget().getRegisterInfo();
	}
	
	const X86Subtarget& getX86SubTarget(MachineFunction &MF) {
		return MF.getSubtarget<X86Subtarget>(); // getSubtarget() is enough but explicit is easier to read
	} 
	
	const X86Subtarget& getX86SubTarget(MachineBasicBlock &MBB) {
		return getX86SubTarget(*MBB.getParent()); // getSubtarget() is enough but explicit is easier to read
	} 
  
public:
  static char ID;
  ZeroStackPass(bool _isPEI) : MachineFunctionPass(ID), IsPEI(_isPEI) {}

  const char *getPassName() const override {
    return "ZM (X86) Stack Invalidate Pass";
  }
  
  
	void validateNotTailCall ( MachineInstr & Inst ) {
	
	// When using the CFG, we can use call tail optimisation, except for the sensitive functions -- we check this later in AfterPE
	#if !ZERO_WITH_CG
		
		unsigned opCode=Inst.getOpcode();
		if ( opCode == X86::TCRETURNdi || opCode == X86::TCRETURNri ||
			opCode == X86::TCRETURNmi || opCode == X86::TCRETURNdi64 || opCode == X86::TCRETURNri64 ||
			opCode == X86::TCRETURNmi64 ) {
		assert ( 0 && "Invalid instruction. Have you passed the '-fno-optimize-sibling-calls' flag?" );
		}
		
	#endif
	
	}

  void runOnMachineBasicBlockBeforePEI(MachineBasicBlock &MBB) {
	
	// Here we compute the maximum stack usage due to calling other functions
	// ie certain arguments may be pushed on the stack. 
	//errs() << "getFullName: '" << MBB.getFullName() << "'\n";
	unsigned ADJUSTSTACKDOWN = getX86SubTarget(MBB).isTarget64BitLP64() ? X86::ADJCALLSTACKDOWN64 : X86::ADJCALLSTACKDOWN32;
	unsigned ADJUSTSTACKUP = getX86SubTarget(MBB).isTarget64BitLP64() ? X86::ADJCALLSTACKUP64 : X86::ADJCALLSTACKUP32;
	
    for (MachineBasicBlock::iterator I = MBB.instr_begin(); I != MBB.instr_end(); ++I) {
      
      MachineInstr *Inst = I; 
      
      if (Inst->isReturn()) {
		  		  
		  validateNotTailCall( *Inst );
		  
      } else if ( Inst->isCall() ) { 
		  	
		// We currently validate both before and after register lowering
		// In one case only is probably enough: TODO
		validateNotLibcNoReturn(*Inst);
		
		// Record the fact that this function is not a leaf
		FunctionIsLeaf = false;
		
		// Check if a this is a call to VDSO function
		setHasLibcVdsoCall(*Inst);
		
		// Let's find how much the stack is lowered at most
		// this is conservative because some of the instructions will in fact NOT
		// push to the stack or change the stack pointer. For example, the prologue
		// may lower the stack by taking into account not only local veriables and 
		// spill slots, but also args passed on the stack. What matters to us is that
		// we erase at least the minimum, in certain cases a few more bytes
		// This is unlikely to affect performance in practice.
		// Below is just a sanity check to make sure prio-vs-after call
		// changes the stack by the same amount of bytes
		
		// Iterate down to find a ADJUSTSTACKUP
		int64_t OffsetUp;
		MachineBasicBlock::iterator UPI = std::next(I);
		bool foundStackUp = false;
		while ( true ) {
			
			unsigned Opc = UPI->getOpcode();
			if ( ADJUSTSTACKUP == Opc ) {
				foundStackUp = true;
				
				// First operand tells us by how much we grow the stack
				MachineInstr::mop_iterator mop = UPI->operands_begin();
				OffsetUp = mop->getImm();
				
				// Note sure what the second operand means. Sanity check it to 0
				assert ( 0 == (++mop)->getImm() );
				break;
			}
			
			if ( UPI == MBB.end() ) { break; }
			
			++UPI;
		}
		assert (foundStackUp && "Could not find ADJUSTSTACKUP");
		
		// Iterate up to find a ADJUSTSTACKDOWN
		MachineBasicBlock::iterator DWI = std::prev(I);
		int64_t OffsetDwn = 0;
		bool foundStackDown = 0;
		while (true) {
			
			unsigned Opc = DWI->getOpcode();

			if ( ADJUSTSTACKDOWN == Opc ) {
				
				foundStackDown = true;
				
				// Compare that the stack up and down match in the instruction
				MachineInstr::mop_iterator mop = DWI->operands_begin();
				OffsetDwn = mop->getImm();

				assert ( OffsetDwn == OffsetUp );
				
				// Note sure what the second operand means. Sanity check it to 0
				assert ( 0 == (++mop)->getImm() );
				
				break;
			} 			
			
			if ( DWI == MBB.begin() ) { break; }
			--DWI;
			
		}
		
		assert (foundStackDown && "Could not find ADJUSTSTACKDOWN");
		
		FunctionStackOffset = MAX(OffsetUp, FunctionStackOffset);
		
	  }
	  
    }
    
  }
  
  void setHasLibcVdsoCall ( MachineInstr & Inst ) {
	
	// libc itself can call thse functions
	if ( Inst.isCall() && !FunctionUseVDSO ) {
						
		
		MachineInstr::mop_iterator mop = Inst.operands_begin() + 0;
								
		if ( mop->isGlobal() ) { 
			// MO_GlobalAddress = Address of a global value -> ga:@fname
			const GlobalValue * GA	= mop->getGlobal();
			
			// see http://legup.eecg.utoronto.ca/doxygen/classllvm_1_1Value.html for value types
			unsigned ValueID = GA->getValueID();
			const Function * GF = 0;
			
			if (  Value::FunctionVal == ValueID ) {
				GF =  dyn_cast<Function>(GA);
				assert ( GF && "global not a function" );
				
			} else if ( Value::GlobalAliasVal == ValueID ) {
				const GlobalAlias * GAS =  dyn_cast<GlobalAlias>(GA);
				assert ( GAS && "global not an alias" );
				// use getBaseObject() 
				const GlobalObject* GO = GAS->getBaseObject();
				assert ( GO && "global alias not an object" );
				GF =  dyn_cast<Function>(GO);
				assert ( GF && "global alias not a function" );
				
			} else {
				assert (0 && "Unsupported GlobalValue type");
			}
			
			assert ( GF && "GF is not set" );
			
			FunctionUseVDSO = isMuslVdso( GF->getName() );

		} else if ( mop->isSymbol() ) {
			// MO_ExternalSymbol = Name of external global symbol -> <es:fname>
			const char *FName = mop->getSymbolName();
			assert ( FName && "FName null" );
			
			FunctionUseVDSO = isMuslVdso( FName );
			
		} else if ( mop->isMCSymbol() ) {
			// MO_MCSymbol = MCSymbol reference (for debug/eh info)  -> <MCSym=fname>
			MCSymbol * MCSym = mop->getMCSymbol();
			assert ( MCSym && "MCSym null");
			
			FunctionUseVDSO = isMuslVdso( MCSym->getName() );
			
		} else if ( mop->isReg() || mop->isFI() ) {
			// cannot verify this, it's a pointer to a function...
			// but unlikely this is exit() anyway, no?
			// TODO: in callgraph, validate using def-use chains that the pointer is marked sensitive
		} else {
			assert ( 0 && "Unsupported call operand" );
		}
	}
  }
  
  void validateNotLibcNoReturn ( MachineInstr & Inst ) {
	
	// libc itself can call thse functions
	if ( !IsLibc && Inst.isCall() ) {
						
		MachineInstr::mop_iterator mop = Inst.operands_begin() + 0;
								
		if ( mop->isGlobal() ) { 
			// MO_GlobalAddress = Address of a global value -> ga:@fname
			const GlobalValue * GA	= mop->getGlobal();
			
			// see http://legup.eecg.utoronto.ca/doxygen/classllvm_1_1Value.html for value types
			unsigned ValueID = GA->getValueID();
			const Function * GF = 0;
			
			if (  Value::FunctionVal == ValueID ) {
				GF =  dyn_cast<Function>(GA);
				assert ( GF && "global not a function" );
				
			} else if ( Value::GlobalAliasVal == ValueID ) {
				const GlobalAlias * GAS =  dyn_cast<GlobalAlias>(GA);
				assert ( GAS && "global not an alias" );
				// use getBaseObject() 
				const GlobalObject* GO = GAS->getBaseObject();
				assert ( GO && "global alias not an object" );
				GF =  dyn_cast<Function>(GO);
				assert ( GF && "global alias not a function" );
				
			} else {
				assert (0 && "Unsupported GlobalValue type");
			}
			
			assert ( GF && "GF is not set" );
			
			// We allow assert/abort, but not explicit exit
#if 	!ALLOW_EXIT_CALLS
			assert ( !isExit( GF->getName() ) && "Found forbidden libc NoReturn function -- global" );
#endif	// ALLOW_EXIT_CALLS			
		} else if ( mop->isSymbol() ) {
			// MO_ExternalSymbol = Name of external global symbol -> <es:fname>
			const char *FName = mop->getSymbolName();
			assert ( FName && "FName null" );
			
#if 	!ALLOW_EXIT_CALLS
			assert ( !isExit(FName) && "Found forbiden libc NoReturn -- symbol");
#endif
			
		} else if ( mop->isMCSymbol() ) {
			// MO_MCSymbol = MCSymbol reference (for debug/eh info)  -> <MCSym=fname>
			MCSymbol * MCSym = mop->getMCSymbol();
			assert ( MCSym && "MCSym null");
			
#if 	!ALLOW_EXIT_CALLS
			assert ( !isExit( MCSym->getName() ) && "Found forbiden libc NoReturn -- MCsymbol" );
#endif
		} else if ( mop->isReg() || mop->isFI() ) {
			// Cannot verify this, it's a pointer to a function...
			// Conservatively assume it's not exit() ...
		} else {
			assert ( 0 && "Unsupported call operand" );
		}
	}
  }
  
  void collectWrittenRegisters(MachineInstr & Inst) {
	  
	MachineBasicBlock & MBB = *Inst.getParent();
	const TargetInstrInfo &TII = getTargetInstrInfo(MBB);
	const TargetRegisterInfo & TRI = getTargetRegisterInfo(MBB);
	const X86RegisterInfo & X86RI = *getX86SubTarget(MBB).getRegisterInfo(); 	// got this from X86FrameLowering.cpp to get stack pointer
	const X86FrameLowering & X86FL = *getX86SubTarget(MBB).getFrameLowering(); 	// got this from X86FrameLowering.cpp to get stack pointer
	MachineFrameInfo &MFI = *MBB.getParent()->getFrameInfo();
	
	// Check if we have a register marked as def
	// we will only keep the smaller common register, ie if there is al, eax, we'll only keep eax since zeroing eax does zero al too
	// Note that if eax is changed but rax upper part contains data, xoring eax will zero rax upper part too, and we're screwed.
	// Fortunately this is not possible because anything that changes eax (xor, mov, etc) also changes rax so we should be safe. 
	// for < 32 bit, eg we change change al, zeroing al will not zero upper parts so optimization could be possible
	// but that's still fine since we would only zero al in this case
	for ( MachineInstr::mop_iterator MOP = Inst.operands_begin(), MOPE=Inst.operands_end(); MOP!=MOPE; ++MOP) {
		MachineOperand &mOp = *MOP;
		if ( mOp.isReg() && mOp.isDef() && !mOp.isImplicit() ) {
		
			unsigned Reg = mOp.getReg();
			_collectWrittenRegisters( MBB, TII, TRI, X86RI, X86FL, MFI, Inst, Reg );
		}
	}

#if ZERO_EACH_FUNCTION || ZERO_WITH_STACKPOINT
	// Note: for CG-based solution, this is done by the python script
	if ( FunctionUseVDSO ) {
		// For each register used by VDSO function, add them to the list of written registers
		for (unsigned n=0; n<LEN(VDSO_UsedRegs); ++n) {
			unsigned Reg = VDSO_UsedRegs[n];
			_collectWrittenRegisters( MBB, TII, TRI, X86RI, X86FL, MFI, Inst, Reg );
		}
	}
#endif // ZERO_EACH_FUNCTION || ZERO_WITH_STACKPOINT	
  }
  
  // This fills RegList with all GP registers, except those
  // callee-saved by this function
  void populateWrittenGPRegisters(MachineInstr & Inst/* one we remove unnecessary logging, we should pass a MachineFunction here */) {
	
	MachineBasicBlock & MBB = *Inst.getParent();
	const TargetInstrInfo &TII = getTargetInstrInfo(MBB);
	const TargetRegisterInfo & TRI = getTargetRegisterInfo(MBB);
	const X86RegisterInfo & X86RI = *getX86SubTarget(MBB).getRegisterInfo(); 	// got this from X86FrameLowering.cpp to get stack pointer
	const X86FrameLowering & X86FL = *getX86SubTarget(MBB).getFrameLowering(); 	// got this from X86FrameLowering.cpp to get stack pointer
	MachineFrameInfo &MFI = *MBB.getParent()->getFrameInfo();
	
	// Now collect for each GP register
	const TargetRegisterClass GPs = X86::GR64RegClass;
	for (unsigned n=0; n<GPs.getNumRegs(); ++n) {
		unsigned Reg = GPs.getRegister(n);
		_collectWrittenRegisters( MBB, TII, TRI, X86RI, X86FL, MFI, Inst, Reg );
	}
	
  }
  
  void _collectWrittenRegisters( MachineBasicBlock & MBB, const TargetInstrInfo &TII, const TargetRegisterInfo & TRI, 
								const X86RegisterInfo & X86RI, const X86FrameLowering & X86FL, MachineFrameInfo &MFI, 
								MachineInstr & Inst, unsigned Reg ) {
  
	bool Add = true;
			
	
	// https://cseweb.ucsd.edu/classes/sp10/cse141/pdf/02/S01_x86_64.key.pdf p.3 for register names
	if ( TRI.isSuperRegisterEq (Reg, X86RI.getStackRegister()) ) { return; }	// stack pointer (RSP), may be used as frame pointer if no-frame-pointer. in both cases, dont zero it
	if ( TRI.isSuperRegisterEq (Reg, TRI.getProgramCounter()) ) { return; }		// program counter (RIP)
	
	// WARNING: if we use no-frame-pointer (and in other circumanstances, see hasFP()), 
	// ebp/rbp may be used to store data. So we should erase except if used as frame pointer
	// Code from X86FrameLowering.cpp
	unsigned FramePtr = X86RI.getFrameRegister(*MBB.getParent());
	const unsigned MachineFramePtr = getX86SubTarget(MBB).isTarget64BitILP32() ? getX86SubSuperRegister(FramePtr, 64) : FramePtr;
	
	if ( (MachineFramePtr == Reg) && X86FL.hasFP(*MBB.getParent())  ) { return; }				// frame pointer (RBP)
	
	if ( TRI.isSuperRegisterEq (Reg, X86::EFLAGS) ) { return; } 
	
	// below is NOT a bug. It's just for me to be alerted the first time we encounter the frame pointer (EBP/RBP?) used for data, 
	// so that I can validate the code works correctly
	if ( (MachineFramePtr == Reg) && !X86FL.hasFP(*MBB.getParent()) ) { assert ( 0 && "frame pointer used for data!" ); }
	
	
	// Not sure what to do with this yet. I think ST must be zeroed if not used as return value... need to read up on this
	assert ( !X86::RSTRegClass.contains(Reg) && "Unsupported ST register changed");
	
	// Don't consider CSR as they are repopulated with data so we should not zero them
	if ( IsBeingCalleeSavedRegister(MFI, TRI, Reg) ) { return; }
									
	// Do we already have this register or a subset/superset?
	for (SmallVector<unsigned, 32>::iterator it = RegList.begin() ; it != RegList.end(); ++it) {
		unsigned RegS = *it;
		if ( TRI.isSuperRegisterEq (Reg, RegS) ) { Add = false; break; }
		if ( TRI.isSubRegister (Reg, RegS) ) {
			RegList.erase (it);
			break;
		}
	}
	
	if ( Add ) {
		RegList.push_back( Reg );
	}
  }

  void runOnMachineBasicBlockAfterPEI(MachineBasicBlock &MBB) {
	
	//Keep a list of defined register, which we zero out on RET
	// Also get the RET to know where to add the instructions	
    for (MachineBasicBlock::iterator I = MBB.instr_begin(); I != MBB.instr_end(); ++I) {
      
      MachineInstr *Inst = I; 
      UNUSED(I);
      
      // Validate it's not an exit() call, as we cannot clean
      // exit(), _exit() and _Exit() should not appear in sensitive functions
      validateNotLibcNoReturn( *Inst ); // assert if fails
      
      // Keep track of returns so we can add our instructions
      if (Inst->isReturn()) {
		  
		  validateNotTailCall( *Inst );
		  
          Returns.push_back(Inst);
          
          continue; // return instruction does not define registers
      }
      
      collectWrittenRegisters( *Inst );
    }
    
  }

	bool runOnMachineFunctionBeforePEI(MachineFunction &F) {
  		
		FunctionUseVDSO = false;
		FunctionIsLeaf = true;		// reset the leaf info - I think can only be true at this point anyway...
		FunctionStackOffset = 0; 	// reset it on entry to a new function
		
		for (MachineFunction::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {
			runOnMachineBasicBlockBeforePEI(*FI);
		}
		   
	   return true;
	}
  

	inline std::string demangle(StringRef SRef) {
        int status = -1; 
		
		const char* name = SRef.str().c_str();
        std::unique_ptr<char, void(*)(void*)> res { abi::__cxa_demangle(name, NULL, NULL, &status), std::free };
        return (status == 0) ? res.get() : std::string(name);
	}
	
	inline std::string demangle_name( StringRef SRef ) {
		std::string demangledF = demangle(SRef);
		std::size_t pos = demangledF.find("(");
		if ( std::string::npos == pos  ) { return demangledF; }
		return demangledF.substr (0, pos); 
	}

	bool IsFunctionMarkedSensitive(const Function & IRFunction) { 
		return ( IRFunction.hasFnAttribute( SENSITIVE_ATTRIBUTE )  );
	}
	
	std::set<std::string> GetTypeAttributes( const Function & IRFunction ) {
		
		AttributeSet AttSet = IRFunction.getAttributes().getFnAttributes();
		std::set<std::string> Ret;
		
		assert ( AttSet.getNumSlots() <= 1 );
		
		// WARNING: dont erase this, I use it as ref for debugging
		//for (unsigned i = 0, e = AttSet.getNumSlots(); i < e; ++i) {
			//uint64_t Index = AttSet.getSlotIndex(i);
			//errs() << "i:" << i << " , Index:" << Index << "\n";
			//errs() << "getAsString:" << AttSet.getAsString(Index) << "\n";
		//}
		
		//AttSet.dump();
		//errs() << "string:" << AttSet.getAsString( AttSet.getSlotIndex(0) ) << "\n";
		
		// Extract the annotated type attributes: noinline norecurse nounwind readnone uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false"
//errs() << "F:" << IRFunction.getName() << " " << AttSet.getNumSlots() << "\n";
//AttSet.dump();
		if ( AttSet.getNumSlots() == 1 ) {
			
			// Must search for "type_annotate_XXX"
			std::string Attr = AttSet.getAsString( AttSet.getSlotIndex(0) );
			std::string needle = TYPE_ATTRIBUTE;
			size_t pos;
			while ( (pos=Attr.find(needle)) != std::string::npos ) {
				Attr = Attr.substr(pos, Attr.size() - pos - needle.size());
				// Now get the end of the string
				pos = Attr.find("\"");
				assert ( pos != std::string::npos && pos > 0 );
				Ret.insert( Attr.substr(0, pos) );
				Attr = Attr.substr( pos+1, Attr.size() - (pos+1) );
			}
		}
		
		return Ret;
	}
	
	
	// In this module, the global variable may not be be linked
	// This is for musl-libc in the folder ldso/
	bool IsLinkerModule(Module & Mod) {
		
		// Module & Mod = *const_cast<Module*>(MF.getParent())
		bool ret = false; 
		char * modname=0, *foldername=0, *fn=0, *token=0;
		if ( IsLibc ) {
			
			modname = strdup( Mod.getName().str().c_str() );
			foldername = dirname(modname);
			assert ( foldername );
			
			// for some reason, if i pass "." to strtok, it crashes...
			if ( 0 == strcmp(foldername, ".") )	{ goto end; }
			
			token = strtok (foldername,"/");
			while (token != NULL) {
				fn = token;
				token = strtok (NULL, "/");
			}
			
			ret = ( fn && ( 0 == strcmp(fn, LIBC_STACKPOINT_DECL_MOD_FOLDER) ) );
			
		}
	
	end:	
		if (modname) free(modname);
		return ret;
	}
	
	
	bool IsGlobalVariableDefinitionModule( Module & Mod ) {
		// Create the variable in this module
		bool ret = false;
		if ( IsLibc ) {
			char * filename = strdup( Mod.getName().str().c_str() ); assert( filename );
			char *fn = basename( filename );
			// When we use the CG solution, the module has a different name because we merge them all into libc.bc
			ret = ( 0 == strcmp(fn, STACKPOINT_FILE_DEF  ) );
			free( filename );
		}
		
		return ret;
	}
	
	void InitStackPointGlobalVariable( Module & Mod, bool Is64bits, unsigned * relocType ) {
		
		assert ( relocType && "relocType null" );
		
		/* WARNING:
		 * I think this is not necessary if I just put a 
		 * #include <stdint.h>
		 * uintptr_t __StackPoint = 0; in src/__GV/__GV.c
		 */
		
		// This will happen only once per module, since after the definition, getGlobalVariable will succeed
		bool IsDefinitionMod = IsGlobalVariableDefinitionModule(Mod); 
		
		*relocType = X86II::MO_GOTPCREL;
		
		GlobalVariable * GV = Mod.getGlobalVariable (STACKPOINT_VAR, true); 
		if ( IsDefinitionMod && !GV  ) {
			// if not defined in code, unint64_t __StackPoint = 0;
			// if it is already defined, extern unint64_t __StackPoint;
			// ie we create the variable without initialization
			LLVMContext & Context = Mod.getContext();
			IntegerType * theType = Is64bits ? Type::getInt64Ty(Context) : Type::getInt32Ty(Context);
			Constant * InitialValue = ConstantInt::get(theType, 0);
			GV 	= new GlobalVariable(Mod, theType, false, GlobalValue::ExternalLinkage, InitialValue, STACKPOINT_VAR);
		}
		
	}
	
	
	// Utility function to find if an item is in a vector
    template <class Container> 
	bool Contains(Container& container, const typename Container::value_type& element) {
		return std::find(container.begin(), container.end(), element) != container.end();
	}

 //  bool runOnMachineFunctionAfterPEI_FunctionBased(MachineFunction &F) {

 //  	MachineFrameInfo &MFI = *F.getFrameInfo();
	// const TargetRegisterInfo & TRI = getTargetRegisterInfo(F);
	// const TargetInstrInfo &TII = getTargetInstrInfo(F);

	// // We only need to find free registers for sensitive functions in this case
	// if ( (ZERO_WITH_CG && IsFunctionMarkedSensitive( *IRFunction )) || !ZERO_WITH_CG ) {
 //  }

  bool runOnMachineFunctionAfterPEI(MachineFunction &F) {
	
	MachineFrameInfo &MFI = *F.getFrameInfo();
	const TargetRegisterInfo & TRI = getTargetRegisterInfo(F);
	const TargetInstrInfo &TII = getTargetInstrInfo(F);
#if ZERO_WITH_STACKPOINT || ZERO_WITH_CG
	const Function *IRFunction = F.getFunction();
	Module *Mod = const_cast<Module*>(IRFunction->getParent());
#endif 

#if ZERO_WITH_CG && ZERO_WITH_CG_BULK_REG
	std::vector<unsigned> BulkRegs;
#endif
	std::vector<unsigned> ReturnedRegs;
	
	if ( /*std::string("main") != IRFunction->getName().str()*/ true ) {
		
		// We don't support variable-sized objects since we cannot determine their size at compilation time
		assert( !MFI.hasVarSizedObjects() && "Variable-sized objects not supported");
		
		Returns.clear();
		RegList.clear();
		
		for (MachineFunction::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {
			runOnMachineBasicBlockAfterPEI(*FI);
		}
		
	
	#if ZERO_WITH_CG && ZERO_WITH_CG_BULK_REG
		// We can tolerate non returning functions, except for the sensitive ones
		if ( IsFunctionMarkedSensitive( *IRFunction ) ) {
			assert ( !F.getFunction()->doesNotReturn() && "Sensitive function does not return" );
		}
	#else	
		// We don't support non-return functions, as both stack-zeroing and register zeroing is done before the ret instruction
		if ( !IsLibc )  { assert ( Returns.size() && !F.getFunction()->doesNotReturn() ); } // we must have a return, lets disable exit()
		else if ( !(Returns.size() && !F.getFunction()->doesNotReturn()) ) { return true; }
	#endif	
		
		// get the size of the stack
		uint64_t StackSize = MFI.getStackSize();
		uint64_t EstimateStackSize = MFI.estimateStackSize(F);
		int64_t Offset = MAX(EstimateStackSize, StackSize);
		//errs() << "Offset:" << Offset << ", FunctionStackOffset:" << FunctionStackOffset << "\n";
		// add the offset due to function calls
		// Not sure this is necessary, since function PEI::calculateCallsInformation() in 
		// lib/CodeGen/PrologEpilogInserter.cpp calls MFI->setMaxCallFrameSize(MaxCallFrameSize)
		// I started this code by including it so it's still here. We can remove 
		// if we conclude this is redundant
		Offset += FunctionStackOffset; // no way this can overflow
		
		assert (Offset >=0 && "Offset < 0" );
	
		// Set name of reg and size
		const X86Subtarget & STI = getX86SubTarget(F);
		unsigned SP = STI.isTarget64BitLP64() ? X86::RSP : X86::ESP;					
		int64_t Size = STI.isTarget64BitLP64() ? 8 : 4;	
		unsigned AX = STI.isTarget64BitLP64() ? X86::RAX : X86::EAX;		
		unsigned CX = STI.isTarget64BitLP64() ? X86::RCX : X86::ECX;		
		unsigned DI = STI.isTarget64BitLP64() ? X86::RDI : X86::EDI;	
		
		#if ZERO_WITH_STACKPOINT
		MachineBasicBlock & OrigLastMBB = F.back(); // original last block before we add our RetMBB
		const BasicBlock *OrigLastBB = OrigLastMBB.getBasicBlock();
		// There may be multiple RETurn blocks. If the block is in a function
		// where the addrss STACKPOINT_VAR is not yet available (before linker runs),
		// then we must *not* dreference a null pointer. So:
		// 1. Create the last block that will contain our RET instruction. It will be discarded if empty
		// 2. Create the check for null pointer that jumps to our newly-created block
		// WARNING: the order is important http://www.gabriel.urdhr.fr/2014/10/06/cleaning-the-stack-in-a-llvm-pass/
		
		MachineBasicBlock * RetMBB = F.CreateMachineBasicBlock( OrigLastBB );
		F.push_back(RetMBB);				// add our empty block to the new Ret block
		RetMBB->addSuccessor(RetMBB); 		// this seems necessary
		#endif
			
		// We have the list of return instructions, check which registers are available to us
		for (SmallVector<MachineInstr*, 4>::iterator i=Returns.begin(), e=Returns.end() ; i!=e ; ++i) {
			
			// Get the RET instruction
			MachineInstr * Ret = *i;
			
			// Get available registers
			std::set<unsigned>  AvailableRegs;
		#if ZERO_WITH_CG
			// We only need to find free registers for sensitive functions in this case
			if ( IsFunctionMarkedSensitive( *IRFunction ) ) {
		#endif
		
			findDeadCallerSavedRegOnReturn(*Ret, *STI.getRegisterInfo(), STI.isTarget64BitLP64(), AvailableRegs);
			//assert ( 2 <= AvailableRegs.size() && "Cound not find 2 available registers" );
		
		#if ZERO_WITH_CG
			}
		#endif	
			// C = Clobbered
			unsigned CRegA = 0, CRegC = 0, CRegDI = 0;
			unsigned CReg1 = 0, CReg2 = 0, CReg3 = 0;
			
		#if ZERO_WITH_STACKPOINT
			
			// WARNING: The code below creates a new basic block, and initializes it with a RET instruction.
			// This is necessary to create a je instruction that jumps to it, ie to the last (RET) instruction. 
			// The sole purpose of this je instruction is to be able to skip accessing the GV
			// at start time, before linker has filled the GOT entry with the actual address.
			MachineInstr * OrigRet = Ret;
			MachineBasicBlock & OrigMBB = *OrigRet->getParent();
			bool IsLastBlock = ( OrigMBB.getFullName() == OrigLastMBB.getFullName()  );
		
			// Add RetMBB to the OrigMBB
			OrigMBB.addSuccessor(RetMBB);		// add the successors
			
			// Add the Ret instruction, the same that was in the original block
			if ( RetMBB->empty() ) {
				MachineInstr * dupRet = TII.duplicate ( OrigRet , F); // duplicate the original instruction
				RetMBB->push_back (dupRet); 
			}
			
			// Remove the RET from the block WITHOUT deleting it. 
			// At the very end of this code, we add this instruction back
			// This crashes on 3.8... :(
			//OrigRet = OrigRet->removeFromParent();
			//MachineBasicBlock & MBB = OrigMBB; // could also do the thing above and keep the stuff below
			MachineBasicBlock & MBB = *Ret->getParent();
			DebugLoc DL = Ret->getDebugLoc();	

		#else	// not ZERO_WITH_STACKPOINT
			MachineBasicBlock & MBB = *Ret->getParent();
			DebugLoc DL = Ret->getDebugLoc();			
		#endif			
			
#if ZERO_EACH_FUNCTION
			// Note: We cannot erase signal interrupt stack handling efficiently: we must add to each function an extra N bytes as the size of cpu state structure
			//       We can erase red zone efficiently
			// So we must increment the offset to account for vdso calls, signal handling, and redzone
			// Note: If we know that signals are not caught or they never touch sensitive memory regions, we don't need 
			// to add an offset for signals

#	if ZERO_EACH_FUNCTION_WITH_SIGNAL
			Offset += OFFSET_SIGNAL_HANDLING;
#	endif
			// the signal may be caught within the VDSO function, so we must add it to the offset
			if ( FunctionUseVDSO ) { Offset += OFFSET_VDSO_CALLS; }
			
			// Now zero the stack for all functions
			// Annotations would require the dev to annotate *all* callees
			// so we disable it now. Also this helps us test on entire code
			if ( Offset > 0 /* && IsFunctionMarkedSensitive( *IRFunction ) */) { 

				MachineInstr * ins = 0;
				int64_t Adjust = (!AvailableRegs.count(AX) + !AvailableRegs.count(CX) + !AvailableRegs.count(DI)) * Size;
				
				if ( Adjust >= Offset || 	// pushing the registers on the stack leaves nothing to zero out. In this case just use multiple MOV
					Offset <= Size ) 		// we can do this in a single MOV
					{	
					
					int64_t Off = 0;
					
					// Note: SP points to relevant data, so we must add S to Off
					#define INSERT_INST(S,O) do{												\
												unsigned n##S = Offset/S;						\
												for (unsigned c=0; c<n##S; ++c) {				\
													ins = BuildMI(MBB, *Ret, DL, TII.get(O))	\
															.addReg(SP).addImm(1)				\
															.addReg(0).addImm(-(Off+S))			\
															.addReg(0).addImm(-5);				\
													Off += S;									\
												}												\
												Offset -= (n##S*S);								\
											}while(0)
					
					INSERT_INST(8, X86::MOV64mi32);
					INSERT_INST(4, X86::MOV32mi);
					INSERT_INST(2, X86::MOV16mi);
					INSERT_INST(1, X86::MOV8mi);
					
					assert ( Offset == 0 && "Offset not zero??" );
					 
				} else {
					
					// In this case we use REP instruction to zero the stack
					//	xor al, al
					//	mov L, rcx
					//	lea rsp-offset, rdi
					//	rep stosb
						
					 
					#define PUSH_REG(R) do{																\
											if ( !AvailableRegs.count(R) ) {							\
												ins = BuildMI(MBB, *Ret, DL, TII.get(PUSH), R);			\
												assert ( Offset >= Size && "Offset < Size" );			\
												Offset -= Size; 										\
											}															\
										} while(0)
					
					// CR = 0 means the register is no longer clobbered
					#define POP_REG_AND_CLEAN(R,CR) do{													\
											if ( !AvailableRegs.count(R) ) {							\
												CR = 0;													\
												ins = BuildMI(MBB, *Ret, DL, TII.get(POP), R);			\
												ins = BuildMI(MBB, *Ret, DL, TII.get(MOVMI))			\
														.addReg(SP).addImm(1)							\
														.addReg(0).addImm(-Size)						\
														.addReg(0).addImm(-4);							\
											}															\
										} while(0)
					

					unsigned PUSH = STI.isTarget64BitLP64() ? X86::PUSH64r : X86::PUSH32r;					
					unsigned POP = STI.isTarget64BitLP64() ? X86::POP64r : X86::POP32r;					
					unsigned MOVMI = STI.isTarget64BitLP64() ? X86::MOV64mi32 : X86::MOV32mi;					
					unsigned LEA = STI.isTarget64BitLP64() ? X86::LEA64r : X86::LEA32r;					
					unsigned REP_STOS = 0; 				
					int64_t SizeUnit = 0;
							
					// Push live registers if needed
					PUSH_REG(AX);
					PUSH_REG(CX);
					PUSH_REG(DI);
							
					// Offset should be strictly greater than 0 after we've pushed the registers to stack
					assert ( Offset > 0 && "Offset <= 0" );
					
					// xor al, ax, eax, or rax - selecting the smaller register saves up some bytes
					if ( ((Offset % 8) == 0) && STI.isTarget64BitLP64() ) { 
						
						SizeUnit = 8;
						Offset /= 8;
						CRegA = X86::RAX;
						ins = BuildMI(MBB, *Ret, DL, TII.get(X86::XOR64rr), CRegA).addReg(CRegA).addReg(CRegA);
						REP_STOS = X86::REP_STOSQ_64;
						
					} else if ( (Offset % 4) == 0 ) { 
						
						SizeUnit = 4;
						Offset /= 4;
						CRegA = X86::EAX;
						ins = BuildMI(MBB, *Ret, DL, TII.get(X86::XOR32rr), CRegA).addReg(CRegA).addReg(CRegA);
						REP_STOS = STI.isTarget64BitLP64() ? X86::REP_STOSD_64 : X86::REP_STOSD_32;
						
					} else if ( (Offset % 2) == 0 ) { 
						
						SizeUnit = 2;
						Offset /= 2;
						CRegA = X86::AX;
						ins = BuildMI(MBB, *Ret, DL, TII.get(X86::XOR16rr), CRegA).addReg(CRegA).addReg(CRegA);
						REP_STOS = STI.isTarget64BitLP64() ? X86::REP_STOSW_64 : X86::REP_STOSW_32;
						
					} else {
						
						SizeUnit = 1;
						Offset /= 1;
						CRegA = X86::AL;
						ins = BuildMI(MBB, *Ret, DL, TII.get(X86::XOR8rr), CRegA).addReg(CRegA).addReg(CRegA);
						REP_STOS = STI.isTarget64BitLP64() ? X86::REP_STOSB_64 : X86::REP_STOSB_32;
						
					}
										
					// mov L/8-4-2-1, ecx
					// Note: I cannot optimize by using CL, CX because they don't zero extend
					// Use ECX rather than RCX to save up 2 bytes
					// Let's ensure that a 32-bit positive integer can hold Offset, otherwise we should set RCX rather than ECX
					assert ( (uint64_t)Offset <= (uint32_t)(-1) ); // We know Offset > 0 here already
					CRegC = X86::ECX;
					ins = BuildMI(MBB, *Ret, DL, TII.get(X86::MOV32ri), CRegC).addImm(Offset); 
										
					// lea rsp, rdi
					CRegDI = DI;
					ins = BuildMI(MBB, *Ret, DL, TII.get(LEA), CRegDI)
							.addReg(SP).addImm(1)
							.addReg(0).addImm(-(SizeUnit * Offset))	// SP now points to relevant data, we must therefore go right below it
							.addReg(0);
												
					// std - stack grows down, DF=1 => RDI -= 1
					// We don't need this because DF must be reset before function call/return
					// So instead of rep toward lower stack addresses, we start low and go upward
					// System V Intel386 ABI and AMD64 ABI says it must be clear on function entry/return
					// Since we're adding this code after epilogue, it's already clear
					// ins = BuildMI(MBB, *Ret, DL, TII.get(X86::STD));
					// Note: Most of the time, DF=0 already. TODO: remove this when unnecessary
					// ins = BuildMI(MBB, *Ret, DL, TII.get(X86::CLD));
												
					// rep stos
					ins = BuildMI(MBB, *Ret, DL, TII.get(REP_STOS));
					
					// pop and clean the register we saved to stack
					POP_REG_AND_CLEAN(DI, CRegDI);
					POP_REG_AND_CLEAN(CX, CRegC);
					POP_REG_AND_CLEAN(AX, CRegA);
					
				}
			}
			
#elif ZERO_WITH_STACKPOINT

			unsigned relocType = X86II::MO_NO_FLAG;	
			
			// Init the global variable __StackPoint that stores the minimum rsp reached during execution
			InitStackPointGlobalVariable(*Mod, STI.isTarget64BitLP64(), &relocType);
			
			// if the function calls a VDSO function, add the offset
			if ( FunctionUseVDSO ) { Offset += OFFSET_VDSO_CALLS; }

			// account for signal/red zone
			Offset += OFFSET_SIGNAL_HANDLING;

			// Keep track of the lower stack values for all functions
			// including the top one. We may be able to do this only for functions
			// in the call graph we care about. But libc must still have all 
			// its functions instrumented anyway...

			if ( Offset > 0 ) { 
					
				// 	lea rsp-N, Reg
				//	cmp Reg, globalValue
				//	cmovg Reg
				//	mov Reg, globalValue
								
				// Assume some registers are available for us to use
				// if not, then we'll push/clean the stack
				// assert ( AvailableRegs.size() >= 3 && "No available registers" );
				
				MachineInstr * ins = 0;
				unsigned LEA = STI.isTarget64BitLP64() ? X86::LEA64r : X86::LEA32r;
				unsigned CMPRR = STI.isTarget64BitLP64() ? X86::CMP64rr : X86::CMP32rr;
				unsigned CMOVA = STI.isTarget64BitLP64() ? X86::CMOVA64rr : X86::CMOVA32rr;
				unsigned MOVMR = STI.isTarget64BitLP64() ? X86::MOV64mr : X86::MOV32mr;	
				unsigned MOVRM = STI.isTarget64BitLP64() ? X86::MOV64rm : X86::MOV32rm;
												
				// Pick the first free registers that are not cx, di and ax
				// Note: We should also check they are of the proper size (64/32 depending on arch)
				// We currently do the check below in an assert()
				#define GET_ELT(n) *std::next(AvailableRegs.begin(), n)
				unsigned FreeReg[3] = {0};
				unsigned * pReg = &FreeReg[0];
				for ( unsigned i=0; i<AvailableRegs.size(); ++i ) {
					unsigned EltReg = GET_ELT(i);
					if ( !isSuperOrSubRegisterEq(TRI, EltReg, AX) && !isSuperOrSubRegisterEq(TRI, EltReg, CX) && !isSuperOrSubRegisterEq(TRI, EltReg, DI) ) {
						*pReg = EltReg;
						++pReg;
					}
				}
				
				assert ( FreeReg[0] && FreeReg[1] && FreeReg[2] && "Cound not find free registers distinct from AX, CX and DI" );
				CReg1 = FreeReg[0];
				CReg2 = FreeReg[1];
				CReg3 = FreeReg[2];
								
				bool areGPRs = STI.isTarget64BitLP64() ? 
											( X86::GR64RegClass.contains(CReg1) && X86::GR64RegClass.contains(CReg2) && X86::GR64RegClass.contains(CReg3) ) :
											( X86::GR32RegClass.contains(CReg1) && X86::GR32RegClass.contains(CReg2) && X86::GR32RegClass.contains(CReg3) );
				assert ( areGPRs && "Available registers not GPR" );
				
				//	lea GV, reg1
				//	mov (reg1), reg2
				//	lea rsp-N, reg3
				//	cmp reg3, reg2
				//	cmovg reg2, reg3
				//	mov reg3,(reg1) -> only if function is *not* marked as sensitive
				//errs() << "Offset:" << Offset << "\n";
				// We load the value stored (which represents the address where the global GV is)
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(MOVRM), CReg1)
							.addReg(X86::RIP)
							.addImm(1)
							.addReg(0)
							.addExternalSymbol(STACKPOINT_VAR, relocType)
							.addReg(0);	
				
				// Add the test code IFF this is the linker module
				if ( IsLinkerModule(*Mod) ) {

					ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(X86::CMP64ri8))
						  .addReg(CReg1)
						  .addImm(0);
										
					ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(X86::JE_1)).addMBB(RetMBB);
				}
							
				// mov (reg1), reg2 - copy the value of GV into reg2
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(MOVRM), CReg2)
							.addReg(CReg1).addImm(1).addReg(0).addImm(0).addReg(0);	
			
				// lea rsp-N, reg3
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(LEA), CReg3)
						.addReg(SP).addImm(1)
						.addReg(0).addImm(-Offset)	// SP now points to relevant data, we must therefore go right below it
						.addReg(0);
											
				// cmp reg3=rsp-N, reg2=GV
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(CMPRR))
							.addReg(CReg2)
							.addReg(CReg3);	
								
				// cmova reg3=rsp-N, reg2=GV
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(CMOVA), CReg2).addReg(CReg2).addReg(CReg3);	
				
				// mov reg2=GV,(reg1)=&GV
				// Note: this is not needed for the top-level function marked sensitive
				// since we reset the value of GV to current rsp before returning
				if ( ! IsFunctionMarkedSensitive( *IRFunction ) ) {
					ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(MOVMR), CReg1)
							.addReg(CReg2).addReg(0).addImm(0).addReg(0).addReg(CReg2);	
				}
			
			} else if ( IsFunctionMarkedSensitive( *IRFunction ) ) { // Offset = 0 here
				
				// For now just assert to see if this happens in practice. We need not erase if this is a marked function anyway
				assert ( 0 && "top-level function with 0 offset" );

			}
			
			// For the top function, add the erasure part using similar code as for ZERO_EXIT_FUNCTION_NAIVE
			if ( IsFunctionMarkedSensitive( *IRFunction ) ) { 
				
				unsigned MOVMI = STI.isTarget64BitLP64() ? X86::MOV64mi32 : X86::MOV32mi;
				unsigned SUBRR = STI.isTarget64BitLP64() ? X86::SUB64rr : X86::SUB32rr;
				unsigned LEA = STI.isTarget64BitLP64() ? X86::LEA64r : X86::LEA32r;
				unsigned MOVMR = STI.isTarget64BitLP64() ? X86::MOV64mr : X86::MOV32mr;
				unsigned MOVRM = STI.isTarget64BitLP64() ? X86::MOV64rm : X86::MOV32rm;
				unsigned SUBRI = STI.isTarget64BitLP64() ? X86::SUB64ri32 : X86::SUB32ri;
				
				int64_t startValue = -1; // 0xff...ff automatically with the relevant size
				MachineInstr * ins = 0;
				
				MachineBasicBlock & FirstMBB = *F.begin();
				MachineInstr & FirstInst = FirstMBB.instr_front();
				
				// Find an available register which is caller saved, so we need not save it ourselves
				// RAX, RCX and RDX are caller save register
				bool is64 = STI.isTarget64BitLP64();
				unsigned CallerSaveRegList[] = {is64 ? X86::RAX : X86::EAX, 
												is64 ? X86::RCX : X86::ECX, 
												is64 ? X86::RDX : X86::EDX};
				unsigned AReg = -1;
				const MachineRegisterInfo &MRI = F.getRegInfo();
				for ( unsigned c=0; c<LEN(CallerSaveRegList); ++c ) {
					if ( !MRI.isLiveIn(CallerSaveRegList[c]) ) {
						AReg = CallerSaveRegList[c];
						break;
					}
				}
				assert ( AReg != (unsigned)-1 && "Could not find available caller save register" );
				
				// 1. Set the value on __StackPoint at the start of the function
				// 1.1 mov 0xGV(rip), Areg
				ins = BuildMI(FirstMBB, FirstInst, FirstInst.getDebugLoc(), TII.get(MOVRM), AReg)
							.addReg(X86::RIP)
							.addImm(1)
							.addReg(0)
							.addExternalSymbol(STACKPOINT_VAR, relocType)
							.addReg(0);	
			 
				// 1.2 mov rsp, (AReg)=&GV
				ins = BuildMI(FirstMBB, FirstInst, FirstInst.getDebugLoc(), TII.get(MOVMI))
							.addReg(AReg).addImm(1)	
							.addReg(0).addImm(0)
							.addReg(0).addImm(startValue);

				// 2. Calculate the offset, which is the difference between the current rsp and the lowest one
				// recorded which is stored in reg2 (the value of GV). reg3 contains the value of rsp-N
				// reg3/2 should never be null since we've added an assertion above assert ( 0 && "top-level function with 0 offset" );
				assert ( CReg3 && CReg2 && "CReg2/3 not set" );
				
				// reg3 currently contains rsp - N. But we want rsp.
				// add reg3, N	-> reg3 += N -> reg3 = current stack pointer - NEEDS 7 bytes for instruction encoding
				// Instead reload rsp thru lea instruction -> NEEDS only 3 bytes for instruction encoding
				//ins = BuildMI(MBB, *Ret, DL, TII.get(ADDRI), CReg3)
				//		.addReg(CReg3).addImm(+Offset);
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(LEA), CReg3)
						.addReg(SP).addImm(1)
						.addReg(0).addImm(0)
						.addReg(0);
			
				// sub reg3=rsp, reg2=GV -> reg3 -= reg2 -> reg3 = offset to erase
				// We known that reg3 >= reg2, so offset >= 0
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(SUBRR), CReg3)
						.addReg(CReg3)
						.addReg(CReg2);
				
				// 3. Do the erasure, similar as for naive per-function ZERO_EXIT_FUNCTION_NAIVE
				// except here we dont check the Offset, we just take the view that we're OK
				// to erase with the expensive version since this is done only once...
				// NOTE: reg3 contains the offset
				#undef PUSH_REG
				#define PUSH_REG(R) do{																\
										if ( !AvailableRegs.count(R) ) {							\
											ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(PUSH), R);	\
											assert ( Offset >= 0 && "Offset < 0" );			\
											Offset += Size; 										\
										}															\
									}while(0)
				
				// CR = 0 means the register is no longer clobbered
				#undef POP_REG_AND_CLEAN
				#define POP_REG_AND_CLEAN(R,CR) do{													\
										if ( !AvailableRegs.count(R) ) {							\
											CR = 0;													\
											ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(POP), R);	\
											ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(MOVMI))	\
													.addReg(SP).addImm(1)							\
													.addReg(0).addImm(-Size)						\
													.addReg(0).addImm(-4);							\
										}															\
									}while(0)
				
				unsigned PUSH = STI.isTarget64BitLP64() ? X86::PUSH64r : X86::PUSH32r;					
				unsigned POP = STI.isTarget64BitLP64() ? X86::POP64r : X86::POP32r;									
				unsigned MOVRR = STI.isTarget64BitLP64() ? X86::MOV64rr : X86::MOV32rr;													
				unsigned REP_STOS = 0; 				
						
				// Note: if the runction is a leaf, we could just zero the stack without accessing GV
				// TODO 
				
				// Push live registers if needed
				// Note: here we don't bother substracting the register size from the
				// total offset because it would complicate the code for little gain
				// so in effect we may erase a little more than needed
				Offset = 0;	// reset the offset: that's very important. PUSH_REG does a +
				PUSH_REG(AX);
				PUSH_REG(CX);
				PUSH_REG(DI);
					
				// Fix the value in register reg3 if we've pushed some registers
				// reg3 -= Offset
				// and we should check if reg3 >= Offset. If this does not hold,
				// it will crash with seg fault at runtime as reg3 will become too big
				// and we will try to erase invalid memory...
				// Instead of adding complexity to the code (if-else), I don't do reg3 -= Offset
				// but I just move the address reg2=GV of the erasure start down. This means we will
				// erase up to 3*8=24 extra bytes. This will conserve the pushed values on 
				// the stack; which we erase with POP_REG_AND_CLEAN() below
				if ( Offset ) {
					// ins = BuildMI(&MBB, DebugLoc(), TII.get(SUBRI), CReg3)
					// 	.addReg(CReg3)
					// 	.addImm(Offset);
					ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(SUBRI), CReg2)
					 	.addReg(CReg2)
					 	.addImm(Offset);
				}
				
				// xor al - Don't want to check for value of CReg3 at runtime, use the byte version by default instead
				CRegA = X86::AL;
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(X86::XOR64rr), CRegA).addReg(CRegA).addReg(CRegA);
				REP_STOS = STI.isTarget64BitLP64() ? X86::REP_STOSB_64 : X86::REP_STOSB_32;
				
				// mov L, ecx		where L = reg3	
				// Note: we cannot optimize by using CL, CX because they don't zero extend	
				CRegC = CX;
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(MOVRR), CRegC).addReg(CReg3); 
				
				// mov reg2=GV (-Offset), rdi
				CRegDI = DI;
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(MOVRR), CRegDI).addReg(CReg2); 
						
				// std - stack grows down, DF=1 => RDI -= 1
				// We don't need this because DF must be reset before function call/return
				// So instead of rep toward lower stack addresses, we start low and go upward
				// System V Intel386 ABI and AMD64 ABI says it must be clear on function entry/return
				// Since we're adding this code after epilogue, it's already clear
				// ins = BuildMI(MBB, *Ret, DL, TII.get(X86::STD));
				// Note: Most of the time, DF=0 already. TODO: remove this when unnecessary
				// ins = BuildMI(MBB, *Ret, DL, TII.get(X86::CLD));
										
				// rep stos
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(REP_STOS));
				
				// Pop and clean the register we saved to stack
				POP_REG_AND_CLEAN(DI, CRegDI);
				POP_REG_AND_CLEAN(CX, CRegC);
				POP_REG_AND_CLEAN(AX, CRegA);
				
				
				// Before we finish, reset the GV to the current stack because sensitive functions may call each other
				// and we dont want to waste time erasing already-erased data.
				// So we set GV to the current stack pointer. When a higher-level sensitive function erases the stack,
				// it will do it only down to the stack here, not re-erasing what was already erased
				// mov rsp, *GV = (rg1)
				ins = BuildMI(MBB, *Ret, DebugLoc(), TII.get(MOVMR), CReg1)
							.addReg(SP).addReg(0).addImm(0).addReg(0).addReg(SP);
				
			}
				

#elif	ZERO_WITH_CG
		// This uses LTO to compute the CG

		// No need to account for VDSO calls and/or signal stack, this
		// is done in python script
		// Offset += (OFFSET_VDSO_CALLS + OFFSET_SIGNAL_HANDLING);

		// For the top function, add the erasure code using similar code as for ZERO_EXIT_FUNCTION_NAIVE
		// For other functions, we do nothing. Stack usage is stored in a file and used by python script
		if ( IsFunctionMarkedSensitive( *IRFunction ) ) { 
			
#	if ZERO_WITH_CG_BULK_REG		
			// Assume for now the sensitive function has a single return to make our life easier
			// A hack to force this on code is to have a wrapper function marked sensitive that simply calls
			// the function of interest
			// TODO: support multiple returns. May already be supported... How about in python script?
			assert ( 1 == Returns.size() && "Sensitive function has multiple returns. Not supported with ZERO_WITH_CG_BULK_REG" ); 
#	endif
			
			MachineInstr * ins = 0;
			
			#undef PUSH_REG
			#define PUSH_REG(R) do{																\
									if ( !AvailableRegs.count(R) ) {							\
										ins = BuildMI(MBB, *Ret, DL, TII.get(PUSH), R);			\
									}															\
								}while(0)
			
			// CR = 0 means the register is no longer clobbered
			#undef POP_REG_AND_CLEAN
			#define POP_REG_AND_CLEAN(R,CR) do{													\
									if ( !AvailableRegs.count(R) ) {							\
										CR = 0;													\
										ins = BuildMI(MBB, *Ret, DL, TII.get(POP), R);			\
										ins = BuildMI(MBB, *Ret, DL, TII.get(MOVMI))			\
												.addReg(SP).addImm(1)							\
												.addReg(0).addImm(-Size)						\
												.addReg(0).addImm(-4);							\
									}															\
								}while(0)
			
			unsigned PUSH = STI.isTarget64BitLP64() ? X86::PUSH64r : X86::PUSH32r;					
			unsigned POP = STI.isTarget64BitLP64() ? X86::POP64r : X86::POP32r;					
			unsigned MOVMI = STI.isTarget64BitLP64() ? X86::MOV64mi32 : X86::MOV32mi;					
			unsigned LEA = STI.isTarget64BitLP64() ? X86::LEA64r : X86::LEA32r;					
			unsigned REP_STOS = 0; 				
			int64_t SizeUnit = 0;
					
			// Push live registers if needed
			// Offset is not used anymore, except for writing to meta file
			PUSH_REG(AX);
			PUSH_REG(CX);
			PUSH_REG(DI);
				
			// xor rax, rax
			// Assume multiple of 8 bytes. We'll make sure to make the offset 8byte aligned in the python script
			CRegA = X86::RAX;
			ins = BuildMI(MBB, *Ret, DL, TII.get(X86::XOR64rr), CRegA).addReg(CRegA).addReg(CRegA);
			REP_STOS = X86::REP_STOSQ_64;
						
			// mov L/8, ecx
			CRegC = X86::ECX;
			ins = BuildMI(MBB, *Ret, DL, TII.get(X86::MOV32ri), CRegC).addImm( 0x01234567/* ECX is only 32bits */ ); 
						
			// lea rsp, rdi
			// magic value will be computed and inserted by python script, making 
			// sure to be a multiple of 8-bytes.
			CRegDI = DI;
			ins = BuildMI(MBB, *Ret, DL, TII.get(LEA), CRegDI)
					.addReg(SP).addImm(1)
					.addReg(0).addImm(-( 0xfedcba9876543210 ))
					.addReg(0);
					
			// std - stack grows down, DF=1 => RDI -= 1
			// We don't need this because DF must be reset before function call/return
			// So instead of rep toward lower stack addresses, we start low and go upward
			// System V Intel386 ABI and AMD64 ABI says it must be clear on function entry/return
			// Since we're adding this code after epilogue, it's already clear
			// ins = BuildMI(MBB, *Ret, DL, TII.get(X86::STD));
			// Note: Most of the time, DF=0 already. TODO: remove this when unnecessary
			// ins = BuildMI(MBB, *Ret, DL, TII.get(X86::CLD));
			
			// rep stos
			ins = BuildMI(MBB, *Ret, DL, TII.get(REP_STOS));
			
			// Pop and clean the register we saved to stack
			POP_REG_AND_CLEAN(DI, CRegDI);
			POP_REG_AND_CLEAN(CX, CRegC);
			POP_REG_AND_CLEAN(AX, CRegA);

#	if ZERO_WITH_CG_BULK_REG		
			
			// Create space for zeroing registers. The python script will replace them in-place.
			// Assume there will be 10 xor max; the python script will test for this
			const size_t NB_XOR = 20;
			for ( size_t nop=1; nop <=NB_XOR; ++nop ) {
				// 66 66 90             	data32 xchg %ax,%ax
				// Generate "3byte" nop, or more precisely, a 2byte padding + 1byte nop
				BuildMI(MBB, *Ret, DL, TII.get(X86::DATA16_PREFIX)); 
				BuildMI(MBB, *Ret, DL, TII.get(X86::DATA16_PREFIX)); 
				BuildMI(MBB, *Ret, DL, TII.get(X86::NOOP)); 
			}
			
#	endif // ZERO_WITH_CG_BULK_REG
			
		}
#endif

#if ZERO_WITH_CG && ZERO_WITH_CG_BULK_REG		
		// Get the list of ALL registers returned, ie across all Ret instructions
		// Note: returned registers will be appended to ReturnedRegs
		// I think they should all return the same anyway...
		addReturnedRegisters(*Ret, ReturnedRegs);
		
#endif

		// now zero registers

#if ZERO_WITH_STACKPOINT
		assert ( !RetMBB->empty() && "Empty RetMBB" );
		MachineInstr & CurrentRet =  RetMBB->instr_front();
#else
		MachineInstr & CurrentRet =  *Ret;
#endif

#if 0 && ZERO_EACH_FUNCTION /* disabled for now. Note: also disable for stack zeroing above and upper bits reg zeroing below */
		if ( !IsFunctionMarkedSensitive( *IRFunction ) ) {
			RegList.clear();
		}
#endif

#if ZERO_WITH_STACKPOINT && ZERO_WITH_STACKPOINT_BULK_REG
		// we want to zero ALL registers instead of doing per-function.
		// if function is not sensitive, do nothing: so I remove all used registers
		// from RegList to ensure the loop below does not enter
		if ( !IsFunctionMarkedSensitive( *IRFunction ) ) {
			// we could add a big if-statement over the loop below
			// instead I just empty the list so the loop won't enter
			RegList.clear();
			
		} else if ( !FunctionIsLeaf ) {
			// Function is sensitive
			// If it has callees, then RegList should be re-populated with all GPs - callee-saved ones:
			// this is because we don't know which GPs are used by callees, so we conservatively assume they all are
			// and we erase them all.
			// If the function is a leaf, then we need not waste time erasing registers other than those used
			// in this function, so we keep the list as is.
			// clear the list
			RegList.clear();
			// and re-populate registers
			populateWrittenGPRegisters( CurrentRet );
		}
#endif	

#if !(ZERO_WITH_CG && ZERO_WITH_CG_BULK_REG)
		// Get registers returned by this particular RET instruction we are processing
		// so that we can:
		// 		1) use them to check if a register is returned (below), and 
		// 		2) zero their upper bits out (further down)
		std::vector<unsigned> SingleRetRegs;
		getReturnedRegisters( CurrentRet, SingleRetRegs );
#endif

		// If ZERO_WITH_STACKPOINT_BULK_REG and not sensitive, RegList is empty
		for ( unsigned Reg : RegList ) {
			// Code taken from X86InstrInfo::breakPartialRegDependency
			unsigned Opc = 0;
			
			// If the register is used to return a value, don't zero it
#if !(ZERO_WITH_CG && ZERO_WITH_CG_BULK_REG)
			// For bulk zeroing in CG, we don't skip because we write to metafile each register returned and written to.
			// The logic on to what to zero out is then done in the python script
			if ( IsRegisterReturnedFromList( MBB, SingleRetRegs, Reg ) ) { continue; }	
#endif			
			// If the register was clobbered with non-sensitive data during stack zeroing, skip it too
			// even if we're zeroing in bulk, we need not consider these clobbered reg anymore -- even though they are used
			// Note: I'm ignoring auto-zero-extend from ENX -> RNX for simplicity. 
			// see https://stackoverflow.com/questions/25455447/x86-64-registers-rax-eax-ax-al-overwriting-full-register-contents
			// Note: for ZERO_WITH_CG CRegX may be 0 if non-sensitve function so no need for MACRO
			if ( CRegA && TRI.isSuperRegisterEq (Reg, CRegA) ) 		{ continue; }
			if ( CRegC && TRI.isSuperRegisterEq (Reg, CRegC) ) 		{ continue; }
			if ( CRegDI && TRI.isSuperRegisterEq(Reg, CRegDI) ) 	{ continue; }
			if ( CReg1 && TRI.isSuperRegisterEq (Reg, CReg1) ) 		{ continue; }
			if ( CReg2 && TRI.isSuperRegisterEq (Reg, CReg2) ) 		{ continue; }
			if ( CReg3 && TRI.isSuperRegisterEq (Reg, CReg3) ) 		{ continue; }
			
			// Select the right instruction depending on register we want to zero out
			if (X86::GR64RegClass.contains(Reg)) Opc = X86::XOR64rr;
			else if (X86::GR32RegClass.contains(Reg)) Opc = X86::XOR32rr;
			else if (X86::GR16RegClass.contains(Reg)) Opc = X86::XOR16rr;
			else if (X86::GR8RegClass.contains(Reg)) Opc = X86::XOR8rr;
			else if (X86::VR128RegClass.contains(Reg)) Opc = getX86SubTarget(MBB).hasAVX() ? X86::VXORPSrr : X86::XORPSrr;
			else if (X86::VR256RegClass.contains(Reg) || X86::VR512RegClass.contains(Reg)) {
				
				// not sure how to handle this case yet ... TODO
				assert (0 && "Found X86::VR256/512RegClass.contains(Reg) to xor");
				
			} else { 
				assert ( 0 && "Not a known register to xor" );
			}

			// Zero the register
#if ZERO_WITH_STACKPOINT
			BuildMI(MBB, *Ret, DebugLoc(), TII.get(Opc), Reg)
					.addReg(Reg).addReg(Reg); 
#elif ZERO_WITH_CG && ZERO_WITH_CG_BULK_REG
			// Don't add the instruction, record the register used instead
			if ( ! Contains(BulkRegs, Reg) ) {
				BulkRegs.push_back(Reg); 
			}
#else
			BuildMI(MBB, *Ret, DL, TII.get(Opc), Reg)
					.addReg(Reg).addReg(Reg); 
#endif 			
		}
		
		// Now that we're done zeroing used registers,
		// zero out upper bits of returned registers:
		// 	- bulk register zeroing: done in python script, only for sensitive functions
		//	- other configs, zero in all functions
#if !( ZERO_WITH_CG && ZERO_WITH_CG_BULK_REG )

#	if /*ZERO_EACH_FUNCTION*/ 0 || (ZERO_WITH_STACKPOINT && ZERO_WITH_STACKPOINT_BULK_REG)
		// If we're zeroing registers in bulk, zero the returned values only in sensitive functions
		if ( IsFunctionMarkedSensitive( *IRFunction ) ) {
			
#	endif // ZERO_WITH_STACKPOINT && ZERO_WITH_STACKPOINT_BULK_REG

		// This is taken care of by python script for bulk register zeroing with CG version
		// This code below erases upper bits of registers that are returned
		bool doneAnXMMReg = false;
		for ( unsigned RR : SingleRetRegs ) {
	
			unsigned SrcR = 0, DstR = 0, OC = 0;
			
			if ( X86::VR512RegClass.contains(RR) ) {
			  
				assert ( getX86SubTarget(F).hasAVX512() && "512bit but AVX512 not supported" );
			  
				// nothing to do, as this is the max register size
				// I keep an assert() because it was not encoutered in my tests,
				// and would like to validate it works
				assert ( 0 && "512bit returned register not supported" ); 

			} else if ( X86::VR256RegClass.contains(RR) ) {
			  
				assert ( getX86SubTarget(F).hasAVX() && "256bit but AVX256 not supported" );
			  
				// Not supported for now. TODO: erase the upper bits
				// Note that function getMOVinfoForRetReg may use
				// ZEROUPPER which assumes no YMM registers are returned!!
				// So we'll have to fix it too
				assert ( 0 && "256bit returned register not supported" ); 

			} if ( X86::VR128RegClass.contains(RR) ) {
					
				// This is an XMM register.
				assert ( getX86SubTarget(F).hasSSE1() && "SSE not supported but XMM register returned" );
					
				// upper bits of all YMM registers are zeroed with a single instruction if HasAVX - see getMOVinfoForRetReg
				if ( doneAnXMMReg && getX86SubTarget(F).hasAVX()) { continue; } 
					
				doneAnXMMReg = true;
				
			}
			
			// Currently we don't handle YMM/ZMM registers -- see above
			if ( ! getMOVinfoForRetReg( RR, SrcR, DstR, OC, getX86SubTarget(F).hasAVX() ) ) {
				continue; // nothing to zero out
			}
		
#	if ZERO_WITH_STACKPOINT
			if ( SrcR && DstR ) { BuildMI(MBB, *Ret, DebugLoc(), TII.get(OC), DstR).addReg(SrcR);	}
			else 				{ BuildMI(MBB, *Ret, DebugLoc(), TII.get(OC)); }
#	else
			if ( SrcR && DstR )	{ BuildMI(MBB, *Ret, DL, TII.get(OC), DstR).addReg(SrcR); }
			else 				{ BuildMI(MBB, *Ret, DL, TII.get(OC)); }
			 
#	endif
		}
		
#	if ZERO_WITH_STACKPOINT && ZERO_WITH_STACKPOINT_BULK_REG
	}
#	endif // ZERO_WITH_STACKPOINT && ZERO_WITH_STACKPOINT_BULK_REG

#endif // !(ZERO_WITH_CG && ZERO_WITH_CG_BULK_REG)


#if ZERO_WITH_STACKPOINT && ZERO_WITH_STACKPOINT_BULK_REG
		// For sensitive functions: we want to zero all AVX registers, using VZEROUPPER and VZEROALL
		// So we must ensure those are not returned by the current function
		// 1. If the function is a leaf, then all written registers were zeroed before, including AVX registers. 
		// 2. If not a leaf, we've re-populated written registers with *all* GPs (minus callee-saved) and 
		// we've zeroed them before. However this did not account for AVX registers. So we zero them now. 
		// We could have repopulated written registers with AVX registers too, instead of having separate code here. 
		// But we don't do this in order to take advantage of VZEROUPPER/VZEROALL if supported
		// on platform
		if ( !FunctionIsLeaf && IsFunctionMarkedSensitive( *IRFunction ) ) {
			
			// Sanity check no AVX registers are returned
			// TODO: support if AVX registers are returned
			for ( unsigned RR : SingleRetRegs ) {
				
				assert ( ! (X86::VR128RegClass.contains(RR) || X86::VR256RegClass.contains(RR) || X86::VR512RegClass.contains(RR) )
						 && "AVX registers returned"
						 );
			}
			
			// Now emit the instruction(s) to zero all AVX registers
			// Note: it's important we try the larger registers first, ie AVX512, AVX2, then AVX
			// list of AVX is:
			// http://llvm.org/docs/doxygen/html/X86Subtarget_8h_source.html NoSSE, SSE1, SSE2, SSE3, SSSE3, SSE41, SSE42, AVX, AVX2, AVX512F
			if ( getX86SubTarget(F).hasAVX512() ) {	// ZMM, 512bit wide
			
				assert ( 0 && "AVX512 not supported" );
				
			} else if ( getX86SubTarget(F).hasAVX() ) { 	// YMM0 - YMM15, 256bit wide
			
				assert ( 0 && "AVX256 not tested" );
				BuildMI(MBB, *Ret, DebugLoc(), TII.get(X86::VZEROALL));
				
			} else {
				
				// Must erase them all one by one
				
				const TargetRegisterClass * XMMs = &X86::VR128RegClass;
				// Since we only support x86_64, we don't need to test for SSE1
				// SEE1 has only XMM0-XMM7 - see https://en.wikipedia.org/wiki/Streaming_SIMD_Extensions
				for (unsigned n=0; n<XMMs->getNumRegs(); ++n) {
					unsigned RR = XMMs->getRegister(n);
					// Cannot use X86::VXORPSrr since this requires AVX
					//BuildMI(&MBB, DebugLoc(), TII.get(X86::XORPSrr), RR).addReg(RR);
					BuildMI(MBB, *Ret, DebugLoc(), TII.get(X86::XORPSrr), RR).addReg(RR).addReg(RR); 
				}
			}
			
		}
		
#endif	// ZERO_WITH_STACKPOINT && ZERO_WITH_STACKPOINT_BULK_REG

#if ZERO_WITH_STACKPOINT
		// Now delete the original RET if not needed
		if ( IsLastBlock ) {
			// can delete the original RET instruction, since
			// RetMBB already contains a RET and the current BB will
			// fall through
			OrigRet->eraseFromParent();
		}
		
#endif
		
	}
	
	
#if ZERO_WITH_CG

	// Add the stack info to the metafile	
	// Note: ldso part of libc is compiled without LTO, but the backend pass is launched with LTO
	if ( !(IsLibc && IsLinkerModule(*Mod)) ) {
		
		// Unfortunately we must re-open the file for each function
		// When MachineModulePass is implemented, we will switch to it
		std::fstream infs;
		std::fstream outfs;
		std::string line;
		std::string RegStr;
		
	#if ZERO_WITH_CG_BULK_REG
		
		// Get the string representation of the registers
		if ( ! ReturnedRegs.size() ) {
			RegStr.append("RET_VOID");	// always write a RET, even if no registers are returned
		} else {
			for (unsigned RetReg : ReturnedRegs) { 
				if ( RegStr.length() ) { RegStr.append( "," ); }
				RegStr.append("RET_");
				RegStr.append( TRI.getName( RetReg ) );
			}
		}
		
		for (unsigned AlteredReg : BulkRegs) { 
			if ( RegStr.length() ) { RegStr.append( "," ); }
			RegStr.append( TRI.getName( AlteredReg ) );
		}
		
	#endif // ZERO_WITH_CG_BULK_REG
		
		// I trust this input file, no path validation ...
		infs.open(META_FILE, std::fstream::in);
		assert ( infs.is_open() );
		
		// the file is deleted once only in the LTOZerostack.cpp pass as a LTO pass
		outfs.open(META_MACHINE_FILE, std::fstream::out | std::fstream::app);
		assert ( outfs.is_open() );
		
		//size_t pos = std::string::npos;
		while( !infs.eof() ) {
			std::getline (infs,line);
			std::string needle = IRFunction->getName().str();
			needle.append(":");
			if ( line.substr(0,needle.length()) == needle ) {
				size_t pos = 0;
				
				if ( IsFunctionMarkedSensitive( *IRFunction ) ) {
					// Prepend the sensitive status of the function if the function is marked sensitive
					outfs << "@" << SENSITIVE_ATTRIBUTE << "_?_";
				}
				
				// WARNING: the python code assumes the annotation info comes AFTER the sensitive info
				// Take care of type annotations to handle function pointers now
				std::set<std::string> TypeAttributes = GetTypeAttributes( *IRFunction );	
				assert ( (TypeAttributes.size() <= 1 ) && "Only one annotation allowed" );
				for ( std::string TypeAnno : TypeAttributes ) {
					// Prepend the type annotation of the function if annotated
					outfs << "@" << TypeAnno << "_?_";
				}
				
		#if ZERO_WITH_CG_BULK_REG // also print the registers
			outfs << IRFunction->getName().str() << "(" << Offset << "|" << RegStr << ")" << ":" << line.substr(pos+needle.length(), line.length()-1-pos-needle.length()) << "\n";
		#else
			outfs << IRFunction->getName().str() << "(" << Offset << ")" << ":" << line.substr(pos+needle.length(), line.length()-1-pos-needle.length()) << "\n";
		#endif // ZERO_WITH_CG_BULK_REG
				
				break;
			}
		}
		infs.close();
		outfs.close();
		
	}
#endif	// ZERO_WITH_CG

	}
	
	return true;
  }
  
	bool getMOVinfoForRetReg( unsigned RetReg, unsigned & SrcR, unsigned & DstR, unsigned & OC, bool HasAVX ) {
		
		bool retValue = false;
		switch ( RetReg ) {
			// ======================================
			//			GP registers - the most common
			// ======================================
			case X86::RAX: 
			case X86::RDX: 
				break; // nothing to zero out
			case X86::EAX:
				// MOVZX64rr32 does not exist, and on x86_64, upper bits of 64bit registers 
				// are silently zeroed out automatically when assigning 32bit values to it
				OC = X86::MOV32rr;
				DstR = X86::EAX;
				SrcR = X86::EAX;
				retValue = true;
				break;
				
			case X86::AX:
				OC = X86::MOVZX64rr16;	
				DstR = X86::RAX;
				SrcR = X86::AX;
				retValue = true;
				break;
				
			case X86::AL:
				OC = X86::MOVZX64rr8;	
				DstR = X86::RAX;
				SrcR = X86::AL;
				retValue = true;
				break;
				
			case X86::AH: 
				assert ( 0 && "Unsupported returned register AH" );
			
			// ======================================
			//			XMM registers
			// ======================================
			case X86::XMM0:
			case X86::XMM1:
			case X86::XMM2:
			case X86::XMM3:
			case X86::XMM4:
			case X86::XMM5:
			case X86::XMM6:
			case X86::XMM7:
			case X86::XMM8:
				// and so on up to X86::XMM15: TODO it we encounter them...
				// Note: if not AVX, then XMM are the biggest register so we need not do anything
				if ( HasAVX ) {
					
					OC = X86::VZEROUPPER;
					retValue = true;
				}
				break;
			
			// ======================================
			//	YMM registers:TODO: use VZEROALL
			//	Note: this will be redundant with XMM registers
			//  WARNING: we can use VZEROALL *only* if there's no XMM registers returned. 
			//  In this latter case, we must erase them one by one :(
			// ======================================
			
			// ======================================
			//	ZMM registers:TODO: must zero 
			//	them one by one :(
			// ======================================
			default: 
				assert ( 0 && "Unknown register returned" );
		}
		
		return retValue;
	}
  
  bool IsCalleeSavedRegister(MachineFunction &MF, unsigned Reg) {
	
	const TargetRegisterInfo & TRI = getTargetRegisterInfo(MF);
	const MCPhysReg *CSRegs = TRI.getCalleeSavedRegs(&MF);
	
	for (unsigned i = 0; CSRegs[i]; ++i) {
		unsigned CSR = CSRegs[i];
		if ( Reg == CSR ) { return true; }
	}
	return false;
  }
  
	bool IsBeingCalleeSavedRegister( MachineFrameInfo &MFI, const TargetRegisterInfo & TRI/*for printing only*/, unsigned Reg ) {
		
		const std::vector< CalleeSavedInfo > & CSIL = MFI.getCalleeSavedInfo();
		for ( CalleeSavedInfo CSI : CSIL ) {
			
			unsigned RegCSI = CSI.getReg();
						
			// push rax
			// eax = blabla
			// pop rax			-> populated before in PEI
			// zero eax 		-> Don't emit
			// ret
			if ( TRI.isSuperRegisterEq (Reg, RegCSI) ) {
				return true;
			}

			// push eax
			// rax = blabla
			// pop eax
			// zero rax 		-> We should emit. Not supported for now
			if ( TRI.isSubRegister (Reg, RegCSI) ) {
				assert (0 && "Smaller CSR than Reg");
			}
		}
		
		return false;
	}
	
	// WARNING: Ret must have a parent
	void addReturnedRegisters( MachineInstr & Ret, std::vector<unsigned> & RegList) {
		
		assert ( Ret.getParent() && "Instruction has no parent" );
		
		for ( MachineInstr::mop_iterator MOP = Ret.operands_begin(), MOPE=Ret.operands_end(); MOP!=MOPE; ++MOP) {
			MachineOperand &mOp = *MOP;
			if ( mOp.isReg() ) {
				unsigned RetReg = mOp.getReg();
				if ( ! Contains(RegList, RetReg) ) {
					RegList.push_back( RetReg );
				}
			}
		}
	}
	
	void getReturnedRegisters( MachineInstr & Ret, std::vector<unsigned> & RegList) {
		
		assert ( Ret.getParent() && "Instruction has no parent" );
		assert ( RegList.size() == 0 && "List of register not empty" );
		
		addReturnedRegisters( Ret, RegList );
	}

	// Add this function because this version does not have support for this
	// in recent version, TargetRegisterInfo has this function. Below is a copy of it
	bool isSuperOrSubRegisterEq(const TargetRegisterInfo & TRI, unsigned RegA, unsigned RegB) const {
    	return TRI.isSubRegisterEq(RegA, RegB) || TRI.isSuperRegister(RegA, RegB);
    }

	bool IsRegisterReturnedFromList( MachineBasicBlock & DummyMBB, std::vector<unsigned> & RegList, unsigned Reg ) {
		
		const TargetRegisterInfo & TRI = getTargetRegisterInfo (DummyMBB);
		
		for ( unsigned RetReg : RegList ) {
			if ( isSuperOrSubRegisterEq(TRI,  RetReg, Reg ) ) {
				return true;
			}
		}
		return false;
	}
	
  
  bool isLibcStartFunction ( StringRef Name ) {
	return isMuslStartFunction(Name);
  }
  
  // These musl-libc functions don't return but that's fine
  // since they are only called at startup
  bool isMuslStartFunction ( StringRef Name ) {	
	for (size_t i=0; i< LEN(MUSL_SAFE_START_NON_RETURN); ++i) {
		if ( Name == MUSL_SAFE_START_NON_RETURN[i] ) return true;
	}
	return false;
  }
  
  
  bool isLibcNoReturnFunction ( StringRef Name ) {
	
	for (size_t i=0; i< LEN(MUSL_SAFE_NON_RETURN); ++i) {
		if ( Name == MUSL_SAFE_NON_RETURN[i] ) return true;
	}
	return false;
  }
  
  bool isCompilerRtNoReturnFunction ( StringRef Name ) {
  	for (size_t i=0; i< LEN(COMPILER_RT_NON_RETURN); ++i) {
		if ( Name == COMPILER_RT_NON_RETURN[i] ) return true;
	}
	return false;
  }
  
  bool isExit ( StringRef Name ) {
  	for (size_t i=0; i< LEN(EXIT_NON_RETURN); ++i) {
		if ( Name == EXIT_NON_RETURN[i] ) return true;
	}

  	for (size_t i=0; i< LEN(EXEC_NON_RETURN); ++i) {
		if ( Name.substr(0,strlen(EXEC_NON_RETURN[i])) == EXEC_NON_RETURN[i] ) return true;
	}
	return false;
  }
  
  bool isMuslVdso ( StringRef Name ) {
  	for (size_t i=0; i< LEN(VDSO_FUNCTIONS); ++i) {
		if ( Name == VDSO_FUNCTIONS[i] ) return true;
	}
	return false;
  }
  
  // here as example. Can be used when compiling openssl
  bool isOsslNoReturn ( StringRef Name ) {
	if ( "OpenSSLDie" == Name ) {
		return true;
	}
	return false;
  }
 
  



    // Taken from X86FrameLowering
	void findDeadCallerSavedRegOnReturn(const MachineInstr &Inst,
                                       const X86RegisterInfo & TRI,
                                       bool Is64Bit, 
                                       std::set<unsigned> & ArrRegs) { 
										   
		const MachineFunction *MF = Inst.getParent()->getParent();
		const Function *F = MF->getFunction();
		if (!F || MF->getMMI().callsEHReturn()) {
			return;
		}
		
		const TargetRegisterClass &AvailableRegs = *TRI.getGPRsForTailCall(*MF);

		unsigned Opc = Inst.getOpcode();
		switch (Opc) {
			default: assert (0 && "Ret instruction not present in switch/case");
			// WARNING: more recent versions of the backend have this instruction!
			//case X86::RET:
			case X86::RETL:
			case X86::RETQ:
			case X86::RETIL:
			case X86::RETIQ:
			case X86::TCRETURNdi:
			case X86::TCRETURNri:
			case X86::TCRETURNmi:
			case X86::TCRETURNdi64:
			case X86::TCRETURNri64:
			case X86::TCRETURNmi64:
			case X86::EH_RETURN:
			case X86::EH_RETURN64: {
				
				SmallSet<uint16_t, 8> Uses;
				for (unsigned i = 0, e = Inst.getNumOperands(); i != e; ++i) {
					
					const MachineOperand &MO = Inst.getOperand(i);
					
					if (!MO.isReg() || MO.isDef()) {
						continue;
					}
					
					unsigned Reg = MO.getReg();
					if (!Reg) {
						continue;
					}
					
					for (MCRegAliasIterator AI(Reg, &TRI, true); AI.isValid(); ++AI) {
						Uses.insert(*AI);
					}
				}

				for (auto CS : AvailableRegs) {
					
					if (!Uses.count(CS) && CS != X86::RIP && !ArrRegs.count(CS)) {
						ArrRegs.insert(CS);
					}
				}
			}
		}

}

  virtual bool runOnMachineFunction(MachineFunction &F) {

 #if DISABLE_PASS
 	return true;
 #endif 	
	const Function *IRFunction = F.getFunction();
	
    // certain functions are allowed to not return, inlibc and compiler-rt
    if ( isLibcStartFunction( IRFunction->getName() ) ) { return false; }
    
    if ( isLibcNoReturnFunction( IRFunction->getName() ) ) { return false; }
    
    if ( isCompilerRtNoReturnFunction( IRFunction->getName() ) ) { return false; }
       
    // Can add other functions here. In production environment, these should be passed
    // thru a compiler option
    // if ( isOsslNoReturn( IRFunction->getName() ) ) { return false; }
        
   	if ( IsPEI ) { /* Prolo/Epilog/Inserted */
		return runOnMachineFunctionAfterPEI(F);
   	} else {
		return runOnMachineFunctionBeforePEI(F);
   	}
  }
};
}

char ZeroStackPass::ID = 0;

FunctionPass *llvm::createZeroStackPass(/*llvm::TargetPassConfig & TPC,*/ bool isPEI ) {
  return new ZeroStackPass(isPEI);
}
