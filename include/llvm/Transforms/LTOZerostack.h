#ifndef LLVM_TRANSFORMS_LTOZEROSTACK_H
#define LLVM_TRANSFORMS_LTOZEROSTACK_H

namespace llvm {

  class ModulePass;

  ModulePass *createLTOZerostackPass();

} // End llvm namespace
#endif
