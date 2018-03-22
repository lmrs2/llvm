add_llvm_library(LLVMLTOZerostack
	LTOZerostack.cpp

	ADDITIONAL_HEADER_DIRS
  	${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms
	)

add_dependencies(LLVMLTOZerostack intrinsics_gen)
