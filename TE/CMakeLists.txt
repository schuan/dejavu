add_llvm_library(LLVMTE
  TE.cpp
  TimedExecution.cpp
  )

add_dependencies(LLVMTE intrinsics_gen)
