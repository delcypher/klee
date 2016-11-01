add_executable(klee
	main.cpp
)

klee_get_llvm_libs(LLVM_LIBS
	bitreader
	bitwriter
	engine
	ipo
	irreader
	jit
	linker
	support
)
set(KLEE_LIBS kleeCore kleeBasic kleeModule kleaverSolver kleaverExpr kleeSupport)

target_link_libraries(klee ${KLEE_LIBS} ${LLVM_LIBS})

install(TARGETS klee RUNTIME DESTINATION bin)

# The KLEE binary depends on the runtimes
add_dependencies(klee BuildKLEERuntimes)
