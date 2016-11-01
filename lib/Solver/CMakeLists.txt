klee_add_component(kleaverSolver
	CachingSolver.cpp
	CexCachingSolver.cpp
	ConstantDivision.cpp
	CoreSolver.cpp
	DummySolver.cpp
	FastCexSolver.cpp
	IncompleteSolver.cpp
	IndependentSolver.cpp
	MetaSMTSolver.cpp
	PCLoggingSolver.cpp
	QueryLoggingSolver.cpp
	SMTLIBLoggingSolver.cpp
	Solver.cpp
	SolverImpl.cpp
	SolverStats.cpp
	STPBuilder.cpp
	STPSolver.cpp
	ValidatingSolver.cpp
	Z3Builder.cpp
	Z3Solver.cpp
)

target_link_libraries(kleaverSolver PRIVATE ${KLEE_SOLVER_LIBRARIES})
