##===- unittests/Solver/Makefile ---------------------------*- Makefile -*-===##

LEVEL := ../..
include $(LEVEL)/Makefile.config

TESTNAME := Solver
USEDLIBS := kleaverSolver.a kleaverExpr.a kleeSupport.a kleeBasic.a
LINK_COMPONENTS := support

include $(LLVM_SRC_ROOT)/unittests/Makefile.unittest

ifneq ($(ENABLE_STP),0)
  LIBS += $(STP_LDFLAGS)
endif

include $(PROJ_SRC_ROOT)/MetaSMT.mk
