#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(klee-replay
	fd_init.c
	file-creator.c
	klee-replay.c
	klee_init_env.c
)

target_link_libraries(klee-replay kleeBasic ${LIBCAP_LIBRARIES} ${LIBUTIL_LIBRARIES})

install(TARGETS klee-replay RUNTIME DESTINATION bin)
