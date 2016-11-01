install(PROGRAMS ktest-tool DESTINATION bin)

# Copy into the build directory's binary directory
# so integration tests can find it
configure_file(ktest-tool "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/ktest-tool" COPYONLY)
