function(klee_add_component target_name)
  add_library(${target_name} ${ARGN})
  # Use of `PUBLIC` means these will propagate to targets that use this component.
  target_compile_options(${target_name} PUBLIC ${KLEE_COMPONENT_CXX_FLAGS})
  target_include_directories(${target_name} PUBLIC ${KLEE_COMPONENT_EXTRA_INCLUDE_DIRS})
  target_compile_definitions(${target_name} PUBLIC ${KLEE_COMPONENT_CXX_DEFINES})
endfunction()
