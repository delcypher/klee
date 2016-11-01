set(GCC_AND_CLANG_WARNINGS
  "-Wall"
)
set(GCC_ONLY_WARNINGS "")
set(CLANG_ONLY_WARNINGS "")

set(WARNING_FLAGS_TO_CHECK "")
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
  list(APPEND WARNING_FLAGS_TO_CHECK ${GCC_AND_CLANG_WARNINGS})
  list(APPEND WARNING_FLAGS_TO_CHECK ${GCC_ONLY_WARNINGS})
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  list(APPEND WARNING_FLAGS_TO_CHECK ${GCC_AND_CLANG_WARNINGS})
  list(APPEND WARNING_FLAGS_TO_CHECK ${CLANG_ONLY_WARNINGS})
else()
  message(AUTHOR_WARNING "Unknown compiler")
endif()

# Loop through flags and use the ones which the compiler supports
foreach (flag ${WARNING_FLAGS_TO_CHECK})
  # Note `add_global_cxx_flag()` is used rather than
  # `klee_component_add_cxx_flag()` because warning
  # flags are typically useful for building everything.
  add_global_cxx_flag("${flag}")
endforeach()

option(WARNINGS_AS_ERRORS "Treat compiler warnings as errors" OFF)
if (WARNINGS_AS_ERRORS)
  if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang") OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
    add_global_cxx_flag("-Werror" REQUIRED)
  else()
    message(AUTHOR_WARNING "Unknown compiler")
  endif()
  message(STATUS "Treating compiler warnings as errors")
else()
  message(STATUS "Not treating compiler warnings as errors")
endif()
