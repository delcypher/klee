###############################################################################
# Minimum CMake version and policies
###############################################################################
cmake_minimum_required(VERSION 2.8.12)
if (POLICY CMP0054)
  # FIXME: This is horrible. With the old behaviour,
  # quoted strings like "MSVC" in if() conditionals
  # get implicitly dereferenced. The NEW behaviour
  # doesn't do this but CMP0054 was only introduced
  # in CMake 3.1 and we support lower versions as the
  # minimum. We could set NEW here but it would be very
  # confusing to use NEW for some builds and OLD for others
  # which could lead to some subtle bugs. Instead when the
  # minimum version is 3.1 change this policy to NEW and remove
  # the hacks in place to work around it.
  cmake_policy(SET CMP0054 OLD)
endif()

# This overrides the default flags for the different CMAKE_BUILD_TYPEs
set(CMAKE_USER_MAKE_RULES_OVERRIDE_C
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake/c_flags_override.cmake")
set(CMAKE_USER_MAKE_RULES_OVERRIDE_CXX
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cxx_flags_override.cmake")
project(KLEE CXX C)

###############################################################################
# Project version
###############################################################################
set(KLEE_VERSION_MAJOR 1)
set(KLEE_VERSION_MINOR 2)
set(KLEE_VERSION_PATCH 0)
set(KLEE_VERSION_TWEAK 0)
set(KLEE_VERSION "${KLEE_VERSION_MAJOR}.${KLEE_VERSION_MINOR}.${KLEE_VERSION_PATCH}.${KLEE_VERSION_TWEAK}")
message(STATUS "KLEE version ${KLEE_VERSION}")
set(PACKAGE_STRING "\"KLEE ${KLEE_VERSION}\"")
set(PACKAGE_URL "\"https://klee.github.io\"")

################################################################################
# Set various useful variables depending on CMake version
################################################################################
if (("${CMAKE_VERSION}" VERSION_EQUAL "3.2") OR ("${CMAKE_VERSION}" VERSION_GREATER "3.2"))
  # In CMake >= 3.2 add_custom_command() supports a ``USES_TERMINAL`` argument
  set(ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG "USES_TERMINAL")
else()
  set(ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG "")
endif()

################################################################################
# Sanity check - Disallow building in source.
# Otherwise we would overwrite the Makefiles of the old build system.
################################################################################
if ("${CMAKE_SOURCE_DIR}" STREQUAL "${CMAKE_BINARY_DIR}")
  message(FATAL_ERROR "In source builds are not allowed. You should invoke "
          "CMake from a different directory.")
endif()

################################################################################
# Build type
################################################################################
message(STATUS "CMake generator: ${CMAKE_GENERATOR}")
if (DEFINED CMAKE_CONFIGURATION_TYPES)
  # Multi-configuration build (e.g. Xcode). Here
  # CMAKE_BUILD_TYPE doesn't matter
  message(STATUS "Available configurations: ${CMAKE_CONFIGURATION_TYPES}")
else()
  # Single configuration generator (e.g. Unix Makefiles, Ninja)
  set(available_build_types Debug Release RelWithDebInfo MinSizeRel)
  if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "CMAKE_BUILD_TYPE is not set. Setting default")
    message(STATUS "The available build types are: ${available_build_types}")
    set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE String
        "Options are ${available_build_types}"
        FORCE)
    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${available_build_types})
  endif()
  message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")
endif()


################################################################################
# Add our CMake module directory to the list of module search directories
################################################################################
list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake/modules")

################################################################################
# Assertions
################################################################################
option(ENABLE_KLEE_ASSERTS "Enable KLEE assertions" ON)
if (ENABLE_KLEE_ASSERTS)
  message(STATUS "KLEE assertions enabled")
  # Assume that -DNDEBUG isn't set.
else()
  message(STATUS "KLEE assertions disabled")
  list(APPEND KLEE_COMPONENT_CXX_DEFINES "NDEBUG")
endif()

################################################################################
# KLEE timestamps
################################################################################
option(KLEE_ENABLE_TIMESTAMP "Add timestamps to KLEE sources" OFF)

################################################################################
# Include useful CMake functions
################################################################################
include(GNUInstallDirs)
include(CheckIncludeFile)
include(CheckIncludeFileCXX)
include(CheckFunctionExists)
include(CheckPrototypeDefinition)
include("${CMAKE_SOURCE_DIR}/cmake/string_to_list.cmake")
include("${CMAKE_SOURCE_DIR}/cmake/klee_component_add_cxx_flag.cmake")
include("${CMAKE_SOURCE_DIR}/cmake/add_global_flag.cmake")

################################################################################
# Compiler flags for KLEE components
# Subsequent commands will append to these. These are used instead of
# directly modifying CMAKE_CXX_FLAGS so that other code can be easily built with
# different flags.
################################################################################
set(KLEE_COMPONENT_EXTRA_INCLUDE_DIRS "")
set(KLEE_COMPONENT_CXX_DEFINES "")
set(KLEE_COMPONENT_CXX_FLAGS "")
set(KLEE_SOLVER_LIBRARIES "")
set(KLEE_COMPONENT_EXTRA_LIBRARIES "")

################################################################################
# Find LLVM
################################################################################
include(${CMAKE_SOURCE_DIR}/cmake/find_llvm.cmake)
set(NEEDED_LLVM_VARS
  LLVM_PACKAGE_VERSION
  LLVM_VERSION_MAJOR
  LLVM_VERSION_MINOR
  LLVM_VERSION_PATCH
  LLVM_DEFINITIONS
  LLVM_ENABLE_ASSERTIONS
  LLVM_ENABLE_EH
  LLVM_ENABLE_RTTI
  LLVM_INCLUDE_DIRS
  LLVM_LIBRARY_DIRS
  LLVM_TOOLS_BINARY_DIR
  TARGET_TRIPLE
)

foreach (vname ${NEEDED_LLVM_VARS})
  message(STATUS "${vname}: \"${${vname}}\"")
  if (NOT (DEFINED "${vname}"))
    message(FATAL_ERROR "${vname} was not defined")
  endif()
endforeach()

if (LLVM_ENABLE_ASSERTIONS)
  # Certain LLVM debugging macros only work when LLVM was built with asserts
  set(ENABLE_KLEE_DEBUG 1) # for config.h
else()
  unset(ENABLE_KLEE_DEBUG) # for config.h
endif()

if (NOT LLVM_ENABLE_EH)
  klee_component_add_cxx_flag("-fno-exceptions" REQUIRED)
endif()

if (NOT LLVM_ENABLE_RTTI)
  klee_component_add_cxx_flag("-fno-rtti" REQUIRED)
endif()

list(APPEND KLEE_COMPONENT_CXX_DEFINES ${LLVM_DEFINITIONS})
list(APPEND KLEE_COMPONENT_EXTRA_INCLUDE_DIRS ${LLVM_INCLUDE_DIRS})

# FIXME: This doesn't look like it's being used.
# For config.h.
if ("${LLVM_PACKAGE_VERSION}" MATCHES "svn$")
  set(LLVM_IS_RELEASE 0)
else()
  set(LLVM_IS_RELEASE 1)
endif()

# Find llvm-link
set(LLVM_LINK "${LLVM_TOOLS_BINARY_DIR}/llvm-link")
if (NOT EXISTS "${LLVM_LINK}")
  message(FATAL_ERROR "Failed to find llvm-link at \"${LLVM_LINK}\"")
endif()

# Find llvm-ar
set(LLVM_AR "${LLVM_TOOLS_BINARY_DIR}/llvm-ar")
if (NOT EXISTS "${LLVM_AR}")
  message(FATAL_ERROR "Failed to find llvm-ar at \"${LLVM_AR}\"")
endif()

# Find llvm-as
set(LLVM_AS "${LLVM_TOOLS_BINARY_DIR}/llvm-as")
if (NOT EXISTS "${LLVM_AS}")
  message(FATAL_ERROR "Failed to find llvm-as at \"${LLVM_AS}\"")
endif()

################################################################################
# Find bitcode compiler
################################################################################
include("${CMAKE_SOURCE_DIR}/cmake/find_bitcode_compiler.cmake")
message(STATUS "LLVMCC: ${LLVMCC}")
if (NOT EXISTS "${LLVMCC}")
  message(FATAL_ERROR "Cannot find C bitcode compiler \"${LLVMCC}\"")
endif()
message(STATUS "LLVMCXX: ${LLVMCXX}")
if (NOT EXISTS "${LLVMCXX}")
  message(FATAL_ERROR "Cannot find C++ bitcode compiler \"${LLVMCXX}\"")
endif()

################################################################################
# C++ version
################################################################################
option(USE_CXX11 "Use C++11" OFF)
if ("${LLVM_PACKAGE_VERSION}" VERSION_GREATER "3.5.0")
  message(STATUS "Using LLVM >= 3.5.0. Forcing using C++11")
  set(USE_CXX11 ON CACHE BOOL "Use C++11" FORCE)
endif()

if (USE_CXX11)
  message(STATUS "Enabling C++11")
  # FIXME: Use CMake's own mechanism for managing C++ version.
  # Set globally because it is unlikely we would want to compile
  # using mixed C++ versions.
  add_global_cxx_flag("-std=c++11" REQUIRED)
else()
  # This is needed because with GCC 6 the default changed from gnu++98 to
  # gnu++14.
  add_global_cxx_flag("-std=gnu++98" REQUIRED)
endif()

################################################################################
# Warnings
################################################################################
include(${CMAKE_SOURCE_DIR}/cmake/compiler_warnings.cmake)

################################################################################
# Solvers
################################################################################

# STP: Use CMake facility to detect. The user can pass `-DSTP_DIR=` to force
# a particular directory.
option(ENABLE_SOLVER_STP "Enable STP solver support" ON)
if (ENABLE_SOLVER_STP)
  find_package(STP CONFIG)
  if (STP_FOUND)
    message(STATUS "Found STP version ${STP_VERSION}")
    list(APPEND KLEE_SOLVER_LIBRARIES "${STP_SHARED_LIBRARY}")
    list(APPEND KLEE_COMPONENT_EXTRA_INCLUDE_DIRS "${STP_INCLUDE_DIRS}")
    message(STATUS "STP_DIR: ${STP_DIR}")
    set(ENABLE_STP 1) # For config.h
  else()
    message(STATUS "STP not found. Try setting `-DSTP_DIR=/path` where"
      " `/path` is the directory containing `STPConfig.cmake`")
    set(ENABLE_STP 0) # For config.h
  endif()
else()
  message(STATUS "STP solver support disabled")
  set(ENABLE_STP 0) # For config.h
endif()

# Z3
option(ENABLE_SOLVER_Z3 "Enable Z3 solver support" ON)
if (ENABLE_SOLVER_Z3)
  find_package(Z3)
  if (Z3_FOUND)
    message(STATUS "Found Z3")
    set(ENABLE_Z3 1) # For config.h
    list(APPEND KLEE_COMPONENT_EXTRA_INCLUDE_DIRS ${Z3_INCLUDE_DIRS})
    list(APPEND KLEE_SOLVER_LIBRARIES ${Z3_LIBRARIES})

    # Check the signature of `Z3_get_error_msg()`
    set (_old_CMAKE_REQUIRED_LIBRARIES "${CMAKE_REQUIRED_LIBRARIES}")
    set(CMAKE_REQUIRED_LIBRARIES ${CMAKE_REQUIRED_LIBRARIES} ${Z3_LIBRARIES})
    check_prototype_definition(Z3_get_error_msg
      "Z3_string Z3_get_error_msg(Z3_context c, Z3_error_code err)"
      "NULL" "${Z3_INCLUDE_DIRS}/z3.h" HAVE_Z3_GET_ERROR_MSG_NEEDS_CONTEXT)
    set(CMAKE_REQUIRED_LIBRARIES ${_old_CMAKE_REQUIRED_LIBRARIES})
    if (HAVE_Z3_GET_ERROR_MSG_NEEDS_CONTEXT)
      message(STATUS "Z3_get_error_msg requires context")
    else()
      message(STATUS "Z3_get_error_msg does not require context")
    endif()
  else()
    message(STATUS "Z3 not found")
    set(ENABLE_Z3 0) # For config.h
  endif()
else()
  message(STATUS "Z3 solver support disabled")
  set(ENABLE_Z3 0) # For config.h
endif()

# metaSMT
option(ENABLE_SOLVER_METASMT "Enable metaSMT solver support" OFF)
if (ENABLE_SOLVER_METASMT)
  set(ENABLE_METASMT 1)
  message(FATAL_ERROR "metaSMT support not implemented")
else()
  set(ENABLE_METASMT 0) # For config.h
endif()

if ((NOT ${ENABLE_Z3}) AND (NOT ${ENABLE_STP}) AND (NOT ${ENABLE_METASMT}))
  message(FATAL_ERROR "No solver was detected. At least one solver is required.")
endif()


################################################################################
# Support for compressed logs
################################################################################
find_package(ZLIB)
if (${ZLIB_FOUND})
  set(HAVE_ZLIB_H 1) # For config.h
	set(TARGET_LIBS ${TARGET_LIBS} z)
  list(APPEND KLEE_COMPONENT_EXTRA_LIBRARIES ${ZLIB_LIBRARIES})
  list(APPEND KLEE_COMPONENT_EXTRA_INCLUDE_DIRS ${ZLIB_INCLUDE_DIRS})
else()
  unset(HAVE_ZLIB_H) # For config.h
endif()

################################################################################
# TCMalloc support
################################################################################
check_include_file_cxx(gperftools/malloc_extension.h HAVE_GPERFTOOLS_MALLOC_EXTENSION_H)
if (${HAVE_GPERFTOOLS_MALLOC_EXTENSION_H})
  # FIXME: We should check the library exists and that it can be linked against too!
  list(APPEND KLEE_COMPONENT_EXTRA_LIBRARIES tcmalloc_minimal)
endif()

################################################################################
# Detect libcap
################################################################################
check_include_file("sys/capability.h" HAVE_SYS_CAPABILITY_H)
if (HAVE_SYS_CAPABILITY_H)
  find_library(LIBCAP_LIBRARIES
    NAMES cap
    DOC "libcap library"
  )
  if (NOT LIBCAP_LIBRARIES)
    message(FATAL_ERROR "Found \"sys/capability.h\" but could not find libcap")
  endif()
else()
  set(LIBCAP_LIBRARIES "")
endif()

################################################################################
# Detect libutil
################################################################################
check_include_file("pty.h" HAVE_PTY_H)
if (HAVE_PTY_H)
  find_library(LIBUTIL_LIBRARIES
    NAMES util
    DOC "libutil library. Typically part of glibc")
  if (NOT LIBCAP_LIBRARIES)
    message(FATAL_ERROR "Found \"pty.h\" but could not find libutil")
  endif()
endif()

################################################################################
# Miscellaneous header file detection
################################################################################
check_function_exists(mallinfo HAVE_MALLINFO) # FIXME: should test CXX compiler not C
check_function_exists(__ctype_b_loc HAVE_CTYPE_EXTERNALS) # FIXME: shoudl test CXX compiler not C

check_include_file_cxx(malloc/malloc.h HAVE_MALLOC_MALLOC_H)
check_function_exists(malloc_zone_statistics HAVE_MALLOC_ZONE_STATISTICS)

# FIXME: Remove these. These macros don't seem to be used by the KLEE code base.
# but are in KLEE's config.h template.
check_include_file_cxx("inttypes.h" HAVE_INTTYPES_H)
check_include_file_cxx("memory.h" HAVE_MEMORY_H)
check_include_file_cxx("stdint.h" HAVE_STDINT_H)
check_include_file_cxx("stdlib.h" HAVE_STDLIB_H)
check_include_file_cxx("strings.h" HAVE_STRINGS_H)
check_include_file_cxx("string.h" HAVE_STRING_H)
check_include_file_cxx("sys/stat.h" HAVE_SYS_STAT_H)
check_include_file_cxx("sys/types.h" HAVE_SYS_TYPES_H)
check_include_file_cxx("unistd.h" HAVE_UNISTD_H)
set(STDC_HEADERS 1) # HACK


# FIXME: This is needed by the runtime not KLEE itself so we are testing the wrong
# compiler.
check_include_file("selinux/selinux.h" HAVE_SELINUX_SELINUX_H)
check_include_file("sys/acl.h" HAVE_SYS_ACL_H)
if (HAVE_SELINUX_SELINUX_H)
  set(HAVE_SELINUX 1)
  # FIXME: I haven't tested this at all!

  # Test what function signature we need to use for SELinux. The signatures
  # have changed between 2.2 and 2.3. In particular, the type of the "security
  # context" parameter was changed from char * to const char *, with this
  # patch: [PATCH] Get rid of security_context_t and fix const declarations.
  # [http://www.spinics.net/lists/selinux/msg14827.html]
  check_prototype_definition(setcon
    "setcon(char* context)"
    "int"
    "selinux/selinux.h"
    SELINUX_SECURITY_CTX_NO_CONST
  )
  if (SELINUX_SECURITY_CTX_NO_CONST)
    set(KLEE_SELINUX_CTX_CONST "")
  else()
    # FIXME: We aren't actually checking if this works
    set(KLEE_SELINUX_CTX_CONST "const")
  endif()
else()
  set(HAVE_SELINUX 0)
endif()

################################################################################
# KLEE runtime support
################################################################################
# This is set here and not in `runtime` because `config.h` needs to be generated.


set(available_klee_runtime_build_types
  "Release"
  "Release+Asserts"
  "Debug"
  "Debug+Asserts"
)
if (NOT KLEE_RUNTIME_BUILD_TYPE)
  message(STATUS "KLEE_RUNTIME_BUILD_TYPE is not set. Setting default")
  message(STATUS "The available runtime build types are: ${available_klee_runtime_build_types}")
  set(KLEE_RUNTIME_BUILD_TYPE "Release+Asserts" CACHE String
    "Options are ${available_klee_runtime_build_types}"
    FORCE)
    # Provide drop down menu options in cmake-gui
    set_property(CACHE
      KLEE_RUNTIME_BUILD_TYPE
      PROPERTY STRINGS ${available_klee_runtime_build_types})
endif()
set(RUNTIME_CONFIGURATION "\"${KLEE_RUNTIME_BUILD_TYPE}\"") # For config.h

set(KLEE_INSTALL_RUNTIMR_DIR "${CMAKE_INSTALL_FULL_LIBDIR}/klee/runtime")
# FIXME: Move this into `config.h`
list(APPEND KLEE_COMPONENT_CXX_DEFINES
  -DKLEE_DIR=\"${CMAKE_BINARY_DIR}\"
  -DKLEE_INSTALL_BIN_DIR=\"${CMAKE_INSTALL_FULL_BINDIR}\"
  -DKLEE_INSTALL_RUNTIME_DIR=\"${KLEE_INSTALL_RUNTIMR_DIR}\")

# Location where KLEE will look for the built runtimes by default.
set(KLEE_RUNTIME_DIRECTORY "${CMAKE_BINARY_DIR}/${KLEE_RUNTIME_BUILD_TYPE}/lib")

################################################################################
# KLEE POSIX Runtime Support
################################################################################
option(ENABLE_POSIX_RUNTIME "Enable KLEE's POSIX runtime" OFF)
if (ENABLE_POSIX_RUNTIME)
  message(STATUS "POSIX runtime enabled")
else()
  message(STATUS "POSIX runtime disabled")
endif()

################################################################################
# KLEE uclibc support
################################################################################
option(ENABLE_KLEE_UCLIBC "Enable support for klee-uclibc" OFF)
if (ENABLE_KLEE_UCLIBC)
  message(STATUS "klee-uclibc support enabled")
  set(SUPPORT_KLEE_UCLIBC 1) # For config.h
  set(KLEE_UCLIBC_PATH "" CACHE PATH "Path to klee-uclibc root directory")
  if (NOT IS_DIRECTORY "${KLEE_UCLIBC_PATH}")
    message(FATAL_ERROR
      "KLEE_UCLIBC_PATH (\"${KLEE_UCLIBC_PATH}\") is not a valid directory")
  endif()

  # Find the C library bitcode archive
  set(KLEE_UCLIBC_BCA_NAME "klee-uclibc.bca")
  set(KLEE_UCLIBC_C_BCA "${KLEE_UCLIBC_PATH}/lib/libc.a")
  if (NOT EXISTS "${KLEE_UCLIBC_PATH}")
    message(FATAL_ERROR
      "klee-uclibc library not found at \"${KLEE_UCLIBC_C_BCA}\"")
  endif()
  message(STATUS "Find klee-uclibc library: \"${KLEE_UCLIBC_C_BCA}\"")
  
  # Make a symlink to KLEE_UCLIBC_C_BCA so KLEE can find it where it
  # is expected.
  file(MAKE_DIRECTORY "${KLEE_RUNTIME_DIRECTORY}")
  execute_process(COMMAND ${CMAKE_COMMAND} -E create_symlink
    "${KLEE_UCLIBC_C_BCA}"
    "${KLEE_RUNTIME_DIRECTORY}/${KLEE_UCLIBC_BCA_NAME}"
  )
list(APPEND KLEE_COMPONENT_CXX_DEFINES
  -DKLEE_UCLIBC_BCA_NAME=\"${KLEE_UCLIBC_BCA_NAME}\")

# Add klee-uclibc to the install target. We install the original
# file rather than the symlink because CMake would just copy the symlink
# rather than the file.
install(FILES "${KLEE_UCLIBC_C_BCA}"
  DESTINATION "${KLEE_INSTALL_RUNTIMR_DIR}"
  RENAME "${KLEE_UCLIBC_BCA_NAME}"
  )

else()
  message(STATUS "klee-uclibc support disabled")
  set(SUPPORT_KLEE_UCLIBC 0) # For config.h
endif()

################################################################################
# Generate `config.h`
################################################################################
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/include/klee/Config/config.h.cmin
	${CMAKE_CURRENT_BINARY_DIR}/include/klee/Config/config.h)

################################################################################
# Generate `CompileTimeInfo.h`
################################################################################
# FIXME: Get information from git and have configure depend on this so we
# only re-generate the file when necessary.
set(AUTO_GEN_MSG "AUTOMATICALLY GENERATED. DO NOT EDIT!")
configure_file(${CMAKE_SOURCE_DIR}/include/klee/Config/CompileTimeInfo.h.cmin
  ${CMAKE_BINARY_DIR}/include/klee/Config/CompileTimeInfo.h
)

################################################################################
# Global include directories
################################################################################
include_directories("${CMAKE_SOURCE_DIR}/include")
include_directories("${CMAKE_BINARY_DIR}/include")

################################################################################
# Set default location for targets in the build directory
################################################################################
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

################################################################################
# KLEE components
################################################################################
include("${CMAKE_SOURCE_DIR}/cmake/klee_add_component.cmake")
add_subdirectory(lib)
add_subdirectory(runtime)

################################################################################
# KLEE tools
################################################################################
add_subdirectory(tools)

################################################################################
# Testing
################################################################################
option(ENABLE_TESTS "Enable tests" ON)

if (ENABLE_TESTS)
  # Find lit
  find_program(
    LIT_TOOL
    NAMES llvm-lit lit
    HINTS "${LLVM_TOOLS_BINARY_DIR}"
    DOC "Path to lit tool"
  )

  set(LIT_ARGS
    "-v;-s"
    CACHE
    STRING
    "Lit arguments"
  )

  if (NOT LIT_TOOL)
    message(FATAL_ERROR "The lit tool is required for testing")
  else()
    message(STATUS "Using lit: ${LIT_TOOL}")
  endif()

  option(ENABLE_UNIT_TESTS "Enable unittests" ON)
  if (ENABLE_UNIT_TESTS)
    message(STATUS "Unit tests enabled")
    add_subdirectory(unittests)
  else()
    message(STATUS "Unit tests disabled")
  endif()
  option(ENABLE_INTEGRATION_TESTS "Enable integration tests" ON)
  if (ENABLE_INTEGRATION_TESTS)
    message(STATUS "Integration tests enabled")
    add_subdirectory(test)
  else()
    message(STATUS "Integration tests disabled")
  endif()

  # Add global test target
  add_custom_target(check
    DEPENDS unittests integrationtests
    COMMENT "Running tests"
  )
else()
  message(STATUS "Testing disabled")
endif()

################################################################################
# Miscellaneous install
################################################################################
install(FILES include/klee/klee.h DESTINATION include/klee)
