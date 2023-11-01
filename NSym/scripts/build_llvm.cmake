# https://cmake.org/cmake/help/book/mastering-cmake/chapter/Cross%20Compiling%20With%20CMake.html

# the name of the target operating system
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR aarch64)

# which compilers to use for C and C++
set(CMAKE_C_COMPILER   wllvm)
set(CMAKE_CXX_COMPILER wllvm++)

# ------------
# where is the target environment located
# set(CMAKE_FIND_ROOT_PATH /usr/aarch64-linux-gnu)
# set(CMAKE_SYSROOT /usr/aarch64-linux-gnu)

# # adjust the default behavior of the FIND_XXX() commands:
# # search programs in the host environment
# set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
# # search headers and libraries in the target environment
# set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
# set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
# set(CMAKE_FIND_ROOT_PATH_MODE_PACKAGE ONLY)
# ------------
# set(CMAKE_SYSTEM_INCLUDE_PATH /usr/aarch64-linux-gnu/include)
