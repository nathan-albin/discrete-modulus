cmake_minimum_required(VERSION 3.20)
project(discrete_modulus_cpp LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(Boost 1.74 REQUIRED COMPONENTS graph)

add_library(discrete_modulus INTERFACE)
target_include_directories(discrete_modulus INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/include)
target_link_libraries(discrete_modulus INTERFACE Boost::graph)

add_executable(spt_mod src/spt_mod.cpp)
target_link_libraries(spt_mod PRIVATE discrete_modulus)

option(DISCRETE_MODULUS_BUILD_TESTS "Build the discrete_modulus C++ test suite" ON)
if(DISCRETE_MODULUS_BUILD_TESTS)
    enable_testing()
    add_subdirectory(test)
endif()
