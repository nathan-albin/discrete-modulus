include(FetchContent)
FetchContent_Declare(
    Catch2
    GIT_REPOSITORY https://github.com/catchorg/Catch2.git
    GIT_TAG v3.7.1
)
FetchContent_MakeAvailable(Catch2)

add_executable(discrete_modulus_tests
    test_graphs.cpp
    test_cunningham.cpp
    test_solver_trace.cpp
)
target_link_libraries(discrete_modulus_tests PRIVATE discrete_modulus Catch2::Catch2WithMain)
target_compile_definitions(discrete_modulus_tests PRIVATE
    DISCRETE_MODULUS_EXAMPLES_DIR="${CMAKE_CURRENT_SOURCE_DIR}/../examples")

list(APPEND CMAKE_MODULE_PATH ${catch2_SOURCE_DIR}/extras)
include(Catch)
catch_discover_tests(discrete_modulus_tests)
