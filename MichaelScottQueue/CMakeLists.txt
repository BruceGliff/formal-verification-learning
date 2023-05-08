cmake_minimum_required(VERSION 3.10.2 FATAL_ERROR)

set_property(GLOBAL PROPERTY USE_FOLDERS ON)
set(CMAKE_BUILD_TYPE Release)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD 20)

set(PROJECT_NAME MichaelScottQueue)
project(${PROJECT_NAME})

add_executable(${PROJECT_NAME} src/main.cc)
target_link_options(${PROJECT_NAME} PRIVATE -latomic -pthread)
