cmake_minimum_required(VERSION 3.0.0)
project(emu)
enable_language(CXX)
set(CMAKE_CXX_STANDARD 14)

set (CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

# Declare main executable
file(GLOB EMU_SOURCES src/*.cpp)
add_executable(emu ${EMU_SOURCES})

# Compiler specific
if(CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
  # Hide Console
  # set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /SUBSYSTEM:WINDOWS /ENTRY:mainCRTStartup")
endif()

# Interface libraries with main executable
target_include_directories(emu PUBLIC src)
target_link_libraries(emu)