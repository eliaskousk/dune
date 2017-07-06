cmake_minimum_required(VERSION 3.7)

project(dune)

#set(LINUX_HEADERS_VERSION 4.4.0-83)
#set(LINUX_HEADERS_PATH /usr/src/linux-headers-${LINUX_HEADERS_VERSION})
set(LINUX_DEV_PATH /home/Storage/SSD/Development/Software/eliaskousk/linux)
set(LINUX_PATH ${LINUX_DEV_PATH})
set(LINUX_HEADERS
        ${LINUX_PATH}/arch/x86/include
#       ${LINUX_PATH}/arch/x86/include/generated
#       ${LINUX_PATH}/arch/x86/include/generated/uapi
        ${LINUX_PATH}/arch/x86/include/uapi
        ${LINUX_PATH}/include
#       ${LINUX_PATH}/include/generated
#       ${LINUX_PATH}/include/generated/uapi
        ${LINUX_PATH}/include/uapi)

add_definitions(-std=c11)
add_definitions(-D__KERNEL__)
add_definitions(-DMODULE)
add_definitions(-nostdinc -isystem /usr/lib/gcc/x86_64-linux-gnu/5/include)
add_definitions(-include ${LINUX_PATH}/include/linux/kconfig.h)

include_directories(kern)
include_directories(kern/kvm)
include_directories(libdune)
include_directories(${LINUX_HEADERS})

file(GLOB SOURCE_FILES "kern/*.c" "kern/kvm/*.c" "libdune/*.c")

add_custom_target(dune COMMAND $(MAKE) -C ${dune_SOURCE_DIR} PWD=${dune_SOURCE_DIR})

add_library(dummylib ${SOURCE_FILES})
