cmake_minimum_required(VERSION 3.7)

project(dune)

# Make Targets
add_definitions(-std=c11)
add_custom_target(dune COMMAND $(MAKE) -C ${dune_SOURCE_DIR} PWD=${dune_SOURCE_DIR})

#
# Dune Library
#

file(GLOB LIB_SOURCE_FILES "libdune/*.c")
add_library(dummy_lib ${LIB_SOURCE_FILES})

TARGET_INCLUDE_DIRECTORIES(dummy_lib PUBLIC libdune)


#
# Dune Kernel Module
#

file(GLOB MOD_SOURCE_FILES "kern/*.c" "kern/kvm/*.c")
add_library(dummy_mod ${MOD_SOURCE_FILES})

TARGET_COMPILE_DEFINITIONS(dummy_mod PUBLIC __KERNEL__)
TARGET_COMPILE_DEFINITIONS(dummy_mod PUBLIC MODULE)
TARGET_COMPILE_DEFINITIONS(dummy_mod PUBLIC CONFIG_X86_64)

TARGET_COMPILE_OPTIONS(dummy_mod PUBLIC -nostdinc)
TARGET_COMPILE_OPTIONS(dummy_mod PUBLIC -isystem /usr/lib/gcc/x86_64-linux-gnu/5/include)
TARGET_COMPILE_OPTIONS(dummy_mod PUBLIC -include ${LINUX_PATH}/include/linux/kconfig.h)

#set(LINUX_HEADERS_VERSION 4.4.0-83)
#set(LINUX_HEADERS_PATH /usr/src/linux-headers-${LINUX_HEADERS_VERSION})
set(LINUX_DEV_PATH /home/Storage/SSD/Development/Software/eliaskousk/linux)
set(LINUX_PATH ${LINUX_DEV_PATH})
set(LINUX_HEADERS
        ${LINUX_PATH}/arch/x86/include
        ${LINUX_PATH}/arch/x86/include/generated
        ${LINUX_PATH}/arch/x86/include/generated/uapi
        ${LINUX_PATH}/arch/x86/include/uapi
        ${LINUX_PATH}/include
        ${LINUX_PATH}/include/generated
        ${LINUX_PATH}/include/generated/uapi
        ${LINUX_PATH}/include/uapi)
TARGET_INCLUDE_DIRECTORIES(dummy_mod PUBLIC kern)
TARGET_INCLUDE_DIRECTORIES(dummy_mod PUBLIC kern/kvm)
TARGET_INCLUDE_DIRECTORIES(dummy_mod PUBLIC ${LINUX_HEADERS})
