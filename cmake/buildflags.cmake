function(get_warning_flags flags)
    set(tmp
        $<$<CXX_COMPILER_ID:Clang>:
            -Weverything
            -Wno-padded
            -Wno-c++98-compat
            -Wno-c++98-compat-pedantic
            -Wno-c++98-compat-bind-to-temporary-copy
            -Wno-c++98-compat-local-type-template-args>
        $<$<CXX_COMPILER_ID:GNU>:
            -ftemplate-backtrace-limit=0
            -Wall -Wextra -Wpedantic
            -pedantic-errors
            -Wconversion -Wsign-conversion
            -Wold-style-cast -Wfloat-equal
            -Wlogical-op -Wundef
            -Wredundant-decls -Wshadow
            -Wwrite-strings
            -Wpointer-arith -Wcast-qual
            -Wformat=2 -Wswitch-default
            -Wmissing-include-dirs -Wcast-align
            -Wswitch-enum -Wnon-virtual-dtor
            -Wctor-dtor-privacy -Wdisabled-optimization
            -Winvalid-pch -Wnoexcept
            -Wmissing-declarations -Woverloaded-virtual
            $<$<NOT:$<VERSION_LESS:CXX_COMPILER_VERSION,5.0>>:
            -Wdouble-promotion -Wtrampolines
            -Wzero-as-null-pointer-constant
            -Wuseless-cast -Wvector-operation-performance>
            $<$<NOT:$<VERSION_LESS:CXX_COMPILER_VERSION,6.0>>:
            -Wshift-overflow=2 -Wnull-dereference
            -Wduplicated-cond>
            $<$<NOT:$<VERSION_LESS:CXX_COMPILER_VERSION,7.0>>:
            -Walloc-zero -Walloca
            -Wduplicated-branches>
            $<$<NOT:$<VERSION_LESS:CXX_COMPILER_VERSION,8.0>>:
            -Wcast-align=strict>
            $<$<NOT:$<VERSION_LESS:CXX_COMPILER_VERSION,9.0>>:
            -Wmismatched-tags -Wredundant-tags>
            $<$<NOT:$<VERSION_LESS:CXX_COMPILER_VERSION,10.0>>:
            -fconcepts-diagnostics-depth=99>
            >
        $<$<CXX_COMPILER_ID:MSVC>:
            /W3
            /wd4324 # padding
            /permissive->)

    if (CMAKE_CXX_COMPILER_ID STREQUAL "Clang" AND
            NOT (CMAKE_CXX_COMPILER_FRONTEND_VARIANT STREQUAL "MSVC"))
        set(tmp ${tmp}
                -ftemplate-backtrace-limit=0)
    endif()

    set(${flags} ${tmp} PARENT_SCOPE)
endfunction()

function(get_werror_flags flags)
    set(${flags}
        $<$<CXX_COMPILER_ID:Clang>:
            -Werror>
        $<$<CXX_COMPILER_ID:GNU>:
            -Werror>
        $<$<CXX_COMPILER_ID:MSVC>:
            /WX>

            PARENT_SCOPE)
endfunction()

function(get_suppress_warnings_flags flags)
    set(${flags}
        $<$<CXX_COMPILER_ID:Clang>:
            -w>
        $<$<CXX_COMPILER_ID:GNU>:
            -w>
        $<$<CXX_COMPILER_ID:MSVC>:
            /w>

            PARENT_SCOPE)
endfunction()

function(get_disable_exceptions_flags flags)
    set(${flags}
        $<$<CXX_COMPILER_ID:Clang>:
            -fno-exceptions>
        $<$<CXX_COMPILER_ID:GNU>:
            -fno-exceptions>
        $<$<CXX_COMPILER_ID:MSVC>:
            /EHs-c->

            PARENT_SCOPE)
endfunction()

function(get_disable_rtti_flags flags)
    set(${flags}
        $<$<CXX_COMPILER_ID:Clang>:
            -fno-rtti>
        $<$<CXX_COMPILER_ID:GNU>:
            -fno-rtti>
        $<$<CXX_COMPILER_ID:MSVC>:
            /GR->

            PARENT_SCOPE)
endfunction()

function(get_coverage_flags flags)
    set(${flags}
        $<$<CXX_COMPILER_ID:GNU>:
            -O0
            -g
            --coverage>
            PARENT_SCOPE)
endfunction()

function(disable_msvc_secure_flags target scope)
    if (CMAKE_CXX_COMPILER_ID STREQUAL "Clang" AND
            CMAKE_CXX_COMPILER_FRONTEND_VARIANT STREQUAL "MSVC")
        target_compile_definitions(${target} ${scope}
                _CRT_SECURE_NO_WARNINGS
                _SCL_SECURE_NO_WARNINGS)
    endif()

    if (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
        target_compile_definitions(${target} ${scope}
                _CRT_SECURE_NO_WARNINGS
                _SCL_SECURE_NO_WARNINGS)
    endif()
endfunction()

function(set_interface_flags target)
    if(SCN_PEDANTIC)
        get_warning_flags(warning_flags)
        target_compile_options(${target} INTERFACE ${warning_flags})
    endif()
    if(SCN_WERROR)
        get_werror_flags(werror_flags)
        target_compile_options(${target} INTERFACE ${werror_flags})
    endif()

    disable_msvc_secure_flags(${target} INTERFACE)
    target_compile_options(${target} INTERFACE
            $<$<CXX_COMPILER_ID:MSVC>:
            /bigobj>)
endfunction()

function(set_library_flags target)
    if(SCN_PEDANTIC)
        get_warning_flags(warning_flags)
        target_compile_options(${target} PRIVATE ${warning_flags})
    endif()
    if(SCN_WERROR)
        get_werror_flags(werror_flags)
        target_compile_options(${target} PRIVATE ${werror_flags})
    endif()
    if(SCN_USE_32BIT)
        target_compile_options(${target} PUBLIC -m32)
        set_target_properties(${target} PROPERTIES LINK_FLAGS -m32)
    endif()
    if(SCN_USE_NATIVE_ARCH)
        target_compile_options(${target} PRIVATE -march=native)
    elseif(SCN_USE_HASWELL_ARCH)
        target_compile_options(${target} PRIVATE -march=haswell)
    endif()
    if(NOT SCN_USE_EXCEPTIONS)
        get_disable_exceptions_flags(noexceptions_flags)
        target_compile_options(${target} PRIVATE ${noexceptions_flags})
    endif()
    if(NOT SCN_USE_RTTI)
        get_disable_rtti_flags(nortti_flags)
        target_compile_options(${target} PRIVATE ${nortti_flags})
    endif()
    if (NOT SCN_USE_IOSTREAMS)
        target_compile_definitions(${target} PUBLIC -DSCN_USE_IOSTREAMS=0)
    endif()
    if(SCN_COVERAGE)
        get_coverage_flags(coverage_flags)
        target_compile_options(${target} PUBLIC ${coverage_flags})
        target_link_options(${target} PUBLIC --coverage)
    endif()

    target_compile_options(${target} PRIVATE
            $<$<CXX_COMPILER_ID:MSVC>:
            /bigobj>)

    target_compile_features(${target} PUBLIC cxx_std_17)
endfunction()