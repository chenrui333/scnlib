# scnlib

[![Linux builds](https://github.com/eliaskosunen/scnlib/actions/workflows/linux.yml/badge.svg?branch=dev)](https://github.com/eliaskosunen/scnlib/actions/workflows/linux.yml)
[![macOS builds](https://github.com/eliaskosunen/scnlib/actions/workflows/macos.yml/badge.svg?branch=dev)](https://github.com/eliaskosunen/scnlib/actions/workflows/macos.yml)
[![Windows builds](https://github.com/eliaskosunen/scnlib/actions/workflows/windows.yml/badge.svg?branch=dev)](https://github.com/eliaskosunen/scnlib/actions/workflows/windows.yml)
[![Other architectures](https://github.com/eliaskosunen/scnlib/actions/workflows/arch.yml/badge.svg?branch=dev)](https://github.com/eliaskosunen/scnlib/actions/workflows/arch.yml)
[![Code Coverage](https://codecov.io/gh/eliaskosunen/scnlib/branch/dev/graph/badge.svg?token=LyWrDluna1)](https://codecov.io/gh/eliaskosunen/scnlib)

[![Latest Release](https://img.shields.io/github/v/release/eliaskosunen/scnlib?sort=semver&display_name=tag)](https://github.com/eliaskosunen/scnlib/releases)
[![License](https://img.shields.io/github/license/eliaskosunen/scnlib.svg)](https://github.com/eliaskosunen/scnlib/blob/master/LICENSE)
[![C++ Standard](https://img.shields.io/badge/C%2B%2B-17%2F20%2F23-blue.svg)](https://img.shields.io/badge/C%2B%2B-17%2F20%2F23-blue.svg)

```cpp
#include <scn/scan.h>
#include <print> // for std::println (C++23)

int main() {
    // Read two integers from stdin
    // with an accompanying message
    if (auto result =
            scn::prompt<int>("What are your two favorite numbers? ", "{} {}")) {
        auto [a, b] = result->values();
        std::println("Oh, cool, {} and {}!", a, b);
    } else {
        std::println(stderr, "Error: {}", result.error().msg());
    }
}
```

## What is this?

`scnlib` is a modern C++ library for replacing `scanf` and `std::istream`.
This library attempts to move use ever so much closer to replacing `iostream`s and C stdio altogether.
It's faster than `iostream` (see Benchmarks), and type-safe, unlike `scanf`.
Think [{fmt}](https://github.com/fmtlib/fmt) or C++20 `std::format`, but in the other direction.

This library is the reference implementation of the ISO C++ standards proposal
[P1729 "Text Parsing"](https://wg21.link/p1729).

This branch (dev) targets v2, and is currently unstable.
The master branch contains the latest stable version of the library, with a substantially different interface, and
support for C++11 and C++14.

## Documentation

The documentation can be found online, from https://scnlib.readthedocs.io.

To build the docs yourself, build the `scn_doc` and `scn_doc_sphinx` targets generated by CMake.
These targets are generated only if the variable `SCN_DOCS` is set in CMake (done automatically if scnlib is the root project).
The `scn_doc` target requires Doxygen, and the `scn_doc_sphinx` target requires Python 3.8 or better, Sphinx, and Breathe.

## Examples

See more examples in the `examples/` folder.

### Reading a `std::string`

```cpp
#include <scn/scan.h>
#include <print>

int main() {
    auto input = std::string_view{"Hello world"};

    // Reading a std::string will read until the first whitespace character
    if (auto result = scn::scan<std::string>(input, "{}")) {
        // Will output "Hello":
        // Access the read value with result->value()
        std::println("{}", result->value());
        
        // Will output " world":
        // result->range() returns a subrange containing the unused input
        std::println("{}", std::string_view{result->range()});
    } else {
        std::println("Couldn't parse a word: {}", result.error().msg());
    }
}
```

### Reading multiple values

```cpp
#include <scn/scan.h>

// scn::ranges is
//  - std::ranges on C++20 or later (if available)
//  - nano::ranges on C++17 (bundled implementation)
namespace ranges = scn::ranges;

int main() {
    auto input = std::string{"123 456 foo"};
    
    auto result = scn::scan<int, int>(input, "{} {}");
    // result == true
    // result->range(): " foo"
    
    // All read values can be accessed through a tuple with result->values()
    auto [a, b] = result->values();
    
    // Read from the remaining input
    // Could also use scn::ranges::subrange{result->begin(), result->end()} as input
    auto result2 = scn::scan<std::string>(result->range(), "{}");
    // result2 == true
    // result2->range().empty: true
    // result2->value() == "foo"
}
```

### Reading from a fancier range

```cpp
#include <scn/scan.h>

namespace ranges = scn::ranges;

int main() {
    auto result = scn::scan<int>("123" | ranges::views::reverse, "{}");
    // result == true
    // result->begin() is an iterator into a reverse_view
    // result->range() is empty
    // result->value() == 321
}
```

### Repeated reading

```cpp
#include <scn/scan.h>
#include <vector>

int main() {
    std::vector<int> vec{};
    auto input = scn::ranges::subrange{std::string_view{"123 456 789"}};
    
    while (auto result = scn::scan<int>(input), "{}")) {
        vec.push_back(result->value());
        input = result->range();
    }
}
```

## Features

 * Blazing fast parsing of values (see Benchmarks)
 * Modern C++ interface, featuring
   * type safety (variadic templates, types not determined by the format string)
   * convenience (ranges)
   * ergonomics (values returned from `scn::scan`, no output parameters)
 * `"{python}"`-like format string syntax
   * Including compile-time format string checking
 * Minimal code size increase (in user code, see Benchmarks)
 * Usable without exceptions, RTTI, or `<iostream>`s
   * Configurable through build flags
   * Limited functionality if enabled
 * Supports, and requires Unicode (input is UTF-8, UTF-16, or UTF-32)
 * Highly portable
   * Tested on multiple platforms, see CI
   * Works on multiple architectures, tested on x86, x86-64, arm, aarch64, riscv64, ppc64le, and riscv64

## Installing

`scnlib` uses CMake.
If your project already uses CMake, integration should be trivial, through whatever means you like:
`make install` + `find_package`, `FetchContent`, `git submodule` + `add_subdirectory`, or something else.

The `scnlib` CMake target is `scn::scn`

```cmake
# Target with which you'd like to use scnlib
add_executable(my_program ...)
target_link_libraries(my_program scn::scn)
```

See docs for usage without CMake.

## Compiler support

A C++17 compatible compiler is required. The following compilers are tested in CI:

 * GCC 7 and newer
 * Clang 8 and newer
 * Visual Studio 2019 and 2022

Including the following environments:

 * 32-bit and 64-bit builds on Windows
 * libc++ on Linux
 * AppleClang on macOS 11 (Big Sur) and 12 (Monterey)
 * clang-cl with VS 2019 and 2022
 * MinGW
 * GCC on armv6, armv7, aarch64, riscv64, s390x, and ppc64le
 * Visual Studio 2022, cross compiling to arm64

## Benchmarks

### Run-time performance

TODO

### Executable size

Debug

.so size: 24M

| Method         | Executable size | Stripped size |
| :------------- | --------------: | ------------: |
| empty          |            33.1 |          14.6 |
| `std::scanf`   |             570 |          26.9 |
| `std::istream` |             545 |          22.9 |
| `scn::input`   |            1967 |          42.8 |

Release

.so size: 1.1M

| Method         | Executable size | Stripped size |
| :------------- | --------------: | ------------: |
| empty          |            24.1 |          14.6 |
| `std::scanf`   |            25.3 |          14.8 |
| `std::istream` |            26.7 |          14.8 |
| `scn::input`   |            25.7 |          14.8 |

MinSizeRel

.so size: 856K

| Method         | Executable size | Stripped size |
| :------------- | --------------: | ------------: |
| empty          |            24.1 |          14.6 |
| `std::scanf`   |            25.3 |          14.8 |
| `std::istream` |            26.7 |          14.8 |
| `scn::input`   |            27.2 |          14.8 |

### Build time

TODO

## Acknowledgements

The contents of this library are heavily influenced by {fmt} and its derivative works.  
https://github.com/fmtlib/fmt

The design of this library is also inspired by the Python `parse` library:  
https://github.com/r1chardj0n3s/parse

### Third-party libraries

NanoRange for C++17 Ranges implementation:  
https://github.com/tcbrindle/NanoRange

fast_float for floating-point number parsing:  
https://github.com/fastfloat/fast_float

simdutf for Unicode handling:  
https://github.com/simdutf/simdutf

## License

scnlib is licensed under the Apache License, version 2.0.  
Copyright (c) 2017 Elias Kosunen  
See LICENSE for further details.
