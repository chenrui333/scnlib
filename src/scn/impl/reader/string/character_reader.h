// Copyright 2017 Elias Kosunen
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// This file is a part of scnlib:
//     https://github.com/eliaskosunen/scnlib

#pragma once

#include <scn/impl/algorithms/read_code_points.h>
#include <scn/impl/reader/common.h>

namespace scn {
    SCN_BEGIN_NAMESPACE

    namespace impl {
        template <typename SourceCharT>
        class character_reader {
        public:
            character_reader(std::basic_string<SourceCharT>& buffer)
                : m_buffer(buffer)
            {
            }

            template <typename SourceRange>
            scan_expected<
                iterator_value_result<ranges::iterator_t<SourceRange>,
                                      std::basic_string_view<SourceCharT>>>
            read(SourceRange& source, int width)
            {
                if constexpr (ranges::contiguous_range<SourceRange>) {
                    return read_n_nocopy(source, width);
                }
                else {
                    m_buffer.clear();
                    auto [it, _] =
                        read_n_copying(source, back_insert(m_buffer), width);
                    SCN_UNUSED(_);
                    SCN_GCC_PUSH
                    SCN_GCC_IGNORE("-Wconversion")
                    return iterator_value_result<
                        ranges::iterator_t<SourceRange>,
                        std::basic_string_view<SourceCharT>>{it, {m_buffer}};
                    SCN_GCC_POP
                }
            }

        private:
            std::basic_string<SourceCharT>& m_buffer;
        };

        template <typename SourceCharT>
        class unicode_character_reader_impl {
        public:
            unicode_character_reader_impl(
                std::basic_string<SourceCharT>& buffer)
                : m_buffer(buffer)
            {
            }

            template <typename SourceRange>
            scan_expected<
                iterator_value_result<ranges::iterator_t<SourceRange>,
                                      std::basic_string_view<SourceCharT>>>
            read(SourceRange& source, int cp_count)
            {
                if constexpr (ranges::contiguous_range<SourceRange>) {
                    return read_n_code_points_nocopy(source, cp_count);
                }
                else {
                    m_buffer.clear();
                    return read_n_code_points_copying(
                               source, back_insert(m_buffer), cp_count)
                        .transform([&](auto result) SCN_NOEXCEPT {
                            SCN_GCC_PUSH
                            SCN_GCC_IGNORE("-Wconversion")
                            return iterator_value_result<
                                ranges::iterator_t<SourceRange>,
                                std::basic_string_view<SourceCharT>>{
                                result.in, {m_buffer}};
                            SCN_GCC_POP
                        });
                }
            }

        private:
            std::basic_string<SourceCharT>& m_buffer;
        };

        template <typename SourceCharT>
        class unicode_character_reader;

        template <>
        class unicode_character_reader<char>
            : public unicode_character_reader_impl<char> {};

        template <>
        class unicode_character_reader<wchar_t>
            : public std::conditional_t<sizeof(wchar_t) == 2,
                                        unicode_character_reader_impl<wchar_t>,
                                        character_reader<wchar_t>> {};
    }  // namespace impl

    SCN_END_NAMESPACE
}  // namespace scn