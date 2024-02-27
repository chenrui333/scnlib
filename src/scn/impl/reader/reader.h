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

#include <scn/detail/args.h>
#include <scn/detail/format_string.h>
#include <scn/detail/xchar.h>

#include <scn/impl/reader/bool_reader.h>
#include <scn/impl/reader/code_unit_and_point_reader.h>
#include <scn/impl/reader/float_reader.h>
#include <scn/impl/reader/integer_reader.h>
#include <scn/impl/reader/pointer_reader.h>
#include <scn/impl/reader/regex_reader.h>
#include <scn/impl/reader/string_reader.h>
#include <scn/impl/util/contiguous_context.h>

namespace scn {
SCN_BEGIN_NAMESPACE

namespace impl {
template <typename Range>
eof_expected<simple_borrowed_iterator_t<Range>> skip_ws_before_if_required(
    bool is_required,
    Range&& range,
    detail::locale_ref loc)
{
    if (auto e = eof_check(range); SCN_UNLIKELY(!e)) {
        return unexpected(e);
    }

    if (!is_required) {
        return ranges::begin(range);
    }

    return skip_classic_whitespace(SCN_FWD(range));
}

template <typename Iterator>
struct skip_fill_result {
    Iterator iterator;
    int skipped_width;
};

template <typename Range>
scan_expected<skip_fill_result<simple_borrowed_iterator_t<Range>>>
skip_fill_impl(Range&& range,
               int spec_width,
               int rem_width,
               const detail::fill_type& fill,
               bool need_skipped_width)
{
    SCN_EXPECT(ranges::begin(range) != ranges::end(range));

    using char_type = detail::char_t<Range>;
    using result_type = skip_fill_result<simple_borrowed_iterator_t<Range>>;

    if (spec_width == 0 && rem_width == 0) {
        if (fill.size() <= sizeof(char_type)) {
            const auto fill_ch = fill.template get_code_unit<char_type>();
            const auto pred = [=](char_type ch) { return ch == fill_ch; };
            auto it = read_while_code_unit(range, pred);
            if (need_skipped_width) {
                const auto fill_ch_width = static_cast<int>(
                    calculate_text_width(static_cast<char32_t>(fill_ch)));
                return result_type{it, static_cast<int>(ranges::distance(
                                           ranges::begin(range), it)) /
                                           fill_ch_width};
            }
            return result_type{it, 0};
        }

        const auto fill_chars = fill.template get_code_units<char_type>();
        auto it = read_while_code_units(range, fill_chars);
        if (need_skipped_width) {
            const auto fill_ch_width =
                static_cast<int>(calculate_text_width(fill_chars));
            return result_type{it, static_cast<int>(ranges::distance(
                                       ranges::begin(range), it)) /
                                       fill_ch_width};
        }
        return result_type{it, 0};
    }

    SCN_UNUSED(need_skipped_width);
    const int rem_width_start = rem_width;
    if (fill.size() <= sizeof(char_type)) {
        const auto fill_ch = fill.template get_code_unit<char_type>();
        const auto fill_width =
            calculate_valid_text_width(static_cast<char32_t>(fill_ch));
        auto it = ranges::begin(range);
        while (it != ranges::end(range)) {
            if (*it != fill_ch) {
                return result_type{it, rem_width_start - rem_width};
            }

            it = read_code_point(ranges::subrange{it, ranges::end(range)});
            rem_width -= fill_width;

            if (rem_width <= 0) {
                break;
            }
        }
        return result_type{it, rem_width_start - rem_width};
    }

    const auto fill_chars = fill.template get_code_units<char_type>();
    const auto fill_width = calculate_valid_text_width(fill_chars);
    auto it = ranges::begin(range);
    while (it != ranges::end(range)) {
        auto [beg, cp_view] =
            read_code_point_into(ranges::subrange{it, ranges::end(range)});
        if (!ranges::equal(cp_view.view(), fill_chars)) {
            return result_type{it, rem_width_start - rem_width};
        }

        rem_width -= fill_width;
        if (rem_width <= 0) {
            break;
        }
    }
    return result_type{it, rem_width_start - rem_width};
}

template <typename Range>
scan_expected<skip_fill_result<simple_borrowed_iterator_t<Range>>>
skip_fill_before(Range&& range,
                 int width,
                 const detail::fill_type& fill,
                 bool need_skipped_width)
{
    if (auto e = eof_check(range); SCN_UNLIKELY(!e)) {
        return unexpected(make_eof_scan_error(e));
    }

    SCN_TRY(r, skip_fill_impl(SCN_FWD(range), width, width, fill,
                              need_skipped_width || width != 0));
    if (r.skipped_width >= width && width != 0) {
        return unexpected_scan_error(scan_error::invalid_scanned_value,
                                     "Too many fill characters before value");
    }
    return r;
}

template <typename Range>
scan_expected<simple_borrowed_iterator_t<Range>> skip_left_fill_after(
    Range&& range,
    int spec_width,
    int rem_width,
    const detail::fill_type& fill)
{
    if (ranges::begin(range) == ranges::end(range)) {
        return ranges::begin(range);
    }

    SCN_TRY(r,
            skip_fill_impl(SCN_FWD(range), spec_width, rem_width, fill, false));
    return r.iterator;
}

template <typename Range>
scan_expected<simple_borrowed_iterator_t<Range>> skip_center_fill_after(
    Range&& range,
    int spec_width,
    int before_width,
    int rem_width,
    const detail::fill_type& fill)
{
    if (auto e = eof_check(range); SCN_UNLIKELY(!e)) {
        if (before_width == 0) {
            return ranges::begin(range);
        }
        return unexpected(make_eof_scan_error(e));
    }

    using char_type = detail::char_t<Range>;
    const auto fill_ch_width =
        calculate_text_width(fill.template get_code_units<char_type>());

    if (spec_width == 0) {
        SCN_TRY(r, skip_fill_impl(SCN_FWD(range), 0,
                                  before_width + fill_ch_width, fill, true));
        if (r.skipped_width != before_width &&
            r.skipped_width != before_width + fill_ch_width) {
            return unexpected_scan_error(
                scan_error::invalid_scanned_value,
                "Wrong number of fill characters for center-aligned value");
        }
        return r.iterator;
    }

    SCN_TRY(r,
            skip_fill_impl(SCN_FWD(range), spec_width, rem_width, fill, true));

    const auto expected_total_padding_width = before_width + r.skipped_width;
    const auto expected_total_padding_chars =
        expected_total_padding_width / fill_ch_width;
    const auto expected_fill_width_before =
        expected_total_padding_chars / 2 * fill_ch_width;
    const auto expected_fill_width_after =
        ((expected_total_padding_chars / 2) +
         (expected_total_padding_chars % 2 != 0)) *
        fill_ch_width;
    if (expected_fill_width_before != before_width ||
        expected_fill_width_after != r.skipped_width) {
        return unexpected_scan_error(
            scan_error::invalid_scanned_value,
            "Wrong number of fill characters for center-aligned value");
    }
    return r.iterator;
}

template <typename T, typename CharT>
constexpr auto make_reader()
{
    if constexpr (std::is_same_v<T, bool>) {
        return reader_impl_for_bool<CharT>{};
    }
    else if constexpr (std::is_same_v<T, char>) {
        return reader_impl_for_char<CharT>{};
    }
    else if constexpr (std::is_same_v<T, wchar_t>) {
        return reader_impl_for_wchar<CharT>{};
    }
    else if constexpr (std::is_same_v<T, char32_t>) {
        return reader_impl_for_code_point<CharT>{};
    }
    else if constexpr (std::is_same_v<T, std::string_view> ||
                       std::is_same_v<T, std::wstring_view>) {
        return reader_impl_for_string<CharT>{};
    }
    else if constexpr (std::is_same_v<T, std::string> ||
                       std::is_same_v<T, std::wstring>) {
        return reader_impl_for_string<CharT>{};
    }
    else if constexpr (std::is_same_v<T, regex_matches> ||
                       std::is_same_v<T, wregex_matches>) {
        return reader_impl_for_regex_matches<CharT>{};
    }
    else if constexpr (std::is_same_v<T, void*>) {
        return reader_impl_for_voidptr<CharT>{};
    }
    else if constexpr (std::is_floating_point_v<T>) {
        return reader_impl_for_float<CharT>{};
    }
    else if constexpr (std::is_integral_v<T> && !std::is_same_v<T, char> &&
                       !std::is_same_v<T, wchar_t> &&
                       !std::is_same_v<T, char32_t> &&
                       !std::is_same_v<T, bool>) {
        return reader_impl_for_int<CharT>{};
    }
    else {
        return reader_impl_for_monostate<CharT>{};
    }
}

template <typename Context>
struct default_arg_reader {
    using context_type = Context;
    using char_type = typename context_type::char_type;
    using args_type = typename context_type::args_type;

    using range_type = typename context_type::range_type;
    using iterator = ranges::iterator_t<range_type>;

    template <typename Reader, typename Range, typename T>
    scan_expected<ranges::iterator_t<Range>> impl(Reader& rd,
                                                  const Range& rng,
                                                  T& value)
    {
        SCN_TRY(it,
                skip_ws_before_if_required(rd.skip_ws_before_read(), rng, loc)
                    .transform_error(make_eof_scan_error));
        return rd.read_default(ranges::subrange{it, ranges::end(rng)}, value,
                               loc);
    }

    template <typename T>
    scan_expected<iterator> operator()(T& value)
    {
        if constexpr (!detail::is_type_disabled<T> &&
                      std::is_same_v<
                          context_type,
                          basic_contiguous_scan_context<char_type>>) {
            auto rd = make_reader<T, char_type>();
            return impl(rd, range, value);
        }
        else if constexpr (!detail::is_type_disabled<T>) {
            auto rd = make_reader<T, char_type>();
            if (!is_segment_contiguous(range)) {
                return impl(rd, range, value);
            }
            auto crange = get_as_contiguous(range);
            SCN_TRY(it, impl(rd, crange, value));
            return ranges_polyfill::batch_next(
                ranges::begin(range), ranges::distance(crange.begin(), it));
        }
        else {
            SCN_EXPECT(false);
            SCN_UNREACHABLE;
        }
    }

    basic_scan_context<char_type> make_custom_ctx()
    {
        if constexpr (std::is_same_v<
                          context_type,
                          basic_contiguous_scan_context<char_type>>) {
            auto it =
                typename detail::basic_scan_buffer<char_type>::forward_iterator{
                    std::basic_string_view<char_type>(range.data(),
                                                      range.size()),
                    0};
            return {it, args, loc};
        }
        else {
            return {range.begin(), args, loc};
        }
    }

    scan_expected<iterator> operator()(
        typename context_type::arg_type::handle h)
    {
        if constexpr (!detail::is_type_disabled<void>) {
            basic_scan_parse_context<char_type> parse_ctx{{}};
            auto ctx = make_custom_ctx();
            if (auto e = h.scan(parse_ctx, ctx); !e) {
                return unexpected(e);
            }

            if constexpr (std::is_same_v<
                              context_type,
                              basic_contiguous_scan_context<char_type>>) {
                return range.begin() + ctx.begin().position();
            }
            else {
                return ctx.begin();
            }
        }
        else {
            SCN_EXPECT(false);
            SCN_UNREACHABLE;
        }
    }

    range_type range;
    args_type args;
    detail::locale_ref loc;
};

template <typename Context>
struct arg_reader {
    using context_type = Context;
    using char_type = typename context_type::char_type;

    using range_type = typename context_type::range_type;
    using iterator = ranges::iterator_t<range_type>;

    template <typename Reader, typename Range, typename T>
    scan_expected<ranges::iterator_t<Range>> impl(Reader& rd,
                                                  const Range& rng,
                                                  T& value)
    {
        int before_align_width = 0;
        auto it = ranges::begin(rng);
        if (SCN_UNLIKELY(specs.align == detail::align_type::right ||
                         specs.align == detail::align_type::center)) {
            if (auto r =
                    skip_fill_before(rng, specs.width, specs.fill,
                                     specs.align == detail::align_type::center);
                SCN_LIKELY(r)) {
                it = r->iterator;
                before_align_width = r->skipped_width;
            }
            else {
                return unexpected(r.error());
            }
            if (SCN_UNLIKELY(it == ranges::end(rng))) {
                return unexpected_scan_error(scan_error::end_of_range, "EOF");
            }
        }
        else {
            SCN_TRY_ASSIGN(it, skip_ws_before_if_required(
                                   rd.skip_ws_before_read(), rng, loc)
                                   .transform_error(make_eof_scan_error));
        }

        auto subr = ranges::subrange{it, ranges::end(rng)};

        if (specs.width != 0) {
            SCN_TRY(w_it,
                    rd.read_specs(
                        take_width(subr, specs.width - before_align_width),
                        specs, value, loc));
            it = w_it.base();
        }
        else {
            SCN_TRY_ASSIGN(it, rd.read_specs(subr, specs, value, loc));
        }

        if (SCN_LIKELY(specs.align == detail::align_type::none ||
                       specs.align == detail::align_type::right)) {
            return it;
        }

        if (specs.width == 0) {
            if (specs.align == detail::align_type::left) {
                return skip_left_fill_after(
                    ranges::subrange{it, ranges::end(rng)}, 0, 0, specs.fill);
            }
            return skip_center_fill_after(
                ranges::subrange{it, ranges::end(rng)}, 0, before_align_width,
                0, specs.fill);
        }

        const auto value_buf =
            make_contiguous_buffer(ranges::subrange{subr.begin(), it});
        const auto value_width = calculate_text_width(value_buf.view());
        const auto remaining_width =
            specs.width - before_align_width - value_width;
        if (specs.align == detail::align_type::left) {
            return skip_left_fill_after(ranges::subrange{it, ranges::end(rng)},
                                        specs.width, remaining_width,
                                        specs.fill);
        }
        return skip_center_fill_after(ranges::subrange{it, ranges::end(rng)},
                                      specs.width, before_align_width,
                                      remaining_width, specs.fill);
    }

    template <typename T>
    scan_expected<iterator> operator()(T& value)
    {
        if constexpr (!detail::is_type_disabled<T> &&
                      std::is_same_v<
                          context_type,
                          basic_contiguous_scan_context<char_type>>) {
            auto rd = make_reader<T, char_type>();
            if (auto e = rd.check_specs(specs); SCN_UNLIKELY(!e)) {
                return unexpected(e);
            }

            return impl(rd, range, value);
        }
        else if constexpr (!detail::is_type_disabled<T>) {
            auto rd = make_reader<T, char_type>();
            if (auto e = rd.check_specs(specs); SCN_UNLIKELY(!e)) {
                return unexpected(e);
            }

            if (!is_segment_contiguous(range) || specs.width != 0) {
                return impl(rd, range, value);
            }

            auto crange = get_as_contiguous(range);
            SCN_TRY(it, impl(rd, crange, value));
            return ranges_polyfill::batch_next(
                ranges::begin(range), ranges::distance(crange.begin(), it));
        }
        else {
            SCN_EXPECT(false);
            SCN_UNREACHABLE;
        }
    }

    scan_expected<iterator> operator()(typename context_type::arg_type::handle)
    {
        SCN_EXPECT(false);
        SCN_UNREACHABLE;
    }

    range_type range;
    const detail::format_specs& specs;
    detail::locale_ref loc;
};

template <typename Context>
struct custom_reader {
    using context_type = Context;
    using char_type = typename context_type::char_type;
    using parse_context_type = typename context_type::parse_context_type;
    using iterator = typename context_type::iterator;

    template <typename T>
    scan_expected<iterator> operator()(T&) const
    {
        SCN_EXPECT(false);
        SCN_UNREACHABLE;
    }

    scan_expected<iterator> operator()(
        typename context_type::arg_type::handle h) const
    {
        if (auto e = h.scan(parse_ctx, ctx); !e) {
            return unexpected(e);
        }
        return {ctx.begin()};
    }

    parse_context_type& parse_ctx;
    context_type& ctx;
};

}  // namespace impl

SCN_END_NAMESPACE
}  // namespace scn
