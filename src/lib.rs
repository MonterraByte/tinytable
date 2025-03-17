// Copyright © 2025 Joaquim Monteiro
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![forbid(unsafe_code)]
#![warn(clippy::pedantic)]
#![allow(clippy::items_after_statements)]
#![allow(clippy::uninlined_format_args)]
#![feature(macro_metavar_expr_concat)]

//! A tiny text table drawing library.
//!
//! Features:
//!
//! * Small code size (it's one function!)
//! * Minimal dependencies (not zero, because Unicode is hard)
//! * Iterator support (you don't need to collect all the data to display at once, it can be streamed)
//! * Unicode support
//! * Nothing more!
//!
//! See [`write_table`] for examples and usage details.

use std::fmt::Display;
use std::fmt::Write as FmtWrite;
use std::io::{self, BufWriter, Write};
use std::num::NonZeroUsize;

use unicode_segmentation::UnicodeSegmentation;
use unicode_width::UnicodeWidthStr;

const HORIZONTAL_LINE: &str = "─";
const VERTICAL_LINE: &str = "│";
const TOP_LEFT: &str = "╭";
const TOP_RIGHT: &str = "╮";
const BOTTOM_LEFT: &str = "╰";
const BOTTOM_RIGHT: &str = "╯";
const INTERSECTION: &str = "┼";
const TOP_INTERSECTION: &str = "┬";
const BOTTOM_INTERSECTION: &str = "┴";
const LEFT_INTERSECTION: &str = "├";
const RIGHT_INTERSECTION: &str = "┤";

/// Render a table.
///
/// Writes a table containing data from `iter`, an [`Iterator`] over rows implementing [`IntoIterator`], which, in turn,
/// yields values that implement [`Display`], into the `to` writer (which can be [`stdout`], a [`Vec<u8>`], etc.).
///
/// The width of each column is fixed (as specified by `column_widths`).
///
/// [`stdout`]: std::io::Stdout
///
/// # Examples
///
/// ```
/// # use std::num::NonZeroUsize;
/// # use tinytable::write_table;
/// let columns = ["x", "x²"];
/// let column_widths = [3, 4].map(|n| NonZeroUsize::new(n).expect("non zero"));
/// let data = [[1, 1], [2, 4], [3, 9], [4, 16]];
/// # let stdout = std::io::stdout();
///
/// write_table(stdout.lock(), data.iter(), &columns, &column_widths)?;
/// # Ok::<(), std::io::Error>(())
/// ```
///
/// ```non_rust
/// ╭───┬────╮
/// │ x │ x² │
/// ├───┼────┤
/// │ 1 │ 1  │
/// │ 2 │ 4  │
/// │ 3 │ 9  │
/// │ 4 │ 16 │
/// ╰───┴────╯
/// ```
///
/// Non-trivial iterators are supported:
///
/// ```
/// # use std::num::NonZeroUsize;
/// # use tinytable::write_table;
/// let columns = ["x", "x²"];
/// let column_widths = [3, 4].map(|n| NonZeroUsize::new(n).expect("non zero"));
/// let iter = (1..).take(4).map(|n| [n, n * n]);
/// # let stdout = std::io::stdout();
///
/// write_table(stdout.lock(), iter, &columns, &column_widths)?;
/// # Ok::<(), std::io::Error>(())
/// ```
///
/// ```non_rust
/// ╭───┬────╮
/// │ x │ x² │
/// ├───┼────┤
/// │ 1 │ 1  │
/// │ 2 │ 4  │
/// │ 3 │ 9  │
/// │ 4 │ 16 │
/// ╰───┴────╯
/// ```
///
/// # Errors
///
/// If an I/O error is encountered while writing to the `to` writer, that error will be returned.
pub fn write_table<
    Cell: Display,
    Row: IntoIterator<Item = Cell>,
    I: Iterator<Item = Row>,
    const COLUMN_COUNT: usize,
>(
    to: impl Write,
    iter: I,
    column_names: &[&str; COLUMN_COUNT],
    column_widths: &[NonZeroUsize; COLUMN_COUNT],
) -> io::Result<()> {
    let _: () = const { assert!(COLUMN_COUNT > 0, "table must have columns") };

    fn draw_horizontal_line<const COLUMN_COUNT: usize, W: Write>(
        writer: &mut BufWriter<W>,
        column_widths: &[NonZeroUsize; COLUMN_COUNT],
        left: &str,
        right: &str,
        intersection: &str,
    ) -> io::Result<()> {
        writer.write_all(left.as_bytes())?;
        for (i, width) in column_widths.iter().enumerate() {
            for _ in 0..width.get() {
                writer.write_all(HORIZONTAL_LINE.as_bytes())?;
            }
            writer.write_all((if i == COLUMN_COUNT - 1 { right } else { intersection }).as_bytes())?;
        }
        writer.write_all("\n".as_bytes())
    }

    fn draw_cell<W: Write>(writer: &mut BufWriter<W>, value: &str, space: usize) -> io::Result<()> {
        let value_width = value.width();
        let padding = if unlikely(value_width > space) {
            let mut remaining = space - 1;
            for grapheme in value.graphemes(true) {
                remaining = match remaining.checked_sub(grapheme.width()) {
                    Some(r) => r,
                    None => break,
                };
                writer.write_all(grapheme.as_bytes())?;
            }
            writer.write_all("…".as_bytes())?;
            remaining
        } else {
            if value_width < space {
                writer.write_all(" ".as_bytes())?;
            }
            writer.write_all(value.as_bytes())?;
            (space - value_width).saturating_sub(1)
        };
        for _ in 0..padding {
            writer.write_all(" ".as_bytes())?;
        }
        writer.write_all(VERTICAL_LINE.as_bytes())
    }

    let mut writer = BufWriter::new(to);
    draw_horizontal_line(&mut writer, column_widths, TOP_LEFT, TOP_RIGHT, TOP_INTERSECTION)?;

    writer.write_all(VERTICAL_LINE.as_bytes())?;
    for (space, name) in column_widths.iter().copied().map(NonZeroUsize::get).zip(column_names) {
        draw_cell(&mut writer, name, space)?;
    }
    writer.write_all("\n".as_bytes())?;

    draw_horizontal_line(
        &mut writer,
        column_widths,
        LEFT_INTERSECTION,
        RIGHT_INTERSECTION,
        INTERSECTION,
    )?;

    let mut value = String::new();
    for row in iter {
        writer.write_all(VERTICAL_LINE.as_bytes())?;

        let mut row_iter = row.into_iter();
        for space in column_widths.iter().copied().map(NonZeroUsize::get) {
            if let Some(col) = row_iter.next() {
                write!(&mut value, "{}", col).expect("formatting to a string shouldn't fail");
            }
            draw_cell(&mut writer, &value, space)?;
            value.clear();
        }

        writer.write_all("\n".as_bytes())?;
    }

    draw_horizontal_line(
        &mut writer,
        column_widths,
        BOTTOM_LEFT,
        BOTTOM_RIGHT,
        BOTTOM_INTERSECTION,
    )?;
    writer.flush()
}

// TODO: replace with ${count()} when feature `macro_metavar_expr` is stabilized
/// INTERNAL USE ONLY. DO NOT USE.
#[doc(hidden)]
#[macro_export]
macro_rules! count_exprs {
    () => {0usize};
    ($_x:expr) => {1usize};
    ($_head:expr, $($tail:expr),*) => {1usize + count_exprs!($($tail),*)};
}

#[macro_export]
macro_rules! display_wrapper_inner {
    ($(with hrtb $hrtb:tt,)? $vis:vis $name:ident, $wrapped_type:ty, $($formatter:expr),+) => {
        $vis struct $name<I: $($hrtb)? ::core::iter::Iterator<Item = $wrapped_type>> {
            iter: I,
            current_value: ::std::rc::Rc<::core::cell::RefCell<::core::option::Option<$wrapped_type>>>,
        }

        impl<I: ::core::iter::Iterator<Item = $wrapped_type>> $name<I> {
            pub fn new(iter: I) -> Self {
                Self {
                    iter,
                    current_value: ::core::default::Default::default(),
                }
            }
        }

        impl<I: ::core::iter::Iterator<Item = $wrapped_type>> ::core::iter::Iterator for $name<I> {
            type Item = ${concat($name, RowIter)};

            fn next(&mut self) -> ::core::option::Option<Self::Item> {
                let new_value = self.iter.next();
                let is_some = new_value.is_some();
                self.current_value.replace(new_value);

                if is_some {
                     Some(${concat($name, RowIter)} {
                         index: 0,
                         current_value_ref: ::std::rc::Rc::downgrade(&self.current_value),
                     })
                } else {
                    None
                }
            }
        }

        $vis struct ${concat($name, RowIter)} {
            index: ::core::primitive::usize,
            current_value_ref: ::std::rc::Weak<::core::cell::RefCell<::core::option::Option<$wrapped_type>>>,
        }

        impl ${concat($name, RowIter)} {
            const FORMATTERS: [fn(&$wrapped_type, &mut ::core::fmt::Formatter) -> ::core::fmt::Result; $crate::count_exprs!($($formatter),+)] = [$($formatter),+];

            #[allow(clippy::inline_always)]
            #[inline(always)]
            fn next_impl(&mut self) -> ::core::option::Option<<Self as ::core::iter::Iterator>::Item> {
                if let Some(formatter) = Self::FORMATTERS.get(self.index) {
                    self.index += 1;
                    Some(${concat($name, CellDisplay)} {
                        formatter: *formatter,
                        current_value_ref: ::std::rc::Weak::clone(&self.current_value_ref),
                    })
                } else {
                    None
                }
            }
        }

        impl ::core::iter::Iterator for ${concat($name, RowIter)} {
            type Item = ${concat($name, CellDisplay)};

            fn next(&mut self) -> ::core::option::Option<Self::Item> {
                self.next_impl()
            }
        }

        $vis struct ${concat($name, CellDisplay)} {
            formatter: fn(&$wrapped_type, &mut ::core::fmt::Formatter) -> ::core::fmt::Result,
            current_value_ref: ::std::rc::Weak<::core::cell::RefCell<::core::option::Option<$wrapped_type>>>,
        }

        impl ::core::fmt::Display for ${concat($name, CellDisplay)} {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                (self.formatter)(self.current_value_ref.upgrade().expect("`Display` wrapper was not dropped").borrow().as_ref().expect("cell `Display` wrapper is used immediately after being created"), f)
            }
        }
    };
}

/// Macro that generates a wrapper that implements `Iterator<Item = ToString>` for any type
/// using the provided formatters.
#[macro_export]
macro_rules! display_wrapper {
    ($vis:vis $name:ident, &$wrapped_type:ty, $($formatter:expr),+) => {
        $crate::display_wrapper_inner!(with hrtb for<'a>, $vis $name, &'a $wrapped_type, $($formatter),+);
    };
    ($vis:vis $name:ident, $wrapped_type:ty, $($formatter:expr),+) => {
        $crate::display_wrapper_inner!($vis $name, $wrapped_type, $($formatter),+);
    };
}
#[allow(clippy::inline_always)]
#[inline(always)]
const fn unlikely(b: bool) -> bool {
    if b {
        cold();
    }
    b
}

#[inline(always)]
#[cold]
const fn cold() {}

#[cfg(test)]
mod tests {
    use super::*;
    use unicode_width::UnicodeWidthStr;

    macro_rules! nz {
        ($val:expr) => {
            ::core::num::NonZeroUsize::new($val).unwrap()
        };
    }

    fn assert_consistent_width(output: &str) {
        let mut width = None;
        for line in output.lines() {
            if let Some(width) = width {
                assert_eq!(line.width(), width);
            } else {
                width = Some(line.width());
            }
        }
    }

    #[test]
    fn simple() {
        let data = [["q3rrq", "qfqh843f9", "qa"], ["123", "", "aaaaaa"]];
        let mut output = Vec::new();
        write_table(&mut output, data.iter(), &["A", "B", "C"], &[nz!(5), nz!(10), nz!(4)])
            .expect("write_table failed");
        let output = String::from_utf8(output).expect("valid UTF-8");
        assert_eq!(
            output,
            "╭─────┬──────────┬────╮
│ A   │ B        │ C  │
├─────┼──────────┼────┤
│q3rrq│ qfqh843f9│ qa │
│ 123 │          │aaa…│
╰─────┴──────────┴────╯
"
        );
        assert_consistent_width(&output);
    }

    #[test]
    fn iter() {
        use std::borrow::ToOwned;
        use std::io::{BufRead, BufReader};

        let data = "asdf eraf r34r23r
awhfde 93ry af3f98
awefz 234 23
3442342 1 4";

        let mut output = Vec::new();
        let file = BufReader::new(data.as_bytes());
        write_table(
            &mut output,
            file.lines()
                .map(|line| line.unwrap().split(' ').map(ToOwned::to_owned).collect::<Vec<_>>()),
            &["col1", "col2", "col3"],
            &[nz!(5), nz!(7), nz!(10)],
        )
        .expect("write_table failed");

        let output = String::from_utf8(output).expect("valid UTF-8");
        assert_eq!(
            output,
            "╭─────┬───────┬──────────╮
│ col1│ col2  │ col3     │
├─────┼───────┼──────────┤
│ asdf│ eraf  │ r34r23r  │
│awhf…│ 93ry  │ af3f98   │
│awefz│ 234   │ 23       │
│3442…│ 1     │ 4        │
╰─────┴───────┴──────────╯
"
        );
        assert_consistent_width(&output);
    }

    #[test]
    fn empty() {
        let data: [[&str; 0]; 0] = [];
        let mut output = Vec::new();
        write_table(&mut output, data.iter(), &["A", "B"], &[nz!(1), nz!(1)]).expect("write_table failed");

        let output = String::from_utf8(output).expect("valid UTF-8");
        assert_eq!(
            output,
            "╭─┬─╮
│A│B│
├─┼─┤
╰─┴─╯
"
        );
        assert_consistent_width(&output);
    }

    #[test]
    fn not_enough_data() {
        let data = [["A"], ["B"], ["C"]];
        let mut output = Vec::new();
        write_table(&mut output, data.iter(), &["1", "2"], &[nz!(3), nz!(5)]).expect("write_table failed");

        let output = String::from_utf8(output).expect("valid UTF-8");
        assert_eq!(
            output,
            "╭───┬─────╮
│ 1 │ 2   │
├───┼─────┤
│ A │     │
│ B │     │
│ C │     │
╰───┴─────╯
"
        );
        assert_consistent_width(&output);
    }

    #[test]
    fn too_much_data() {
        let data = [["A", "B", "C"], ["D", "E", "F"], ["G", "H", "I"]];
        let mut output = Vec::new();
        write_table(&mut output, data.iter(), &["1", "2"], &[nz!(3), nz!(3)]).expect("write_table failed");

        let output = String::from_utf8(output).expect("valid UTF-8");
        assert_eq!(
            output,
            "╭───┬───╮
│ 1 │ 2 │
├───┼───┤
│ A │ B │
│ D │ E │
│ G │ H │
╰───┴───╯
"
        );
        assert_consistent_width(&output);
    }

    #[test]
    fn unicode() {
        let data = [["あいうえお", "スペース"], ["🦀🦀🦀🦀🦀🦀", "🗿🗿🗿"]];
        let mut output = Vec::new();
        write_table(&mut output, data.iter(), &["A", "B"], &[nz!(12), nz!(7)]).expect("write_table failed");

        let output = String::from_utf8(output).expect("valid UTF-8");
        assert_eq!(
            output,
            "╭────────────┬───────╮
│ A          │ B     │
├────────────┼───────┤
│ あいうえお │スペー…│
│🦀🦀🦀🦀🦀🦀│ 🗿🗿🗿│
╰────────────┴───────╯
"
        );
        assert_consistent_width(&output);
    }
    mod display_wrapper {
        use super::*;
        use std::net::Ipv4Addr;

        const COLUMN_NAMES: [&str; 3] = ["Full address", "BE bits", "Private"];
        const COLUMN_WIDTHS: [NonZeroUsize; 3] = [nz!(17), nz!(12), nz!(7)];
        display_wrapper!(
            AddrWrapper,
            Ipv4Addr,
            |a, f| write!(f, "{}", a),
            |a, f| write!(f, "0x{:x}", a.to_bits().to_be()),
            |a, f| write!(f, "{}", if a.is_private() { "yes" } else { "no" })
        );
        display_wrapper!(
            AddrRefWrapper,
            &Ipv4Addr,
            |a, f| write!(f, "{}", a),
            |a, f| write!(f, "0x{:x}", a.to_bits().to_be()),
            |a, f| write!(f, "{}", if a.is_private() { "yes" } else { "no" })
        );

        #[test]
        fn test() {
            let addrs: [Ipv4Addr; 3] = [
                Ipv4Addr::new(192, 168, 0, 1),
                Ipv4Addr::new(1, 1, 1, 1),
                Ipv4Addr::new(255, 127, 63, 31),
            ];

            let mut output = Vec::new();
            write_table(
                &mut output,
                AddrWrapper::new(addrs.iter().copied()),
                &COLUMN_NAMES,
                &COLUMN_WIDTHS,
            )
            .expect("write_table failed");

            let output = String::from_utf8(output).expect("valid UTF-8");
            assert_eq!(
                output,
                "╭─────────────────┬────────────┬───────╮
│ Full address    │ BE bits    │Private│
├─────────────────┼────────────┼───────┤
│ 192.168.0.1     │ 0x100a8c0  │ yes   │
│ 1.1.1.1         │ 0x1010101  │ no    │
│ 255.127.63.31   │ 0x1f3f7fff │ no    │
╰─────────────────┴────────────┴───────╯
"
            );
            assert_consistent_width(&output);

            let mut ref_output = Vec::new();
            write_table(
                &mut ref_output,
                AddrRefWrapper::new(addrs.iter()),
                &COLUMN_NAMES,
                &COLUMN_WIDTHS,
            )
            .expect("write_table failed");
            assert_eq!(output.as_bytes(), ref_output);
        }
    }
}

/// ```compile_fail
/// let data: [[&str; 0]; 0] = [];
/// tinytable::write_table(::std::io::stdout(), data.iter(), &[], &[]).unwrap();
/// ```
#[cfg(doctest)]
fn no_columns() {}
