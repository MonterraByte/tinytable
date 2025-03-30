// Copyright © 2025 Joaquim Monteiro
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![forbid(unsafe_code)]
#![warn(clippy::pedantic)]
#![allow(clippy::items_after_statements)]
#![allow(clippy::missing_panics_doc)]
#![allow(clippy::uninlined_format_args)]

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

use std::fmt::Write as FmtWrite;
use std::fmt::{self, Display};
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
pub fn write_table<Cell: Display, Row: IntoIterator<Item = Cell>, const COLUMN_COUNT: usize>(
    to: impl Write,
    iter: impl Iterator<Item = Row>,
    column_names: &[&str; COLUMN_COUNT],
    column_widths: &[NonZeroUsize; COLUMN_COUNT],
) -> io::Result<()> {
    let mut writer = write_table_start(to, column_names, column_widths)?;

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

    write_table_end(writer, column_widths)
}

/// Render a table using custom formatters.
///
/// Variant of [`write_table`] that converts values to text using the provided `formatters` instead of the [`Display`]
/// trait. Besides being able to use a different representation than the one provided by a type's [`Display`]
/// implementation, it is also useful for displaying values that do not implement [`Display`].
///
/// # Examples
///
/// ```
/// # use std::net::Ipv4Addr;
/// # use std::num::NonZeroUsize;
/// # use tinytable::write_table_with_fmt;
/// # let stdout = std::io::stdout();
/// use std::fmt::Write;
///
/// let addrs = [
///     Ipv4Addr::new(192, 168, 0, 1),
///     Ipv4Addr::new(1, 1, 1, 1),
///     Ipv4Addr::new(255, 127, 63, 31),
/// ];
/// let column_names = ["Full address", "BE bits", "Private"];
/// let column_widths = [17, 12, 7].map(|n| NonZeroUsize::new(n).expect("non zero"));
///
/// let formatters: [fn(&Ipv4Addr, &mut String) -> std::fmt::Result; 3] = [
///     |addr, f| write!(f, "{}", addr),
///     |addr, f| write!(f, "0x{:x}", addr.to_bits().to_be()),
///     |addr, f| write!(f, "{}", if addr.is_private() { "yes" } else { "no" }),
/// ];
///
/// write_table_with_fmt(stdout.lock(), addrs.iter().copied(), &formatters, &column_names, &column_widths)?;
/// # Ok::<(), std::io::Error>(())
/// ```
///
/// ```non_rust
/// ╭─────────────────┬────────────┬───────╮
/// │ Full address    │ BE bits    │Private│
/// ├─────────────────┼────────────┼───────┤
/// │ 192.168.0.1     │ 0x100a8c0  │ yes   │
/// │ 1.1.1.1         │ 0x1010101  │ no    │
/// │ 255.127.63.31   │ 0x1f3f7fff │ no    │
/// ╰─────────────────┴────────────┴───────╯
/// ```
///
/// # Errors
///
/// If an I/O error is encountered while writing to the `to` writer, that error will be returned.
pub fn write_table_with_fmt<Row, const COLUMN_COUNT: usize>(
    to: impl Write,
    iter: impl Iterator<Item = Row>,
    formatters: &[fn(&Row, &mut String) -> fmt::Result; COLUMN_COUNT],
    column_names: &[&str; COLUMN_COUNT],
    column_widths: &[NonZeroUsize; COLUMN_COUNT],
) -> io::Result<()> {
    let mut writer = write_table_start(to, column_names, column_widths)?;

    let mut value = String::new();
    for row in iter {
        writer.write_all(VERTICAL_LINE.as_bytes())?;

        let mut formatters = formatters.iter();
        for space in column_widths.iter().copied().map(NonZeroUsize::get) {
            if let Some(formatter) = formatters.next() {
                formatter(&row, &mut value).expect("formatting to a string shouldn't fail");
            }
            draw_cell(&mut writer, &value, space)?;
            value.clear();
        }

        writer.write_all("\n".as_bytes())?;
    }

    write_table_end(writer, column_widths)
}

fn write_table_start<W: Write, const COLUMN_COUNT: usize>(
    to: W,
    column_names: &[&str; COLUMN_COUNT],
    column_widths: &[NonZeroUsize; COLUMN_COUNT],
) -> Result<BufWriter<W>, io::Error> {
    let _: () = const { assert!(COLUMN_COUNT > 0, "table must have columns") };

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

    Ok(writer)
}

fn write_table_end<W: Write, const COLUMN_COUNT: usize>(
    mut writer: BufWriter<W>,
    column_widths: &[NonZeroUsize; COLUMN_COUNT],
) -> Result<(), io::Error> {
    draw_horizontal_line(
        &mut writer,
        column_widths,
        BOTTOM_LEFT,
        BOTTOM_RIGHT,
        BOTTOM_INTERSECTION,
    )?;
    writer.flush()
}

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

    mod custom_fmt {
        use super::*;
        use std::net::Ipv4Addr;

        #[test]
        fn test() {
            let addrs = [
                Ipv4Addr::new(192, 168, 0, 1),
                Ipv4Addr::new(1, 1, 1, 1),
                Ipv4Addr::new(255, 127, 63, 31),
            ];
            let column_names = ["Full address", "BE bits", "Private"];
            let column_widths = [nz!(17), nz!(12), nz!(7)];

            let formatters: [fn(&Ipv4Addr, &mut String) -> fmt::Result; 3] = [
                |a, f| write!(f, "{}", a),
                |a, f| write!(f, "0x{:x}", a.to_bits().to_be()),
                |a, f| write!(f, "{}", if a.is_private() { "yes" } else { "no" }),
            ];

            let mut output = Vec::new();
            write_table_with_fmt(
                &mut output,
                addrs.iter().copied(),
                &formatters,
                &column_names,
                &column_widths,
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
        }
    }
}

/// ```compile_fail
/// let data: [[&str; 0]; 0] = [];
/// tinytable::write_table(::std::io::stdout(), data.iter(), &[], &[]).unwrap();
/// ```
#[cfg(doctest)]
fn no_columns() {}
