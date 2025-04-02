use std::num::NonZeroUsize;
use std::{io, iter};

use tinytable::{write_table, write_table_with_fmt};

#[cfg(tinytable_profile_alloc)]
use divan::AllocProfiler;

#[cfg(tinytable_profile_alloc)]
#[global_allocator]
static ALLOC: AllocProfiler = AllocProfiler::system();

fn main() {
    divan::main();
}

const COLUMNS: usize = 10;
const COLUMN_WIDTHS: [NonZeroUsize; COLUMNS] = [NonZeroUsize::new(10).unwrap(); COLUMNS];

#[divan::bench(args = [10, 100, 1000, 10000])]
fn no_padding(rows: usize) {
    const S: &str = "          ";
    const ROW: [&str; COLUMNS] = [S; COLUMNS];

    let mut output = io::empty();
    write_table(&mut output, iter::repeat_n(ROW, rows), &ROW, &COLUMN_WIDTHS).expect("write_table failed");
}

#[divan::bench(args = [10, 100, 1000, 10000])]
fn no_padding_unicode(rows: usize) {
    const S: &str = "あいうえお";
    const ROW: [&str; COLUMNS] = [S; COLUMNS];

    let mut output = io::empty();
    write_table(&mut output, iter::repeat_n(ROW, rows), &ROW, &COLUMN_WIDTHS).expect("write_table failed");
}

#[divan::bench(args = [10, 100, 1000, 10000])]
fn all_padding(rows: usize) {
    const S: &str = "";
    const ROW: [&str; COLUMNS] = [S; COLUMNS];

    let mut output = io::empty();
    write_table(&mut output, iter::repeat_n(ROW, rows), &ROW, &COLUMN_WIDTHS).expect("write_table failed");
}

#[divan::bench(args = [10, 100, 1000, 10000])]
fn single_padding(rows: usize) {
    const S: &str = "        ";
    const ROW: [&str; COLUMNS] = [S; COLUMNS];

    let mut output = io::empty();
    write_table(&mut output, iter::repeat_n(ROW, rows), &ROW, &COLUMN_WIDTHS).expect("write_table failed");
}

#[cfg(feature = "fallible-iterator")]
#[divan::bench(args = [10, 100, 1000, 10000])]
fn single_padding_fallible(rows: usize) {
    use fallible_iterator::FallibleIterator;
    use tinytable::write_table_fallible;

    const S: &str = "        ";
    const ROW: [&str; COLUMNS] = [S; COLUMNS];

    let mut output = io::empty();
    write_table_fallible(
        &mut output,
        fallible_iterator::repeat::<_, ()>(ROW).take(rows),
        &ROW,
        &COLUMN_WIDTHS,
    )
    .expect("write_table failed");
}

#[divan::bench(args = [10, 100, 1000, 10000])]
fn single_padding_unicode(rows: usize) {
    const S: &str = "あいうえ";
    const ROW: [&str; COLUMNS] = [S; COLUMNS];

    let mut output = io::empty();
    write_table(&mut output, iter::repeat_n(ROW, rows), &ROW, &COLUMN_WIDTHS).expect("write_table failed");
}

#[divan::bench(args = [10, 100, 1000, 10000])]
fn single_padding_fmt_reuse_cell(rows: usize) {
    const ROW: &str = "        ";
    const COLUMN_NAMES: [&str; COLUMNS] = [ROW; COLUMNS];

    fn fmt(row: &&str, f: &mut String) -> std::fmt::Result {
        use std::fmt::Write;
        write!(f, "{}", row)
    }

    let mut output = io::empty();
    write_table_with_fmt(
        &mut output,
        iter::repeat_n(ROW, rows),
        &[fmt; COLUMNS],
        &COLUMN_NAMES,
        &COLUMN_WIDTHS,
    )
    .expect("write_table failed");
}

#[divan::bench(args = [10, 100, 1000, 10000])]
fn single_padding_fmt_visitor(rows: usize) {
    const S: &str = "        ";
    const ROW: [&str; COLUMNS] = [S; COLUMNS];

    fn fmt(index: usize) -> impl Fn(&[&str; COLUMNS], &mut String) -> std::fmt::Result {
        use std::fmt::Write;
        move |row: &[&str; COLUMNS], f: &mut String| write!(f, "{}", row[index])
    }

    let mut output = io::empty();
    write_table_with_fmt(
        &mut output,
        iter::repeat_n(ROW, rows),
        &[
            fmt(0),
            fmt(1),
            fmt(2),
            fmt(3),
            fmt(4),
            fmt(5),
            fmt(6),
            fmt(7),
            fmt(8),
            fmt(9),
        ],
        &ROW,
        &COLUMN_WIDTHS,
    )
    .expect("write_table failed");
}

#[divan::bench(args = [10, 100, 1000, 10000])]
fn too_long(rows: usize) {
    const S: &str = "                ";
    const ROW: [&str; COLUMNS] = [S; COLUMNS];

    let mut output = io::empty();
    write_table(&mut output, iter::repeat_n(ROW, rows), &ROW, &COLUMN_WIDTHS).expect("write_table failed");
}
