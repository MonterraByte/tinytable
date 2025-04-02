use std::num::NonZeroUsize;
use std::{io, iter};

use tinytable::write_table;

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

#[divan::bench(args = [10, 100, 1000, 10000])]
fn too_long(rows: usize) {
    const S: &str = "                ";
    const ROW: [&str; COLUMNS] = [S; COLUMNS];

    let mut output = io::empty();
    write_table(&mut output, iter::repeat_n(ROW, rows), &ROW, &COLUMN_WIDTHS).expect("write_table failed");
}
