use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::fs::File;

const TORRENT_PATH: &'static str = concat!(env!("CARGO_MANIFEST_DIR"), "/data/torrent.benc");
const DEEP1_PATH: &'static str = concat!(env!("CARGO_MANIFEST_DIR"), "/data/max_depth.benc");
const DEEP2_PATH: &'static str = concat!(env!("CARGO_MANIFEST_DIR"), "/data/really_deep.benc");

pub fn load(c: &mut Criterion) {
    c.bench_function("load torrent file", |b| {
        let mut file = File::open(TORRENT_PATH).unwrap();

        b.iter(|| {
            bencode::load(black_box(&mut file)).expect("Failed loading file");
        })
    });

    c.bench_function("load max depth", |b| {
        let mut file = File::open(DEEP1_PATH).unwrap();

        b.iter(|| {
            bencode::load(black_box(&mut file)).expect("Failed loading file");
        })
    });

    c.bench_function("load really deep", |b| {
        let mut file = File::open(DEEP2_PATH).unwrap();

        b.iter(|| {
            bencode::load(black_box(&mut file)).expect("Failed loading file");
        })
    });
}

pub fn encode(c: &mut Criterion) {
    let mut file = File::open(TORRENT_PATH).unwrap();
    let mut buffer = Vec::new();
    let value = bencode::load(&mut file).expect("Failed loading file");

    c.bench_function("encode value", |b| {
        b.iter(|| {
            value
                .encode(black_box(&mut buffer))
                .expect("Failed loading file");
            buffer.clear();
        })
    });
}

criterion_group!(benches, load, encode);
criterion_main!(benches);
