use bencode::Value;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use nanoserde::{DeJson, SerJson};

const DICT_MIXED: &'static str = "{\
    \"bar\":1,\
    \"baz\":2,\
    \"buz\":{\
        \"abcde\":\"fghij\",\
        \"boz\":\"bez\",\
        \"fghij\":[\"klmnop\",\"qrstuv\",{\"wxyz\":0}]\
    },\
    \"foo\":0,\
    \"zyx\":[0,1,2]\
}";

fn val<T>(t: T) -> Value
where
    T: Into<Value>,
{
    t.into()
}

pub fn serialize(c: &mut Criterion) {
    let dict_mixed = black_box(val(maplit::btreemap! {
        "foo".into() => 0.into(),
        "bar".into() => 1.into(),
        "baz".into() => 2.into(),
        "buz".into() => val(maplit::btreemap! {
            "abcde".into() => "fghij".into(),
            "boz".into() => "bez".into(),
            "fghij".into() => vec![
                "klmnop".into(), "qrstuv".into(), val(maplit::btreemap! {
                    "wxyz".into() => 0.into()
                })
            ].into(),
        }),
        "zyx".into() => vec![Value::Int(0), Value::Int(1), Value::Int(2)].into(),
    }));

    c.bench_function("serialize", |b| {
        b.iter(|| {
            dict_mixed.serialize_json();
        })
    });
}

pub fn deserialize(c: &mut Criterion) {
    c.bench_function("deserialize", |b| {
        b.iter(|| {
            Value::deserialize_json(black_box(DICT_MIXED)).expect("Couldn't deserialize JSON");
        })
    });
}

criterion_group!(benches, serialize, deserialize);
criterion_main!(benches);
