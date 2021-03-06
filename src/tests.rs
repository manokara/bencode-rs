use super::Value;
use std::collections::BTreeMap;

const TORRENT_PATH: &'static str = concat!(env!("CARGO_MANIFEST_DIR"), "/data/torrent.benc");
const DICT_VAL_INT: &[u8] = b"d3:bari1e3:bazi2e3:fooi0ee";
const LIST_VAL_STR: &[u8] = b"l3:foo3:bar3:baze";
const LIST_VAL_INT: &[u8] = b"li0ei1ei2ee";
const LIST_NESTED: &[u8] = b"lli0ei1ei2eeli3ei4ei5eeli6ei7ei8eee";
const LIST_NEGATIVES: &[u8] = b"li-1ei-2ei-3ee";
const DICT_MIXED: &[u8] = b"d3:bari1e3:bazi2e3:buzd5:abcde5:fghij3:boz\
                            3:bez5:fghijl6:klmnop6:qrstuvd4:wxyzi0eeee3:fooi0e3:zyxli0ei1ei2eee";

fn check_value(source: &[u8], value: Value) {
    match super::load(source) {
        Ok(v) => assert_eq!(v, value),
        Err(e) => panic!("Got {:?}", e),
    }
}

fn val<T>(t: T) -> Value
where
    T: Into<Value>,
{
    t.into()
}

#[test]
fn load_primitive_int() {
    check_value(b"i123456e", Value::Int(123456));
}

#[test]
fn load_primitive_str() {
    check_value(b"6:foobar", Value::Str("foobar".into()));
}

#[test]
fn load_dict_val_int() {
    let mut map = BTreeMap::new();
    map.insert("foo".into(), Value::Int(0));
    map.insert("bar".into(), Value::Int(1));
    map.insert("baz".into(), Value::Int(2));

    check_value(DICT_VAL_INT, Value::Dict(map));
}

#[test]
fn load_list_val_str() {
    let list = Value::List(vec![
        Value::Str("foo".into()),
        Value::Str("bar".into()),
        Value::Str("baz".into()),
    ]);

    check_value(LIST_VAL_STR, list);
}

#[test]
fn load_list_val_int() {
    let list = Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(2)]);

    check_value(LIST_VAL_INT, list);
}

#[test]
fn load_list_nested() {
    let list = val(vec![
        val(vec![Value::Int(0), Value::Int(1), Value::Int(2)]),
        val(vec![Value::Int(3), Value::Int(4), Value::Int(5)]),
        val(vec![Value::Int(6), Value::Int(7), Value::Int(8)]),
    ]);

    check_value(LIST_NESTED, list);
}

#[test]
fn load_list_negatives() {
    let list = val(vec![(-1).into(), (-2).into(), (-3).into()] as Vec<Value>);

    check_value(LIST_NEGATIVES, list);
}

#[test]
fn load_dict_mixed() {
    let dict = val(maplit::btreemap! {
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
    });

    check_value(DICT_MIXED, dict);
}

#[test]
fn select_dict_simple() {
    let dict = val(maplit::btreemap! {
        "foo".into() => 0.into(),
        "bar".into() => 1.into(),
        "baz".into() => 2.into(),
    });

    assert_eq!(dict.select(".foo").unwrap(), &Value::Int(0));
    assert_eq!(dict.select(".bar").unwrap(), &Value::Int(1));
    assert_eq!(dict.select(".baz").unwrap(), &Value::Int(2));
}

#[test]
fn select_list_nested() {
    let list_1 = val(vec![Value::Int(0), Value::Int(1), Value::Int(2)]);
    let list_2 = val(vec![Value::Int(3), Value::Int(4), Value::Int(5)]);
    let list_3 = val(vec![Value::Int(6), Value::Int(7), Value::Int(8)]);
    let list = val(vec![list_1.clone(), list_2.clone(), list_3.clone()]);

    assert_eq!(list.select("[0]").unwrap(), &list_1);
    assert_eq!(list.select("[1]").unwrap(), &list_2);
    assert_eq!(list.select("[2]").unwrap(), &list_3);
    assert_eq!(list.select("[0][0]").unwrap(), &Value::Int(0));
    assert_eq!(list.select("[0][1]").unwrap(), &Value::Int(1));
    assert_eq!(list.select("[0][2]").unwrap(), &Value::Int(2));
    assert_eq!(list.select("[1][0]").unwrap(), &Value::Int(3));
    assert_eq!(list.select("[1][1]").unwrap(), &Value::Int(4));
    assert_eq!(list.select("[1][2]").unwrap(), &Value::Int(5));
    assert_eq!(list.select("[2][0]").unwrap(), &Value::Int(6));
    assert_eq!(list.select("[2][1]").unwrap(), &Value::Int(7));
    assert_eq!(list.select("[2][2]").unwrap(), &Value::Int(8));
}

#[test]
fn select_dict_mixed() {
    let mut root_map = BTreeMap::new();
    let mut buz_map = BTreeMap::new();
    let mut fghij_map = BTreeMap::new();

    fghij_map.insert("wxyz".into(), Value::Int(0));

    let fghij_list = Value::List(vec![
        Value::Str("klmnop".into()),
        Value::Str("qrstuv".into()),
        Value::Dict(fghij_map.clone()),
    ]);
    let zyx_list = Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(2)]);

    buz_map.insert("abcde".into(), Value::Str("fghij".into()));
    buz_map.insert("boz".into(), Value::Str("bez".into()));
    buz_map.insert("fghij".into(), fghij_list.clone());
    root_map.insert("foo".into(), Value::Int(0));
    root_map.insert("bar".into(), Value::Int(1));
    root_map.insert("baz".into(), Value::Int(2));
    root_map.insert("buz".into(), Value::Dict(buz_map.clone()));
    root_map.insert("zyx".into(), zyx_list);
    let dict = Value::Dict(root_map);

    assert_eq!(dict.select(".foo").unwrap(), &Value::Int(0));
    assert_eq!(dict.select(".bar").unwrap(), &Value::Int(1));
    assert_eq!(dict.select(".baz").unwrap(), &Value::Int(2));
    assert_eq!(dict.select(".buz").unwrap(), &Value::Dict(buz_map));
    assert_eq!(
        dict.select(".buz.abcde").unwrap(),
        &Value::Str("fghij".into())
    );
    assert_eq!(dict.select(".buz.boz").unwrap(), &Value::Str("bez".into()));
    assert_eq!(dict.select(".buz.fghij").unwrap(), &fghij_list);
    assert_eq!(
        dict.select(".buz.fghij[0]").unwrap(),
        &Value::Str("klmnop".into())
    );
    assert_eq!(
        dict.select(".buz.fghij[1]").unwrap(),
        &Value::Str("qrstuv".into())
    );
    assert_eq!(
        dict.select(".buz.fghij[2]").unwrap(),
        &Value::Dict(fghij_map)
    );
    assert_eq!(dict.select(".buz.fghij[2].wxyz").unwrap(), &Value::Int(0));
}

#[test]
fn load_expect() {
    use super::{load_dict, load_list, load_prim};

    macro_rules! check_ok {
        ($exp:expr) => {
            if let Err(e) = $exp {
                panic!("Failed with {:?}", e);
            }
        };
    }

    macro_rules! check_err {
        ($exp:expr) => {
            if let Ok(_) = $exp {
                panic!("Succeeded when it was not supposed to");
            }
        };
    }

    // load_dict, valid
    check_ok!(load_dict(DICT_VAL_INT));
    check_ok!(load_dict(DICT_MIXED));

    // load_dict, invalid
    check_err!(load_dict(LIST_VAL_INT));
    check_err!(load_dict(LIST_VAL_STR));
    check_err!(load_dict(LIST_NESTED));
    check_err!(load_dict(b"i0e"));
    check_err!(load_dict(b"3:foo"));

    // load_list, valid
    check_ok!(load_list(LIST_VAL_INT));
    check_ok!(load_list(LIST_VAL_STR));
    check_ok!(load_list(LIST_NESTED));

    // load_list, invalid
    check_err!(load_list(DICT_VAL_INT));
    check_err!(load_list(DICT_MIXED));
    check_err!(load_list(b"i0e"));
    check_err!(load_list(b"3:foo"));

    // load_prim, valid
    check_ok!(load_prim(b"i0e"));
    check_ok!(load_prim(b"3:foo"));

    // load_prim, invalid
    check_err!(load_prim(DICT_MIXED));
    check_err!(load_prim(LIST_VAL_INT));
    check_err!(load_prim(LIST_VAL_STR));
    check_err!(load_prim(LIST_NESTED));
}

#[test]
fn value_get() {
    let mut root_map = BTreeMap::new();
    let mut buz_map = BTreeMap::new();
    let mut fghij_map = BTreeMap::new();

    fghij_map.insert("wxyz".into(), Value::Int(0));

    let fghij_list = Value::List(vec![
        Value::Str("klmnop".into()),
        Value::Str("qrstuv".into()),
        Value::Dict(fghij_map.clone()),
    ]);
    let zyx_list = Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(2)]);

    buz_map.insert("abcde".into(), Value::Str("fghij".into()));
    buz_map.insert("boz".into(), Value::Str("bez".into()));
    buz_map.insert("fghij".into(), fghij_list.clone());
    root_map.insert("foo".into(), Value::Int(0));
    root_map.insert("bar".into(), Value::Int(1));
    root_map.insert("baz".into(), Value::Int(2));
    root_map.insert("buz".into(), Value::Dict(buz_map.clone()));
    root_map.insert("zyx".into(), zyx_list);
    let dict = Value::Dict(root_map);

    //-------------------
    assert_eq!(dict.get("foo"), Some(&Value::Int(0)));
    assert_eq!(dict.get("bar"), Some(&Value::Int(1)));
    assert_eq!(dict.get("baz"), Some(&Value::Int(2)));

    let buz_abcde = dict.get("buz").and_then(|b| b.get("abcde"));
    let buz_boz = dict.get("buz").and_then(|b| b.get("boz"));
    let fghij_0 = dict
        .get("buz")
        .and_then(|b| b.get("fghij"))
        .and_then(|f| f.get(0));
    let fghij_1 = dict
        .get("buz")
        .and_then(|b| b.get("fghij"))
        .and_then(|f| f.get(1));
    let wxyz = dict
        .get("buz")
        .and_then(|b| b.get("fghij"))
        .and_then(|f| f.get(2))
        .and_then(|m| m.get("wxyz"));
    let zyx_0 = dict.get("zyx").and_then(|z| z.get(0));
    let zyx_1 = dict.get("zyx").and_then(|z| z.get(1));
    let zyx_2 = dict.get("zyx").and_then(|z| z.get(2));

    assert_eq!(buz_abcde, Some(&Value::Str("fghij".into())));
    assert_eq!(buz_boz, Some(&Value::Str("bez".into())));
    assert_eq!(fghij_0, Some(&Value::Str("klmnop".into())));
    assert_eq!(fghij_1, Some(&Value::Str("qrstuv".into())));
    assert_eq!(wxyz, Some(&Value::Int(0)));
    assert_eq!(zyx_0, Some(&Value::Int(0)));
    assert_eq!(zyx_1, Some(&Value::Int(1)));
    assert_eq!(zyx_2, Some(&Value::Int(2)));
}

#[test]
fn value_get_mut() {
    let mut root_map = BTreeMap::new();
    let mut buz_map = BTreeMap::new();
    let mut fghij_map = BTreeMap::new();

    fghij_map.insert("wxyz".into(), Value::Int(0));

    let fghij_list = Value::List(vec![
        Value::Str("klmnop".into()),
        Value::Str("qrstuv".into()),
        Value::Dict(fghij_map.clone()),
    ]);
    let zyx_list = Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(2)]);

    buz_map.insert("abcde".into(), Value::Str("fghij".into()));
    buz_map.insert("boz".into(), Value::Str("bez".into()));
    buz_map.insert("fghij".into(), fghij_list.clone());
    root_map.insert("foo".into(), Value::Int(0));
    root_map.insert("bar".into(), Value::Int(1));
    root_map.insert("baz".into(), Value::Int(2));
    root_map.insert("buz".into(), Value::Dict(buz_map.clone()));
    root_map.insert("zyx".into(), zyx_list);
    let mut dict = Value::Dict(root_map);

    *dict.get_mut("foo").unwrap() = Value::Int(9);
    *dict.get_mut("bar").unwrap() = Value::Int(8);
    *dict.get_mut("baz").unwrap() = Value::Int(7);
    *dict.get_mut("buz").unwrap() = Value::Int(6);
    *dict.get_mut("zyx").unwrap() = Value::Int(5);

    assert_eq!(dict.get("foo").unwrap(), &Value::Int(9));
    assert_eq!(dict.get("bar").unwrap(), &Value::Int(8));
    assert_eq!(dict.get("baz").unwrap(), &Value::Int(7));
    assert_eq!(dict.get("buz").unwrap(), &Value::Int(6));
    assert_eq!(dict.get("buz").and_then(|b| b.get("abcde")), None);
    assert_eq!(dict.get("buz").and_then(|b| b.get(0)), None);
}

#[test]
fn select_mut_dict_simple() {
    let mut map = BTreeMap::new();
    map.insert("foo".into(), Value::Int(0));
    map.insert("bar".into(), Value::Int(1));
    map.insert("baz".into(), Value::Int(2));
    let mut dict = Value::Dict(map);

    *dict.select_mut(".foo").unwrap() = Value::Int(9);
    *dict.select_mut(".bar").unwrap() = Value::Int(8);
    *dict.select_mut(".baz").unwrap() = Value::Int(7);
    assert_eq!(dict.get("foo").unwrap(), &Value::Int(9));
    assert_eq!(dict.get("bar").unwrap(), &Value::Int(8));
    assert_eq!(dict.get("baz").unwrap(), &Value::Int(7));
}

#[test]
fn select_mut_dict_mixed() {
    let mut root_map = BTreeMap::new();
    let mut buz_map = BTreeMap::new();
    let mut fghij_map = BTreeMap::new();

    fghij_map.insert("wxyz".into(), Value::Int(0));

    let fghij_list = Value::List(vec![
        Value::Str("klmnop".into()),
        Value::Str("qrstuv".into()),
        Value::Dict(fghij_map.clone()),
    ]);
    let zyx_list = Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(2)]);

    buz_map.insert("abcde".into(), Value::Str("fghij".into()));
    buz_map.insert("boz".into(), Value::Str("bez".into()));
    buz_map.insert("fghij".into(), fghij_list.clone());
    root_map.insert("foo".into(), Value::Int(0));
    root_map.insert("bar".into(), Value::Int(1));
    root_map.insert("baz".into(), Value::Int(2));
    root_map.insert("buz".into(), Value::Dict(buz_map.clone()));
    root_map.insert("zyx".into(), zyx_list);
    let mut dict = Value::Dict(root_map);

    *dict.select_mut(".buz.fghij[0]").unwrap() = Value::Int(0);
    dict.select_mut(".buz.fghij[2]")
        .unwrap()
        .to_map_mut()
        .unwrap()
        .insert("foo".into(), Value::Int(1));
    dict.select_mut(".buz.fghij[2]")
        .unwrap()
        .to_map_mut()
        .unwrap()
        .insert("bar".into(), Value::Int(2));
    dict.select_mut(".buz.fghij[2]")
        .unwrap()
        .to_map_mut()
        .unwrap()
        .insert("baz".into(), Value::Int(3));

    assert_eq!(dict.select(".buz.fghij[0]").unwrap(), &Value::Int(0));
    assert_eq!(
        dict.select(".buz.fghij[1]").unwrap(),
        &Value::Str("qrstuv".into())
    );
    assert_eq!(dict.select(".buz.fghij[2].wxyz").unwrap(), &Value::Int(0));
    assert_eq!(dict.select(".buz.fghij[2].foo").unwrap(), &Value::Int(1));
    assert_eq!(dict.select(".buz.fghij[2].bar").unwrap(), &Value::Int(2));
    assert_eq!(dict.select(".buz.fghij[2].baz").unwrap(), &Value::Int(3));
}

#[test]
fn value_cmp() {
    let dict = val(maplit::btreemap! {
        "foo".into() => 0.into(),
        "bar".into() => 1.into(),
        "baz".into() => 2.into(),
        "a".into() => "b".into(),
        "b".into() => b"b".as_ref().into(),
    });

    assert_eq!(dict.get("foo").unwrap(), 0i64);
    assert_eq!(dict.get("bar").unwrap(), 1u32);
    assert_eq!(dict.get("baz").unwrap(), 2u8);
    assert_eq!(dict.get("a").unwrap(), "b");
    assert_eq!(dict.get("b").unwrap(), b"b".as_ref());
    assert_eq!(dict.get("b").unwrap(), &vec!['b' as u8]);
    assert_eq!(val(0), 0);
    assert_eq!(val("foo"), "foo");
    assert_eq!(val(0) < 1, true);
    assert_eq!(val("ab") > "aa", true);
}

#[test]
fn value_encode() {
    let mut buffer = Vec::new();

    let list_int = val(vec![0.into(), 1.into(), 2.into()] as Vec<Value>);
    let list_str = val(vec!["foo".into(), "bar".into(), "baz".into()] as Vec<Value>);
    let list_nested = val(vec![
        val(vec![0.into(), 1.into(), 2.into()] as Vec<Value>),
        val(vec![3.into(), 4.into(), 5.into()] as Vec<Value>),
        val(vec![6.into(), 7.into(), 8.into()] as Vec<Value>),
    ]);
    let list_negatives = val(vec![(-1).into(), (-2).into(), (-3).into()] as Vec<Value>);
    let dict_simple = val(maplit::btreemap! {
        "foo".into() => 0.into(),
        "bar".into() => 1.into(),
        "baz".into() => 2.into(),
    });
    let dict_mixed = val(maplit::btreemap! {
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
    });

    list_int.encode(&mut buffer).unwrap();
    assert_eq!(buffer, LIST_VAL_INT);
    buffer.clear();

    list_str.encode(&mut buffer).unwrap();
    assert_eq!(buffer, LIST_VAL_STR);
    buffer.clear();

    list_nested.encode(&mut buffer).unwrap();
    assert_eq!(buffer, LIST_NESTED);
    buffer.clear();

    dict_simple.encode(&mut buffer).unwrap();
    assert_eq!(buffer, DICT_VAL_INT);
    buffer.clear();

    dict_mixed.encode(&mut buffer).unwrap();
    assert_eq!(buffer, DICT_MIXED);
    buffer.clear();

    list_negatives.encode(&mut buffer).unwrap();
    assert_eq!(buffer, LIST_NEGATIVES);
    buffer.clear();
}

#[test]
fn value_traverse() {
    use super::TraverseAction;

    let root_value = super::load(DICT_MIXED).unwrap();
    let matching_value = root_value
        .traverse::<_, ()>(|_key, _index, parent, value, _selector| {
            if let Some(value) = value {
                // Dive into the structure
                if value.is_container() {
                    return Ok(TraverseAction::Enter);
                }

                if value == "qrstuv" {
                    return Ok(TraverseAction::Stop);
                }
            } else if parent != &root_value {
                // End of container, go back up (unless we're at the root)
                // In this particular case this will never happen, since the path to the
                // value is straight down.
                return Ok(TraverseAction::Exit);
            }

            Ok(TraverseAction::Continue)
        })
        .unwrap();

    assert_eq!(matching_value, "qrstuv");
}

#[test]
fn value_insert() {
    let mut root_value = super::load(DICT_MIXED).unwrap();

    root_value.insert("eureka", 7).unwrap();
    assert_eq!(root_value.get("eureka").unwrap(), 7);

    let zyx = root_value.select_mut(".zyx").unwrap();
    zyx.insert(1, 10).unwrap();
    zyx.insert(4, 20).unwrap();
    assert_eq!(zyx.get(0).unwrap(), 0);
    assert_eq!(zyx.get(1).unwrap(), 10);
    assert_eq!(zyx.get(2).unwrap(), 1);
    assert_eq!(zyx.get(3).unwrap(), 2);
    assert_eq!(zyx.get(4).unwrap(), 20);
}

#[test]
fn value_remove() {
    let mut mixed = super::load(DICT_MIXED).unwrap();
    let mut list = super::load(LIST_VAL_INT).unwrap();
    let mixed_final = maplit::btreemap! {
        "foo".into() => 0.into(),
        "bar".into() => 1.into(),
        "baz".into() => 2.into(),
    };
    let list_final: Vec<Value> = vec![0.into(), 2.into()];

    mixed.remove("buz").unwrap();
    mixed.remove("zyx").unwrap();
    list.remove(1).unwrap();
    assert_eq!(mixed.to_map().unwrap(), &mixed_final);
    assert_eq!(list.to_vec().unwrap(), &list_final);
}

#[test]
fn load_torrent() {
    let mut file = std::fs::File::open(TORRENT_PATH).unwrap();
    let root = super::load(&mut file).unwrap();

    assert_eq!(root.select(".comment").unwrap(), "ManjaroLinux");
    assert_eq!(
        root.select(".info.name").unwrap(),
        "manjaro-xfce-20.1.2-201019-linux58.iso"
    );
}

#[test]
#[should_panic]
fn trailing_data() {
    const DATA1: &[u8] = b"d3:foo3:bari0e";
    const DATA2: &[u8] = b"d3:foo3:bar3:baz";
    const DATA3: &[u8] = b"d3:foo3:barle";
    const DATA4: &[u8] = b"d3:foo3:barde";
    const DATA5: &[u8] = b"d3:foo3:bar  ";

    super::load(DATA1).unwrap();
    super::load(DATA2).unwrap();
    super::load(DATA3).unwrap();
    super::load(DATA4).unwrap();
    super::load(DATA5).unwrap();
}

