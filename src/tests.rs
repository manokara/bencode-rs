use std::collections::BTreeMap;
use super::Value;

const DICT_VAL_INT: &'static str = "d3:fooi0e3:bari1e3:bazi2ee";
const LIST_VAL_STR: &'static str = "l3:foo3:bar3:baze";
const LIST_VAL_INT: &'static str = "li0ei1ei2ee";
const LIST_NESTED: &'static str = "lli0ei1ei2eeli3ei4ei5eeli6ei7ei8eee";
const DICT_MIXED: &'static str = "d3:fooi0e3:bari1e3:bazi2e3:buzd3:boz3:bez\
                                  5:abcde5:fghij5:fghijl6:klmnop6:qrstuvd4:wxyzi0eeee3:zyxli0ei1ei2eee";

fn check_value(source: &'static str, value: Value) {
    match super::load_str(source) {
        Ok(v) => assert_eq!(v, value),
        Err(e) => panic!("Got {:?}", e),
    }
}

#[test]
fn load_primitive_int() {
    check_value("i123456e", Value::Int(123456));
}

#[test]
fn load_primitive_str() {
    check_value("6:foobar", Value::Str("foobar".into()));
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
        Value::Str("baz".into())
    ]);

    check_value(LIST_VAL_STR, list);
}

#[test]
fn load_list_val_int() {
    let list = Value::List(vec![
        Value::Int(0),
        Value::Int(1),
        Value::Int(2),
    ]);

    check_value(LIST_VAL_INT, list);
}

#[test]
fn load_list_nested() {
    let list_1 = Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(2)]);
    let list_2 = Value::List(vec![Value::Int(3), Value::Int(4), Value::Int(5)]);
    let list_3 = Value::List(vec![Value::Int(6), Value::Int(7), Value::Int(8)]);
    let list = Value::List(vec![list_1, list_2, list_3]);

    check_value(LIST_NESTED, list);
}

#[test]
fn load_dict_mixed() {
    let mut root_map = BTreeMap::new();
    let mut buz_map = BTreeMap::new();
    let mut fghij_map = BTreeMap::new();

    fghij_map.insert("wxyz".into(), Value::Int(0));

    let fghij_list = Value::List(vec![
        Value::Str("klmnop".into()), Value::Str("qrstuv".into()), Value::Dict(fghij_map),
    ]);
    let zyx_list = Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(2)]);

    buz_map.insert("abcde".into(), Value::Str("fghij".into()));
    buz_map.insert("boz".into(), Value::Str("bez".into()));
    buz_map.insert("fghij".into(), fghij_list);
    root_map.insert("foo".into(), Value::Int(0));
    root_map.insert("bar".into(), Value::Int(1));
    root_map.insert("baz".into(), Value::Int(2));
    root_map.insert("buz".into(), Value::Dict(buz_map));
    root_map.insert("zyx".into(), zyx_list);

    check_value(DICT_MIXED, Value::Dict(root_map));
}

#[test]
fn select_dict_simple() {
    let mut map = BTreeMap::new();
    map.insert("foo".into(), Value::Int(0));
    map.insert("bar".into(), Value::Int(1));
    map.insert("baz".into(), Value::Int(2));
    let dict = Value::Dict(map);

    assert_eq!(dict.select(".foo").unwrap(), &Value::Int(0));
    assert_eq!(dict.select(".bar").unwrap(), &Value::Int(1));
    assert_eq!(dict.select(".baz").unwrap(), &Value::Int(2));
}

#[test]
fn select_list_nested() {
    let list_1 = Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(2)]);
    let list_2 = Value::List(vec![Value::Int(3), Value::Int(4), Value::Int(5)]);
    let list_3 = Value::List(vec![Value::Int(6), Value::Int(7), Value::Int(8)]);
    let list = Value::List(vec![list_1.clone(), list_2.clone(), list_3.clone()]);

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
        Value::Str("klmnop".into()), Value::Str("qrstuv".into()), Value::Dict(fghij_map.clone()),
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
    assert_eq!(dict.select(".buz.abcde").unwrap(), &Value::Str("fghij".into()));
    assert_eq!(dict.select(".buz.boz").unwrap(), &Value::Str("bez".into()));
    assert_eq!(dict.select(".buz.fghij").unwrap(), &fghij_list);
    assert_eq!(dict.select(".buz.fghij[0]").unwrap(), &Value::Str("klmnop".into()));
    assert_eq!(dict.select(".buz.fghij[1]").unwrap(), &Value::Str("qrstuv".into()));
    assert_eq!(dict.select(".buz.fghij[2]").unwrap(), &Value::Dict(fghij_map));
    assert_eq!(dict.select(".buz.fghij[2].wxyz").unwrap(), &Value::Int(0));
}

#[test]
fn load_expect() {
    use super::{load_dict_str, load_list_str};

    assert_eq!(load_dict_str(LIST_NESTED).is_ok(), false);
    assert_eq!(load_dict_str(LIST_VAL_INT).is_ok(), false);
    assert_eq!(load_dict_str(LIST_VAL_STR).is_ok(), false);
    assert_eq!(load_dict_str(LIST_VAL_STR).is_ok(), false);
    assert_eq!(load_list_str(DICT_VAL_INT).is_ok(), false);
    assert_eq!(load_list_str(DICT_MIXED).is_ok(), false);
}

#[test]
fn value_get() {
    let mut root_map = BTreeMap::new();
    let mut buz_map = BTreeMap::new();
    let mut fghij_map = BTreeMap::new();

    fghij_map.insert("wxyz".into(), Value::Int(0));

    let fghij_list = Value::List(vec![
        Value::Str("klmnop".into()), Value::Str("qrstuv".into()), Value::Dict(fghij_map.clone()),
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
    let fghij_0 = dict.get("buz").and_then(|b| b.get("fghij")).and_then(|f| f.get(0));
    let fghij_1 = dict.get("buz").and_then(|b| b.get("fghij")).and_then(|f| f.get(1));
    let wxyz = dict.get("buz").and_then(|b| b.get("fghij")).and_then(|f| f.get(2))
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
        Value::Str("klmnop".into()), Value::Str("qrstuv".into()), Value::Dict(fghij_map.clone()),
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
        Value::Str("klmnop".into()), Value::Str("qrstuv".into()), Value::Dict(fghij_map.clone()),
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
    dict.select_mut(".buz.fghij[2]").unwrap().to_map_mut().unwrap().insert("foo".into(), Value::Int(1));
    dict.select_mut(".buz.fghij[2]").unwrap().to_map_mut().unwrap().insert("bar".into(), Value::Int(2));
    dict.select_mut(".buz.fghij[2]").unwrap().to_map_mut().unwrap().insert("baz".into(), Value::Int(3));

    assert_eq!(dict.select(".buz.fghij[0]").unwrap(), &Value::Int(0));
    assert_eq!(dict.select(".buz.fghij[1]").unwrap(), &Value::Str("qrstuv".into()));
    assert_eq!(dict.select(".buz.fghij[2].wxyz").unwrap(), &Value::Int(0));
    assert_eq!(dict.select(".buz.fghij[2].foo").unwrap(), &Value::Int(1));
    assert_eq!(dict.select(".buz.fghij[2].bar").unwrap(), &Value::Int(2));
    assert_eq!(dict.select(".buz.fghij[2].baz").unwrap(), &Value::Int(3));
}
