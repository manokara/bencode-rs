use super::Value;
use nanoserde::{DeJson, DeJsonErr, DeJsonState, DeJsonTok, SerJson, SerJsonState};
use std::{collections::BTreeMap, ops::Range, str::Chars};

const INT_RANGE: &'static str = "0..=9223372036854775807";
const STR_BOUNDS: Range<char> = 32 as char..128 as char;

impl DeJson for Value {
    fn de_json(state: &mut DeJsonState, input: &mut Chars) -> Result<Self, DeJsonErr> {
        if state.tok == DeJsonTok::CurlyOpen {
            let mut map = BTreeMap::new();
            state.next_tok(input)?;

            while state.tok != DeJsonTok::CurlyClose {
                let key = state.as_string()?;
                state.next_tok(input)?;
                state.colon(input)?;

                let val = DeJson::de_json(state, input)?;
                state.eat_comma_curly(input)?;
                map.insert(key, val);
            }

            state.curly_close(input)?;
            Ok(Value::Dict(map))
        } else if state.tok == DeJsonTok::BlockOpen {
            let mut vec = Vec::new();
            state.next_tok(input)?;

            while state.tok != DeJsonTok::BlockClose {
                let val = DeJson::de_json(state, input)?;
                vec.push(val);
                state.eat_comma_block(input)?;
            }

            state.block_close(input)?;
            Ok(Value::List(vec))
        } else if state.tok == DeJsonTok::Str {
            let val = state.as_string()?;
            state.next_tok(input)?;

            if val
                .chars()
                .all(|c| STR_BOUNDS.contains(&c) || c == '\r' || c == '\n')
            {
                Ok(Value::Str(val))
            } else {
                Ok(Value::Bytes(val.into_bytes()))
            }
        } else if let DeJsonTok::U64(i) = state.tok {
            if i <= i64::MAX as u64 {
                state.next_tok(input)?;
                Ok(Value::Int(i as i64))
            } else {
                Err(state.err_range(INT_RANGE))
            }
        } else if let DeJsonTok::I64(i) = state.tok {
            state.next_tok(input)?;
            Ok(Value::Int(i))
        } else {
            Err(state.err_token("anything else"))
        }
    }
}

impl SerJson for Value {
    fn ser_json(&self, indent: usize, state: &mut SerJsonState) {
        match self {
            Value::Dict(m) => {
                state.out.push('{');

                if m.len() > 0 {
                    let last = m.len() - 1;

                    for (index, (key, val)) in m.iter().enumerate() {
                        state.indent(indent + 1);

                        state.out.push('"');
                        state.out.push_str(key);
                        state.out.push('"');
                        state.out.push(':');
                        val.ser_json(indent + 1, state);

                        if index != last {
                            state.out.push(',');
                        }
                    }
                }

                state.out.push('}');
            }

            Value::List(v) => {
                state.out.push('[');

                if v.len() > 0 {
                    let last = v.len() - 1;

                    for (index, val) in v.iter().enumerate() {
                        state.indent(indent + 1);
                        val.ser_json(indent + 1, state);

                        if index != last {
                            state.out.push(',');
                        }
                    }
                }

                state.out.push(']');
            }

            Value::Bytes(v) => {
                let mut bytes = v.iter();

                // TODO: Maybe do something more efficient than this?
                while let Some(b) = bytes.next() {
                    let c = *b as char;

                    if STR_BOUNDS.contains(&c) {
                        state.out.push(c);
                    } else {
                        match c {
                            '\r' => state.out.push_str("\\r"),
                            '\n' => state.out.push_str("\\n"),
                            _ => state.out.extend(format!("\\\\u{{{}}}", c).chars()),
                        }
                    }
                }
            }

            Value::Str(s) => s.ser_json(indent, state),
            Value::Int(i) => i.ser_json(indent, state),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{DeJson, SerJson, Value};

    const DICT_VAL_INT: &'static str = "{\"bar\":1,\"baz\":2,\"foo\":0}";
    const LIST_VAL_STR: &'static str = "[\"foo\",\"bar\",\"baz\"]";
    const LIST_VAL_INT: &'static str = "[0,1,2]";
    const LIST_NESTED: &'static str = "[[0,1,2],[3,4,5],[6,7,8]]";
    const LIST_NEGATIVES: &'static str = "[-1,-2,-3]";
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

    #[test]
    fn deserialize() {
        let dict_val_int = val(maplit::btreemap! {
            "foo".into() => 0.into(),
            "bar".into() => 1.into(),
            "baz".into() => 2.into(),
        });
        let list_val_str = val(vec!["foo".into(), "bar".into(), "baz".into()] as Vec<Value>);
        let list_val_int = val(vec![0.into(), 1.into(), 2.into()] as Vec<Value>);
        let list_nested = val(vec![
            val(vec![0.into(), 1.into(), 2.into()] as Vec<Value>),
            val(vec![3.into(), 4.into(), 5.into()] as Vec<Value>),
            val(vec![6.into(), 7.into(), 8.into()] as Vec<Value>),
        ]);
        let list_negatives = val(vec![(-1).into(), (-2).into(), (-3).into()] as Vec<Value>);
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

        let val1 = Value::deserialize_json(DICT_VAL_INT).unwrap();
        let val2 = Value::deserialize_json(LIST_VAL_STR).unwrap();
        let val3 = Value::deserialize_json(LIST_VAL_INT).unwrap();
        let val4 = Value::deserialize_json(LIST_NESTED).unwrap();
        let val5 = Value::deserialize_json(LIST_NEGATIVES).unwrap();
        let val6 = Value::deserialize_json(DICT_MIXED).unwrap();

        assert_eq!(dict_val_int, val1);
        assert_eq!(list_val_str, val2);
        assert_eq!(list_val_int, val3);
        assert_eq!(list_nested, val4);
        assert_eq!(list_negatives, val5);
        assert_eq!(dict_mixed, val6);
    }

    #[test]
    fn serialize() {
        let dict_val_int = val(maplit::btreemap! {
            "foo".into() => 0.into(),
            "bar".into() => 1.into(),
            "baz".into() => 2.into(),
        });
        let list_val_str = val(vec!["foo".into(), "bar".into(), "baz".into()] as Vec<Value>);
        let list_val_int = val(vec![0.into(), 1.into(), 2.into()] as Vec<Value>);
        let list_nested = val(vec![
            val(vec![0.into(), 1.into(), 2.into()] as Vec<Value>),
            val(vec![3.into(), 4.into(), 5.into()] as Vec<Value>),
            val(vec![6.into(), 7.into(), 8.into()] as Vec<Value>),
        ]);
        let list_negatives = val(vec![(-1).into(), (-2).into(), (-3).into()] as Vec<Value>);
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

        let json1 = dict_val_int.serialize_json();
        let json2 = list_val_str.serialize_json();
        let json3 = list_val_int.serialize_json();
        let json4 = list_nested.serialize_json();
        let json5 = list_negatives.serialize_json();
        let json6 = dict_mixed.serialize_json();

        assert_eq!(json1, DICT_VAL_INT);
        assert_eq!(json2, LIST_VAL_STR);
        assert_eq!(json3, LIST_VAL_INT);
        assert_eq!(json4, LIST_NESTED);
        assert_eq!(json5, LIST_NEGATIVES);
        assert_eq!(json6, DICT_MIXED);
    }

    #[test]
    fn str_or_bytes() {
        let json1 = "\"hello world\"";
        let json2 = "\"/home/user/Downloads/foo.txt\"";
        let json3 = "\"\u{1}\u{2}\u{3}\"";
        let val1 = val("hello world");
        let val2 = val("/home/user/Downloads/foo.txt");
        let val3 = val(b"\x01\x02\x03" as &[u8]);

        assert_eq!(Value::deserialize_json(json1).unwrap(), val1);
        assert_eq!(Value::deserialize_json(json2).unwrap(), val2);
        assert_eq!(Value::deserialize_json(json3).unwrap(), val3);
    }
}
