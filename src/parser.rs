use std::{
    cell::RefCell,
    collections::BTreeMap,
    convert::{TryFrom, TryInto},
    fmt,
    io::{Cursor, Error as IoError, Read, Seek, SeekFrom},
    rc::Rc,
};
use super::Value;

const MAX_INT_BUF: usize = 32;
const CHUNK_SIZE: u64 = 2048;

enum Token {
    Dict,
    Int,
    List,
    End,
    Colon,
}

#[derive(Debug, PartialEq)]
enum State {
    Root,
    Dict,
    Int,
    Str,
    DictKey,
    DictVal,
    StrRem,
    DictFlush,
    DictValStr,
    DictValInt,
    DictValDict,
    DictValList,
    ListVal,
    ListValStr,
    ListValInt,
    ListValDict,
    ListValList,
    ListFlush,
    RootValInt,
    RootValStr,
    RootValDict,
    RootValList,
    Done,
}

enum LocalValue {
    DictRef(Rc<RefCell<BTreeMap<String, Value>>>),
    ListRef(Rc<RefCell<Vec<Value>>>),
    Owned(Value),
}

/// An error from the [`load`] function.
///
/// [`load`]: fn.load.html
#[derive(Debug)]
pub enum ParserError {
    /// `(inner_error)`
    ///
    /// An IO error has occured.
    Io(IoError),

    /// Stream was empty.
    Empty,

    /// `(position, reason)`
    ///
    /// There was a syntax error in the stream.
    Syntax(usize, String),

    /// Reached end of stream while trying to parse something.
    ///
    /// This can be caused by a missing 'e' token, or the stream simply cuts in the middle of the
    /// structure.
    Eof,

    /// The root value was not the one expected.
    ///
    /// This is only returned by the [`load_dict`] and [`load_list`] functions. Note that when using
    /// these functions, this variant will used if there's anything other than "start structure"
    /// token.
    ///
    /// [`load_dict`]: fn.load_dict.html
    /// [`load_list`]: fn.load_list.html
    UnexpectedRoot,
}


/// Parse a bencode data structure from a stream.
///
/// If you expect the stream to contain a certain type, see the [`load_dict`], [`load_list`] and
/// [`load_prim`] functions.
///
/// The parser will try to convert bytestrings to UTF-8 and return a [`Value::Str`] variant if the
/// conversion is succesful, otherwise the value will be [`Value::Bytes`].
///
/// If you're dealing with byte slices, you can use the [`load_str`] function.
///
/// # Errors
///
/// There are many ways this function can fail. It will fail if the stream is empty, if there are
/// syntax errors or an integer string is way too big. See [`ParserError`].
///
/// [`load_dict`]: fn.load_dict.html
/// [`load_list`]: fn.load_list.html
/// [`load_prim`]: fn.load_prim.html
/// [`Value::Str`]: enum.Value.html#variant.Str
/// [`Value::Bytes`]: enum.Value.html#variant.Bytes
/// [`load_str`]: fn.load_str.html
/// [`ParserError`]: enum.ParserError.html
pub fn load(stream: &mut (impl Read + Seek)) -> Result<Value, ParserError> {
    let file_size = stream.seek(SeekFrom::End(0))?;
    stream.seek(SeekFrom::Start(0))?;

    if file_size == 0 {
        return Err(ParserError::Empty);
    }

    let mut file_index = 0u64;
    let mut buf_index = 0usize;
    let mut state = State::Root;
    let mut next_state = Vec::new();
    let mut buf = Vec::new();
    let mut buf_chars = buf.iter().peekable();
    let mut buf_str = Vec::new();
    let mut buf_str_remainder = 0u64;
    let mut buf_int = String::new();
    let mut key_stack = Vec::new();
    let mut val_stack = Vec::new();
    let mut item_stack = Vec::new();
    let mut dict_stack = Vec::new();
    let mut list_stack = Vec::new();
    let root;

    while file_index + (buf_index as u64) < file_size {
        let real_index = file_index + buf_index as u64;

        if real_index >= (file_index + buf.len() as u64) && real_index < file_size {
            buf.clear();
            stream.take(CHUNK_SIZE).read_to_end(&mut buf)?;
            buf_chars = buf.iter().peekable();
            file_index += buf_index as u64;
            buf_index = 0;
        }

        match state {
            State::Root => {
                let c = **buf_chars.peek().unwrap();

                match c.try_into() {
                    // Dict value
                    Ok(Token::Dict) => {
                        buf_chars.next();
                        buf_index += 1;
                        dict_stack.push(Rc::new(RefCell::new(BTreeMap::new())));
                        key_stack.push(None);
                        val_stack.push(None);

                        state = State::DictKey;
                        next_state.push(State::RootValDict);
                    }

                    // List value
                    Ok(Token::List) => {
                        buf_chars.next();
                        buf_index += 1;
                        list_stack.push(Rc::new(RefCell::new(Vec::new())));
                        item_stack.push(None);

                        state = State::ListVal;
                        next_state.push(State::RootValList);
                    }

                    // Int value
                    Ok(Token::Int) => {
                        state = State::Int;
                        buf_chars.next();
                        buf_index += 1;
                        next_state.push(State::RootValInt);
                    }


                    // Str value
                    Err(_) => {
                        state = State::Str;
                        next_state.push(State::RootValStr);
                    }

                    // End, Colon
                    Ok(a) => return Err(
                        ParserError::Syntax(real_index as usize,
                                      format!("Unexpected '{}' token", Into::<u8>::into(a) as char))
                    ),
                }
            }

            // Root int value
            // Just increase buf_index here so the loop can be broken
            State::RootValInt => {
                buf_index += 1;
            }

            // Read dict key or end the dict if it's empty
            State::DictKey => {
                let c = **buf_chars.peek().unwrap();

                if c == Token::End.into() {
                    buf_chars.next();
                    buf_index += 1;
                    state = next_state.pop().unwrap();
                } else {
                    if buf_str.len() == 0 {
                        state = State::Str;
                        next_state.push(State::DictKey);
                    } else {
                        let key = String::from_utf8(buf_str.clone())
                            .map_err(|_| ParserError::Syntax(real_index as usize, "Dict key must be a utf8 string".into()))?;
                        *key_stack.last_mut().unwrap() = Some(key);
                        buf_str.clear();
                        state = State::DictVal;
                    }
                }
            }

            // Read dict value
            State::DictVal => {
                let c = **buf_chars.peek().ok_or(ParserError::Eof)?;

                match c.try_into() {
                    // Dict value
                    Ok(Token::Dict) => {
                        let map = Rc::new(RefCell::new(BTreeMap::new()));

                        buf_chars.next();
                        buf_index += 1;
                        *val_stack.last_mut().unwrap() = Some(LocalValue::DictRef(Rc::clone(&map)));
                        dict_stack.push(map);
                        key_stack.push(None);
                        val_stack.push(None);

                        state = State::DictKey;
                        next_state.push(State::DictValDict);
                    }

                    // List value
                    Ok(Token::List) => {
                        let vec = Rc::new(RefCell::new(Vec::new()));

                        buf_chars.next();
                        buf_index += 1;
                        *val_stack.last_mut().unwrap() = Some(LocalValue::ListRef(Rc::clone(&vec)));
                        list_stack.push(vec);
                        item_stack.push(None);

                        state = State::ListVal;
                        next_state.push(State::DictValList);
                    }

                    // Int value
                    Ok(Token::Int) => {
                        buf_chars.next();
                        buf_index += 1;
                        state = State::Int;
                        next_state.push(State::DictValInt);
                    }

                    // String value
                    Err(_) => {
                        state = State::Str;
                        next_state.push(State::DictValStr);
                    }

                    // Colon, End
                    _ => return Err(ParserError::Syntax(real_index as usize, format!("Unexpected '{}' token", c))),
                }
            }

            // Process current dict value as str
            State::DictValStr => {
                *val_stack.last_mut().unwrap() = Some(LocalValue::Owned(str_or_bytes(buf_str.clone())));
                buf_str.clear();
                state = State::DictFlush;
            }

            // Process current dict value as int
            State::DictValInt => {
                // Unwrap here because Int state already checks for EOF
                let c = *buf_chars.next().unwrap();

                if c != Token::End.into() {
                    return Err(ParserError::Syntax(real_index as usize, "Expected 'e' token".into()));
                }

                let val = buf_int.parse::<i64>().map_err(|_| ParserError::Syntax(real_index as usize, "Invalid integer".into()))?;
                *val_stack.last_mut().unwrap() = Some(LocalValue::Owned(Value::Int(val)));
                buf_int.clear();
                buf_index += 1;

                state = State::DictFlush;
            }

            // Process current dict value as dict
            State::DictValDict => {
                let dict = dict_stack.pop().unwrap();

                *val_stack.last_mut().unwrap() = Some(LocalValue::DictRef(dict));
                key_stack.pop().unwrap();
                val_stack.pop().unwrap();
                state = State::DictFlush;
            }

            // Process current dict value as list
            State::DictValList => {
                let list = list_stack.pop().unwrap();

                *val_stack.last_mut().unwrap() = Some(LocalValue::ListRef(list));
                item_stack.pop().unwrap();
                state = State::DictFlush;
            }

            // Insert current (key, value) pair into current dict
            State::DictFlush => {
                let key = key_stack.last().unwrap().clone().unwrap();
                let val = val_stack.last().unwrap().as_ref().unwrap().to_owned();
                dict_stack.last_mut().unwrap().borrow_mut().insert(key, val);

                let c = **buf_chars.peek().ok_or(ParserError::Eof)?;

                if c == Token::End.into() {
                    buf_chars.next();
                    buf_index += 1;
                    state = next_state.pop().unwrap();
                } else {
                    state = State::DictKey;
                }
            }

            // List value
            State::ListVal => {
                let c = **buf_chars.peek().ok_or(ParserError::Eof)?;

                match c.try_into() {
                    // End of list
                    Ok(Token::End) => {
                        buf_chars.next();
                        buf_index += 1;
                        state = next_state.pop().unwrap();
                    }

                    // Dict value
                    Ok(Token::Dict) => {
                        let d = Rc::new(RefCell::new(BTreeMap::new()));

                        *item_stack.last_mut().unwrap() = Some(LocalValue::DictRef(Rc::clone(&d)));
                        buf_chars.next();
                        dict_stack.push(d);
                        key_stack.push(None);
                        val_stack.push(None);
                        buf_index += 1;

                        state = State::DictKey;
                        next_state.push(State::ListValDict);
                    }

                    // List value
                    Ok(Token::List) => {
                        let l = Rc::new(RefCell::new(Vec::new()));

                        *item_stack.last_mut().unwrap() = Some(LocalValue::ListRef(Rc::clone(&l)));
                        buf_chars.next();
                        list_stack.push(l);
                        item_stack.push(None);
                        buf_index += 1;

                        next_state.push(State::ListValList);
                    }

                    // Int value
                    Ok(Token::Int) => {
                        buf_chars.next();
                        buf_index += 1;
                        state = State::Int;
                        next_state.push(State::ListValInt);
                    }

                    // String value
                    Err(_) => {
                        state = State::Str;
                        next_state.push(State::ListValStr);
                    }

                    // Colon
                    _ => return Err(ParserError::Syntax(real_index as usize, "Unexpected ':' token".into())),
                }
            }

            // Process current list value as str
            State::ListValStr => {
                *item_stack.last_mut().unwrap() = Some(LocalValue::Owned(str_or_bytes(buf_str.clone())));
                buf_str.clear();
                state = State::ListFlush;
            }

            // Process current list value as int
            State::ListValInt => {
                // Unwrap here because Int state already checks for EOF
                let c = *buf_chars.next().unwrap();

                if c != Token::End.into() {
                    return Err(ParserError::Syntax(real_index as usize, "Expected 'e' token".into()));
                }

                let val = buf_int.parse::<i64>().map_err(|_| ParserError::Syntax(real_index as usize, "Invalid integer".into()))?;

                *item_stack.last_mut().unwrap() = Some(LocalValue::Owned(Value::Int(val)));
                buf_int.clear();
                buf_index += 1;
                state = State::ListFlush;
            }

            // Process current list value as dict
            State::ListValDict => {
                let dict = dict_stack.pop().unwrap().borrow().clone();

                *item_stack.last_mut().unwrap() = Some(LocalValue::Owned(Value::Dict(dict)));
                key_stack.pop();
                val_stack.pop();

                state = State::ListFlush;
            }

            // Process current list value as list
            State::ListValList => {
                let list = list_stack.pop().unwrap().borrow().clone();

                *item_stack.last_mut().unwrap() = Some(LocalValue::Owned(Value::List(list)));
                item_stack.pop();

                state = State::ListFlush;
            }

            // Add current list value to the current list
            State::ListFlush => {
                let val = item_stack.last().unwrap().as_ref().unwrap().to_owned();
                list_stack.last_mut().unwrap().borrow_mut().push(val);

                let c = **buf_chars.peek().unwrap();

                if c == Token::End.into() {
                    buf_chars.next();
                    buf_index += 1;
                    state = next_state.pop().unwrap();
                } else {
                    state = State::ListVal;
                }
            }

            // Process string
            State::Str => {
                if buf_int.len() == 0 {
                    buf_str.clear();
                    buf_str_remainder = 0;
                    state = State::Int;
                    next_state.push(State::Str);
                } else {
                    let c = *buf_chars.next().ok_or(ParserError::Eof)?;

                    if c != Token::Colon.into() {
                        return Err(ParserError::Syntax(real_index as usize, "Expected ':'".into()));
                    }

                    let buf_str_size = buf_int.parse::<u64>().map_err(|_| ParserError::Syntax(real_index as usize, "Invalid integer".into()))?;
                    buf_int.clear();
                    buf_index += 1;

                    // String is bigger than buffer
                    if buf_index + buf_str_size as usize > buf.len() {
                        let chunk_size = buf.len() - buf_index;
                        buf_str_remainder = buf_str_size - chunk_size as u64;
                        buf_str.extend(buf_chars.by_ref());
                        buf_index += chunk_size;
                        state = State::StrRem;
                    } else {
                        buf_str.extend(buf_chars.by_ref().take(buf_str_size as usize));
                        buf_index += buf_str_size as usize;
                        state = next_state.pop().unwrap();
                    }
                }
            }

            // Process string remainder
            State::StrRem => {
                if buf_str_remainder > 0 && buf_index + buf_str_remainder as usize > buf.len() {
                    let chunk_size = buf.len() - buf_index;
                    buf_str_remainder -= chunk_size as u64;
                    buf_str.extend(buf_chars.by_ref());
                    buf_index += chunk_size;
                } else {
                    buf_str.extend(buf_chars.by_ref().take(buf_str_remainder as usize));
                    buf_index += buf_str_remainder as usize;
                    buf_str_remainder = 0;
                    state = next_state.pop().unwrap();
                }
            }

            // Int
            State::Int => {
                const CHARS: &[char] = &['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '-'];

                let c = **buf_chars.peek().ok_or(ParserError::Eof)? as char;

                if CHARS.contains(&c) {
                    // Only allow minus at the beginning
                    if c == '-' && buf_int.len() > 0 {
                        return Err(ParserError::Syntax(real_index as usize, "Unexpected '-'".into()));
                    }

                    buf_int.push(c);
                    buf_chars.next();
                    buf_index += 1;
                } else {
                    if buf_int.len() == 0 {
                        return Err(ParserError::Syntax(real_index as usize, "Empty integer".into()));
                    }

                    if buf_int.len() > MAX_INT_BUF {
                        return Err(ParserError::Syntax(real_index as usize, "Integer string too big".into()));
                    }

                    state = next_state.pop().unwrap();
                }
            }

            _ => unreachable!(),
        }
    }

    if next_state.len() > 0 {
        return Err(ParserError::Eof);
    }

    match state {
        State::RootValInt => {
            // Unwrap here because Int state already checks for EOF
            let c = *buf_chars.next().unwrap();

            if c != Token::End.into() {
                return Err(ParserError::Syntax(file_size as usize - 1, "Expected 'e' token".into()));
            }

            let val = buf_int.parse::<i64>()
                .map_err(|_| ParserError::Syntax(file_index as usize + buf_index,
                                           "Invalid integer".into()))?;
            root = Some(Value::Int(val));
        }

        State::RootValStr => root = Some(str_or_bytes(buf_str)),

        State::RootValDict => {
            let dict = dict_stack.pop().unwrap().borrow().clone();

            root = Some(Value::Dict(dict));
        }

        State::RootValList => {
            let list = list_stack.pop().unwrap().borrow().clone();

            root = Some(Value::List(list));
        }

        _ => unreachable!(),
    }

    Ok(root.unwrap())
}

/// Parse a bencode data structure from a string.
///
/// This is a helper function that wraps the slice in a Cursor and calls [`load`].
///
/// [`load`]: fn.load.html
pub fn load_str(s: &[u8]) -> Result<Value, ParserError> {
    let mut cursor = Cursor::new(s);
    load(&mut cursor)
}

/// Parse a bencode stream expecting a dict as the root value.
///
/// If your application requires the root value to a be a dict and you want to avoid unnecessary
/// allocations, this function will check if the first token in the stream is 'd' and then actually
/// parse the stream.
///
/// If you're dealing with byte slices, you can use the [`load_dict_str`] function.
///
/// # Errors
///
/// If the first character in the stream is not a 'd', we fail with `ParserError::UnexpectedRoot`.
/// Other parsing errors may be returned following the check.
///
/// [`load_dict_str`]: fn.load_dict_str.html
pub fn load_dict(stream: &mut (impl Read + Seek)) -> Result<Value, ParserError> {
    let mut buf = [0u8];

    stream.read_exact(&mut buf)?;

    match buf[0].try_into() {
        Ok(Token::Dict) => {
            stream.seek(SeekFrom::Start(0))?;
            load(stream)
        }

        _ => Err(ParserError::UnexpectedRoot)
    }
}

/// Parse a bencode string expecting a dict as the root value.
///
/// This is a helper function that wraps the slice in a Cursor and calls [`load_dict`].
///
/// [`load_dict`]: fn.load_dict.html
pub fn load_dict_str(s: &[u8]) -> Result<Value, ParserError> {
    let mut cursor = Cursor::new(s);
    load_dict(&mut cursor)
}

/// Parse a bencode stream expecting a list as the root value.
///
/// If your application requires the root value to a be a list and you want to avoid unnecessary
/// allocations, this function will check if the first token in the stream is 'l' and then actually
/// parse the stream.
///
/// If you're dealing with byte slices, you can use the [`load_list_str`] function.
///
/// # Errors
///
/// If the first character in the stream is not a 'l', we fail with `ParserError::UnexpectedRoot`.
/// Other parsing errors may be returned following the check.
///
/// [`load_list_str`]: fn.load_list_str.html
pub fn load_list(stream: &mut (impl Read + Seek)) -> Result<Value, ParserError> {
    let mut buf = [0u8];

    stream.read_exact(&mut buf)?;

    match buf[0].try_into() {
        Ok(Token::List) => {
            stream.seek(SeekFrom::Start(0))?;
            load(stream)
        }

        _ => Err(ParserError::UnexpectedRoot)
    }
}

/// Parse a bencode string expecting a list as the root value.
///
/// This is a helper function that wraps the slice in a Cursor and calls [`load_list`].
///
/// [`load_dict`]: fn.load_dict.html
pub fn load_list_str(s: &[u8]) -> Result<Value, ParserError> {
    let mut cursor = Cursor::new(s);
    load_list(&mut cursor)
}

/// Parse a bencode stream expecting a primitive as the root value.
///
/// If your application requires the root value to a be a primitive and you want to avoid
/// unnecessary allocations, this function will check if the first token in the stream is not one of
/// the container tokens ('d' or 'e') and then actually parse the stream.
///
/// If you're dealing with byte slices, you can use the [`load_prim_str`] function.
///
/// # Errors
///
/// If the first character in the stream is a 'd' or 'l', we fail with
/// `ParserError::UnexpectedRoot`. Other parsing errors may be returned following the check.
///
/// [`load_prim_str`]: fn.load_prim_str.html
pub fn load_prim(stream: &mut (impl Read + Seek)) -> Result<Value, ParserError> {
    let mut buf = [0u8];

    stream.read_exact(&mut buf)?;

    match buf[0].try_into() {
        Ok(Token::List) => Err(ParserError::UnexpectedRoot),
        Ok(Token::Dict) => Err(ParserError::UnexpectedRoot),
        _ => {
            stream.seek(SeekFrom::Start(0))?;
            load(stream)
        }
    }
}

/// Parse a bencode string expecting a primitive as the root value.
///
/// This is a helper function that wraps the slice in a Cursor and calls [`load_prim`].
///
/// [`load_prim`]: fn.load_prim.html
pub fn load_prim_str(s: &[u8]) -> Result<Value, ParserError> {
    let mut cursor = Cursor::new(s);
    load_prim(&mut cursor)
}

/// Try to convert a raw buffer to utf8 and return the appropriate Value.
fn str_or_bytes(vec: Vec<u8>) -> Value {
    match String::from_utf8(vec) {
        Ok(s) => Value::Str(s),
        Err(e) => Value::Bytes(e.into_bytes()),
    }
}

impl LocalValue {
    fn to_owned(&self) -> Value {
        match self {
            Self::DictRef(r) => Value::Dict(r.borrow().clone()),
            Self::ListRef(r) => Value::List(r.borrow().clone()),
            Self::Owned(v) => v.clone(),
        }
    }
}

impl From<IoError> for ParserError {
    fn from(e: IoError) -> Self {
        Self::Io(e)
    }
}

impl Into<u8> for Token {
    fn into(self) -> u8 {
        match self {
            Self::Dict => 'd' as u8,
            Self::Int => 'i' as u8,
            Self::List => 'l' as u8,
            Self::Colon => ':' as u8,
            Self::End => 'e' as u8,
        }
    }
}

impl TryFrom<u8> for Token {
    type Error = ();

    fn try_from(c: u8) ->  Result<Token, Self::Error> {
        const D: u8 = 'd' as u8;
        const I: u8 = 'i' as u8;
        const L: u8 = 'l' as u8;
        const C: u8 = ':' as u8;
        const E: u8 = 'e' as u8;

        match c {
            D => Ok(Token::Dict),
            I => Ok(Token::Int),
            L => Ok(Token::List),
            C => Ok(Token::Colon),
            E => Ok(Token::End),
            _ => Err(()),
        }
    }
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParserError::Io(e) => write!(f, "IO Error: {}", e),
            ParserError::Empty => write!(f, "Empty file"),
            ParserError::Syntax(n, s) => write!(f, "Syntax error at {}: {}", n + 1, s),
            ParserError::Eof => write!(f, "Unexpected end of file reached"),
            ParserError::UnexpectedRoot => write!(f, "Unexpected root value"),
        }
    }
}
