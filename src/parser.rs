use super::Value;
use std::{
    cell::RefCell,
    collections::BTreeMap,
    convert::{TryFrom, TryInto},
    fmt,
    io::{Error as IoError, Read, Result as IOResult, Seek, SeekFrom},
    rc::Rc,
};

const MAX_INT_BUF: usize = 32;
const MAX_DEPTH: usize = 32;
const CHUNK_SIZE: u64 = 8096;

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

    /// Too many nested structures
    ///
    /// This can only happen if the stream has no size. See [`Stream`].
    ///
    /// [`Stream`]: enum.Stream.html
    RecursionLimit,
}

/// Wrapper for the input stream used in [`load`].
///
/// Sized streams are slices and any type that implements [`Read`] and [`Seek`]. In the latter, if
/// there are IO errors of any kind when seeking, the stream will be considered unsized.
///
/// Ideally, types that only implement [`Read`] would be converted automatically, but that would
/// require [specialization] which is very unstable. You must use Stream explicitly with the
/// [`new`] method.
///
/// [`load`]: fn.load.html
/// [`Read`]: https://doc.rust-lang.org/std/io/trait.Read.html
/// [`Seek`]: https://doc.rust-lang.org/std/io/trait.Seek.html
/// [specialization]: https://github.com/rust-lang/rfcs/blob/master/text/1210-impl-specialization.md
/// [`new`]: #method.new
pub enum Stream<'a> {
    Sized(Box<&'a mut dyn Read>, usize),
    Slice(&'a [u8], usize),
    Unsized(Box<&'a mut dyn Read>),
}

/// Parse a bencode data structure from a stream.
///
/// If you expect the stream to contain a certain type, see the [`load_dict`], [`load_list`] and
/// [`load_prim`] functions.
///
/// The parser will try to convert bytestrings to UTF-8 and return a [`Value::Str`] variant if the
/// conversion is succesful, otherwise the value will be [`Value::Bytes`].
///
/// # Stream
///
/// Depending on the input stream, the parser will behave differently. If the stream is sized (see
/// [`Stream`]) the parser will try to run until EOF, otherwise it will run as long as it does not
/// exceed the recursion limit (32 containers deep).
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
/// [`Stream`]: enum.Stream.html
/// [`ParserError`]: enum.ParserError.html
pub fn load<'a, S>(stream: S) -> Result<Value, ParserError>
where
    S: Into<Stream<'a>>,
{
    real_load(stream, State::Root, None)
}

/// Parse a bencode stream expecting a list as the root value.
///
/// If your application requires the root value to a be a dict and you want to avoid unnecessary
/// allocations, this function will check if the first token in the stream is 'd' and then actually
/// parse the stream.
///
/// # Errors
///
/// If the first character in the stream is not a 'd', we fail with `ParserError::UnexpectedRoot`.
/// Other parsing errors may be returned following the check.
pub fn load_dict<'a, S>(stream: S) -> Result<Value, ParserError>
where
    S: Into<Stream<'a>>,
{
    let mut buf = [0u8];
    let mut stream = stream.into();

    stream.read_exact(&mut buf)?;

    match buf[0].try_into() {
        Ok(Token::Dict) => real_load(stream, State::DictKey, None),

        _ => Err(ParserError::UnexpectedRoot),
    }
}

/// Parse a bencode stream expecting a list as the root value.
///
/// If your application requires the root value to a be a list and you want to avoid unnecessary
/// allocations, this function will check if the first token in the stream is 'l' and then actually
/// parse the stream.
///
/// # Errors
///
/// If the first character in the stream is not a 'l', we fail with `ParserError::UnexpectedRoot`.
/// Other parsing errors may be returned following the check.
pub fn load_list<'a, S>(stream: S) -> Result<Value, ParserError>
where
    S: Into<Stream<'a>>,
{
    let mut buf = [0u8];
    let mut stream = stream.into();

    stream.read_exact(&mut buf)?;

    match buf[0].try_into() {
        Ok(Token::List) => real_load(stream, State::ListVal, None),

        _ => Err(ParserError::UnexpectedRoot),
    }
}

/// Parse a bencode stream expecting a primitive as the root value.
///
/// If your application requires the root value to a be a primitive and you want to avoid
/// unnecessary allocations, this function will check if the first token in the stream is not one of
/// the container tokens ('d' or 'l') and then actually parse the stream.
///
/// # Errors
///
/// If the first character in the stream is a 'd' or 'l', we fail with
/// `ParserError::UnexpectedRoot`. Other parsing errors may be returned following the check.
pub fn load_prim<'a, S>(stream: S) -> Result<Value, ParserError>
where
    S: Into<Stream<'a>>,
{
    let mut buf = [0u8];
    let mut stream = stream.into();

    stream.read_exact(&mut buf)?;

    match buf[0].try_into() {
        Ok(Token::List) => Err(ParserError::UnexpectedRoot),
        Ok(Token::Dict) => Err(ParserError::UnexpectedRoot),
        Ok(Token::End) | Ok(Token::Colon) => Err(ParserError::Syntax(
            0,
            format!("Unexpected '{}' token", buf[0] as char),
        )),
        Ok(Token::Int) => real_load(stream, State::Int, None),
        Err(_) => real_load(stream, State::Str, Some(buf[0])),
    }
}

fn real_load<'a, S>(
    stream: S,
    initial_state: State,
    mut first_char: Option<u8>,
) -> Result<Value, ParserError>
where
    S: Into<Stream<'a>>,
{
    let stream = &mut stream.into();
    let file_size = stream.size();

    if let Some(&size) = file_size.as_ref() {
        if size == 0 {
            return Err(ParserError::Empty);
        }
    }

    let mut file_index = 0u64;
    let mut buf_index = 0usize;
    let mut state = initial_state;
    let mut next_state = Vec::new();
    let mut buf = Vec::<u8>::with_capacity(CHUNK_SIZE as usize);
    let mut buf_chars;
    let mut buf_str = Vec::new();
    let mut buf_str_remainder = 0u64;
    let mut buf_int = String::new();
    let mut key_stack = Vec::new();
    let mut val_stack = Vec::new();
    let mut item_stack = Vec::new();
    let mut dict_stack = Vec::new();
    let mut list_stack = Vec::new();
    let mut depth = 0;
    let root;

    stream.take(CHUNK_SIZE).read_to_end(&mut buf)?;
    buf_chars = buf.iter().peekable();

    // Initial state
    match state {
        State::Root => {
            let c = **buf_chars.peek().unwrap();

            match c.try_into() {
                // Dict value
                Ok(Token::Dict) => {
                    buf_chars.next();
                    buf_index += 1;
                    depth += 1;
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
                    depth += 1;
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
                Ok(a) => {
                    return Err(ParserError::Syntax(
                        0,
                        format!("Unexpected '{}' token", Into::<u8>::into(a) as char),
                    ))
                }
            }
        }

        // load_dict
        State::DictKey => {
            depth += 1;
            dict_stack.push(Rc::new(RefCell::new(BTreeMap::new())));
            key_stack.push(None);
            val_stack.push(None);

            next_state.push(State::RootValDict);
        }

        // load_list
        State::ListVal => {
            depth += 1;
            list_stack.push(Rc::new(RefCell::new(Vec::new())));
            item_stack.push(None);

            next_state.push(State::RootValList);
        }

        // load_prim
        State::Int => {
            next_state.push(State::RootValInt);
        }

        // load_prim
        State::Str => {
            next_state.push(State::RootValStr);
        }

        _ => unreachable!(),
    }

    loop {
        let real_index = file_index + buf_index as u64;

        if real_index >= (file_index + buf.len() as u64) {
            buf.clear();
            stream.take(CHUNK_SIZE).read_to_end(&mut buf)?;
            buf_chars = buf.iter().peekable();
            file_index += buf_index as u64;
            buf_index = 0;
        }

        match state {
            State::Root => unreachable!(),

            // Root states
            State::RootValInt | State::RootValStr | State::RootValDict | State::RootValList => {
                if state == State::RootValInt {
                    buf_index += 1;
                }

                break;
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
                        let key = String::from_utf8(buf_str.clone()).map_err(|_| {
                            ParserError::Syntax(
                                real_index as usize,
                                "Dict key must be a utf8 string".into(),
                            )
                        })?;
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
                        if depth < MAX_DEPTH || file_size.is_some() {
                            let map = Rc::new(RefCell::new(BTreeMap::new()));
                            depth += 1;

                            buf_chars.next();
                            buf_index += 1;
                            *val_stack.last_mut().unwrap() =
                                Some(LocalValue::DictRef(Rc::clone(&map)));
                            dict_stack.push(map);
                            key_stack.push(None);
                            val_stack.push(None);
                            state = State::DictKey;
                            next_state.push(State::DictValDict);
                        } else if file_size.is_none() && depth == MAX_DEPTH {
                            return Err(ParserError::RecursionLimit);
                        }
                    }

                    // List value
                    Ok(Token::List) => {
                        if depth < MAX_DEPTH || file_size.is_some() {
                            let vec = Rc::new(RefCell::new(Vec::new()));
                            depth += 1;

                            buf_chars.next();
                            buf_index += 1;
                            *val_stack.last_mut().unwrap() =
                                Some(LocalValue::ListRef(Rc::clone(&vec)));
                            list_stack.push(vec);
                            item_stack.push(None);
                            state = State::ListVal;
                            next_state.push(State::DictValList);
                        } else if file_size.is_none() && depth == MAX_DEPTH {
                            return Err(ParserError::RecursionLimit);
                        }
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
                    _ => {
                        return Err(ParserError::Syntax(
                            real_index as usize,
                            format!("Unexpected '{}' token", c),
                        ))
                    }
                }
            }

            // Process current dict value as str
            State::DictValStr => {
                *val_stack.last_mut().unwrap() =
                    Some(LocalValue::Owned(str_or_bytes(buf_str.clone())));
                buf_str.clear();
                state = State::DictFlush;
            }

            // Process current dict value as int
            State::DictValInt => {
                // Unwrap here because Int state already checks for EOF
                let c = *buf_chars.next().unwrap();

                if c != Token::End.into() {
                    return Err(ParserError::Syntax(
                        real_index as usize,
                        "Expected 'e' token".into(),
                    ));
                }

                let val = buf_int.parse::<i64>().map_err(|_| {
                    ParserError::Syntax(real_index as usize, "Invalid integer".into())
                })?;
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
                depth -= 1;
                state = State::DictFlush;
            }

            // Process current dict value as list
            State::DictValList => {
                let list = list_stack.pop().unwrap();

                *val_stack.last_mut().unwrap() = Some(LocalValue::ListRef(list));
                item_stack.pop().unwrap();
                depth -= 1;
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
                        if depth < MAX_DEPTH || file_size.is_some() {
                            let d = Rc::new(RefCell::new(BTreeMap::new()));
                            depth += 1;

                            *item_stack.last_mut().unwrap() =
                                Some(LocalValue::DictRef(Rc::clone(&d)));
                            buf_chars.next();
                            dict_stack.push(d);
                            key_stack.push(None);
                            val_stack.push(None);
                            buf_index += 1;

                            state = State::DictKey;
                            next_state.push(State::ListValDict);
                        } else if file_size.is_none() && depth == MAX_DEPTH {
                            return Err(ParserError::RecursionLimit);
                        }
                    }

                    // List value
                    Ok(Token::List) => {
                        if depth < MAX_DEPTH || file_size.is_some() {
                            let l = Rc::new(RefCell::new(Vec::new()));
                            depth += 1;

                            *item_stack.last_mut().unwrap() =
                                Some(LocalValue::ListRef(Rc::clone(&l)));
                            buf_chars.next();
                            list_stack.push(l);
                            item_stack.push(None);
                            buf_index += 1;

                            next_state.push(State::ListValList);
                        } else if file_size.is_none() && depth == MAX_DEPTH {
                            return Err(ParserError::RecursionLimit);
                        }
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
                    _ => {
                        return Err(ParserError::Syntax(
                            real_index as usize,
                            "Unexpected ':' token".into(),
                        ))
                    }
                }
            }

            // Process current list value as str
            State::ListValStr => {
                *item_stack.last_mut().unwrap() =
                    Some(LocalValue::Owned(str_or_bytes(buf_str.clone())));
                buf_str.clear();
                state = State::ListFlush;
            }

            // Process current list value as int
            State::ListValInt => {
                // Unwrap here because Int state already checks for EOF
                let c = *buf_chars.next().unwrap();

                if c != Token::End.into() {
                    return Err(ParserError::Syntax(
                        real_index as usize,
                        "Expected 'e' token".into(),
                    ));
                }

                let val = buf_int.parse::<i64>().map_err(|_| {
                    ParserError::Syntax(real_index as usize, "Invalid integer".into())
                })?;

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
                        return Err(ParserError::Syntax(
                            real_index as usize,
                            "Expected ':'".into(),
                        ));
                    }

                    let buf_str_size = buf_int.parse::<u64>().map_err(|_| {
                        ParserError::Syntax(real_index as usize, "Invalid integer".into())
                    })?;
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

                let (advance, c) = if let Some(b) = first_char.take() {
                    (false, b as char)
                } else {
                    (true, **buf_chars.peek().ok_or(ParserError::Eof)? as char)
                };

                if CHARS.contains(&c) {
                    // Only allow minus at the beginning
                    if c == '-' && buf_int.len() > 0 {
                        return Err(ParserError::Syntax(
                            real_index as usize,
                            "Unexpected '-'".into(),
                        ));
                    }

                    buf_int.push(c);

                    // Only advance iterator if c didn't come from first_char
                    if advance {
                        buf_chars.next();
                        buf_index += 1;
                    }
                } else {
                    if buf_int.len() == 0 {
                        return Err(ParserError::Syntax(
                            real_index as usize,
                            "Empty integer".into(),
                        ));
                    }

                    if buf_int.len() > MAX_INT_BUF {
                        return Err(ParserError::Syntax(
                            real_index as usize,
                            "Integer string too big".into(),
                        ));
                    }

                    state = next_state.pop().unwrap();
                }
            }
        }

        if let Some(&size) = file_size.as_ref() {
            if file_index + buf_index as u64 == size as u64 {
                break;
            }
        }
    }

    let final_index = file_index as usize + buf_index;

    if next_state.len() > 0 {
        return Err(ParserError::Eof);
    }

    match state {
        State::RootValInt => {
            // Unwrap here because Int state already checks for EOF
            let c = *buf_chars.next().unwrap();

            if c != Token::End.into() {
                return Err(ParserError::Syntax(
                    final_index - 1,
                    "Expected 'e' token".into(),
                ));
            }

            let val = buf_int.parse::<i64>().map_err(|_| {
                ParserError::Syntax(file_index as usize + buf_index, "Invalid integer".into())
            })?;
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

impl<'a> Stream<'a> {
    /// Creates a new stream from a [`Read`]able type.
    ///
    /// [`Read`]: https://doc.rust-lang.org/std/io/trait.Read.html
    pub fn new<T>(t: &'a mut T) -> Self
    where
        T: Read,
    {
        Self::Unsized(Box::new(t))
    }

    /// Returns the size of this stream, if possible.
    pub fn size(&self) -> Option<usize> {
        match self {
            Self::Sized(_, size) => Some(*size),
            Self::Slice(_, size) => Some(*size),
            Self::Unsized(_) => None,
        }
    }
}

impl<'a, T> From<&'a mut T> for Stream<'a>
where
    T: Read + Seek,
{
    fn from(t: &'a mut T) -> Self {
        let result1 = t.seek(SeekFrom::End(0));
        let result2 = t.seek(SeekFrom::Start(0));
        let result = result1.or(result2);

        match result {
            Ok(size) => Self::Sized(Box::new(t), size as usize),
            Err(_) => Self::Unsized(Box::new(t)),
        }
    }
}

impl<'a, T> From<&'a T> for Stream<'a>
where
    T: AsRef<[u8]>,
{
    fn from(t: &'a T) -> Self {
        let slice = t.as_ref();
        Self::Slice(slice, slice.len())
    }
}

impl<'a> From<&'a [u8]> for Stream<'a> {
    fn from(s: &'a [u8]) -> Self {
        let slice = s.as_ref();
        Self::Slice(slice, slice.len())
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

    fn try_from(c: u8) -> Result<Token, Self::Error> {
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
            ParserError::RecursionLimit => write!(f, "Too many nested structures"),
        }
    }
}

impl<'a> fmt::Debug for Stream<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Stream::Sized(_, size) => write!(f, "Sized({})", size),
            Stream::Slice(_, size) => write!(f, "Slice({})", size),
            Stream::Unsized(_) => write!(f, "Unsized"),
        }
    }
}

impl<'a> Read for Stream<'a> {
    fn read(&mut self, buf: &mut [u8]) -> IOResult<usize> {
        match self {
            Self::Sized(stream, _) => stream.read(buf),
            Self::Slice(slice, _) => slice.read(buf),
            Self::Unsized(stream) => stream.read(buf),
        }
    }
}
