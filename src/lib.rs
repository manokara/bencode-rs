const MAX_INT_BUF: usize = 32;
const CHUNK_SIZE: u64 = 2048;

use std::{
    cell::RefCell,
    collections::BTreeMap,
    convert::{TryFrom, TryInto},
    fmt,
    io::{Cursor, Error as IoError, Read, Seek, SeekFrom},
    rc::Rc,
};

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

#[derive(Debug, PartialEq)]
enum TraverseState {
    Root,
    Dict,
    List,
    Done,
}

/// Describes an action to be taken when traversing a Value container.
///
/// See [`Value::traverse`](enum.Value.html#method.traverse).
#[derive(Debug)]
pub enum TraverseAction {
    /// Enter the current value if it is a container.
    Enter,
    /// Goes back to the parent container of the current Value.
    Exit,
    /// Keep going through items in the container.
    Continue,
    /// Stop traversing and return the current value.
    Stop,
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
}

/// An error from the [`Value::traverse`] method.
///
/// [`Value::traverse`]: enum.Value.html#method.traverse
#[derive(Debug)]
pub enum TraverseError<E = ()> {
    /// `(context)`
    ///
    /// Tried to enter a value in the current context that was not a container.
    NotContainer(String),

    /// Tried to go back to the parent container, but we were at the root.
    AtRoot,

    /// `(context)`
    ///
    /// Reached the end of the current container.
    End(String),

    /// `(context, error)`
    ///
    /// An error occurred processing a value and the traversal was aborted.
    Aborted(String, E),
}

/// An error from the [`Value::select`] method.
///
/// [`Value::select`]: enum.Value.html#method.select
#[derive(Debug)]
pub enum SelectError {
    /// `(context, key)`
    ///
    /// Key does not exist in this context.
    Key(String, String),

    /// `(context, index)`
    ///
    /// Index is out of bounds for this context.
    Index(String, usize),

    /// `(context)`
    ///
    /// Context does not take keys.
    Subscriptable(String),

    /// `(context)`
    ///
    /// Context does not take indexes.
    Indexable(String),

    /// `(context)`
    ///
    /// Context is not a container and can't be selected into.
    Primitive(String),

    /// `(context, pos, reason)`
    ///
    /// Error processing selector syntax.
    Syntax(String, usize, String),

    /// Reached end of selector while trying to parse it. e.g. didn't close a bracket.
    End,
}

/// A bencode value
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Value {
    /// Integer
    Int(i64),
    /// UTF-8 string
    Str(String),
    /// Raw bytestring
    Bytes(Vec<u8>),
    /// Dictionary
    Dict(BTreeMap<String, Value>),
    /// List
    List(Vec<Value>),
}

/// A helper struct for recursively displaying [`Value`]s.
///
/// [`Value`]: enum.Value.html
pub struct ValueDisplay<'a> {
    root: &'a Value,
    max_depth: usize,
    max_list_items: usize,
    max_root_bytes: usize,
    max_bytes: usize,
    indent_size: usize,
}

/// Parse a bencode data structure from a stream.
///
/// The parser will try to convert bytestrings to UTF-8 and return a [`Value::Str`] variant if the
/// conversion is succesful, otherwise the value will be [`Value::Bytes`].
///
/// # Errors
///
/// There are many ways this function can fail. It will fail if the stream is empty, if there are
/// syntax errors or an integer string is way too big. See [`ParserError`].
///
/// [`Value::Str`]: enum.Value.html#variant.Str
/// [`Value::Bytes`]: enum.Value.html#variant.Bytes
/// [`ParserError`]: enum.ParserError.html
pub fn load(stream: &mut (impl Read + Seek)) -> Result<Value, ParserError> {
    enum LocalValue {
        DictRef(Rc<RefCell<BTreeMap<String, Value>>>),
        ListRef(Rc<RefCell<Vec<Value>>>),
        Owned(Value),
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
/// This is a helper function that wraps the str in a Cursor and calls [`load`].
///
/// [`load`]: fn.load.html
pub fn load_str(s: &str) -> Result<Value, ParserError> {
    let mut cursor = Cursor::new(s);
    load(&mut cursor)
}

/// Try to convert a raw buffer to utf8 and return the appropriate Value.
fn str_or_bytes(vec: Vec<u8>) -> Value {
    match String::from_utf8(vec) {
        Ok(s) => Value::Str(s),
        Err(e) => Value::Bytes(e.into_bytes()),
    }
}

fn repr_bytes(bytes: &[u8], truncate_at: usize) -> String {
    let mut buf = String::from("b\"");

    for b in bytes.iter().take(truncate_at) {
        if (32..128).contains(b) {
            buf.push(*b as char);
        } else {
            buf.extend(format!("\\x{:02X}", b).chars());
        }
    }

    buf.push('"');

    if bytes.len() > truncate_at {
        buf.extend(format!("... {} more bytes", bytes.len() - truncate_at).chars());
    }

    buf
}

impl Value {
    /// Is the current value an int?
    pub fn is_int(&self) -> bool {
        matches!(self, Value::Int(_))
    }

    /// Is the current value a string?
    pub fn is_str(&self) -> bool {
        matches!(self, Value::Str(_))
    }

    /// Is the current value a byte sequence?
    pub fn is_bytes(&self) -> bool {
        matches!(self, Value::Bytes(_))
    }

    /// Is the current value a dict?
    pub fn is_dict(&self) -> bool {
        matches!(self, Value::Dict(_))
    }

    /// Is the current value a list?
    pub fn is_list(&self) -> bool {
        matches!(self, Value::List(_))
    }

    /// Is the current value a container?
    pub fn is_container(&self) -> bool {
        self.is_dict() || self.is_list()
    }

    /// Get the length of the inner value.
    ///
    /// - dicts and lists: the amount of elements in them.
    /// - strs and bytes: their length
    /// - int: 0
    pub fn len(&self) -> usize {
        match self {
            Value::Int(_) => 0,
            Value::Str(s) => s.len(),
            Value::Bytes(b) => b.len(),
            Value::Dict(m) => m.len(),
            Value::List(l) => l.len(),
        }
    }

    /// Try to convert this value to its inner i64
    pub fn to_i64(&self) -> Option<i64> {
        if let Value::Int(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    /// Try to convert this value to a string slice
    pub fn to_str(&self) -> Option<&str> {
        if let Value::Str(s) = self {
            Some(s.as_str())
        } else {
            None
        }
    }

    /// Try to convert this value to a byte slice
    pub fn to_bytes(&self) -> Option<&[u8]> {
        if let Value::Bytes(v) = self {
            Some(v.as_slice())
        } else {
            None
        }
    }

    /// Try to convert this value to a map reference
    pub fn to_map(&self) -> Option<&BTreeMap<String, Value>> {
        if let Value::Dict(map) = self {
            Some(map)
        } else {
            None
        }
    }

    /// Try to convert this value to a vec reference
    pub fn to_vec(&self) -> Option<&Vec<Value>> {
        if let Value::List(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Get a short name for the current type
    pub fn value_type(value: &Self) -> &'static str {
        match value {
            Self::Int(_) => "int",
            Self::Str(_) => "str",
            Self::Bytes(_) => "bytes",
            Self::Dict(_) => "dict",
            Self::List(_) => "list",
        }
    }

    /// Returns the internal display struct, which can be configured.
    ///
    /// See [`ValueDisplay`](struct.ValueDisplay.html).
    pub fn display<'a>(&'a self) -> ValueDisplay<'a> {
        ValueDisplay::new(self)
    }

    /// Select a value inside this one if it is a container (dict or list).
    ///
    /// # Syntax
    ///
    /// - Selecting with key: `.keyname`.
    /// - Selecting with an index: `[n]`, where `n` is >= 0.
    ///
    /// `keyname` can be be anything and also can contain spaces, but if it has dots or an open
    /// bracket (`[`), put a `\` before them. An empty selector will return this value.
    ///
    /// ## Examples
    ///
    /// - `.bar`: Selects key `bar` in the root.
    /// - `.buz.fghij[1]`: Selects key `buz` (dict) in the root (dict), then key `fghij` (list), then
    /// index number 1.
    /// - `[2].foo.bar`: Selects index 2 (dict) in the root (list), then key `foo` (dict) then key `bar` .
    ///
    /// # Errors
    ///
    /// See [`SelectError`]'s documentation. The `context` in its variants has the same meaning as
    /// described in [`Value::traverse`].
    ///
    /// [`SelectError`]: enum.SelectError.html
    /// [`Value::traverse`]: enum.Value.html#method.traverse
    pub fn select(&self, mut selector: &str) -> Result<&Value, SelectError> {
        if selector.is_empty() {
            return Ok(self);
        }

        let full_selector = &selector[..];
        let mut is_dict = false;
        let mut last_key = String::new();
        let mut last_index = 0;

        let result = self.traverse(|key, index, _root, _value, _context| {
            if let Some(current_key) = key {
                let (sel, key) = Self::parse_key_selector(selector, full_selector)?;
                last_key.replace_range(0.., &key);
                is_dict = true;

                if current_key == key {
                    if sel.is_empty() {
                        return Ok(TraverseAction::Stop);
                    }

                    selector = sel;
                } else {
                    return Ok(TraverseAction::Continue);
                }
            } else if let Some(current_index) = index {
                let (sel, index) = Self::parse_index_selector(selector, full_selector)?;
                last_index = index;
                is_dict = false;

                if current_index == index {
                    if sel.is_empty() {
                        return Ok(TraverseAction::Stop);
                    }

                    selector = sel;
                } else {
                    return Ok(TraverseAction::Continue);
                }
            }

            Ok(TraverseAction::Enter)
        });

        result.map_err(|e| match e {
            TraverseError::NotContainer(ctx) => SelectError::Primitive(ctx),
            TraverseError::Aborted(_, e) => e,
            TraverseError::End(ctx) => if is_dict {
                SelectError::Key(ctx, last_key)
            } else {
                SelectError::Index(ctx, last_index)
            },
            TraverseError::AtRoot => unreachable!(),
        })
    }

    /// Traverses a container Value (dict or list) and returns a reference to another Value inside
    /// it.
    ///
    /// This function is not recursive by default. Instead, the whole process is controlled by calls
    /// to the closure `f` on each child value that returns a [`TraverseAction`] describing what to
    /// do next.
    ///
    /// # Closure
    ///
    /// **Arguments**
    ///
    /// - `key`: An Option that contains the key of the current value if the parent container is a dict.
    /// - `index`: An Option that contains the index of current value if the parent container is a list.
    /// - `parent`: The container value that is being iterated on.
    /// - `value`: The current value held by the parent's iterator.
    /// - `context`: A string describing the parent container using the [`select`] syntax. An empty
    /// context means the parent is the root value (`self`).
    ///
    /// For each element of the current container, the closure is called with these arguments and
    /// expects a [`TraverseAction`]:
    ///
    /// - `TraverseAction::Enter`: Go inside of the current value if it is a container. Will throw
    /// an error otherwise.
    /// - `TraverseAction::Exit`: Goes to the parent container, if there is one. If you're at the
    /// root value (`self`), this will throw an error.
    /// - `TraverseAction::Stop`: Stops the process and returns the current value.
    /// - `TraverseAction::Continue`: Go to the next item in the current container.
    ///
    /// `key` and `index` can be used for determining the type of the current container other than
    /// [`Value::is_dict`] or [`Value::is_list`]. `key` being Some means the current container is a
    /// dict, while `index` being Some means it is a list.
    ///
    /// However, if both are None, it means the current container has no more items. You only have
    /// one option here: return `TraverseAction::Exit` to go back to the parent container and
    /// process the rest of its elements. Any other action will throw the `TraverseError::End`
    /// error.
    ///
    /// # Errors
    ///
    /// If there are no more items in the current container and nothing was done by the closure as
    /// described above, this function will return `TraverseError::End`.
    ///
    /// See [`TraverseError`] for information on other types of errors. The `context` in its
    /// variants has the same meaning as the closure argument.
    ///
    /// [`TraverseAction`]: enum.TraverseAction.html
    /// [`select`]: #method.select
    /// [`Value::is_dict`]: enum.Value.html#method.is_dict
    /// [`Value::is_list`]: enum.Value.html#method.is_dict
    /// [`TraverseError`]: enum.TraverseError.html
    pub fn traverse<'a, F, E>(&'a self, mut f: F) -> Result<&'a Value, TraverseError<E>>
    where
        F: FnMut(Option<&str>, Option<usize>, &'a Value, &'a Value, &str) -> Result<TraverseAction, E>,
    {
        if !self.is_container() {
            return Err(TraverseError::NotContainer("<root>".into()));
        }

        let mut state = TraverseState::Root;
        let mut next_state = Vec::new();
        let mut dict_stack = Vec::new();
        let mut list_stack = Vec::new();
        let mut context = String::new();
        let mut value = None;

        while state != TraverseState::Done {
            match state {
                TraverseState::Root => {
                    if let Some(m) = self.to_map() {
                        state = TraverseState::Dict;
                        dict_stack.push((self, m.iter().enumerate().peekable()));
                        next_state.push(TraverseState::Done);
                    } else if let Some(v) = self.to_vec() {
                        state = TraverseState::List;
                        list_stack.push((self, v.iter().enumerate().peekable()));
                        next_state.push(TraverseState::Done);
                    }
                }

                TraverseState::Dict => {
                    let (root, it) = dict_stack.last_mut().unwrap();
                    let next = it.next();

                    if let Some((_i, (key, val))) = next {
                        let action = f(Some(key.as_str()), None, root, val, &context)
                            .map_err(|e| TraverseError::Aborted(context.clone(), e))?;

                        match action {
                            TraverseAction::Enter => {
                                context.extend(format!(".{}", key).chars());

                                if val.is_dict() {
                                    let map = val.to_map().unwrap();

                                    dict_stack.push((val, map.iter().enumerate().peekable()));
                                    next_state.push(TraverseState::Dict);
                                } else if val.is_list() {
                                    let vec = val.to_vec().unwrap();

                                    list_stack.push((val, vec.iter().enumerate().peekable()));
                                    next_state.push(TraverseState::Dict);
                                    state = TraverseState::List;
                                } else {
                                    return Err(TraverseError::NotContainer(context));
                                }
                            }

                            TraverseAction::Exit => {
                                let is_done = *next_state.last().unwrap() == TraverseState::Done;

                                if is_done {
                                    return Err(TraverseError::AtRoot);
                                }

                                // TODO: Check for possible escaped dots
                                let key_pos = context.rfind('.').unwrap();
                                let _ = dict_stack.pop().unwrap();
                                context.truncate(key_pos);
                                state = next_state.pop().unwrap();
                            }

                            TraverseAction::Stop => {
                                value = Some(val);
                                state = TraverseState::Done;
                            }

                            TraverseAction::Continue => (),
                        }
                    } else {
                        let action = f(None, None, root, &Value::Int(0), &context)
                            .map_err(|e| TraverseError::Aborted(context.clone(), e))?;

                        match action {
                            TraverseAction::Exit => {
                                let is_done = *next_state.last().unwrap() == TraverseState::Done;

                                if is_done {
                                    return Err(TraverseError::AtRoot);
                                }

                                let _ = dict_stack.pop().unwrap();
                                state = next_state.pop().unwrap();
                            }

                            _ => state = TraverseState::Done,
                        }
                    }
                }

                TraverseState::List => {
                    let (root, it) = list_stack.last_mut().unwrap();
                    let next = it.next();

                    if let Some((index, val)) = next {
                        let action = f(None, Some(index), root, val, &context)
                            .map_err(|e| TraverseError::Aborted(context.clone(), e))?;

                        match action {
                            TraverseAction::Enter => {
                                context.extend(format!("[{}]", index).chars());

                                if let Some(map) = val.to_map() {
                                    dict_stack.push((val, map.iter().enumerate().peekable()));
                                    next_state.push(TraverseState::List);
                                    state = TraverseState::Dict;
                                } else if let Some(vec) = val.to_vec() {
                                    list_stack.push((val, vec.iter().enumerate().peekable()));
                                    next_state.push(TraverseState::List);
                                } else {
                                    return Err(TraverseError::NotContainer(context));
                                }
                            }

                            TraverseAction::Exit => {
                                let is_done = *next_state.last().unwrap() == TraverseState::Done;

                                if is_done {
                                    return Err(TraverseError::AtRoot);
                                }

                                // TODO: Check for possible escaped dots
                                let key_pos = context.rfind('[').unwrap();
                                let _ = list_stack.pop().unwrap();
                                context.truncate(key_pos);
                                state = next_state.pop().unwrap();
                            }

                            TraverseAction::Stop => {
                                value = Some(val);
                                state = TraverseState::Done;
                            }

                            TraverseAction::Continue => (),
                        }
                    } else {
                        let action = f(None, None, root, &Value::Int(0), &context)
                            .map_err(|e| TraverseError::Aborted(context.clone(), e))?;

                        match action {
                            TraverseAction::Exit => {
                                let is_done = *next_state.last().unwrap() == TraverseState::Done;

                                if is_done {
                                    return Err(TraverseError::AtRoot);
                                }

                                let _ = list_stack.pop().unwrap();
                                state = next_state.pop().unwrap();
                            }

                            _ => state = TraverseState::Done,
                        }
                    }
                }

                // Done
                _ => unreachable!(),
            }
        }

        value.ok_or(TraverseError::End(context))
    }

    fn parse_key_selector<'a>(input: &'a str, full_input: &str) -> Result<(&'a str, String), SelectError> {
        const END_CHARS: &[char] = &['.', '['];

        let mut buf = String::new();
        let mut escaped = false;
        let pos = || full_input.len() - input.len() + 1;
        let context = || {
            let c = &full_input[..pos()];

            if !c.is_empty() {
                c.into()
            } else {
                "<root>".into()
            }
        };
        let mut chars = input.chars();

        if chars.next().unwrap() != '.' {
            return Err(SelectError::Syntax(context(), pos(), "Expected dot".into()));
        }

        let mut input = &input[1..];

        for (i, c) in chars.enumerate() {
            if END_CHARS.contains(&c) {
                if escaped {
                    buf.push(c);
                    input = &input[(i + 1)..];
                    escaped = false;
                } else {
                    buf.push_str(&input[..i]);
                    input = &input[i..];
                    break;
                }
            } else if c == '\\' {
                if escaped {
                    buf.push(c);
                    input = &input[(i + 1)..];
                    escaped = false;
                } else {
                    buf.push_str(&input[..i]);
                    input = &input[(i + 1)..];
                    escaped = true;
                }
            } else if escaped {
                return Err(SelectError::Syntax(context(), pos(), format!("Cannot escape '{}'", c)));
            }
        }

        if escaped {
            return Err(SelectError::Syntax(context(), pos(), "Trailing escape".into()));
        }

        if buf.is_empty() && !input.is_empty() {
            buf.push_str(input);
            input = &input[input.len()..];
        }

        Ok((input, buf))
    }

    fn parse_index_selector<'a>(input: &'a str, full_input: &str) -> Result<(&'a str, usize), SelectError> {
        let pos = || full_input.len() - input.len() + 1;
        let context = || {
            let c = &full_input[..pos()];

            if !c.is_empty() {
                c.into()
            } else {
                "<root>".into()
            }
        };

        let mut chars = input.chars();
        let mut index = None;
        let first_char = chars.next().unwrap();

        if first_char != '[' {
            return Err(SelectError::Syntax(context(), pos(), "Expected '['".into()));
        }

        let mut input = &input[1..];

        for (i, c) in chars.enumerate() {
            if c == ']' {
                let index_ = input[..i].parse::<usize>().map_err(|_| {
                    SelectError::Syntax(context(), pos(), "Not a number".into())
                })?;
                input = &input[(i + 1)..];
                index = Some(index_);
                break;
            } else if c == '-' {
                return Err(SelectError::Syntax(context(), pos(), "Unexpected '-'".into()));
            }
        }

        if index.is_none() {
            return Err(SelectError::End);
        }

        Ok((input, index.unwrap()))
    }
}

impl<'a> ValueDisplay<'a> {
    /// Creates a new ValueDisplay with default values.
    ///
    /// - max_depth: 5
    /// - max_list_items: 10
    /// - max_root_bytes: 32
    /// - max_bytes: 10
    /// - indent_size: 2
    pub fn new(root: &'a Value) -> Self {
        Self {
            root,
            max_depth: 5,
            max_list_items: 10,
            max_root_bytes: 32,
            max_bytes: 10,
            indent_size: 2,
        }
    }

    /// Sets how far down the root value is going to be shown.
    pub fn max_depth(mut self, depth: usize) -> Self {
        self.max_depth = depth;
        self
    }

    /// Sets the maximum number of items shown in a list.
    ///
    /// Excess items are truncated, followed by an ellipsis.
    pub fn max_list_items(mut self, max: usize) -> Self {
        self.max_list_items = max;
        self
    }

    /// Sets how many bytes are shown if they're the root Value.
    ///
    /// Excess bytes are truncated, followed by an ellipsis.
    pub fn max_root_bytes(mut self, max: usize) -> Self {
        self.max_root_bytes = max;
        self
    }

    /// Sets how many bytes are shown if they're inside a container.
    ///
    /// Excess bytes are truncated, followed by an ellipsis.
    pub fn max_bytes(mut self, max: usize) -> Self {
        self.max_bytes = max;
        self
    }

    /// Sets the indentation size in spaces.
    pub fn indent_size(mut self, size: usize) -> Self {
        self.indent_size = size;
        self
    }
}

impl<'a> fmt::Display for ValueDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut indent = 0;
        let mut depth = 1;
        let mut is_dict_stack = Vec::new();
        let mut count_stack = Vec::new();
        let ValueDisplay{
            root, max_depth, max_list_items, max_root_bytes, max_bytes, indent_size
        } = self;

        if root.is_dict() {
            write!(f, "{{\n")?;
            indent += 1;
            is_dict_stack.push(true);
        } else if root.is_list() {
            write!(f, "[")?;
            is_dict_stack.push(false);
            count_stack.push(root.to_vec().unwrap().len());
        }

        let result = root.traverse::<_, fmt::Error>(|key, index, root, value, _context| {
            if let Some(key) = key {
                write!(f, "{:indent$}", "", indent = indent * indent_size)?;
                write!(f, "{:?}: ", key)?;

                if let Some(i) = value.to_i64() {
                    write!(f, "{},\n", i)?;
                } else if let Some(s) = value.to_str() {
                    write!(f, "{:?},\n", s)?;
                } else if let Some(b) = value.to_bytes() {
                    write!(f, "{},\n", repr_bytes(b, *max_bytes))?;
                } else if value.is_dict() {
                    if value.len() == 0 {
                        write!(f, "{{}},\n")?;
                    } else if depth < *max_depth {
                        write!(f, "{{\n")?;
                        indent += 1;
                        depth += 1;
                        is_dict_stack.push(true);

                        return Ok(TraverseAction::Enter);
                    } else {
                        write!(f, "{{...}},\n")?;
                    }
                } else if value.is_list() {
                    let count = value.len();

                    if count == 0 {
                        write!(f, "[],\n")?;
                    } else if depth < *max_depth {
                        write!(f, "[")?;
                        depth += 1;
                        is_dict_stack.push(false);
                        count_stack.push(count);

                        return Ok(TraverseAction::Enter);
                    } else {
                        write!(f, "[...],\n")?;
                    }
                }
            } else if let Some(index) = index {
                let count = *count_stack.last().unwrap();
                let is_last = count == 1;
                *count_stack.last_mut().unwrap() -= 1;

                if index == *max_list_items {
                    let count = root.len();
                    write!(f, "... {} more]", count - index)?;
                    let _ = is_dict_stack.pop().unwrap();
                    let _ = count_stack.pop().unwrap();
                    let is_dict = *is_dict_stack.last().unwrap();
                    depth -= 1;

                    if is_dict {
                        write!(f, ",\n")?;
                    } else {
                        let count = count_stack.last().unwrap();

                        if *count > 0 {
                            write!(f, ", ")?;
                        }
                    }

                    return Ok(TraverseAction::Exit);
                } else if let Some(i) = value.to_i64() {
                    write!(f, "{}", i)?;

                    if !is_last {
                        write!(f, ", ")?;
                    }
                } else if let Some(s) = value.to_str() {
                    write!(f, "{:?}", s)?;

                    if !is_last {
                        write!(f, ", ")?;
                    }
                } else if let Some(b) = value.to_bytes() {
                    write!(f, "{}", repr_bytes(b, *max_bytes))?;

                    if !is_last {
                        write!(f, ", ")?;
                    }
                } else if value.is_dict() {
                    if value.len() == 0 {
                        write!(f, "{{}}")?;
                    } else if depth < *max_depth {
                        write!(f, "{{\n")?;
                        indent += 1;
                        depth += 1;
                        is_dict_stack.push(true);

                        return Ok(TraverseAction::Enter);
                    } else {
                        write!(f, "{{...}}")?;
                    }
                } else if value.is_list() {
                    let count = value.len();

                    if count == 0 {
                        write!(f, "[]")?;
                    } else if depth < *max_depth {
                        write!(f, "[")?;
                        depth += 1;
                        is_dict_stack.push(false);
                        count_stack.push(count);

                        return Ok(TraverseAction::Enter);
                    } else {
                        write!(f, "[...]")?;
                    }
                }
            } else {
                depth -= 1;
                let was_dict = *is_dict_stack.last().unwrap();

                if was_dict {
                    indent -= 1;
                    write!(f, "{:indent$}", "", indent = indent * indent_size)?;
                    write!(f, "}}")?;
                } else {
                    write!(f, "]")?;
                    let _ = count_stack.pop().unwrap();
                }

                let _ = is_dict_stack.pop().unwrap();
                let is_dict = is_dict_stack.last();

                if let Some(&is_dict) = is_dict {
                    if is_dict {
                        write!(f, ",\n")?;
                    } else {
                        let count = count_stack.last().unwrap();

                        if *count > 0 {
                            write!(f, ", ")?;
                        }
                    }

                    return Ok(TraverseAction::Exit);
                }
            }

            Ok(TraverseAction::Continue)
        });

        if let Err(TraverseError::NotContainer(_)) = result {
            if let Some(i) = root.to_i64() {
                write!(f, "{}", i)?;
            } else if let Some(s) = root.to_str() {
                write!(f, "{:?}", s)?;
            } else if let Some(b) = root.to_bytes() {
                write!(f, "{}", repr_bytes(b, *max_root_bytes))?;
            }
        } else if !matches!(result, Err(TraverseError::End(_))) ||
          (matches!(result, Err(TraverseError::End(_))) && depth > 0) {
            return Err(fmt::Error);
        }

        Ok(())
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        ValueDisplay::new(self).fmt(f)
    }
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParserError::Io(e) => write!(f, "IO Error: {}", e),
            ParserError::Empty => write!(f, "Empty file"),
            ParserError::Syntax(n, s) => write!(f, "Syntax error at {}: {}", n + 1, s),
            ParserError::Eof => write!(f, "Unexpected end of file reached"),
        }
    }
}

impl fmt::Display for SelectError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SelectError::Key(ctx, key) => write!(f, "[{:?}] Unknown key '{}'", ctx, key),
            SelectError::Index(ctx, index) => write!(f, "[{:?}] Index {} out of bounds", ctx, index),
            SelectError::Subscriptable(ctx) => write!(f, "[{:?}] Current value cannot be subscripted", ctx),
            SelectError::Indexable(ctx) => write!(f, "[{:?}] Current value cannot be indexed", ctx),
            SelectError::Primitive(ctx) => write!(f, "[{:?}] Current value is not selectable!", ctx),
            SelectError::Syntax(ctx, pos, msg) => write!(f, "[{:?}] Syntax error at {}: {}", ctx, pos, msg),
            SelectError::End => write!(f, "Reached end of selector prematurely"),
        }
    }
}

impl From<IoError> for ParserError {
    fn from(e: IoError) -> Self {
        Self::Io(e)
    }
}

impl<E> Into<Result<TraverseAction, E>> for TraverseAction {
    fn into(self) -> Result<Self, E> {
        Ok(self)
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

#[cfg(test)]
mod tests {
    use super::{BTreeMap, Value};

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
}
