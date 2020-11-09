use std::{
    cmp::Ordering,
    collections::BTreeMap,
    fmt,
};

#[derive(Debug, PartialEq)]
enum TraverseState {
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
    /// Goes to the parent container of the current container.
    Exit,
    /// Keep going through items in the container.
    Continue,
    /// Stop traversing and return the current value.
    Stop,
}

/// An error from the [`Value::traverse`] method.
///
/// [`Value::traverse`]: enum.Value.html#method.traverse
#[derive(Debug)]
pub enum TraverseError<E = ()> {
    /// `(parent)`
    ///
    /// Tried to enter a value in the current container that was not a container.
    NotContainer(String),

    /// Tried to go back to the parent container, but we were at the root.
    AtRoot,

    /// `(parent)`
    ///
    /// Reached the end of the current container.
    End(String),

    /// `(parent, error)`
    ///
    /// An error occurred processing a value and the traversal was aborted.
    Aborted(String, E),
}

/// An error from the [`Value::select`] method.
///
/// [`Value::select`]: enum.Value.html#method.select
#[derive(Debug)]
pub enum SelectError {
    /// `(container, key)`
    ///
    /// Key does not exist in this container.
    Key(String, String),

    /// `(container, index)`
    ///
    /// Index is out of bounds for this container.
    Index(String, usize),

    /// `(parent)`
    ///
    /// Value is not a container and can't be selected into.
    Primitive(String),

    /// `(container, pos, reason)`
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

/// A valid accessor for a container value.
///
/// See [`Value::get`] and [`Value::get_mut`].
///
/// [`Value::get`]: enum.Value.html#method.get
/// [`Value::get_mut`]: enum.Value.html#method.get_mut
pub enum ValueAccessor<'a> {
    /// Access with an index
    Index(usize),
    /// Access with a key
    Key(&'a str),
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

    /// Try to convert this value to a mutable map reference
    pub fn to_map_mut(&mut self) -> Option<&mut BTreeMap<String, Value>> {
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

    /// Try to convert this value to a mutable vec reference
    pub fn to_vec_mut(&mut self) -> Option<&mut Vec<Value>> {
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

    /// Returns a reference to an item inside this value with an index or key.
    ///
    /// Return value will be None if the element does not exist in this container or if this value
    /// is not a container. See also [`is_container`](#method.is_container).
    pub fn get<'a, A>(&self, a: A) -> Option<&Value> where A: Into<ValueAccessor<'a>> {
        match a.into() {
            ValueAccessor::Index(n) => self.to_vec().and_then(|v| v.get(n)),
            ValueAccessor::Key(s) => self.to_map().and_then(|m| m.get(s)),
        }
    }

    /// Returns a mutable reference to an item inside this value with an index or a key.
    ///
    /// Return value will be None if the element does not exist in this container or if this value
    /// is not a container. See also [`is_container`](#method.is_container).
    pub fn get_mut<'a, A>(&mut self, a: A) -> Option<&mut Value> where A: Into<ValueAccessor<'a>> {
        match a.into() {
            ValueAccessor::Index(n) => self.to_vec_mut().and_then(|v| v.get_mut(n)),
            ValueAccessor::Key(s) => self.to_map_mut().and_then(|m| m.get_mut(s)),
        }
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
    /// See [`SelectError`]'s documentation.
    ///
    /// [`SelectError`]: enum.SelectError.html
    /// [`Value::traverse`]: enum.Value.html#method.traverse
    pub fn select(&self, mut selector: &str) -> Result<&Value, SelectError> {
        if selector.is_empty() {
            return Ok(self);
        }

        let full_selector = &selector[..];
        let mut container = String::new();
        let mut value = self;

        loop {
            if value.is_dict() {
                let (sel, key) = Self::parse_key_selector(selector, full_selector)?;
                value = value.get(&key).ok_or(SelectError::Key(container.clone(), key.clone()))?;
                container.extend(format!(".{}", key).chars());

                if sel.is_empty() {
                    break;
                }

                selector = sel;
            } else if value.is_list() {
                let (sel, index) = Self::parse_index_selector(selector, full_selector)?;
                value = value.get(index).ok_or(SelectError::Index(container.clone(), index))?;
                container.extend(format!("[{}]", index).chars());

                if sel.is_empty() {
                    break;
                }

                selector = sel;
            } else {
                return Err(SelectError::Primitive(container));
            }
        }

        Ok(value)
    }

    /// Selects a value inside this container and returns a mutable reference.
    ///
    /// See [`select`](#method.select).
    pub fn select_mut(&mut self, mut selector: &str) -> Result<&mut Value, SelectError> {
        if selector.is_empty() {
            return Ok(self);
        }

        let full_selector = &selector[..];
        let mut container = String::new();
        let mut value = self;

        loop {
            if value.is_dict() {
                let (sel, key) = Self::parse_key_selector(selector, full_selector)?;
                value = value.get_mut(&key).ok_or(SelectError::Key(container.clone(), key.clone()))?;
                container.extend(format!(".{}", key).chars());

                if sel.is_empty() {
                    break;
                }

                selector = sel;
            } else if value.is_list() {
                let (sel, index) = Self::parse_index_selector(selector, full_selector)?;
                value = value.get_mut(index).ok_or(SelectError::Index(container.clone(), index))?;
                container.extend(format!("[{}]", index).chars());

                if sel.is_empty() {
                    break;
                }

                selector = sel;
            } else {
                return Err(SelectError::Primitive(container));
            }
        }

        Ok(value)
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
    /// - `key`: An Option that contains the key of the current value if the parent container is a
    /// dict.

    /// - `index`: An Option that contains the index of current value if the parent container is a
    /// list.
    /// - `parent`: The container value that is being iterated on.
    /// - `value`: The current value held by the parent's iterator.
    /// - `selector`: A string describing the current value using [`select`] syntax.
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
    /// # Mutable traversing
    ///
    /// Due to (reasonable) borrow checker restrictions, there can't be a mutable version of this
    /// function. Instead, use the `selector` argument of the closure to make a list of Values you
    /// want to change, then use [`select_mut`] on them.
    ///
    /// # Errors
    ///
    /// If there are no more items in the current container and nothing was done by the closure as
    /// described above, this function will return `TraverseError::End`.
    ///
    /// See [`TraverseError`] for information on other types of errors.
    ///
    /// [`TraverseAction`]: enum.TraverseAction.html
    /// [`select`]: #method.select
    /// [`Value::is_dict`]: enum.Value.html#method.is_dict
    /// [`Value::is_list`]: enum.Value.html#method.is_dict
    /// [`select_mut`]: #method.select_mut
    /// [`TraverseError`]: enum.TraverseError.html
    pub fn traverse<'a, F, E>(&'a self, mut f: F) -> Result<&'a Value, TraverseError<E>>
    where
        F: FnMut(Option<&str>, Option<usize>, &'a Value, &'a Value, &str) -> Result<TraverseAction, E>,
    {
        if !self.is_container() {
            return Err(TraverseError::NotContainer("<root>".into()));
        }

        let mut next_state = Vec::new();
        let mut context = String::new();
        let mut value_stack = vec![self];
        let mut keys_stack = self.to_map().map(|m| vec![m.keys()]).unwrap_or(Vec::new());
        let mut index_stack = self.to_vec().map(|v| vec![0..v.len()]).unwrap_or(Vec::new());
        let mut state = if self.is_dict() { TraverseState::Dict } else { TraverseState::List };
        let mut value = None;

        while state != TraverseState::Done {
            match state {
                TraverseState::Dict => {
                    let root = value_stack.last().unwrap();
                    let it = keys_stack.last_mut().unwrap();
                    let next = it.next();

                    if let Some(key) = next {
                        let key = key.as_str();
                        let val = root.get(key).unwrap();
                        let action = f(Some(key), None, root, val, &context)
                            .map_err(|e| TraverseError::Aborted(context.clone(), e))?;

                        match action {
                            TraverseAction::Enter => {
                                context.extend(format!(".{}", key).chars());

                                if let Some(m) = val.to_map() {
                                    value_stack.push(val);
                                    keys_stack.push(m.keys());
                                    next_state.push(TraverseState::Dict);
                                } else if val.is_list() {
                                    value_stack.push(val);
                                    index_stack.push(0..val.len());
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
                                let _ = keys_stack.pop().unwrap();
                                let _ = value_stack.pop().unwrap();
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

                                let _ = keys_stack.pop().unwrap();
                                let _ = value_stack.pop().unwrap();
                                state = next_state.pop().unwrap();
                            }

                            _ => state = TraverseState::Done,
                        }
                    }
                }

                TraverseState::List => {
                    let root = value_stack.last().unwrap();
                    let it = index_stack.last_mut().unwrap();
                    let next = it.next();

                    if let Some(index) = next {
                        let val = root.get(index).unwrap();
                        let action = f(None, Some(index), root, val, &context)
                            .map_err(|e| TraverseError::Aborted(context.clone(), e))?;

                        match action {
                            TraverseAction::Enter => {
                                context.extend(format!("[{}]", index).chars());

                                if let Some(m) = val.to_map() {
                                    value_stack.push(val);
                                    keys_stack.push(m.keys());
                                    next_state.push(TraverseState::List);
                                    state = TraverseState::Dict;
                                } else if let Some(vec) = val.to_vec() {
                                    value_stack.push(val);
                                    index_stack.push(0..vec.len());
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
                                let _ = index_stack.pop().unwrap();
                                let _ = value_stack.pop().unwrap();
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

                                let _ = index_stack.pop().unwrap();
                                let _ = value_stack.pop().unwrap();
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

    /// Encodes a Value into a byte stream.
    ///
    /// Dictionary encoding keys are lexigraphically sorted as per the standard, which is provided
    /// for free by the internal BTreeMap.
    pub fn encode(&self, stream: &mut impl std::io::Write) -> std::io::Result<()> {
        match self {
            Value::Dict(m) => {
                write!(stream, "d")?;

                for (key, value) in m {
                    write!(stream, "{}:{}", key.len(), key)?;
                    value.encode(stream)?;
                }

                write!(stream, "e")
            }

            Value::List(v) => {
                write!(stream, "l")?;

                for value in v {
                    value.encode(stream)?;
                }

                write!(stream, "e")
            }

            Value::Bytes(v) => {
                write!(stream, "{}:", v.len())?;
                stream.write_all(v)
            }

            Value::Str(s) => write!(stream, "{}:{}", s.len(), s),
            Value::Int(i) => write!(stream, "i{}e", i.to_string()),
        }
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

impl From<BTreeMap<String, Value>> for Value {
    fn from(m: BTreeMap<String, Value>) -> Self {
        Value::Dict(m)
    }
}

impl From<Vec<Value>> for Value {
    fn from(v: Vec<Value>) -> Self {
        Value::List(v)
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::Str(s)
    }
}

impl From<Vec<u8>> for Value {
    fn from(v: Vec<u8>) -> Self {
        Value::Bytes(v)
    }
}

impl<'a> From<&'a str> for Value {
    fn from(s: &'a str) -> Self {
        Value::Str(s.into())
    }
}

impl<'a> From<&'a String> for Value {
    fn from(s: &'a String) -> Self {
        Value::Str(s.clone())
    }
}

impl<'a> From<&'a [u8]> for Value {
    fn from(s: &'a [u8]) -> Self {
        Value::Bytes(s.to_vec())
    }
}

macro_rules! impl_from_int {
    ($($t:ty) +) => {
        $(
            impl From<$t> for Value {
                fn from(i: $t) -> Self {
                    Value::Int(i as i64)
                }
            }
        )+
    }
}

impl_from_int!(i64 u32 i32 u16 i16 u8 i8);

impl<'a> From<usize> for ValueAccessor<'a> {
    fn from(n: usize) -> Self {
        ValueAccessor::Index(n)
    }
}

impl<'a> From<&'a str> for ValueAccessor<'a> {
    fn from(s: &'a str) -> Self {
        ValueAccessor::Key(s)
    }
}

impl<'a> From<&'a String> for ValueAccessor<'a> {
    fn from(s: &'a String) -> Self {
        ValueAccessor::Key(s.as_str())
    }
}

impl fmt::Display for SelectError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SelectError::Key(ctx, key) => write!(f, "[{:?}] Unknown key '{}'", ctx, key),
            SelectError::Index(ctx, index) => write!(f, "[{:?}] Index {} out of bounds", ctx, index),
            SelectError::Primitive(ctx) => write!(f, "[{:?}] Current value is not selectable!", ctx),
            SelectError::Syntax(ctx, pos, msg) => write!(f, "[{:?}] Syntax error at {}: {}", ctx, pos, msg),
            SelectError::End => write!(f, "Reached end of selector prematurely"),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        ValueDisplay::new(self).fmt(f)
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

        let result = root.traverse::<_, fmt::Error>(|key, index, root, value, _selector| {
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

impl<'a> PartialEq<str> for Value {
    fn eq(&self, rhs: &str) -> bool {
        if let Value::Str(s) = self {
            s == rhs
        } else {
            false
        }
    }
}

impl<'a> PartialEq<&'a str> for Value {
    fn eq(&self, rhs: &&'a str) -> bool {
        if let Value::Str(s) = self {
            s == rhs
        } else {
            false
        }
    }
}

impl PartialEq<String> for Value {
    fn eq(&self, rhs: &String) -> bool {
        if let Value::Str(s) = self {
            s == rhs
        } else {
            false
        }
    }
}

impl PartialEq<[u8]> for Value {
    fn eq(&self, rhs: &[u8]) -> bool {
        if let Value::Bytes(v) = self {
            v.as_slice() == rhs
        } else {
            false
        }
    }
}

impl<'a> PartialEq<&'a [u8]> for Value {
    fn eq(&self, rhs: &&'a [u8]) -> bool {
        if let Value::Bytes(v) = self {
            v.as_slice() == *rhs
        } else {
            false
        }
    }
}

impl PartialEq<Vec<u8>> for Value {
    fn eq(&self, rhs: &Vec<u8>) -> bool {
        if let Value::Bytes(v) = self {
            v == rhs
        } else {
            false
        }
    }
}

impl PartialOrd<String> for Value {
    fn partial_cmp(&self, rhs: &String) -> Option<Ordering> {
        if let Value::Str(s) = self {
            s.partial_cmp(rhs)
        } else {
            None
        }
    }
}

impl PartialOrd<str> for Value {
    fn partial_cmp(&self, rhs: &str) -> Option<Ordering> {
        if let Value::Str(s) = self {
            s.as_str().partial_cmp(rhs)
        } else {
            None
        }
    }
}

impl<'a> PartialOrd<&'a str> for Value {
    fn partial_cmp(&self, rhs: &&'a str) -> Option<Ordering> {
        if let Value::Str(s) = self {
            s.as_str().partial_cmp(rhs)
        } else {
            None
        }
    }
}

impl PartialOrd<[u8]> for Value {
    fn partial_cmp(&self, rhs: &[u8]) -> Option<Ordering> {
        if let Value::Bytes(v) = self {
            v.as_slice().partial_cmp(rhs)
        } else {
            None
        }
    }
}

impl<'a> PartialOrd<&'a [u8]> for Value {
    fn partial_cmp(&self, rhs: &&'a [u8]) -> Option<Ordering> {
        if let Value::Bytes(v) = self {
            v.as_slice().partial_cmp(rhs)
        } else {
            None
        }
    }
}

impl PartialOrd<Vec<u8>> for Value {
    fn partial_cmp(&self, rhs: &Vec<u8>) -> Option<Ordering> {
        if let Value::Bytes(v) = self {
            v.partial_cmp(rhs)
        } else {
            None
        }
    }
}

macro_rules! impl_cmp_int {
    ($($t:ty) +) => {
        $(
            impl PartialEq<$t> for Value {
                fn eq(&self, rhs: &$t) -> bool {
                    if let Value::Int(i) = self {
                        *i == *rhs as i64
                    } else {
                        false
                    }
                }
            }

            impl<'a> PartialEq<$t> for &'a Value {
                fn eq(&self, rhs: &$t) -> bool {
                    if let Value::Int(i) = self {
                        *i == *rhs as i64
                    } else {
                        false
                    }
                }
            }

            impl PartialOrd<$t> for Value {
                fn partial_cmp(&self, rhs: &$t) -> Option<Ordering> {
                    if let Value::Int(i) = self {
                        i.partial_cmp(&(*rhs as i64))
                    } else {
                        None
                    }
                }
            }

            impl<'a> PartialOrd<$t> for &'a Value {
                fn partial_cmp(&self, rhs: &$t) -> Option<Ordering> {
                    if let Value::Int(i) = self {
                        i.partial_cmp(&(*rhs as i64))
                    } else {
                        None
                    }
                }
            }
        )+
    };
}

impl_cmp_int!(i64 u32 i32 u16 i16 u8 i8);
