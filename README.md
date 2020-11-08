# bencode

Yet another library for parsing bencode. It has a focus on being able to manipulate bencode data as is (e.g. for bencode editors), so it's not zero copy like many others, but should be fairly efficient.

Everything is documented, but I don't think I'm going to publish this to crates.io so you'll have to read it locally with `cargo doc`.

## Usage

### Loading from a byte slice

```rust
const SAMPLE: &[u8] = b"li1ei3ei3ei7ee";

let value = bencode::load_str(SAMPLE).unwrap();

/// You can do direct comparisions with primitive values like strings, bytes and integers.
assert_eq!(bencode.get(0).unwrap(), &1);
assert_eq!(bencode.get(1).unwrap(), &3);
assert_eq!(bencode.get(2).unwrap(), &3);
assert_eq!(bencode.get(3).unwrap(), &7);
```

### Loading from a file

```rust
let mut file = File::open("somedata.bencode").unwrap();
let value = bencode::load(&mut file).unwrap();
let inner_value = value.get("foo")
    .and_then(|v| v.get("foobar"))
    .and_then(|v| v.get("foobarbaz"))
    .unwrap();
    
assert_eq!(inner_value, "hello world");
```

### Selecting values

```rust
let mut file = File::open("somedata.bencode").unwrap();
let value = bencode::load(&mut file).unwrap();
let inner_value = value.select(".foo.foobar.foobarbaz").unwrap();
let another_value = value.select(".list[1].foo").unwrap();
```

### Converting values to inner types

```rust
let mut file = File::open("somedata.bencode").unwrap();
let value = bencode::load(&mut file).unwrap();
let inner_value = value.select(".something[0]"); // An int

/// The library differentiates strings and bytes, where strings are valid
/// UTF-8 and bytes are any other data that failed the conversion.
assert_eq!(inner_value.to_str(), None);
assert_eq!(inner_value.to_bytes(), None);
assert_eq!(inner_value.to_i64(), Some(4));
assert_eq!(inner_value.to_map(), None);
assert_eq!(inner_value.to_vec(), None);
``` 

### Traversing structures

```rust
const DICT: &[u8] = b"d3:bari1e3:bazi2e3:buzd5:abcde5:fghij3:boz\
                      3:bez5:fghijl6:klmnop6:qrstuvd4:wxyzi0eeee\
                      3:fooi0e3:zyxli0ei1ei2eee";
                                            
use bencode::TraverseAction;

let value = bencode::load_str(DICT).unwrap();
let matching_value = value.traverse(|key, index, parent, value, selector| {
	// Dive into the structure
	if value.is_container() {
		return Ok(TraverseAction::Enter);
	}
	
	// End of container, go back up (unless we're at the root)
	// In this particular case this will never happen, since the 
	// path to the value is straight down.
	if key.is_none() && index.is_none() && parent != value {
		return Ok(TraverseAction::Exit);
	}
	
	if value == "qrstuv" {
		return Ok(TraverseAction::Stop);
	}
	
	Ok(TraverseAction::Continue)
}).unwrap();

assert_eq!(matching_value, "qrstuv");
```

### Modifying values

```rust
const SAMPLE: &[u8] = b"li1ei3ei3ei7ee";

let mut value = bencode::load_str(SAMPLE).unwrap();
*value.get_mut(0).unwrap() = 0.into();
*value.get_mut(2).unwrap() = "foobar".into();
assert_eq!(value.get(0).unwrap(), &0);
assert_eq!(value.get(2).unwrap(), "foobar");
```

### Encode a value

```rust
const DICT: &[u8] = b"d3:bari1e3:bazi2e3:buzd5:abcde5:fghij3:boz\
                      3:bez5:fghijl6:klmnop6:qrstuvd4:wxyzi0eeee\
                      3:fooi0e3:zyxli0ei1ei2eee";

let value = bencode::load_str(DICT).unwrap();
let mut buffer = Vec::new();
value.encode(&mut buffer).unwrap();
assert_eq!(buffer, DICT);
```