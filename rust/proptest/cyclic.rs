// vim: ts=4 sw=4 et:
/**
 * Cyclic buffer challenge in Rust with property-based testing.
 *
 * Translated from C to Rust with Claude Sonnet 4.5.
 */

// Buffer size - override with: BUF_SIZE=20 cargo build
// Supported values: 10, 20, 50, 100
#[cfg(buf_size_20)]
const BUF_SIZE: usize = 20;
#[cfg(buf_size_50)]
const BUF_SIZE: usize = 50;
#[cfg(buf_size_100)]
const BUF_SIZE: usize = 100;
#[cfg(not(any(buf_size_20, buf_size_50, buf_size_100)))]
const BUF_SIZE: usize = 10;

// Number of property test cases - override with PROPTEST_CASES=500 cargo test
// Supported values: 100, 500, 1000, 10000
#[cfg(all(test, proptest_500))]
const PROPTEST_CASES: usize = 500;
#[cfg(all(test, proptest_1000))]
const PROPTEST_CASES: usize = 1000;
#[cfg(all(test, proptest_10000))]
const PROPTEST_CASES: usize = 10000;
#[cfg(all(test, not(any(proptest_500, proptest_1000, proptest_10000))))]
const PROPTEST_CASES: usize = 100;

pub struct CyclicBuffer {
    buffer: [i32; BUF_SIZE],
    head: usize,  // next element to read
    tail: usize,  // next free slot to write
    count: usize, // number of elements in buffer
}

impl CyclicBuffer {
    pub fn new() -> Self {
        CyclicBuffer {
            buffer: [0; BUF_SIZE],
            head: 0,
            tail: 0,
            count: 0,
        }
    }

    /// Write an element to the cyclic buffer
    pub fn write(&mut self, in_val: i32) {
        // BUG: missing the overflow check!
        self.buffer[self.tail] = in_val;
        self.tail = (self.tail + 1) % BUF_SIZE;
        self.count += 1;
    }

    /// Read an element from the cyclic buffer
    pub fn read(&mut self) -> Option<i32> {
        if self.count == 0 {
            return None; // empty
        }
        let out_val = self.buffer[self.head];
        self.head = (self.head + 1) % BUF_SIZE;
        self.count -= 1;
        Some(out_val)
    }
}

impl Default for CyclicBuffer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_and_read() {
        let mut cb = CyclicBuffer::new();
        cb.write(42);
        assert_eq!(cb.read(), Some(42));
        assert_eq!(cb.read(), None);
    }

    #[test]
    fn test_multiple_writes_and_reads() {
        let mut cb = CyclicBuffer::new();
        for i in 0..5 {
            cb.write(i);
        }
        for i in 0..5 {
            assert_eq!(cb.read(), Some(i));
        }
    }
}

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;

    #[derive(Debug, Clone)]
    enum Operation {
        Write(i32),
        Read,
    }

    proptest! {
        #[test]
        fn test_no_overflow_with_valid_operations(ops in prop::collection::vec(
            prop_oneof![
                any::<i32>().prop_map(Operation::Write),
                Just(Operation::Read),
            ],
            0..PROPTEST_CASES
        )) {
            let mut cb = CyclicBuffer::new();
            let mut count = 0;

            for op in ops {
                match op {
                    Operation::Write(val) => {
                        cb.write(val);
                        count += 1;

                        // check our safety property
                        assert!(count <= BUF_SIZE,
                            "Buffer overflow: count = {}, BUF_SIZE = {}", count, BUF_SIZE);
                    }
                    Operation::Read => {
                        let elem = cb.read();
                        assert_eq!(elem.is_some(), count > 0,
                            "Read operation mismatch: expected Some when count > 0, got {:?}", elem);
                        if elem.is_some() {
                            assert!(count > 0, "Read returned Some but count is 0");
                            count -= 1;
                        } else {
                            assert!(count == 0, "Read returned None but count > 0");
                        }
                    }
                }
            }
        }
    }
}
