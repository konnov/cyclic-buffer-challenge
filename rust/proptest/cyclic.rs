// vim: ts=4 sw=4 et:
/**
 * Cyclic buffer challenge in Rust with property-based testing.
 *
 * Translated from C to Rust with Claude Sonnet 4.5.
 */

// Define buffer size - can be overridden with --cfg
const BUF_SIZE: usize = 10;

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
            0..100      // NOTE: if you bump BUF_SIZE, increase the number of tests!
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
