// -*- mode: Bluespec; -*-
/**
 * A very simple specification of a circular buffer with a bug.
 *
 * Translated from TLA+ to Quint with Claude.
 */
module buggy_circular_buffer {

  // Size of the circular buffer.
  const BUFFER_SIZE: int

  // The set of possible buffer elements.
  const BUFFER_ELEMS: Set[int]

  // The integer buffer of size BUFFER_SIZE.
  var buffer: int -> int

  // Index of the next element to POP.
  var headIndex: int

  // Index of the next free slot for PUSH.
  var tailIndex: int

  // Number of elements currently stored.
  var count: int

  /// Initial state
  action init = all {
    BUFFER_SIZE > 0,
    buffer' = 0.to(BUFFER_SIZE - 1).mapBy(i => 0),
    headIndex' = 0,
    tailIndex' = 0,
    count' = 0,
  }

  /// Buggy PUT: Advance tail, increment count, but no fullness check!
  action putElem(x: int): bool = all {
    BUFFER_ELEMS.contains(x),
    val nextTail = (tailIndex + 1) % BUFFER_SIZE
    all {
      buffer' = buffer.set(tailIndex, x),
      headIndex' = headIndex,
      tailIndex' = nextTail,
      count' = count + 1,
    }
  }

  /// GET: Only allowed when count > 0.
  action getElem: bool = all {
    count > 0,
    buffer' = buffer,
    val nextHead = (headIndex + 1) % BUFFER_SIZE
    all {
      headIndex' = nextHead,
      tailIndex' = tailIndex,
      count' = count - 1,
    }
  }

  /// Either Put or Get may happen in any step.
  action step = any {
    nondet x = BUFFER_ELEMS.oneOf()
    putElem(x),
    getElem,
  }

  /// Safety property we *intend* to hold, but it is violated:
  /// count must never exceed the buffer capacity.
  val safeInv: bool = count <= BUFFER_SIZE

  /// View for the model checker to observe the count variable.
  val countView: int = count
}

// Model checking instance: 10 elements of 8-bit unsigned integers
module mc10u8_buggy_circular_buffer {
  import buggy_circular_buffer(
    BUFFER_SIZE = 10,
    BUFFER_ELEMS = 0.to(255)
  ).*
}

// Model checking instance: 25 elements of 8-bit unsigned integers
module mc25u8_buggy_circular_buffer {
  import buggy_circular_buffer(
    BUFFER_SIZE = 25,
    BUFFER_ELEMS = 0.to(255)
  ).*
}

// Model checking instance: 100 elements of 1-bit values
module mc100u1_buggy_circular_buffer {
  import buggy_circular_buffer(
    BUFFER_SIZE = 100,
    BUFFER_ELEMS = 0.to(1)
  ).*
}

// Model checking instance: 100 elements of 8-bit values
module mc100u8_buggy_circular_buffer {
  import buggy_circular_buffer(
    BUFFER_SIZE = 100,
    BUFFER_ELEMS = 0.to(255)
  ).*
}
