----------------------- MODULE MC2u1_BuggyCircularBuffer ----------------------
\* A model checking instance with up to 2 elements of 1-bit unsigned integers.
EXTENDS Integers

\* Fix buffer size to 2
BUFFER_SIZE == 2

\* We store bits in the buffer
BUFFER_ELEMS == {0, 1}

\* Declare the same variables as in BuggyCircularBuffer.tla
VARIABLES
    \* @type: Int -> Int;
    buffer,
    \* @type: Int;
    head,
    \* @type: Int;
    tail,
    \* @type: Int;
    count

\* So we can instantiate BuggyCircularBuffer.tla
INSTANCE BuggyCircularBuffer
==============================================================================
