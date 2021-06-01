# A general and principled approach to Rust's niche

The Rust compiler has recently introduced (see [74699](https://github.com/rust-lang/rust/pull/74699/files)) a
notion of _niche_. Roughly speaking, the idea consists in:
* an ability to declare sub-types of usual base types at the language level.
* support on the compiler side to exploit this sub-typing information to optimize the memory-representation of data-types. 

A typical example is the declaration of a non-zero int32, and the compiler representing an option on such a value in memory over 32 bits, using the ``0'' pattern to represent None.

With this work, we explore how far this idea can be pushed in the context of an
ML-like language. We are both interested in extending the applicability of the
techniques, as well as ensuring static guarantees.

## Meta

- Author(s):
  - Gabriel Radanne
  - Yannick Zakowski
