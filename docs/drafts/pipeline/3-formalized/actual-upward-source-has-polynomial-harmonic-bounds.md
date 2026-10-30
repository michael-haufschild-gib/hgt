# The actual upward source has polynomial harmonic bounds

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement and proof

For each fixed positive conductor and smooth unit-supported profile of
positive mass, one `K>0` and one horizon give the actual normalized
upward residual squared bound `Kc¹⁰/√(log N)` simultaneously for all
`c≥1` satisfying `4(e+3)²c²≤N`.

Use the exact small-width offset identity with `B=ceil(ec)`.
Its three errors are logarithmic-kernel replacement, moving both
horizon cutoffs, and the signed reciprocal-shell mean.
Their normalized squared bounds are respectively
`C_a c⁴(B+1)⁶/√(log N)`, `C_b(B+1)⁶/√(log N)`, and
`C_d c⁶/√(log N)`. The last is the average of positive and reflected
affine-source errors. Since `B+1≤(e+2)c`, all are at most a constant
times `c¹⁰/√(log N)`. The square of the sum is at most three times
the sum of squares. The stated horizon condition supplies all support
and Taylor conditions without removing any prime powers or source terms.

## Lean status

`TheActualUpwardSourceHasPolynomialHarmonicBounds.lean` proves the
literal row estimate and its normalized Euclidean-vector form. Final direct
Lean check passed; both transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Umbrella wired. Supporting source
estimate; no separate contribution count.
