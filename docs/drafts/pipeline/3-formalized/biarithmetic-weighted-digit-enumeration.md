# Exact signed digit moments on ordinary integer blocks

- **ID:** biarithmetic-weighted-digit-enumeration
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Digital energy and payment](../1-in-progress/biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** Arbitrary signed base-five digit readouts have the exact complete-prefix and annular second moments on ordinary natural-number indices, including a positive lower bound determined by the leading weight alone.

## Enumeration and moments

Mathlib's `finFunctionFinEquiv` bijects the words `Fin M -> Fin 5` with
`Fin (5^M)`. Its inverse reads digit `i` as `floor(n/5^i) mod5`.
Consequently the checked word moments transfer directly to the integer range:

`sum_(n<5^M) W_x(n)^2 = 5^M [2 sum_(i<M)x_i^2+4(sum_(i<M)x_i)^2]`.

The full digit readout uses exactly `Nat.log 5 n+1` digits. The natural logarithm
criterion makes that length `M+1` throughout `5^M<=n<5^(M+1)`.
Subtract the complete prefix moment at `M` from the one at `M+1`; the leading
digit is zero below `5^M`. The exact annular formula is

`sum_block W_x(n)^2
 =4*5^M [(5/4)x_M^2+2 sum_(i<M)x_i^2+((5/2)x_M+2 sum_(i<M)x_i)^2]`.

Every omitted term in this decomposition is nonnegative, so the moment is at
least `5^(M+1)x_M^2`, regardless of the other coefficient signs. Geometric
weights `x_i=a^i` recover the previously defined `fiveDigitRow a n` exactly.
These are classical finite digit identities, now connected to the actual
integer indexing used by pronic energy. No asymptotic or independence premise
is imposed on an arithmetic source.

## Verification

Lean: `BiarithmeticGeometry/WeightedDigitEnumeration.lean`.
Main declarations: `fiveTruncatedDigitReadout_word`,
`sum_sq_fiveTruncatedDigitReadout`, `fiveWeightedDigitRow_on_block`,
`fiveWeightedDigitRow_geometric`, `sum_sq_fiveWeightedDigitRow_block`, and
`fiveWeightedDigitRow_block_lower`.

- [x] Exact paper enumeration, geometric-row comparison, and both moment formulas.
- [x] Direct repository source check and umbrella import.
- [x] Six transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
