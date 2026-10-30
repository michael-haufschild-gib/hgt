# Completed conductor energies have polynomial bounds

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement and proof

Every fixed positive conductor has `|E_m(c)|≤C_m c²` for `c≥1`.
At affine multiplier zero, `c_m(0)=ϕ(m)` cancels from the global
signed-mean bound, giving `|shellCorrection|≤4(log 4+4)c²` uniformly
in conductor. The reference energy is a fixed constant minus `log c`,
plus a possible pole charge between zero and `c`. Thus its absolute
value is at most a fixed constant times `c²`. Subtract the shell term.
This controls amplification of quantitative Gram errors.

## Lean status

`CompletedConductorEnergiesHavePolynomialBounds.lean` proves both the
conductor-uniform shell bound and each fixed conductor energy bound.
Final direct Lean check passed; both transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella wired.
Supporting estimate; no separate contribution count.
