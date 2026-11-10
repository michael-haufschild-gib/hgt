# Compact divisor rigidity of pole-preserving gauge families

- **ID:** B130-gauge-family-divisor
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Quadratic gauge rigidity; F3/B142.
- **Statement:** Compact-open specialization of actual regularized gauge fibres to ζ eventually fixes the exact zero divisor on every compact subset.

## Exact theorem

Fix `1/2≤c<1`. For an arbitrary filter, let `U_i` be holomorphic on
`Ω_c={Re s>c}`, agree with `(s-1)F_{x_i}(s)` for `Re s>1`, and converge
locally uniformly on `Ω_c` to the entire residue factor `Z=(s-1)ζ(s)`.

For every compact `K⊂Ω_c`, eventually

`∀s∈K, ord_s U_i = ord_s Z`.

Thus both zero locations and multiplicities eventually agree on `K`.
The eventual index may depend on `K`. Real nonvanishing, quadratic prime
summability, and derivative convergence are derived, not additional inputs.
No existence of a nontrivial family is asserted.

## Proof

Choose `c<c'<1` below the real parts of all points of `K`. The function
`Z` is nonzero on the compact real interval `[c',1]`; locally uniform
convergence makes `U_i` nonzero there eventually. Above one the actual
Euler product is nonzero. Hence quadratic gauge rigidity applies on
`Re s>c'`, giving the paired divisor identity and excluding zeros outside
zeta's zero set.

At each fixed point `ρ`, the order `m=ord_ρ Z` is finite, and Schwarz
reflection gives `ord_conj(ρ) Z=m`. Locally uniform holomorphic convergence
gives convergence of the `m`th derivatives at both points to nonzero
values. Thus the two orders of `U_i` are at most `m` eventually. Their
sum is exactly `2m` by paired-divisor conservation, so each equals `m`.
This proves pointwise eventual multiplicity equality, including at the pole.

The zeros of the nontrivial entire function `Z` in `K` form a finite set.
Intersect their eventual multiplicity assertions with the eventual paired
zero-support law. At every remaining point of `K`, both orders are zero.
This gives simultaneous equality throughout `K`.

## Lean and audit

Module: `ArithmeticWeightTheory/GaugeDeformations/CompactDivisorRigidity.lean`.
Imported by the `ArithmeticWeightTheory` umbrella.

- `eventually_gauge_order_eq` — eventual equality at each fixed point.
- `eventually_gauge_divisor_eq_on_compact` — simultaneous equality on every compact subset.

The final direct Lean check passed. Both transitive audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.

## Novelty and boundary

Ordinary locally uniform holomorphic convergence preserves total multiplicity
in isolating disks, while zeros may move. Here the actual Euler identity
fixes the possible locations, and paired conservation forces each individual
multiplicity to stabilize. The existing absolute-perturbation isozericity
theorem instead assumes absolute weighted prime summability. Neither that
summability nor real nonvanishing is assumed here.

Corpus searches found compact Rouché domination, finite compact zero sets,
and derivative convergence, but not this exact gauge-family conclusion.
The proof uses the [quadratic paired-divisor theorem](quadratic-gauge-rigidity-at-the-zeta-fibre.md).
No external novelty claim.

This constrains a compact-open pole-only specialization at ζ. It constructs
neither a purity family nor B130's arithmetic Stepanov bound. B130 remains open.
