# Holomorphic edge zeros force Liouville power saving

- **ID:** B130-local-zero-classification
- **Stage:** 3-formalized
- **Type:** THEOREM — formalized
- **Source:** Local residue classification and the existing edge-divisor theorem.

## Theorem

An individual gauge fibre admits a holomorphic germ at one that vanishes
there iff `Σ_p |χ_x(p)+1| p^(-σ)<∞` for some `1/2<σ<1`.
The zero is simple. The associated meromorphic continuation has
the opposite divisor to ζ on a half-plane extending left of one.

## Dependency-closed proof

Let `y` reverse every prime phase of `x`. The first-order Euler terms
cancel, giving `F_x F_y=E_x`, where
`E_x=exp(h_x+h_y)` is holomorphic and nowhere zero on `Re s>1/2`.
This proves the required product identity directly from the established
Euler logarithm and analytic remainder, for all unimodular prime phases.

Suppose the local holomorphic germ `G=F_x` vanishes at one. Divide out
its zero: `D(s)=G(s)/(s-1)`, extended at one by `G′(1)`. Analyticity of
this divided difference is standard. The existing universal edge bound
`|F_x(1+δ)|≥c δ`, `c>0`, and continuity imply `|D(1)|≥c`; hence the zero
is simple. Then `U=E_x/D` is holomorphic near one, nonzero there, and
agrees with `(s-1)F_y`. The local residue classification forces
`Σ_p |χ_y(p)-1|p^(-σ)<∞` for some `1/2<σ<1`. Since
`χ_y=-χ_x` at primes, this is the asserted Liouville power saving.

Conversely this summability gives a nonzero local residue `U` for `F_y`.
The germ `(s-1)E_x/U` is holomorphic, vanishes at one, and equals `F_x`
on the Euler side. Its derivative at one is `E_x(1)/U(1)≠0`.

For the exact continuation let `H_y` be the isozeric exponent of `F_y`
and put `J_x=h_x+h_y-H_y`. It is holomorphic on `Re s>σ`.
The explicit continuation is `(s-1)exp(J_x)/Z(s)`, with `Z=(s-1)ζ`.
It equals `F_x` on the Euler half-plane, has a simple zero at one, and
agrees with the given germ by analytic uniqueness. Away from one it is
`exp(J_x)/ζ`, so its meromorphic order is exactly the negative of ζ's
order. No extra summability or continuation input is assumed.

## Corpus boundary

`TheEdgeDivisorOfAFibre.edgeZero_iff_antiPretentious` characterizes the
radial edge-zero bound by harmonic quadratic energy.
`eventually_mul_le_norm_gaugeFibre` already bounds edge-zero order by one.
`TheNaturalBoundaryIsLiouvilleOdd.tsum_mul_tsum_twin` proves the product
identity for order-two phases; general unimodular phases remain to check.
The power saving and reciprocal-ζ divisor classification are
stronger than those statements. Search found those predecessors, not
the target. No external novelty claim; no B130 arithmetic estimate.

## Lean result

`GaugeDeformations/LocalZeroClassification.lean` proves:

- `deriv_ne_zero_of_local_gauge_zero`: every holomorphic edge zero is simple.
- `liouville_power_saving_of_local_zero`: absolute Liouville summability
  at an exponent in `(1/2,1)` follows from the given zero germ.
- `local_gauge_zero_iff`: the exact equivalence for every gauge.
- `liouvilleContinuation_order`: the continuation has meromorphic order
  exactly `-meromorphicOrderAt ζ` away from one.
- `local_zero_reciprocal_continuation`: the given germ extends to this
  explicit meromorphic function on a half-plane left of one.

The phase reversal and actual fibre product identity are proved for all
unimodular gauge phases. The four capstone axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Final direct Lean check
passed without warnings.

[Uniform family result: a common half-plane for joint pole germs](joint-pole-germs-force-a-common-isozeric-half-plane.md).
