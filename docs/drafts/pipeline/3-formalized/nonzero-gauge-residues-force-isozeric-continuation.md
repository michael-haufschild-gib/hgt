# Nonzero gauge residues force isozeric continuation

- **ID:** B130-local-residue-classification
- **Stage:** 3-formalized
- **Type:** THEOREM — formalized
- **Source:** Tangent power saving and quadratic gauge rigidity.

## Theorem

For an individual gauge `x`, local holomorphic continuation of
`(s-1)F_x(s)` through one with nonzero value there is equivalent to
`Σ_p |χ_x(p)-1| p^(-σ)<∞` for some `σ<1`.

Thus a local nonzero residue forces a global isozeric continuation
on some half-plane extending left of one. This concerns the individual
fibre, not only a tangent to a parameter family.

## Dependency-closed proof

Write `U=(s-1)F_x` locally at one, with `U(1)≠0`, and
`V(s)=conj(U(conj(s)))`. Schwarz reflection makes `V` holomorphic near
one, with `V(1)≠0`, and regularizes the opposite gauge on the Euler side.
The existing paired Euler identity gives
`UV=Z² exp(-2D+R)`, where `Z=(s-1)ζ`, `D=Σ(1-Re χ_x(p))p⁻ˢ`, and `R`
is holomorphic on `Re s>1/2`.

Differentiating on the Euler side and clearing denominators gives
`P D₁=N`, with `D₁=Σ(1-Re χ_x(p))log(p)p⁻ˢ`,
`P=2ZUV`, and `N=Z(U′V+UV′)-2Z′UV-R′ZUV`.
Both `P,N` are holomorphic near one and `P(1)≠0`. Hence `N/P` continues
`D₁` holomorphically across one. Its coefficients are nonnegative and
its Dirichlet series converges for every real exponent greater than one.
If it converged at no exponent below one, the existing local Landau
noncontinuation theorem at abscissa one would give a contradiction.
Thus `D₁`, and then `D` since `log p≥log 2>0`, converge below one.

Increase this exponent to `τ∈(1/2,1)`. The identity
`|χ_x(p)-1|²=2(1-Re χ_x(p))` gives quadratic energy at `τ=1-δ`.
The existing weighted Cauchy–Schwarz estimate gives absolute
summability at `1-δ/4<1`. The Euler deformation theorem now constructs
`F̃_x=ζ exp(H_x)` on this half-plane. Its regularization agrees with
`U` as a germ by the identity theorem on a small disk at one. Its zeros
and their multiplicities equal those of ζ away from the pole.

Conversely, absolute prime summability at an exponent below one makes
`H_x` holomorphic near one; `Z exp(H_x)` is the required regularization,
with nonzero value `exp(H_x(1))` at one. This proves the equivalence.

All inputs are existing Lean theorems: the paired Euler identity,
derivative series, local Landau theorem, logarithmic-weight removal,
weighted Cauchy–Schwarz, and Euler deformation theorem. No analytic
continuation of an auxiliary series is assumed.

## Novelty and boundary

The corpus theorem `real_nonvanishing_iff_quadratic_summable` assumes
continuation and real nonvanishing on an entire half-plane. The
input is only a neighborhood of the pole. Searches found that theorem
and the tangent power gap, not this local classification. No external
novelty claim. No B130 arithmetic bound is produced.

## Lean result

`GaugeDeformations/LocalResidueClassification.lean` proves:

- `absolute_prime_below_one_of_local_residue`: absolute prime summability
  at an exponent in `(1/2,1)` follows from the given analytic residue germ.
- `local_nonzero_residue_iff`: the exact equivalence for every gauge.
- `local_residue_isozeric_continuation`: the given germ equals `Z exp(H_x)`;
  the actual Euler identity and all ζ zero multiplicities hold on the
  resulting half-plane, away from the pole.

The input is `AnalyticAt U 1`, `U(1)≠0`, and local Euler-side agreement.
No whole-half-plane continuation or real nonvanishing is assumed.
Final direct Lean check passed. All three capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

[Dual classification: holomorphic edge zeros](holomorphic-edge-zeros-force-liouville-power-saving.md).
