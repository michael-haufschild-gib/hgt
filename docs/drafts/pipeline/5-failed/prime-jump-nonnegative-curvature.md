# Nonnegative pointwise curvature of the cutoff prime generator

- **ID:** DG-PRIME-CD0
- **Stage:** 5-failed
- **Type:** FALSIFIED; positive survivor formalized
- **Source:** `../3-formalized/differential-geometry-four-integrations.md`
- **Statement:** The actual pole-profile prime jump generator does not satisfy
  `Γ₂(f)(x) ≥ 0` for every smooth real function and every point inside the cutoff.

## Exact obstruction

Set `a=log(21/10)`, `l=log 2`, `m=log 3`, and
`f(x)=1946−(156596/15)e^x+(42369/2)e^(2x)−(122059/6)e^(3x)
+9258e^(4x)−(7998/5)e^(5x)`. This function is smooth. The actual cutoff selects
signed indices `2,3,4`, since `exp(2a)=441/100`.
At multiplicative positions `(1/2,2/3,1,4/3,3/2,2)`, its values are
`(8,−8,6,−14,15,0)`. All these positions are strictly within the cutoff.
The four rows needed at `x=log 2` are:

| Position | Targets | Rates |
|---|---|---|
| `2` | `1,2/3,1/2` | `2l/3,5m/9,l/2` |
| `1` | `1/2,2` | `3l/4,3l/4` |
| `2/3` | `4/3,2` | `7l/10,3m/5` |
| `1/2` | `1,3/2,2` | `2l/3,5m/9,l/2` |

Direct substitution in `Γ₂=LΓ/2−Γ(f,Lf)` gives
`Q=(125/3)l²−(13805/216)lm+(1696/81)m²`.
The exact decomposition is

`Q=−(848/405)(2m−3l)(8l−5m)
   −(3229/16200)l(8l−5m)−(14156/2025)l²`.

Here `l>0`, `3l<2m` follows from `8<9`, and `5m<8l` follows from `243<256`.
Therefore `Q<0`. This is a dependency-closed paper proof.

Lean: `RHTower.PrimeCurvatureCounterexample.gammaTwo_witness_eq`,
`gammaTwo_witness_neg`, and `exists_smooth_negative_curvature`, in
`formal/GaloisForLFunctions/RHTower/CCMPrimePoleNegativeCurvature.lean`.
The literal rates, cutoff, and logarithmic shifts are evaluated in Lean; this is
not only an independently defined finite graph. Leaf build passes; the final
existential statement uses only `propext`, `Classical.choice`, and `Quot.sound`.

## No-go closure

- **Exact killing mechanism:** position-dependent prime rates and cutoff produce
  a negative iterated energy even with commuting shifts and a smooth witness.
- **Strongest positive survivor:** for any nonnegative finite jump rates with
  degree bounded by `D`,
  `Γ₂(f) ≥ (Lf)²/2 − D Γ(f)`. The proof completes the two-step square; it does not
  require commuting shifts. For the actual prime generator, `D` is the explicit
  existing prime Schur envelope, proved using Chebyshev and reciprocal-Mangoldt
  estimates. No additional row-bound premise is assumed in this specialization.
- **New insight:** retain the rate defect and quantify its loss. A curvature route
  to Weil positivity must compensate that loss using the actual archimedean and
  pole terms, or study a different combined operator. Commuting shifts alone do
  not give nonnegative curvature for the prime part.
- **Status:** dependency-closed paper proof and Lean proof for both obstruction
  and survivor. Survivor modules `HTGeometry/JumpCurvatureBounds.lean` and
  `RHTower/CCMPrimePoleCurvatureBounds.lean` pass leaf builds and standard-axiom
  audits. The full prime/Gamma source identity is in `CCMWeilJumpEnergy.lean`;
  its arithmetic comparison remains open.

This retires only the blanket nonnegative-curvature assertion for the prime
jump generator. It is not a counterexample to Weil positivity or RH. The original
polynomial witness is not compactly supported. The subsequent
`CCMConstrainedPrimeCurvatureInstability` theorem realizes its six samples on
literal compact smooth exact-pole sources with arbitrarily small complete form
norm and `|Q|`, making point curvature unbounded below there as well. Strong
positive survivor: every finite physical sampling fibre is form-norm dense and
has exactly the original constrained Rayleigh infimum; see
`../3-formalized/rw-finite-sampling-ground-rigidity.md`.

## Log

- 2026-09-28 — exact literal-operator obstruction and quantitative positive
  survivor formalized; no-go closed at this stated scope.
- 2026-09-29 — compact exact-pole source strengthening and exact finite-sample
  ground rigidity formalized; eight public theorems pass direct source and
  standard-axiom audits. A sharper one-direction curvature survivor is under
  final audit in `../2-fully-proven/rw-prime-curvature-one-negative-direction.md`.
