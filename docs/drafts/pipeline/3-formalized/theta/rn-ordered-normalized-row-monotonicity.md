# RN: strict decrease of an ordered normalized kernel row

- **ID:** RN-P-7c
- **Stage:** 3-formalized
- **Type:** THEOREM; formalized and audited
- **Source:** RN-P-7b coupled affine-interpolation equations; `ThetaTailTwoPointPositivity.strictMonoOn_decaySlope_div`.
- **Statement:** For every `x≥0`, `y↦H(x,y)/(k(x)k(y))` is strictly decreasing on `[x,∞)`.

## Goal

Replace the false uniform row-curvature assumption with a literal-source
ordering law that can constrain the coefficients in the actual Schur
projection. This is a stronger row comparison than the already proved
`L(x,y)<L(x,x)` for `x<y`. It does not by itself settle the coupled
two-row affine intersection or arbitrary-rank positivity.

## Gates

- [x] Corpus search and existing source theorem inspected.
- [x] Dependency-closed paper proof below.
- [x] Lean formalization, wiring, axiom audit and final direct leaf audit.

Lean: `ThetaTailOrderedRowMonotonicity.lean`, namespace `RHTower.ThetaTailRow`.
`deriv_normalized_neg` and `strictAntiOn_normalized_row` passed the targeted
`lake --old build` and final `lake env lean GaloisForLFunctions/RHTower/ThetaTailOrderedRowMonotonicity.lean`
audit. Both axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

## Paper proof [PROVED HERE]

Write `k=thetaCuspFullSource`, `p=-(log k)'`,
`L(x,y)=H(x,y)/(k(x)k(y))`. The corpus proves positivity and Schwartz
regularity of `k` and strict increase of `p(z)/z` on the positive ray.
The actual kernel has the common-tail formula

    L(x,y)=∫₀∞ (x+y+2t) a(t) dt,
    a(t)=k(x+t)k(y+t)/(k(x)k(y)).

For fixed `x`, differentiation in `y` is legitimate. Before division by
`k(x)k(y)`, the derivative integrand is
`k(x+t)[k(y+t)+(x+y+2t)k'(y+t)]`. On a compact neighborhood of `y`,
the global Schwartz bounds on `k,k'` dominate its absolute value by
`C(1+|t|)|k(x+t)|`, an integrable function. The quotient denominator is
nonzero. Hence, writing `s(t)=x+y+2t` and
`P(t)=p(x+t)+p(y+t)`,

    ∂ᵧL = ∫₀∞ a(t)[1-s(t)(p(y+t)-p(y))] dt.

Also `a'=-P a`. Schwartz decay gives `t a(t)→0` at infinity and the
factor `t` kills the lower boundary. Thus
`∫₀∞ a(t)[1-tP(t)]dt=0`, and

    ∂ᵧL = ∫₀∞ a(t)[tP(t)-s(t)(p(y+t)-p(y))] dt.       (1)

Take `0≤x≤y`, `y>0`, `t>0`. Strict increase of `p(z)/z` gives

    p(x+t) ≤ (x+t)p(y+t)/(y+t),
    p(y) < y p(y+t)/(y+t).

Using the first inequality and then the second, the bracket in `(1)` obeys

    tP(t)-s(t)(p(y+t)-p(y))
    ≤ s(t)[p(y)-y p(y+t)/(y+t)] < 0.

Since `a(t)>0`, the integral is strictly negative. The derivative therefore
is negative on the interior of `[x,∞)`, including every `y>0` with `y≥x`.
Continuity at the endpoint and the mean-value theorem give strict decrease
on the full interval. The possible point `x=y=0` needs no negative derivative.

## Remaining source problem

This proves an ordered row comparison on paper without either row-curvature
orientation. The next real mathematical burden is a coupled comparison of
two actual rows (and its Schur-projected successors), not another scalar
convexity assertion. No inverse-matrix coefficient signs are inferred from
this statement alone.

## Log

- 2026-10-02 — Derived exact negative integral bracket from the corpus's
  squared-coordinate decay-slope theorem. Deep derivative search completed
  with 64,371 indexed files; source/compiler coverage remains incomplete
  and no applicable duplicate endpoint monotonicity theorem was returned.
  Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` signature
  inspected for the formalization.
