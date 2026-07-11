# Modulus-slope field: the subharmonicity constraint at all scales

- **ID:** modulus-slope-field
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RHTower route review (logs/rhtower-route-review-2026-07-11.md), route 5 — modulus holography / charge tomography
- **Statement:** The two-circle slope `modulusSlope ρ r₁ r₂` of the circle average of `log‖ξ‖` is, at every center and every radius pair `0 < r₁ < r₂`, a nonnegative field, monotone in the radius pair (convexity of the circle average in `log r`), bracketed by the enclosed divisor mass `n(r₁) ≤ slope ≤ n(r₂)`; a sample vanishes iff the enclosed open ball is ξ-zero-free; and RH ⟺ the field is flat over every right-half-contained radius pair.

## Goal

Upgrade the tomography criterion (`rh_iff_forall_modulusSlope_eq_zero`, germ radii only) to a
single constrained object at all scales, with both surfaces of the constraint explicit:

- **Disproof surface:** `not_riemannHypothesis_of_modulusSlope_ne_zero` — ONE nonzero slope
  sample over a right-half-contained ball refutes RH.  Two circle averages of `log‖ξ‖` at any
  fixed scale; no shrinking radii, no located zero, no phase.  This is a finite, numerically
  certifiable object (two integrals of `log|ξ|` plus a strict inequality).
- **Proof surface:** `rh_iff_forall_rightHalf_modulusSlope_eq_zero` — RH is the flatness of the
  field, with no `∃R₀` germ quantifier.  Vanishing propagates downward through the convexity law
  (`modulusSlope_eq_zero_of_outer_eq_zero`), so one flat sample per point decides the whole ball
  below it.

Non-circularity: everything is unconditional bookkeeping on Jensen's formula; the only RH-grade
content is on the two surfaces, stated as such.

## Gates
- [x] 0 → 1  in-progress: well-posed (field + three laws), source-pure (mathlib Jensen), attack executed
- [x] 1 → 2  fully-proven: the two-radius Jensen difference is an exact weighted divisor sum; all laws follow
- [x] 2 → 3  formalized: `formal/GaloisForLFunctions/RHTower/ModulusSlopeField.lean`;
      `lake build GaloisForLFunctions.RHTower.ModulusSlopeField` green; static lint passed;
      `#print axioms` on all seven capstones = `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready

## Lean surface

| Theorem | Content |
|---|---|
| `xi_circleAverage_sub_eq_divisor_sum` | `A(r₂)−A(r₁) = ∑_{‖u−ρ‖≤r₂} ord_u(ξ)·w(u)`, `w = log r₂ − log(max r₁ ‖u−ρ‖)` |
| `modulusSlope_nonneg` | field ≥ 0 (two-radius subharmonicity of `log‖ξ‖`) |
| `ballOrderSum_le_modulusSlope`, `modulusSlope_le_ballOrderSum` | `n(r₁) ≤ slope(r₁,r₂) ≤ n(r₂)` |
| `modulusSlope_radii_mono` | slope monotone in the radius pair (convexity in `log r`) |
| `modulusSlope_eq_zero_of_outer_eq_zero` | flatness propagates downward |
| `modulusSlope_eq_zero_iff_ball_zeroFree` | one vanishing sample ⟺ enclosed open ball zero-free |
| `modulusSlope_eq_ballOrderSum_of_annulus_zeroFree` | exact integer readoff at every zero-free annulus |
| `not_riemannHypothesis_of_modulusSlope_ne_zero` | disproof surface: one nonzero right-half sample ⟹ ¬RH |
| `rh_iff_forall_rightHalf_modulusSlope_eq_zero` | proof surface: RH ⟺ field flat, all scales, no germ quantifier |

## Approach

Two-radius difference of mathlib's Jensen formula (`MeromorphicOn.circleAverage_log_norm`): the
trailing coefficient is radius-free and cancels, leaving the exact weighted divisor sum.  All
laws are Finset estimates on that sum.  Zeros on the outer circle carry weight zero, so the
dichotomy reads the OPEN ball — the field cannot see its own boundary.

## Next (opened by this card)

- The proof surface now asks for a *convexity-forcing* input: what constraint on ξ (FE +
  growth + Euler side) bounds `modulusSlope` from ABOVE at large scales?  The bracketing
  `slope ≤ n(r₂)` combined with `XiZeroDensity`/`CompletedZetaGrowth` gives upper bounds; the
  open question is a lower-bound mechanism forcing flat samples at right-half centers.
- The disproof surface is a numeric target: certified quadrature of two circle averages of
  `log|ξ|` with interval arithmetic.  Sits next to the clean-radii selectors
  (`exists_two_radii_avoiding_xi_zeros`).
- Weld the field to the deck/ladder column: `modulusSlope` at level `2^k` reads the rung
  (`rhLadder_iff_circleAverage_slope_exp_eq_one`); the new all-scale laws transport those
  criteria off the germ.

## Log
- 2026-07-11 — created directly at 3-formalized; module compiled clean on first pass, axiom-clean.
