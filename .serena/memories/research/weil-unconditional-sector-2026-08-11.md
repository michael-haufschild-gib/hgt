# The unconditional sector of the resolvent Hankel criterion (step 27)

Assignment: close the gap `M(X) ≤ 2H/(X+1)²` vs `0` at one finite shift. Verdict: the gap IS RH —
the corpus converse (`riemannHypothesis_of_forall_xiResolventHankelForm_re_nonneg`) converts any
unconditional full-Hankel positivity at one shift into RH, so only the *sector* was closable.

## New modules (all unconditional, axioms clean)
- `RHTower/XiResolventUnconditionalSector.lean`:
  - `re_pow_pos_of_sector` : `(2n+1)|Im z| < Re z → 0 < Re z^(n+1)` — closed-form sector power law
    (Bernoulli induction `(a−nb)aⁿ ≤ (a−b)ⁿa` + `geom_sum₂_mul` drift bound; no trig, no sqrt).
  - `sector_xiSpectralSq_add` / `sector_xiResolventPoint` : divisor cone `(2n+1)|Im| < Re` at
    `X ≥ ((2n+1)²+1)/4` (height gap + strip + AM-GM discriminant trick).
  - `xiResolventMoment_re_pos_of_add_one_sq_le` : **every moment Rₙ(X) > 0 for X ≥ (n+1)²** —
    unbounded degree, quadratic shift law.
  - `xiResolventHankelForm_re_nonneg_of_nonneg(_of_sq_le)`, `_re_pos_of_nonneg` : Hankel form
    positive on the nonneg-coefficient cone at `X ≥ (2N+1)²`.
  - `exists_coeff_neg_and_pos_of_xiResolventHankelForm_re_neg` : negativity witnesses change sign.
- `RHTower/XiSquaredCompleteMonotonicityFarRay.lean`:
  - `xiShiftedReciprocalSquare_eq_xiResolventPoint`, `xiShiftedReciprocalMoment_eq_xiResolventMoment`
    (the two moment charts are THE SAME object), `xiResolventMoment_im_eq_zero` (moments real).
  - `alternating_iteratedDeriv_squaredXiRadialField_pos_of_sq_le` : **(−1)ⁿ g⁽ⁿ⁾(y) > 0 for ALL n
    once y ≥ (n+1)²**, g = ξ′(1/2+√y)/(2√y ξ(1/2+√y)); `_of_le_or_far` : union with corpus n ≤ 18.

## Corpus assets discovered (avoid re-deriving)
- `HTGeometry/SectorPowerPositivity.lean`: tangent-addition sector calculus
  (`re_mul_pos_and_abs_im_le`, budget chain `re_pow_pos_and_abs_im_le_of_chain`, 7 powers at 1/5).
  Closed form loses factor ≈ π vs the chain (m ≈ 1/(2c) vs (π/2)/c) — sharpening candidate.
- `RHTower/SquaredXiCompleteMonotonicity.lean`: CM through order 18 on all y > 0; derivative ladder
  `hasDerivAt_xiShiftedReciprocalMoment` (d/dv Rₙ = −(n+1)R_{n+1});
  `iteratedDeriv_squaredXiRadialField`; moment realness; arithmetic identification on the ray;
  stronger height gaps `xiZeroCopy_fortyOne_div_two_lt_im_sq` (20.5 < γ²) and off-line quartet 85.

## Wall status
Obstruction confined to sign-changing bilinear tests, wedge {n ≥ 19, y < (n+1)²} for CM. Blockers:
(1) full-Hankel-unconditional ⇒ RH; (2) step-13b symmetry insufficiency; (3) RH ⟺ Σ‖u‖² = R₁(X)
(realization/GNS wall); (4) degree-2 Turán minor: bulk and negative core decay at the SAME X⁻⁶ rate.
External calibration: resolvent-chart analogue of Bombieri short-support Weil positivity.

## Next candidates
Heine k-tuple expansion of k×k Hankel determinants (generalizing the pair expansion); π-factor
aperture sharpening via parametric tangent chain; S₁(X) ≤ C·H/√X; quantitative detection floor.
