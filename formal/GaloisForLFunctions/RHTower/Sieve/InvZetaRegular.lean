import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.Sieve.TruncatedContourShift

/-!
# The regular reciprocal of zeta

`riemannZeta` is the analytic continuation, which has a pole at `s = 1`; the value assigned there is
a junk value, nonzero by `riemannZeta_one_ne_zero`.  Consequently `fun s => (riemannZeta s)⁻¹` takes
a nonzero value at `1` while its limit there is `0`: it is discontinuous at exactly the point a
contour from `re s > 1` to `re s < 1` must cross, so Cauchy's theorem cannot be applied to it.

Mathematically there is no singularity — `ζ` has a simple pole, so `1/ζ` has a removable singularity
at `1` with value `0`.  The corrected function is obtained from the entire unit
`G(s) = (s-1)·ζ(s)` (`zetaResidueUnit`) as

`invZeta s = (s - 1) · G(s)⁻¹`,

which needs no case split: away from `1` the factor `(s-1)` cancels against the one inside `G`, and
at `1` it vanishes, supplying the removable value.  So `invZeta` agrees with `1/ζ` off the pole, is
differentiable wherever `ζ` is nonvanishing, and is differentiable at `1` itself.
-/

namespace RHTower.Sieve

open Complex RHTower GaloisForLFunctions.HTGeometry

/-- **The regular reciprocal of zeta.**  The removable-singularity correction of `1/ζ` at `s = 1`. -/
noncomputable def invZeta (s : ℂ) : ℂ := (s - 1) * (zetaResidueUnit s)⁻¹

/-- Off the pole, `invZeta` is the reciprocal of zeta. -/
theorem invZeta_eq_inv {s : ℂ} (hs : s ≠ 1) : invZeta s = (riemannZeta s)⁻¹ := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  simp only [invZeta, zetaResidueUnit, Function.update_of_ne hs, mul_inv]
  rw [← mul_assoc, mul_inv_cancel₀ hs1, one_mul]

/-- At the pole the corrected value is `0` — the value of the analytic continuation of `1/ζ`. -/
@[simp] theorem invZeta_one : invZeta 1 = 0 := by simp [invZeta]

/-- Off the pole, the unit vanishes exactly where zeta does. -/
theorem zetaResidueUnit_ne_zero_iff {s : ℂ} (hs : s ≠ 1) :
    zetaResidueUnit s ≠ 0 ↔ riemannZeta s ≠ 0 := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  simp [zetaResidueUnit, Function.update_of_ne hs, hs1]

/-- **The Riemann hypothesis as nonvanishing of the entire zeta unit.**  Off the pole the unit
`(s-1)·ζ(s)` vanishes exactly where `ζ` does, and at the pole itself it takes the residue value, so
no exclusion is needed on the right of the critical line. -/
theorem riemannHypothesis_iff_zetaResidueUnit_ne_zero :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → zetaResidueUnit s ≠ 0 := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  constructor
  · intro h s hs
    rcases eq_or_ne s 1 with rfl | hne
    · rw [zetaResidueUnit_one]; norm_num
    · exact (zetaResidueUnit_ne_zero_iff hne).mpr (h s hs)
  · intro h s hs
    rcases eq_or_ne s 1 with rfl | hne
    · exact riemannZeta_ne_zero_of_one_le_re (by simp)
    · exact (zetaResidueUnit_ne_zero_iff hne).mp (h s hs)

/-- `invZeta` is differentiable wherever the entire unit is nonvanishing. -/
theorem differentiableAt_invZeta {s : ℂ} (h : zetaResidueUnit s ≠ 0) :
    DifferentiableAt ℂ invZeta s :=
  (differentiableAt_id.sub_const 1).mul
    (((analyticAt_zetaResidueUnit s).differentiableAt).inv h)

/-- Away from the pole, nonvanishing of zeta suffices. -/
theorem differentiableAt_invZeta_of_zeta_ne_zero {s : ℂ} (hs : s ≠ 1) (h : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ invZeta s :=
  differentiableAt_invZeta ((zetaResidueUnit_ne_zero_iff hs).2 h)

/-- **The pole is no obstruction.**  `invZeta` is differentiable at `s = 1` itself. -/
theorem differentiableAt_invZeta_one : DifferentiableAt ℂ invZeta 1 :=
  differentiableAt_invZeta (by rw [zetaResidueUnit_one]; norm_num)

/-- The norm of the correction agrees with the norm of the reciprocal off the pole, so every bound
proved for `‖1/ζ‖` transfers verbatim. -/
theorem norm_invZeta_eq {s : ℂ} (hs : s ≠ 1) : ‖invZeta s‖ = ‖(riemannZeta s)⁻¹‖ := by
  rw [invZeta_eq_inv hs]

/-- **`invZeta` is holomorphic on a zero-free strip.**  The hypothesis is only about zeros of `ζ`;
the pole is handled by the correction.  This is the hypothesis
`integral_vertical_sub_eq_horizontal` consumes. -/
theorem differentiableOn_invZeta_verticalStrip {c d : ℝ}
    (h : ∀ s ∈ verticalStrip c d, s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ invZeta (verticalStrip c d) := by
  intro s hs
  rcases eq_or_ne s 1 with rfl | hs1
  · exact differentiableAt_invZeta_one.differentiableWithinAt
  · exact (differentiableAt_invZeta_of_zeta_ne_zero hs1 (h s hs hs1)).differentiableWithinAt

/-- **The truncated contour shift for the reciprocal of zeta.**  Specialisation of Cauchy's theorem
on the rectangle to `invZeta`, with the single hypothesis that `ζ` has no zeros in the strip. -/
theorem integral_invZeta_vertical_sub_eq_horizontal {c d : ℝ} (hcd : c ≤ d)
    (h : ∀ s ∈ verticalStrip c d, s ≠ 1 → riemannZeta s ≠ 0) (T : ℝ) :
    (Complex.I • (∫ y : ℝ in (-T)..T, invZeta ((d : ℂ) + (y : ℝ) * Complex.I)))
        - Complex.I • (∫ y : ℝ in (-T)..T, invZeta ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
  integral_vertical_sub_eq_horizontal hcd (differentiableOn_invZeta_verticalStrip h) T

/-!
## The rectangle form

The zero-free region of `ζ` narrows as the height grows, so no strip `c ≤ re s ≤ d` with `c < 1` is
zero-free.  Cauchy's theorem on the truncated rectangle needs holomorphy only on that rectangle, and
for each fixed height `T` a zero-free rectangle does exist.  These are the forms the assembly uses.
-/

/-- **The truncated contour shift, rectangle hypothesis.**  Holomorphy is required only on the
rectangle actually integrated over, not on the whole strip. -/
theorem integral_vertical_sub_eq_horizontal_rect {G : ℂ → ℂ} {c d : ℝ} (T : ℝ)
    (hdiff : DifferentiableOn ℂ G (Set.uIcc c d ×ℂ Set.uIcc (-T) T)) :
    (Complex.I • (∫ y : ℝ in (-T)..T, G ((d : ℂ) + (y : ℝ) * Complex.I)))
        - Complex.I • (∫ y : ℝ in (-T)..T, G ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ x : ℝ in c..d, G ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in c..d, G ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
  have hz : ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re = c := by simp
  have hz' : ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im = -T := by simp
  have hw : ((d : ℂ) + ((T : ℝ) : ℂ) * Complex.I).re = d := by simp
  have hw' : ((d : ℂ) + ((T : ℝ) : ℂ) * Complex.I).im = T := by simp
  have hsub : DifferentiableOn ℂ G
      (Set.uIcc ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re
          ((d : ℂ) + ((T : ℝ) : ℂ) * Complex.I).re ×ℂ
        Set.uIcc ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im
          ((d : ℂ) + ((T : ℝ) : ℂ) * Complex.I).im) := by
    rw [hz, hz', hw, hw']
    exact hdiff
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
    ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ((d : ℂ) + ((T : ℝ) : ℂ) * Complex.I) hsub
  rw [hz, hz', hw, hw'] at hcauchy
  linear_combination hcauchy

/-- **`invZeta` is holomorphic on a zero-free rectangle.**  As with the strip form, the hypothesis
constrains only the zeros of `ζ`; the pole at `s = 1` is absorbed by the correction. -/
theorem differentiableOn_invZeta_rect {c d T : ℝ}
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ invZeta (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  intro s hs
  rcases eq_or_ne s 1 with rfl | hs1
  · exact differentiableAt_invZeta_one.differentiableWithinAt
  · exact (differentiableAt_invZeta_of_zeta_ne_zero hs1 (h s hs hs1)).differentiableWithinAt

/-- **The truncated contour shift for `1/ζ`, at a fixed height.**  The only hypothesis is that `ζ`
has no zeros in the rectangle `[c,d] × [-T,T]` — a condition the classical zero-free region supplies
for each `T` with `c = 1 - c₀/log T`.  The pole of `ζ` inside the rectangle costs nothing. -/
theorem integral_invZeta_vertical_sub_eq_horizontal_rect {c d T : ℝ}
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) :
    (Complex.I • (∫ y : ℝ in (-T)..T, invZeta ((d : ℂ) + (y : ℝ) * Complex.I)))
        - Complex.I • (∫ y : ℝ in (-T)..T, invZeta ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
  integral_vertical_sub_eq_horizontal_rect T (differentiableOn_invZeta_rect h)

end RHTower.Sieve
