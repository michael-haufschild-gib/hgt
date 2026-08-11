import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Ridge-matched coherence barrier

Very small singular packets do not automatically create large regularized cross coherence.  If
one synthesis packet has unregularized Rayleigh energy at most `ε r`, Cauchy--Schwarz bounds its
coupling square by the exact visibility factor `ε / (1 + ε)`.  Crossing the Route-G threshold
`1 / 15` therefore forces both packets above the ridge-scale floor `r / 14`.

These are Hilbert-space inequalities.  No spectral, zero-spacing, simplicity, or arithmetic
premise is built into them.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H X Y : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

/-- Tikhonov energy of one synthesis coordinate. -/
def ridgeSynthesisEnergy (S : X →L[ℂ] H) (r : ℝ) (x : X) : ℝ :=
  ‖S x‖ ^ 2 + r * ‖x‖ ^ 2

/-- Squared Hilbert coupling is bounded by the product of the two synthesis energies. -/
theorem cross_inner_norm_sq_le
    (A : X →L[ℂ] H) (C : Y →L[ℂ] H) (x : X) (y : Y) :
    ‖inner ℂ (A x) (C y)‖ ^ 2 ≤ ‖A x‖ ^ 2 * ‖C y‖ ^ 2 := by
  have hcs : ‖inner ℂ (A x) (C y)‖ ≤ ‖A x‖ * ‖C y‖ :=
    norm_inner_le_norm _ _
  have hcross : 0 ≤ ‖inner ℂ (A x) (C y)‖ := norm_nonneg _
  have hprod : 0 ≤ ‖A x‖ * ‖C y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [mul_nonneg (sub_nonneg.mpr hcs) (add_nonneg hprod hcross)]

/-- A right packet whose unregularized synthesis energy is at most `ε r` times its coefficient
mass has normalized coupling square at most `ε / (1 + ε)`.  The division-free statement also
covers zero packets. -/
theorem cross_sq_visibility_le_right
    (A : X →L[ℂ] H) (C : Y →L[ℂ] H) (r ε : ℝ) (x : X) (y : Y)
    (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hsmall : ‖C y‖ ^ 2 ≤ ε * r * ‖y‖ ^ 2) :
    (1 + ε) * ‖inner ℂ (A x) (C y)‖ ^ 2 ≤
      ε * ridgeSynthesisEnergy A r x * ridgeSynthesisEnergy C r y := by
  have hcs := cross_inner_norm_sq_le A C x y
  have hA : ‖A x‖ ^ 2 ≤ ridgeSynthesisEnergy A r x := by
    simp only [ridgeSynthesisEnergy]
    nlinarith [mul_nonneg hr (sq_nonneg ‖x‖)]
  have hA0 : 0 ≤ ridgeSynthesisEnergy A r x :=
    (sq_nonneg ‖A x‖).trans hA
  have hC : (1 + ε) * ‖C y‖ ^ 2 ≤
      ε * ridgeSynthesisEnergy C r y := by
    simp only [ridgeSynthesisEnergy]
    nlinarith
  calc
    (1 + ε) * ‖inner ℂ (A x) (C y)‖ ^ 2
        ≤ (1 + ε) * (‖A x‖ ^ 2 * ‖C y‖ ^ 2) := by gcongr
    _ = ‖A x‖ ^ 2 * ((1 + ε) * ‖C y‖ ^ 2) := by ring
    _ ≤ ridgeSynthesisEnergy A r x *
        (ε * ridgeSynthesisEnergy C r y) := by gcongr
    _ = ε * ridgeSynthesisEnergy A r x * ridgeSynthesisEnergy C r y := by ring

/-- Left-coordinate version of `cross_sq_visibility_le_right`. -/
theorem cross_sq_visibility_le_left
    (A : X →L[ℂ] H) (C : Y →L[ℂ] H) (r ε : ℝ) (x : X) (y : Y)
    (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hsmall : ‖A x‖ ^ 2 ≤ ε * r * ‖x‖ ^ 2) :
    (1 + ε) * ‖inner ℂ (A x) (C y)‖ ^ 2 ≤
      ε * ridgeSynthesisEnergy A r x * ridgeSynthesisEnergy C r y := by
  have h := cross_sq_visibility_le_right C A r ε y x hr hε hsmall
  calc
    (1 + ε) * ‖inner ℂ (A x) (C y)‖ ^ 2 =
        (1 + ε) * ‖inner ℂ (C y) (A x)‖ ^ 2 := by rw [norm_inner_symm]
    _ ≤ ε * ridgeSynthesisEnergy C r y * ridgeSynthesisEnergy A r x := h
    _ = ε * ridgeSynthesisEnergy A r x * ridgeSynthesisEnergy C r y := by ring

/-- Crossing the Suzuki high-assistance threshold forces both synthesis packets above the exact
ridge-scale floor `r / 14`. -/
theorem cross_sq_gt_oneFifteenth_forces_ridge_matched
    (A : X →L[ℂ] H) (C : Y →L[ℂ] H) (r : ℝ) (x : X) (y : Y)
    (hr : 0 ≤ r)
    (hcoh : ridgeSynthesisEnergy A r x * ridgeSynthesisEnergy C r y / 15 <
      ‖inner ℂ (A x) (C y)‖ ^ 2) :
    r * ‖x‖ ^ 2 / 14 < ‖A x‖ ^ 2 ∧
      r * ‖y‖ ^ 2 / 14 < ‖C y‖ ^ 2 := by
  constructor
  · by_contra h
    have hsmall : ‖A x‖ ^ 2 ≤ (1 / 14 : ℝ) * r * ‖x‖ ^ 2 := by
      have := le_of_not_gt h
      nlinarith
    have hvis := cross_sq_visibility_le_left A C r (1 / 14) x y hr (by norm_num) hsmall
    nlinarith
  · by_contra h
    have hsmall : ‖C y‖ ^ 2 ≤ (1 / 14 : ℝ) * r * ‖y‖ ^ 2 := by
      have := le_of_not_gt h
      nlinarith
    have hvis := cross_sq_visibility_le_right A C r (1 / 14) x y hr (by norm_num) hsmall
    nlinarith

end GaloisForLFunctions.HTGeometry
