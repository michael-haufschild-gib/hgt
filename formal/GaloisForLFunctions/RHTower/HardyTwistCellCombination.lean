import GaloisForLFunctions.RHTower.HardyPhaseCellCancellation

/-!
# Cell bounds for a real twisted-phase combination

The real smooth AFE for Hardy's `Z` produces, on every grid cell, integrals of
`a·cos(θ(τ) − τ log n) + b·sin(θ(τ) − τ log n)` with `τ`-independent real coefficients `a, b`
coming from the real and imaginary parts of the AFE weights.  Both are covered by the bare cell
bound, the sine through the quarter-period shift `sin t = cos(t − π/2)`.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

theorem continuous_hardyTwistPhase (L : ℝ) : Continuous (hardyTwistPhase L) :=
  continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_hardyTwistPhase L τ).continuousAt

theorem intervalIntegrable_cos_hardyTwistPhase (L φ u v : ℝ) :
    IntervalIntegrable (fun τ => Real.cos (hardyTwistPhase L τ + φ)) volume u v :=
  (Real.continuous_cos.comp
    ((continuous_hardyTwistPhase L).add continuous_const)).intervalIntegrable u v

theorem intervalIntegrable_sin_hardyTwistPhase (L u v : ℝ) :
    IntervalIntegrable (fun τ => Real.sin (hardyTwistPhase L τ)) volume u v :=
  (Real.continuous_sin.comp (continuous_hardyTwistPhase L)).intervalIntegrable u v

/-- **The cell bound for a real combination of the two twisted phases.** -/
theorem abs_integral_hardyTwistCombination_le {u v L δ T a b : ℝ} (huv : u ≤ v) (hδ : 0 < δ)
    (hT : 0 < T) (hu : T ≤ u)
    (herr : 33 / (16 * T ^ (2 : ℕ)) + Real.pi / (2 * T) ≤ δ)
    (hL : L ≤ Real.log (T / (2 * Real.pi)) / 2 - 2 * δ) :
    |∫ τ in u..v, (a * Real.cos (hardyTwistPhase L τ)
        + b * Real.sin (hardyTwistPhase L τ))|
      ≤ (|a| + |b|) * (2 / δ + (v - u) * (1 / T ^ (2 : ℕ) + Real.pi / (4 * T)) / δ ^ (2 : ℕ)) := by
  set B : ℝ := 2 / δ + (v - u) * (1 / T ^ (2 : ℕ) + Real.pi / (4 * T)) / δ ^ (2 : ℕ) with hB
  have hcosBound : |∫ τ in u..v, Real.cos (hardyTwistPhase L τ)| ≤ B := by
    have h := abs_integral_cos_hardyTwistPhase_le (u := u) (v := v) (L := L) (φ := 0)
      huv hδ hT hu herr hL
    have hcongr : (∫ τ in u..v, Real.cos (hardyTwistPhase L τ + 0))
        = ∫ τ in u..v, Real.cos (hardyTwistPhase L τ) := by
      refine intervalIntegral.integral_congr fun τ _ => ?_
      rw [add_zero]
    rw [hcongr] at h
    exact h
  have hsinBound : |∫ τ in u..v, Real.sin (hardyTwistPhase L τ)| ≤ B := by
    have h := abs_integral_cos_hardyTwistPhase_le (u := u) (v := v) (L := L)
      (φ := -(Real.pi / 2)) huv hδ hT hu herr hL
    have hcongr : (∫ τ in u..v, Real.cos (hardyTwistPhase L τ + -(Real.pi / 2)))
        = ∫ τ in u..v, Real.sin (hardyTwistPhase L τ) := by
      refine intervalIntegral.integral_congr fun τ _ => ?_
      rw [← sub_eq_add_neg, Real.cos_sub_pi_div_two]
    rw [hcongr] at h
    exact h
  have hint₁ : IntervalIntegrable (fun τ => a * Real.cos (hardyTwistPhase L τ)) volume u v := by
    have := (intervalIntegrable_cos_hardyTwistPhase L 0 u v).const_mul a
    simpa using this
  have hint₂ : IntervalIntegrable (fun τ => b * Real.sin (hardyTwistPhase L τ)) volume u v :=
    (intervalIntegrable_sin_hardyTwistPhase L u v).const_mul b
  rw [intervalIntegral.integral_add hint₁ hint₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hBnonneg : 0 ≤ B := le_trans (abs_nonneg _) hcosBound
  calc |a * (∫ τ in u..v, Real.cos (hardyTwistPhase L τ))
        + b * (∫ τ in u..v, Real.sin (hardyTwistPhase L τ))|
      ≤ |a * (∫ τ in u..v, Real.cos (hardyTwistPhase L τ))|
        + |b * (∫ τ in u..v, Real.sin (hardyTwistPhase L τ))| := abs_add_le _ _
    _ = |a| * |∫ τ in u..v, Real.cos (hardyTwistPhase L τ)|
        + |b| * |∫ τ in u..v, Real.sin (hardyTwistPhase L τ)| := by
        rw [abs_mul, abs_mul]
    _ ≤ |a| * B + |b| * B := by
        gcongr
    _ = (|a| + |b|) * B := by ring

/-- **The cell bound for one AFE term.**  A twisted-phase term with a `τ`-independent complex
weight `w` and amplitude `(√n)⁻¹` obeys the bare cell bound scaled by `(√n)⁻¹(|Re w| + |Im w|)`. -/
theorem abs_integral_afeTerm_le {u v L δ T c : ℝ} (hc : 0 ≤ c) {w : ℂ} (huv : u ≤ v) (hδ : 0 < δ)
    (hT : 0 < T) (hu : T ≤ u)
    (herr : 33 / (16 * T ^ (2 : ℕ)) + Real.pi / (2 * T) ≤ δ)
    (hL : L ≤ Real.log (T / (2 * Real.pi)) / 2 - 2 * δ) :
    |∫ τ in u..v, c * (Real.cos (hardyTwistPhase L τ) * w.re
        - Real.sin (hardyTwistPhase L τ) * w.im)|
      ≤ c * (|w.re| + |w.im|) *
        (2 / δ + (v - u) * (1 / T ^ (2 : ℕ) + Real.pi / (4 * T)) / δ ^ (2 : ℕ)) := by
  have hrw : (∫ τ in u..v, c * (Real.cos (hardyTwistPhase L τ) * w.re
        - Real.sin (hardyTwistPhase L τ) * w.im))
      = c * ∫ τ in u..v, (w.re * Real.cos (hardyTwistPhase L τ)
          + (-w.im) * Real.sin (hardyTwistPhase L τ)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    ring
  rw [hrw, abs_mul, abs_of_nonneg hc]
  have hmain := abs_integral_hardyTwistCombination_le (u := u) (v := v) (L := L) (δ := δ)
    (T := T) (a := w.re) (b := -w.im) huv hδ hT hu herr hL
  rw [abs_neg] at hmain
  calc c * |∫ τ in u..v, (w.re * Real.cos (hardyTwistPhase L τ)
        + (-w.im) * Real.sin (hardyTwistPhase L τ))|
      ≤ c * ((|w.re| + |w.im|) *
          (2 / δ + (v - u) * (1 / T ^ (2 : ℕ) + Real.pi / (4 * T)) / δ ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hmain hc
    _ = c * (|w.re| + |w.im|) *
        (2 / δ + (v - u) * (1 / T ^ (2 : ℕ) + Real.pi / (4 * T)) / δ ^ (2 : ℕ)) := by ring

end RHTower

end
