/-
# Chen--Gupta--Li Proposition 5.1 axial Fourier tail

Builds the literal nonzero-integer frequency estimate needed after the two
zero-coordinate character correlations in the source `S₁` argument.  The
remaining one-dimensional Fourier tail is dominated by a closed inverse-square
integer series; its finite total is retained symbolically.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51
import GaloisForLFunctions.HTGeometry.IntegerPowerSeriesBounds

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- Punctured integer frequencies for one axial CGL Fourier coordinate. -/
abbrev CGLProposition51PuncturedFrequency := {m : ℤ // m ≠ 0}

/-- The exact, finite mass of the inverse-square punctured integer weight. -/
noncomputable def cglProposition51PuncturedInverseSquareMass : ℝ :=
  ∑' m : CGLProposition51PuncturedFrequency, 1 / ((m.val : ℝ) ^ (2 : ℕ))

theorem cglProposition51_summable_puncturedInverseSquare :
    Summable fun m : CGLProposition51PuncturedFrequency => 1 / ((m.val : ℝ) ^ (2 : ℕ)) := by
  have hbase : Summable fun m : ℤ => 1 / ((m : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  change Summable ((fun m : ℤ => 1 / ((m : ℝ) ^ (2 : ℕ))) ∘ Subtype.val)
  exact hbase.subtype (fun m : ℤ => m ≠ 0)

/-- The all-order cutoff budget is nonnegative. -/
theorem cglSmoothBumpHtAllOrderBudget_nonneg (w : CGLSmoothBump) (n : ℕ) :
    0 ≤ cglSmoothBumpHtAllOrderBudget w n := by
  unfold cglSmoothBumpHtAllOrderBudget
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)

/-- The remaining Fourier coordinate of an axial `S₁` frequency. -/
noncomputable def cglProposition51AxialNonzeroFourierAmplitude
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (t : ℝ) (m : CGLProposition51PuncturedFrequency) : ℂ :=
  (cglAffineFourierScale N Q : ℂ) *
    𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ)
      (cglAffineFourierScale N Q * (m.val : ℝ))

/-- Second-order Fourier decay gives an explicit inverse-square majorant for
the nonzero axial coordinate. -/
theorem norm_cglProposition51AxialNonzeroFourierAmplitude_le_inverseSquare
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (t : ℝ) (m : CGLProposition51PuncturedFrequency) :
    ‖cglProposition51AxialNonzeroFourierAmplitude w N Q t m‖ ≤
      ((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ (2 : ℕ)) *
        (1 + |t|) ^ (2 : ℕ) / cglAffineFourierScale N Q) *
          (1 / ((m.val : ℝ) ^ (2 : ℕ))) := by
  let s : ℝ := cglAffineFourierScale N Q
  let x : ℝ := |(m.val : ℝ)|
  let F : ℝ := ‖𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ)
    (cglAffineFourierScale N Q * (m.val : ℝ))‖
  let B : ℝ := cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ (2 : ℕ)
  have hs : 0 < s := by simpa [s] using cglAffineFourierScale_pos N Q
  have hm : (m.val : ℝ) ≠ 0 := by exact_mod_cast m.property
  have hx : 0 < x := by simpa [x] using abs_pos.mpr hm
  have hsource : (s * x) ^ (2 : ℕ) * F ≤ B * (1 + |t|) ^ (2 : ℕ) := by
    simpa [s, x, F, B, abs_mul, abs_of_pos hs] using
      cglSmoothBumpHt_allOrder_fourier_decay w.toCGLSmoothBump 2 t
        (cglAffineFourierScale N Q * (m.val : ℝ))
  have hden : 0 < s * x ^ (2 : ℕ) := mul_pos hs (pow_pos hx _)
  have hnorm : ‖cglProposition51AxialNonzeroFourierAmplitude w N Q t m‖ = s * F := by
    unfold cglProposition51AxialNonzeroFourierAmplitude
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  rw [hnorm]
  calc
    s * F = ((s * x) ^ (2 : ℕ) * F) / (s * x ^ (2 : ℕ)) := by field_simp
    _ ≤ (B * (1 + |t|) ^ (2 : ℕ)) / (s * x ^ (2 : ℕ)) :=
      div_le_div_of_nonneg_right hsource hden.le
    _ = ((B * (1 + |t|) ^ (2 : ℕ)) / s) * (1 / x ^ (2 : ℕ)) := by field_simp
    _ = _ := by
      dsimp [B, s, x]
      rw [sq_abs]

/-- The absolute sum of the remaining nonzero Fourier coordinate. -/
noncomputable def cglProposition51AxialFrequencyTailMass
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (t : ℝ) : ℝ :=
  ∑' m : CGLProposition51PuncturedFrequency,
    ‖cglProposition51AxialNonzeroFourierAmplitude w N Q t m‖

theorem cglProposition51_axialFrequencyTail_summable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (t : ℝ) :
    Summable fun m : CGLProposition51PuncturedFrequency =>
      ‖cglProposition51AxialNonzeroFourierAmplitude w N Q t m‖ := by
  let C : ℝ :=
    (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ (2 : ℕ) *
      (1 + |t|) ^ (2 : ℕ)) / cglAffineFourierScale N Q
  have hmajor : Summable fun m : CGLProposition51PuncturedFrequency =>
      C * (1 / ((m.val : ℝ) ^ (2 : ℕ))) :=
    cglProposition51_summable_puncturedInverseSquare.mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hmajor
  simpa [C, div_eq_mul_inv, mul_assoc] using
    norm_cglProposition51AxialNonzeroFourierAmplitude_le_inverseSquare w N Q t m

/-- Closed bound for the axial nonzero-frequency Fourier mass.  The only
constant left is the convergent inverse-square integer mass, rather than an
unproved asymptotic placeholder. -/
theorem cglProposition51_axialFrequencyTailMass_le
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (t : ℝ) :
    cglProposition51AxialFrequencyTailMass w N Q t ≤
      ((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ (2 : ℕ)) *
        (1 + |t|) ^ (2 : ℕ) / cglAffineFourierScale N Q) *
          cglProposition51PuncturedInverseSquareMass := by
  let C : ℝ :=
    (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ (2 : ℕ) *
      (1 + |t|) ^ (2 : ℕ)) / cglAffineFourierScale N Q
  have hleft := cglProposition51_axialFrequencyTail_summable w N Q t
  have hright : Summable fun m : CGLProposition51PuncturedFrequency =>
      C * (1 / ((m.val : ℝ) ^ (2 : ℕ))) :=
    cglProposition51_summable_puncturedInverseSquare.mul_left C
  unfold cglProposition51AxialFrequencyTailMass cglProposition51PuncturedInverseSquareMass
  calc
    ∑' m : CGLProposition51PuncturedFrequency,
        ‖cglProposition51AxialNonzeroFourierAmplitude w N Q t m‖ ≤
      ∑' m : CGLProposition51PuncturedFrequency, C * (1 / ((m.val : ℝ) ^ (2 : ℕ))) :=
        hleft.tsum_le_tsum (fun m => by
          simpa [C, div_eq_mul_inv, mul_assoc] using
            norm_cglProposition51AxialNonzeroFourierAmplitude_le_inverseSquare w N Q t m) hright
    _ = C * ∑' m : CGLProposition51PuncturedFrequency, 1 / ((m.val : ℝ) ^ (2 : ℕ)) :=
      tsum_mul_left
    _ = _ := by rfl

end RHTower
