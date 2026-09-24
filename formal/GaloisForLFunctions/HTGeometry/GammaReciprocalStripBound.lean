import GaloisForLFunctions.HTGeometry.GammaReciprocalExpBound
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# The reciprocal archimedean Gamma factor on a vertical strip

`Γ(z) = (z-1)Γ(z-1)` moves the reflection bound one unit to the right, and above unit height the
extra factor `(z-1)^{-1}` is harmless.  Applied to `Gammaℝ s = π^{-s/2} Γ(s/2)` this gives

```text
‖1/Gammaℝ(s)‖ ≤ C(σ) e^{π|t|/2}    on every vertical strip with Re s < 4 and |Im s| ≥ 2,
```

one constant for the whole strip.  All the height dependence of a completed `L`-function's
uncompleted form sits here.
-/

open Complex Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One recurrence step for the reciprocal Gamma function. -/
theorem norm_inv_Gamma_le_shift {z : ℂ} (hz : z.re < 2) (him : 1 ≤ |z.im|) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ Real.Gamma (2 - z.re) * Real.exp (Real.pi * |z.im|) / Real.pi := by
  have hz1 : z - 1 ≠ 0 := by
    intro h
    have hc := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im] at hc
    rw [hc] at him
    norm_num at him
  have hrec : Complex.Gamma z = (z - 1) * Complex.Gamma (z - 1) := by
    have h := Complex.Gamma_add_one (z - 1) hz1
    rwa [sub_add_cancel] at h
  have h2 : ‖(Complex.Gamma (z - 1))⁻¹‖
      ≤ Real.Gamma (2 - z.re) * Real.exp (Real.pi * |z.im|) / Real.pi := by
    have hlt : (z - 1).re < 1 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have h := norm_inv_Gamma_le (z := z - 1) hlt
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
    have hrw : (1 : ℝ) - (z.re - 1) = 2 - z.re := by ring
    rwa [hrw] at h
  have h1 : ‖(z - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    refine inv_le_one_of_one_le₀ ?_
    have hle : |(z - 1).im| ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at hle
    linarith
  rw [hrec, mul_inv, norm_mul]
  have hnn : (0 : ℝ) ≤ ‖(Complex.Gamma (z - 1))⁻¹‖ := norm_nonneg _
  nlinarith [h1, h2, hnn, norm_nonneg ((z - 1)⁻¹)]

/-- **The reciprocal archimedean Gamma factor is at most exponential in the height.** -/
theorem norm_inv_Gammaℝ_le {s : ℂ} (hs : s.re < 4) (him : 2 ≤ |s.im|) :
    ‖(Complex.Gammaℝ s)⁻¹‖
      ≤ Real.pi ^ (s.re / 2)
        * (Real.Gamma (2 - s.re / 2) * Real.exp (Real.pi * |s.im| / 2) / Real.pi) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hre : (s / 2).re = s.re / 2 := by simp
  have hIm : (s / 2).im = s.im / 2 := by simp
  have h1 : ‖(((Real.pi : ℂ)) ^ (-s / 2))⁻¹‖ = Real.pi ^ (s.re / 2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hπ, ← Real.rpow_neg hπ.le]
    congr 1
    have hnn : (-s / 2).re = -(s.re / 2) := by simp; ring
    rw [hnn]
    ring
  have h2 : ‖(Complex.Gamma (s / 2))⁻¹‖
      ≤ Real.Gamma (2 - s.re / 2) * Real.exp (Real.pi * |s.im| / 2) / Real.pi := by
    have h := norm_inv_Gamma_le_shift (z := s / 2) (by rw [hre]; linarith)
      (by rw [hIm, abs_div]; rw [show |(2:ℝ)| = 2 by norm_num]; linarith)
    rw [hre, hIm, abs_div, show |(2:ℝ)| = 2 by norm_num] at h
    have hrw : Real.pi * (|s.im| / 2) = Real.pi * |s.im| / 2 := by ring
    rwa [hrw] at h
  rw [Complex.Gammaℝ_def, mul_inv, norm_mul, h1]
  refine mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hπ.le _)

/-- **One constant for the whole strip.** -/
theorem exists_bound_norm_inv_Gammaℝ (σ₀ σ₁ : ℝ) (hσ : σ₁ < 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖(Complex.Gammaℝ s)⁻¹‖ ≤ C * Real.exp (Real.pi * |s.im| / 2) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨CΓ, hCΓ0, hCΓ⟩ :=
    exists_bound_Real_Gamma_Icc (a := 2 - σ₁ / 2) (b := 2 - min σ₀ σ₁ / 2) (by linarith)
  set P : ℝ := Real.pi ^ (max σ₁ 0 / 2) with hP
  have hP0 : (0 : ℝ) ≤ P := Real.rpow_nonneg hπ.le _
  refine ⟨P * (CΓ / Real.pi), by positivity, fun s h0 h1 him => ?_⟩
  have hbase := norm_inv_Gammaℝ_le (s := s) (by linarith) him
  refine hbase.trans ?_
  have hπpow : Real.pi ^ (s.re / 2) ≤ P := by
    rw [hP]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith [Real.two_le_pi]) ?_
    have hmx : s.re ≤ max σ₁ 0 := le_trans h1 (le_max_left _ _)
    linarith
  have hΓb : Real.Gamma (2 - s.re / 2) ≤ CΓ := by
    refine hCΓ _ (by linarith) ?_
    have hmn : min σ₀ σ₁ ≤ s.re := le_trans (min_le_left _ _) h0
    linarith
  have hΓ0 : (0 : ℝ) ≤ Real.Gamma (2 - s.re / 2) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  calc Real.pi ^ (s.re / 2)
        * (Real.Gamma (2 - s.re / 2) * Real.exp (Real.pi * |s.im| / 2) / Real.pi)
      ≤ P * (CΓ * Real.exp (Real.pi * |s.im| / 2) / Real.pi) := by gcongr
    _ = P * (CΓ / Real.pi) * Real.exp (Real.pi * |s.im| / 2) := by ring

end

end GaloisForLFunctions.HTGeometry
