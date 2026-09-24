import GaloisForLFunctions.HTGeometry.GammaReciprocalStripBound
import GaloisForLFunctions.HTGeometry.MellinMajorant
import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-!
# Exponential strip bounds for the Hurwitz and exponential zeta functions

A completed Hurwitz zeta function is a Mellin transform of a rapidly decaying kernel plus two
simple poles, so it is **bounded on every vertical strip, uniformly in the height** (above height
two, where the poles are harmless).  Dividing by the archimedean factor multiplies that by
`‖1/Gammaℝ‖`, which is at most exponential in the height.  Hence

```text
‖ζ(s, a)‖, ‖expZeta(a, s)‖ ≤ C(σ₀, σ₁, a) · e^{π|t|/2}     (σ₀ ≤ Re s ≤ σ₁ < 3, |t| ≥ 2).
```

Mathlib records no size estimate for these functions.  The bound is far from sharp — the truth is
polynomial — but it is the a priori growth hypothesis a Phragmén--Lindelöf argument consumes, and
it is uniform in the abscissa.
-/

open Complex HurwitzZeta Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `Λ` and `Λ₀` agree for a strong functional-equation pair. -/
theorem Λ_eq_Λ₀_of_strong {P : WeakFEPair ℂ} (hP : IsStrongFEPair P) (s : ℂ) :
    P.Λ s = P.Λ₀ s := by
  rw [WeakFEPair.Λ, hP.hf₀, hP.hg₀, smul_zero, smul_zero, sub_zero, sub_zero]

/-- Above height two a simple pole contributes at most one half. -/
theorem norm_one_div_le_of_two_le_abs_im {w : ℂ} (h : 2 ≤ |w.im|) : ‖(1 : ℂ) / w‖ ≤ 1 / 2 := by
  have h1 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have h2 : (0 : ℝ) < ‖w‖ := lt_of_lt_of_le (by norm_num) (le_trans h h1)
  rw [norm_div, norm_one, div_le_div_iff₀ h2 (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **The completed even Hurwitz zeta is bounded on a vertical strip.** -/
theorem exists_bound_norm_completedHurwitzZetaEven (a : UnitAddCircle) (σ₀ σ₁ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖completedHurwitzZetaEven a s‖ ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_WeakFEPair_Λ₀ (hurwitzEvenFEPair a) (σ₀ / 2) (σ₁ / 2)
  refine ⟨C / 2 + 1, by positivity, fun s h0 h1 him => ?_⟩
  have hΛ : ‖(hurwitzEvenFEPair a).Λ₀ (s / 2)‖ ≤ C := by
    refine hC (s / 2) ?_ ?_ <;> · simp only [Complex.div_ofNat_re]; linarith
  have hpole1 : ‖((if a = 0 then (1 : ℂ) else 0)) / s‖ ≤ 1 / 2 := by
    by_cases ha : a = 0
    · rw [if_pos ha]
      exact norm_one_div_le_of_two_le_abs_im him
    · rw [if_neg ha, zero_div, norm_zero]; norm_num
  have hpole2 : ‖(1 : ℂ) / (1 - s)‖ ≤ 1 / 2 := by
    refine norm_one_div_le_of_two_le_abs_im ?_
    simpa [Complex.sub_im] using him
  rw [completedHurwitzZetaEven_eq]
  have hcm : completedHurwitzZetaEven₀ a s = ((hurwitzEvenFEPair a).Λ₀ (s / 2)) / 2 := rfl
  rw [hcm]
  refine le_trans (norm_sub_le _ _) ?_
  have hstep : ‖(hurwitzEvenFEPair a).Λ₀ (s / 2) / 2 - (if a = 0 then (1 : ℂ) else 0) / s‖
      ≤ ‖(hurwitzEvenFEPair a).Λ₀ (s / 2)‖ / 2 + 1 / 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    linarith
  linarith

/-- **The completed cosine zeta is bounded on a vertical strip.** -/
theorem exists_bound_norm_completedCosZeta (a : UnitAddCircle) (σ₀ σ₁ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖completedCosZeta a s‖ ≤ B := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_bound_norm_WeakFEPair_Λ₀ (hurwitzEvenFEPair a).symm (σ₀ / 2) (σ₁ / 2)
  refine ⟨C / 2 + 1, by positivity, fun s h0 h1 him => ?_⟩
  have hΛ : ‖(hurwitzEvenFEPair a).symm.Λ₀ (s / 2)‖ ≤ C := by
    refine hC (s / 2) ?_ ?_ <;> · simp only [Complex.div_ofNat_re]; linarith
  have hpole1 : ‖(1 : ℂ) / s‖ ≤ 1 / 2 := norm_one_div_le_of_two_le_abs_im him
  have hpole2 : ‖((if a = 0 then (1 : ℂ) else 0)) / (1 - s)‖ ≤ 1 / 2 := by
    by_cases ha : a = 0
    · rw [if_pos ha]
      refine norm_one_div_le_of_two_le_abs_im ?_
      simpa [Complex.sub_im] using him
    · rw [if_neg ha, zero_div, norm_zero]; norm_num
  rw [completedCosZeta_eq]
  have hcm : completedCosZeta₀ a s = ((hurwitzEvenFEPair a).symm.Λ₀ (s / 2)) / 2 := rfl
  rw [hcm]
  refine le_trans (norm_sub_le _ _) ?_
  have hstep : ‖(hurwitzEvenFEPair a).symm.Λ₀ (s / 2) / 2 - (1 : ℂ) / s‖
      ≤ ‖(hurwitzEvenFEPair a).symm.Λ₀ (s / 2)‖ / 2 + 1 / 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    linarith
  linarith

/-- **The completed odd Hurwitz zeta is bounded on a vertical strip.** -/
theorem exists_bound_norm_completedHurwitzZetaOdd (a : UnitAddCircle) (σ₀ σ₁ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ →
      ‖completedHurwitzZetaOdd a s‖ ≤ B := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_bound_norm_WeakFEPair_Λ₀ (hurwitzOddFEPair a) ((σ₀ + 1) / 2) ((σ₁ + 1) / 2)
  refine ⟨C / 2, by positivity, fun s h0 h1 => ?_⟩
  have hΛ : ‖(hurwitzOddFEPair a).Λ₀ ((s + 1) / 2)‖ ≤ C := by
    refine hC ((s + 1) / 2) ?_ ?_ <;>
      · simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]; linarith
  have hcm : completedHurwitzZetaOdd a s = ((hurwitzOddFEPair a).Λ₀ ((s + 1) / 2)) / 2 := by
    rw [completedHurwitzZetaOdd, Λ_eq_Λ₀_of_strong (isStrong_hurwitzOddFEPair a)]
  rw [hcm, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
  linarith

/-- **The completed sine zeta is bounded on a vertical strip.** -/
theorem exists_bound_norm_completedSinZeta (a : UnitAddCircle) (σ₀ σ₁ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ →
      ‖completedSinZeta a s‖ ≤ B := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_bound_norm_WeakFEPair_Λ₀ (hurwitzOddFEPair a).symm ((σ₀ + 1) / 2) ((σ₁ + 1) / 2)
  refine ⟨C / 2, by positivity, fun s h0 h1 => ?_⟩
  have hΛ : ‖(hurwitzOddFEPair a).symm.Λ₀ ((s + 1) / 2)‖ ≤ C := by
    refine hC ((s + 1) / 2) ?_ ?_ <;>
      · simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]; linarith
  have hcm : completedSinZeta a s = ((hurwitzOddFEPair a).symm.Λ₀ ((s + 1) / 2)) / 2 := by
    rw [completedSinZeta, Λ_eq_Λ₀_of_strong (isStrong_hurwitzOddFEPair a).symm]
  rw [hcm, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
  linarith

/-- Dividing a strip-bounded function by `Gammaℝ` costs one exponential in the height. -/
theorem exists_bound_norm_div_Gammaℝ {f : ℂ → ℂ} {σ₀ σ₁ : ℝ} (hσ : σ₁ < 4) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| → ‖f s‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖f s / Complex.Gammaℝ s‖ ≤ C * Real.exp (Real.pi * |s.im| / 2) := by
  obtain ⟨CG, hCG0, hCG⟩ := exists_bound_norm_inv_Gammaℝ σ₀ σ₁ hσ
  refine ⟨B * CG, by positivity, fun s h0 h1 him => ?_⟩
  rw [div_eq_mul_inv, norm_mul]
  calc ‖f s‖ * ‖(Complex.Gammaℝ s)⁻¹‖
      ≤ B * (CG * Real.exp (Real.pi * |s.im| / 2)) :=
        mul_le_mul (hB s h0 h1 him) (hCG s h0 h1 him) (norm_nonneg _) hB0
    _ = B * CG * Real.exp (Real.pi * |s.im| / 2) := by ring

/-- The same with the shifted archimedean factor `Gammaℝ (s+1)`. -/
theorem exists_bound_norm_div_Gammaℝ_succ {f : ℂ → ℂ} {σ₀ σ₁ : ℝ} (hσ : σ₁ < 3) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → ‖f s‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖f s / Complex.Gammaℝ (s + 1)‖ ≤ C * Real.exp (Real.pi * |s.im| / 2) := by
  obtain ⟨CG, hCG0, hCG⟩ := exists_bound_norm_inv_Gammaℝ (σ₀ + 1) (σ₁ + 1) (by linarith)
  refine ⟨B * CG, by positivity, fun s h0 h1 him => ?_⟩
  have hre : (s + 1).re = s.re + 1 := by simp
  have himq : (s + 1).im = s.im := by simp
  have hG := hCG (s + 1) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [himq]; exact him)
  rw [himq] at hG
  rw [div_eq_mul_inv, norm_mul]
  calc ‖f s‖ * ‖(Complex.Gammaℝ (s + 1))⁻¹‖
      ≤ B * (CG * Real.exp (Real.pi * |s.im| / 2)) :=
        mul_le_mul (hB s h0 h1) hG (norm_nonneg _) hB0
    _ = B * CG * Real.exp (Real.pi * |s.im| / 2) := by ring

/-- **Exponential strip bound for the even Hurwitz zeta.** -/
theorem exists_bound_norm_hurwitzZetaEven_strip (a : UnitAddCircle) (σ₀ σ₁ : ℝ) (hσ : σ₁ < 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖hurwitzZetaEven a s‖ ≤ C * Real.exp (Real.pi * |s.im| / 2) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_norm_completedHurwitzZetaEven a σ₀ σ₁
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_div_Gammaℝ (f := completedHurwitzZetaEven a) hσ hB0 hB
  refine ⟨C, hC0, fun s h0 h1 him => ?_⟩
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at him; norm_num at him
  rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs0)]
  exact hC s h0 h1 him

/-- **Exponential strip bound for the cosine zeta.** -/
theorem exists_bound_norm_cosZeta_strip (a : UnitAddCircle) (σ₀ σ₁ : ℝ) (hσ : σ₁ < 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖cosZeta a s‖ ≤ C * Real.exp (Real.pi * |s.im| / 2) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_norm_completedCosZeta a σ₀ σ₁
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_div_Gammaℝ (f := completedCosZeta a) hσ hB0 hB
  refine ⟨C, hC0, fun s h0 h1 him => ?_⟩
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at him; norm_num at him
  rw [cosZeta, Function.update_of_ne hs0]
  exact hC s h0 h1 him

/-- **Exponential strip bound for the odd Hurwitz zeta.** -/
theorem exists_bound_norm_hurwitzZetaOdd_strip (a : UnitAddCircle) (σ₀ σ₁ : ℝ) (hσ : σ₁ < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖hurwitzZetaOdd a s‖ ≤ C * Real.exp (Real.pi * |s.im| / 2) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_norm_completedHurwitzZetaOdd a σ₀ σ₁
  obtain ⟨C, hC0, hC⟩ :=
    exists_bound_norm_div_Gammaℝ_succ (f := completedHurwitzZetaOdd a) hσ hB0 hB
  exact ⟨C, hC0, fun s h0 h1 him => hC s h0 h1 him⟩

/-- **Exponential strip bound for the sine zeta.** -/
theorem exists_bound_norm_sinZeta_strip (a : UnitAddCircle) (σ₀ σ₁ : ℝ) (hσ : σ₁ < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖sinZeta a s‖ ≤ C * Real.exp (Real.pi * |s.im| / 2) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_norm_completedSinZeta a σ₀ σ₁
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_div_Gammaℝ_succ (f := completedSinZeta a) hσ hB0 hB
  exact ⟨C, hC0, fun s h0 h1 him => hC s h0 h1 him⟩

/-- **Exponential strip bound for the Hurwitz zeta.** -/
theorem exists_bound_norm_hurwitzZeta_strip (a : UnitAddCircle) (σ₀ σ₁ : ℝ) (hσ : σ₁ < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖hurwitzZeta a s‖ ≤ C * Real.exp (Real.pi * |s.im| / 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_norm_hurwitzZetaEven_strip a σ₀ σ₁ (by linarith)
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_norm_hurwitzZetaOdd_strip a σ₀ σ₁ hσ
  refine ⟨C₁ + C₂, by positivity, fun s h0 h1 him => ?_⟩
  rw [hurwitzZeta]
  refine le_trans (norm_add_le _ _) ?_
  have h1' := hC₁ s h0 h1 him
  have h2' := hC₂ s h0 h1 him
  nlinarith [Real.exp_pos (Real.pi * |s.im| / 2)]

/-- **Exponential strip bound for the exponential zeta.** -/
theorem exists_bound_norm_expZeta_strip (a : UnitAddCircle) (σ₀ σ₁ : ℝ) (hσ : σ₁ < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖expZeta a s‖ ≤ C * Real.exp (Real.pi * |s.im| / 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_norm_cosZeta_strip a σ₀ σ₁ (by linarith)
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_norm_sinZeta_strip a σ₀ σ₁ hσ
  refine ⟨C₁ + C₂, by positivity, fun s h0 h1 him => ?_⟩
  rw [expZeta]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  have h1' := hC₁ s h0 h1 him
  have h2' := hC₂ s h0 h1 him
  nlinarith [Real.exp_pos (Real.pi * |s.im| / 2)]

end

end GaloisForLFunctions.HTGeometry
