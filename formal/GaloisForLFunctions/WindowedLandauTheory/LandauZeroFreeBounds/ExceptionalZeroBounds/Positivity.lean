import GaloisForLFunctions.RHTower.DirichletLUniformZeroFreeRegion
import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.NoZeroComplexOf

/-! Nonnegative Euler coefficients for the logarithmic-derivative combinations. -/

open Complex LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

noncomputable section

namespace WindowedLandauTheory.ZeroFreeDirichlet

lemma negLogDeriv_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : negLD χ s = LSeries (↗χ * ↗Λ) s := by
  unfold negLD
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  ring

lemma hasSum_re_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : HasSum (fun n ↦ (term (↗χ * ↗Λ) s n).re) (negLD χ s).re := by
  rw [negLogDeriv_eq_LSeries χ hs]
  exact Complex.hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs).hasSum

lemma term_ofReal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ) (n : ℕ) :
    term (↗χ * ↗Λ) (σ : ℂ) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  · rw [LSeries.term_def, if_neg hn]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    simp only [Pi.mul_apply]
    ring

lemma vonMangoldt_div_rpow_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ Λ n / (n : ℝ) ^ σ :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

lemma eq_one_or_eq_neg_one_of_sq_eq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    {n : ℕ} (hu : IsUnit (n : ZMod q)) : χ n = 1 ∨ χ n = -1 := by
  have h : χ n * χ n = 1 := by
    rw [← pow_two, ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply hu]
  exact mul_self_eq_one_iff.mp h

lemma term_two_real_nonneg {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (σ : ℝ) (n : ℕ) :
    0 ≤ (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + (term (↗χ₁ * ↗Λ) (σ : ℂ) n).re + (term (↗χ₂ * ↗Λ) (σ : ℂ) n).re
      + (term (↗(χ₁ * χ₂) * ↗Λ) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  have ha := vonMangoldt_div_rpow_nonneg σ n
  rw [term_ofReal, term_ofReal, term_ofReal,
    term_ofReal, MulChar.mul_apply]
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu]
    rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₁ h₁ hu with h | h <;>
      rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₂ h₂ hu with h' | h' <;> rw [h, h'] <;>
      generalize Λ n / (n : ℝ) ^ σ = a at ha ⊢ <;>
      simp [Complex.re_ofReal_mul] <;> linarith
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    simp

theorem negLogDerivPositivity : Positivity := by
  intro q _ σ hσ
  have hs1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have H1 : ∀ χ : DirichletCharacter ℂ q, HasSum (fun n ↦ (term (↗χ * ↗Λ) (σ : ℂ) n).re)
      (negLD χ (σ : ℂ)).re := fun χ => hasSum_re_term χ hs1
  refine ⟨fun χ t => ?_, fun χ _ => ?_, fun χ₁ χ₂ h₁ h₂ => ?_⟩
  · exact RHTower.three_four_one_logDeriv χ hσ t
  · exact RHTower.two_term_logDeriv χ hσ
  · exact HasSum.nonneg (fun n => term_two_real_nonneg χ₁ χ₂ h₁ h₂ σ n)
      ((((H1 1).add (H1 χ₁)).add (H1 χ₂)).add (H1 (χ₁ * χ₂)))

end WindowedLandauTheory.ZeroFreeDirichlet
