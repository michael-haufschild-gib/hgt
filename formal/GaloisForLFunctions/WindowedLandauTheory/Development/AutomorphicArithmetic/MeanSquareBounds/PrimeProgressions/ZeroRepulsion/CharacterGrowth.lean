import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.CauchyMoments
import Zeta23.ThmE.LGrowth

/-! Polynomial growth and pole derivatives for local character expansions. -/

open Finset Complex Classical

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

lemma dhl_prod_le (M : ℕ) [NeZero M] (s : ℂ) (hs : 0 ≤ s.re) :
    ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ M := by
  rw [norm_prod]
  have h1 : ∀ p ∈ M.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
    have hn : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp'.pos]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      simpa using hs
    calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ ≤ p := by rw [norm_one]; linarith
  calc ∏ p ∈ M.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ ≤ ∏ p ∈ M.primeFactors, (p : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) h1
    _ = ((∏ p ∈ M.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ M := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos M) (Nat.prod_primeFactors_dvd M)

lemma dhl_triv_growth (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.LFunctionTrivChar₁ M s‖ ≤ 4 * M * (1 + ‖s‖) ^ 2 := by
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
  have hs0 := norm_nonneg s
  by_cases h1 : s = 1
  · subst h1
    have := dhl_prod_le M 1 (by simp)
    simp only [Function.update_self]
    have e : ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) = ∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ))) := by
      refine Finset.prod_congr rfl (fun p _ => ?_)
      rw [cpow_neg_one]
    rw [e]
    refine this.trans ?_
    rw [norm_one]
    nlinarith
  · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne h1,
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta h1, norm_mul, norm_mul]
    have hP := dhl_prod_le M s (by linarith)
    have hζ := Zeta23.RvM.norm_riemannZeta_le_of_re_pos (by linarith : 0 < s.re) h1
    rw [norm_sub_rev] at hζ
    have hz : ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re) := by
      refine hζ.trans ?_
      rw [div_eq_mul_one_div (‖s‖)]
      linarith only [norm_nonneg s]
    have hpos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
    have hle : ‖s - 1‖ ≤ 1 + ‖s‖ := by
      have := norm_sub_le s 1; rw [norm_one] at this; linarith
    have hb : 1 / s.re ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hz2 : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 4 * (1 + ‖s‖) ^ 2 := by
      calc ‖s - 1‖ * ‖riemannZeta s‖
          ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) := by gcongr
        _ = ‖s - 1‖ + 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by field_simp
        _ ≤ (1 + ‖s‖) + 1 + (1 + ‖s‖) * (‖s‖ * (1 + 2)) := by gcongr
        _ ≤ 4 * (1 + ‖s‖) ^ 2 := by nlinarith
    calc ‖s - 1‖ * (‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * ‖riemannZeta s‖)
        = ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * (‖s - 1‖ * ‖riemannZeta s‖) := by ring
      _ ≤ M * (4 * (1 + ‖s‖) ^ 2) := by gcongr
      _ = 4 * M * (1 + ‖s‖) ^ 2 := by ring

lemma dhl_pole (k : ℕ) (s : ℂ) :
    (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z : ℂ => 1 / (z - 1)) s
      = 1 / (s - 1) ^ (k + 1) := by
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h1 : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow]; simp
  rw [dhc_iter, one_mul, one_div, ← mul_assoc, div_mul_eq_mul_div]
  rw [← mul_assoc, mul_div_cancel_right₀ _ hk, h1, one_mul]

lemma dhl_log (K X : ℝ) (hK : 1 ≤ K) (hX : 2 ≤ X) :
    Real.log (K * X ^ 2) ≤ 2 * ((Real.log K + 2) * Real.log X) := by
  have hl : (1 / 2 : ℝ) ≤ Real.log X :=
    (by linarith only [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hX)
  have hk : 0 ≤ Real.log K := Real.log_nonneg hK
  rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
  push_cast
  nlinarith only [hl, mul_nonneg hk (sub_nonneg.mpr hl)]

end QH.PrimeProgressions
