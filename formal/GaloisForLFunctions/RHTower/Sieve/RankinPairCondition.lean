import GaloisForLFunctions.RHTower.Sieve.RankinTruncation
import GaloisForLFunctions.RHTower.Sieve.RoughPairSieve
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# The Rankin condition for the shifted pair sieve

At the exponent `α = 1/log h` the Rankin weight `p^α` stays below `e` across the whole sifting
range, so the Rankin sum is bounded by `6e` times Mertens' first theorem — an absolute constant.
The level therefore only has to exceed a fixed power of the sifting bound, and the sieve keeps its
full two-logarithm saving.
-/

namespace RHTower.Sieve

open Finset

/-- The sieve density of a shifted pair is at most `6/p`. -/
theorem pairClass_div_le_six (d : ℕ) {p : ℕ} (hp : (3 : ℝ) ≤ (p : ℝ)) :
    pairClassCount d p / ((p : ℝ) - pairClassCount d p) ≤ 6 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rw [pairClassCount]
  split_ifs with hdvd
  · rw [div_le_div_iff₀ (by linarith) hp0]
    linarith
  · rw [div_le_div_iff₀ (by linarith) hp0]
    linarith

/-- **The Rankin sum of the pair sieve is absolutely bounded.** -/
theorem rankin_pairSum_le {P₁ h : ℕ} (hP₁ : 2 ≤ P₁) (hh2 : 2 ≤ h) (d : ℕ) :
    (∑ p ∈ rangePrimes P₁ h,
        ((p : ℝ) ^ (1 / Real.log h) - 1)
          * (pairClassCount d p / ((p : ℝ) - pairClassCount d p)))
      ≤ 6 * Real.exp 1 * (1 / Real.log h) * (Real.log h + mertensFirstConst) := by
  classical
  have hh1R : (1 : ℝ) < (h : ℝ) := by exact_mod_cast hh2
  have hlogh : (0 : ℝ) < Real.log h := Real.log_pos hh1R
  set α : ℝ := 1 / Real.log h with hα
  have hα0 : (0 : ℝ) < α := by rw [hα]; positivity
  -- each term
  have hterm : ∀ p ∈ rangePrimes P₁ h,
      ((p : ℝ) ^ α - 1) * (pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        ≤ 6 * Real.exp 1 * α * (Real.log p / (p : ℝ)) := by
    intro p hp
    have hmem := hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hmem
    have hp3 : 3 ≤ p := by omega
    have hph : p ≤ h := hmem.1.2
    have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hlogph : Real.log p ≤ Real.log h := Real.log_le_log hp0 (by exact_mod_cast hph)
    set u : ℝ := α * Real.log p with hu
    have hu0 : (0 : ℝ) ≤ u := by rw [hu]; positivity
    have hu1 : u ≤ 1 := by
      rw [hu, hα, one_div, inv_mul_eq_div, div_le_one hlogh]
      exact hlogph
    have hrw : (p : ℝ) ^ α = Real.exp u := by
      rw [Real.rpow_def_of_pos hp0, hu]
      ring_nf
    -- `e^u − 1 ≤ u·e` on `[0,1]`
    have hexp : Real.exp u - 1 ≤ u * Real.exp 1 := by
      have h1 : 1 - u ≤ Real.exp (-u) := by
        have := Real.add_one_le_exp (-u)
        linarith
      have h2 : (0 : ℝ) < Real.exp u := Real.exp_pos u
      have h3 : Real.exp (-u) = (Real.exp u)⁻¹ := by rw [Real.exp_neg]
      rw [h3] at h1
      have h4 : (1 - u) * Real.exp u ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_right h1 h2.le
        rw [inv_mul_cancel₀ (ne_of_gt h2)] at hmul
        exact hmul
      have h5 : Real.exp u ≤ Real.exp 1 := Real.exp_le_exp.2 hu1
      nlinarith [h4, h5, hu0, h2]
    have hnum : (0 : ℝ) ≤ (p : ℝ) ^ α - 1 := by
      rw [hrw]
      have := Real.one_le_exp hu0
      linarith
    have hdens := pairClass_div_le_six d hp3R
    have hdens0 : (0 : ℝ) ≤ pairClassCount d p / ((p : ℝ) - pairClassCount d p) := by
      rw [pairClassCount]
      split_ifs <;> [skip; skip] <;>
        · refine div_nonneg (by norm_num) (by linarith)
    calc ((p : ℝ) ^ α - 1) * (pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        ≤ ((p : ℝ) ^ α - 1) * (6 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hdens hnum
      _ ≤ (u * Real.exp 1) * (6 / (p : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hrw] at hnum ⊢
          linarith [hexp]
      _ = 6 * Real.exp 1 * α * (Real.log p / (p : ℝ)) := by
          rw [hu]
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : rangePrimes P₁ h ⊆ Nat.primesLE h := by
    intro p hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Nat.mem_primesLE]
    exact ⟨hp.1.2, hp.2⟩
  have hmert : (∑ p ∈ rangePrimes P₁ h, Real.log p / (p : ℝ)) ≤ mertensA h := by
    rw [mertensA]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesLE hp).two_le
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_of_lt hp2
    exact div_nonneg (Real.log_nonneg this) (by linarith)
  have hmertA : mertensA h ≤ Real.log h + mertensFirstConst := by
    have := abs_mertensA_sub_log_le (N := h) (by omega)
    have h2 := abs_le.1 this
    linarith [h2.2]
  have hcoef : (0 : ℝ) ≤ 6 * Real.exp 1 * α := by positivity
  exact mul_le_mul_of_nonneg_left (le_trans hmert hmertA) hcoef

/-- **The Rankin condition at level `h^18`.** -/
theorem rankin_pairSieve_condition {P₁ h : ℕ} (hP₁ : 2 ≤ P₁) (hh2 : 2 ≤ h)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) (d : ℕ) :
    (∑ p ∈ rangePrimes P₁ h,
        ((p : ℝ) ^ (1 / Real.log h) - 1)
          * (pairClassCount d p / ((p : ℝ) - pairClassCount d p)))
      + Real.log 2 ≤ (1 / Real.log h) * Real.log ((h : ℝ) ^ (18 : ℝ)) := by
  have hh1R : (1 : ℝ) < (h : ℝ) := by exact_mod_cast hh2
  have hlogh : (0 : ℝ) < Real.log h := Real.log_pos hh1R
  have hC0 : (0 : ℝ) ≤ mertensFirstConst := mertensFirstConst_nonneg
  have hrhs : (1 / Real.log h) * Real.log ((h : ℝ) ^ (18 : ℝ)) = 18 := by
    rw [Real.log_rpow (by linarith : (0:ℝ) < (h:ℝ))]
    field_simp
  rw [hrhs]
  have hmain := rankin_pairSum_le hP₁ hh2 d
  have hratio : (1 / Real.log h) * mertensFirstConst ≤ 1 / 20 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hlogh (by norm_num)]
    linarith
  have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hlog2 : Real.log 2 < 0.6932 := by
    have := Real.log_two_lt_d9
    linarith
  have hval : 6 * Real.exp 1 * (1 / Real.log h) * (Real.log h + mertensFirstConst)
      = 6 * Real.exp 1 * (1 + (1 / Real.log h) * mertensFirstConst) := by
    field_simp
  rw [hval] at hmain
  have hbound : 6 * Real.exp 1 * (1 + (1 / Real.log h) * mertensFirstConst)
      ≤ 6 * 2.7182818286 * (1 + 1 / 20) := by
    have h1 : (0 : ℝ) ≤ 1 + (1 / Real.log h) * mertensFirstConst := by positivity
    have h2 : (0 : ℝ) < 6 * Real.exp 1 := by positivity
    nlinarith [hexp, hratio, h1]
  nlinarith [hmain, hbound, hlog2]

end RHTower.Sieve
