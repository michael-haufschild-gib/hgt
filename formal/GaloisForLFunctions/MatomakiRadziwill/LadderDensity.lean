import GaloisForLFunctions.MatomakiRadziwill.LadderNonRough
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# Harmonic mass of a scale

The primes of `(M, N]` (`primesIoc`) have harmonic mass `mertensS N − mertensS M`
(`sum_primesIoc_eq`), so Mertens' second theorem with explicit constants (`Sieve.le_mertensS`,
`Sieve.mertensS_le`) gives, for the scale `e^a < p ≤ e^b`, `1 ≤ a`, `a + 1 ≤ b`
(`sum_primesIoc_exp_ge`):

`Σ_{e^a < p ≤ e^b} 1/p ≥ log(b/a) − C_M`,   `C_M = mertensSecondLowerConst + mertensSecondUpperConst + log 2`.

This is the quantity `A` in Turán's bound for the integers avoiding the scale.
-/

open Finset RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The primes of `(M, N]`. -/
def primesIoc (M N : ℕ) : Finset ℕ := (Ioc M N).filter Nat.Prime

theorem sum_primesIoc_eq {M N : ℕ} (hMN : M ≤ N) :
    ∑ p ∈ primesIoc M N, (1 : ℝ) / (p : ℝ) = mertensS N - mertensS M := by
  classical
  have hunion : Nat.primesLE N = Nat.primesLE M ∪ primesIoc M N := by
    ext p
    simp only [Nat.primesLE_eq_filter_range, primesIoc, mem_union, mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : p ≤ M
      · exact Or.inl ⟨by omega, h2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by omega, h3⟩
  have hdisj : Disjoint (Nat.primesLE M) (primesIoc M N) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Nat.primesLE_eq_filter_range, primesIoc, mem_filter, mem_range, mem_Ioc] at hp hp'
    omega
  rw [mertensS, mertensS, hunion, sum_union hdisj]
  ring

/-- The Mertens constant of a scale. -/
def mertensScaleConst : ℝ := mertensSecondLowerConst + mertensSecondUpperConst + Real.log 2

/-- **The harmonic mass of the scale `e^a < p ≤ e^b`.** -/
theorem sum_primesIoc_exp_ge {a b : ℝ} (ha : 1 ≤ a) (hb : a + 1 ≤ b) :
    Real.log (b / a) - mertensScaleConst
      ≤ ∑ p ∈ primesIoc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊, (1 : ℝ) / (p : ℝ) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hea : (2 : ℝ) ≤ Real.exp a := le_trans he (Real.exp_le_exp.mpr ha)
  have hM : 2 ≤ ⌊Real.exp a⌋₊ := Nat.le_floor (by exact_mod_cast hea)
  have hMN : ⌊Real.exp a⌋₊ ≤ ⌊Real.exp b⌋₊ := Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hN : 2 ≤ ⌊Real.exp b⌋₊ := le_trans hM hMN
  rw [sum_primesIoc_eq hMN]
  have hlow := le_mertensS hN
  have hup := mertensS_le hM
  -- `log log N ≥ log (b − 1)`
  have hb1 : 1 ≤ b - 1 := by linarith
  have hNreal : Real.exp (b - 1) ≤ (⌊Real.exp b⌋₊ : ℝ) := by
    have h1 : Real.exp b - 1 < (⌊Real.exp b⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    have h2 : Real.exp (b - 1) ≤ Real.exp b - 1 := by
      rw [Real.exp_sub]
      have heb : Real.exp 1 ≤ Real.exp b := Real.exp_le_exp.mpr (by linarith)
      have hpos := Real.exp_pos b
      rw [div_le_iff₀ (Real.exp_pos 1)]
      nlinarith
    linarith
  have hlogN : b - 1 ≤ Real.log ⌊Real.exp b⌋₊ := by
    rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos (b - 1)])]
    exact hNreal
  have hloglogN : Real.log (b - 1) ≤ logLog ⌊Real.exp b⌋₊ := by
    unfold logLog
    exact Real.log_le_log (by linarith) hlogN
  -- `log log M ≤ log a`
  have hMreal : (⌊Real.exp a⌋₊ : ℝ) ≤ Real.exp a := Nat.floor_le (Real.exp_pos a).le
  have hM2 : (2 : ℝ) ≤ ⌊Real.exp a⌋₊ := by exact_mod_cast hM
  have hlogM : Real.log ⌊Real.exp a⌋₊ ≤ a := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    exact hMreal
  have hlogM0 : 0 < Real.log ⌊Real.exp a⌋₊ := Real.log_pos (by linarith)
  have hloglogM : logLog ⌊Real.exp a⌋₊ ≤ Real.log a := by
    unfold logLog
    exact Real.log_le_log hlogM0 hlogM
  -- `log (b − 1) ≥ log (b/a) + log a − log 2`
  have hb2 : b / 2 ≤ b - 1 := by linarith
  have hkey : Real.log (b / a) + Real.log a - Real.log 2 ≤ Real.log (b - 1) := by
    have h1 : Real.log (b / a) + Real.log a = Real.log b := by
      rw [← Real.log_mul (div_pos (by linarith) (by linarith)).ne' (ne_of_gt (by linarith))]
      congr 1
      field_simp
    have h2 : Real.log b - Real.log 2 = Real.log (b / 2) := (Real.log_div (by linarith)
      (by norm_num)).symm
    have h3 : Real.log (b / 2) ≤ Real.log (b - 1) := Real.log_le_log (by linarith) hb2
    linarith
  unfold mertensScaleConst
  linarith

end

end GaloisForLFunctions.MatomakiRadziwill
