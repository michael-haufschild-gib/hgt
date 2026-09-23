import GaloisForLFunctions.RHTower.DeningerMertensSummatory
import Mathlib.Analysis.PSeries

/-!
# The Möbius summatory function is inverse-square summable

The unconditional saving `|M(N)| ≤ B N exp(-(log N)^{1/3}/108)` makes `∑_N |M(N)|/N²` converge.
This is the discrete form of the only analytic input of the Möbius calculus of the ray, and no
power comparison proves it: `exp(-c(log N)^{1/3})` dominates every `N^{-ε}`.

Cauchy condensation is what works.  The condensed series is `∑_k exp(-c k^{1/3})`, and that one is
elementary: a single term of the exponential series gives `exp(c x^{1/3}) ≥ (c x^{1/3})^(7 : ℕ)/7!`, and
`x^{7/3} ≥ x²` for `x ≥ 1`.

* `deningerCubeRootExp_summable` : `∑_k exp(-c k^{1/3}) < ∞`.
* `deningerSavingRay_summable` : `∑_N exp(-(log N)^{1/3}/108)/N < ∞`, by condensation.
* `deningerMertensM_invSq_summable` : **`∑_N |M(N)|/N² < ∞`.**
-/

namespace RHTower

open Filter

noncomputable section

/-! ## The condensed series -/

/-- A single term of the exponential series beats the square. -/
theorem deningerCubeRootExp_le {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-(c * x ^ ((1 : ℝ) / 3))) ≤ 5040 / c ^ 7 * (1 / x ^ 2) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have harg : (0 : ℝ) ≤ c * x ^ ((1 : ℝ) / 3) :=
    mul_nonneg hc.le (Real.rpow_nonneg hx0.le _)
  have hseries := Real.pow_div_factorial_le_exp (c * x ^ ((1 : ℝ) / 3)) harg 7
  have hfac : (Nat.factorial 7 : ℝ) = 5040 := by norm_num [Nat.factorial]
  rw [hfac] at hseries
  have hpow : (c * x ^ ((1 : ℝ) / 3)) ^ 7 = c ^ 7 * x ^ ((7 : ℝ) / 3) := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 3)) 7, ← Real.rpow_mul hx0.le]
    norm_num
  rw [hpow] at hseries
  have hge : x ^ (2 : ℝ) ≤ x ^ ((7 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hx2 : x ^ (2 : ℝ) = x ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hx2] at hge
  have hc7 : (0 : ℝ) < c ^ 7 := by positivity
  have hlower : c ^ 7 * x ^ 2 / 5040 ≤ Real.exp (c * x ^ ((1 : ℝ) / 3)) := by
    refine le_trans ?_ hseries
    have := mul_le_mul_of_nonneg_left hge hc7.le
    linarith
  have hxsq : (0 : ℝ) < x ^ 2 := by positivity
  have hfrac : (0 : ℝ) < 5040 / (c ^ 7 * x ^ 2) := by positivity
  have heq : 5040 / c ^ 7 * (1 / x ^ 2) = 5040 / (c ^ 7 * x ^ 2) := by
    field_simp
  rw [Real.exp_neg, heq, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  have hstep := mul_le_mul_of_nonneg_left hlower hfrac.le
  have hone : 5040 / (c ^ 7 * x ^ 2) * (c ^ 7 * x ^ 2 / 5040) = 1 := by
    field_simp
  rw [hone] at hstep
  exact hstep

/-- **The condensed series converges.** -/
theorem deningerCubeRootExp_summable {c : ℝ} (hc : 0 < c) :
    Summable fun k : ℕ => Real.exp (-(c * (k : ℝ) ^ ((1 : ℝ) / 3))) := by
  rw [← summable_nat_add_iff 1]
  have hmaj : Summable fun k : ℕ => 5040 / c ^ 7 * (1 / (((k + 1 : ℕ)) : ℝ) ^ 2) := by
    refine Summable.mul_left _ ?_
    exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_) hmaj
  have hx : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    exact_mod_cast this
  exact deningerCubeRootExp_le hc hx

/-! ## The saving ray series -/

/-- The saving weighted by the reciprocal. -/
def deningerSavingRay (n : ℕ) : ℝ := deningerMertensSaving (n : ℝ) / (n : ℝ)

theorem deningerSavingRay_nonneg (n : ℕ) : 0 ≤ deningerSavingRay n :=
  div_nonneg (deningerMertensSaving_pos _).le (Nat.cast_nonneg n)

theorem deningerSavingRay_antitone ⦃m n : ℕ⦄ (hm : 0 < m) (hmn : m ≤ n) :
    deningerSavingRay n ≤ deningerSavingRay m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmr : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hnr : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hmr (by exact_mod_cast hmn)
  have hlogm : (0 : ℝ) ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hmr (by exact_mod_cast hmn)
  have hcube : Real.log (m : ℝ) ^ ((1 : ℝ) / 3) ≤ Real.log (n : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hlogm hlog (by norm_num)
  have hmnr : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  simp only [deningerSavingRay, deningerMertensSaving]
  have hnum : Real.exp (-((Real.log (n : ℝ)) ^ ((1 : ℝ) / 3) / 108))
      ≤ Real.exp (-((Real.log (m : ℝ)) ^ ((1 : ℝ) / 3) / 108)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 : Real.exp (-((Real.log (n : ℝ)) ^ ((1 : ℝ) / 3) / 108)) / (n : ℝ)
      ≤ Real.exp (-((Real.log (m : ℝ)) ^ ((1 : ℝ) / 3) / 108)) / (n : ℝ) := by
    gcongr
  have h2 : Real.exp (-((Real.log (m : ℝ)) ^ ((1 : ℝ) / 3) / 108)) / (n : ℝ)
      ≤ Real.exp (-((Real.log (m : ℝ)) ^ ((1 : ℝ) / 3) / 108)) / (m : ℝ) := by
    gcongr
  linarith

/-- **The saving ray series converges**, by Cauchy condensation. -/
theorem deningerSavingRay_summable : Summable deningerSavingRay := by
  set c : ℝ := Real.log 2 ^ ((1 : ℝ) / 3) / 108 with hcdef
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by
    rw [hcdef]
    have : (0 : ℝ) < Real.log 2 ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hlog2 _
    positivity
  rw [← summable_condensed_iff_of_nonneg deningerSavingRay_nonneg deningerSavingRay_antitone]
  refine (deningerCubeRootExp_summable hc).congr fun k => ?_
  have hpow : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  rw [deningerSavingRay, deningerMertensSaving, hcast]
  have hlogpow : Real.log ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 := Real.log_pow 2 k
  rw [hlogpow, Real.mul_rpow (Nat.cast_nonneg k) hlog2.le]
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [mul_div_assoc, mul_div_cancel₀ _ (ne_of_gt h2k)]
  congr 1
  rw [hcdef]
  ring

/-! ## The inverse-square summability -/

/-- **The Möbius summatory function is inverse-square summable.**  This is the discrete form of
the only arithmetic input of the Möbius calculus of the ray. -/
theorem deningerMertensM_invSq_summable :
    Summable fun n : ℕ => |Sieve.mertensM n| / (n : ℝ) ^ 2 := by
  obtain ⟨B, hB, hle⟩ := deningerMertensM_div_sq_le
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hle
  rw [← summable_nat_add_iff N₀]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((deningerSavingRay_summable.comp_injective (add_left_injective N₀)).mul_left B)
  exact hN₀ (n + N₀) (Nat.le_add_left N₀ n)

end

end RHTower
