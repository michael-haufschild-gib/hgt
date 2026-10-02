import GaloisForLFunctions.RHTower.Sieve.MertensSecondExpRate
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The actual Mertens error on the logarithmic source clock

The corpus's exponential arithmetic Mertens remainder survives the real
floor substitution. Its quadratic decay is the input needed to replace
the late-prime convolution while preserving the signed first moment.
-/

noncomputable section
open Filter Topology
namespace RHTower

/-- The literal prime reciprocal error, with the corpus's Mertens constant. -/
def criticalMertensLogError (t : ℝ) : ℝ :=
  Sieve.mertensS ⌊Real.exp t⌋₊ - Real.log t - Sieve.meisselMertensConst

private theorem logFloor_exp_control {t : ℝ} (ht : 2 ≤ t) :
    t / 2 ≤ Real.log ⌊Real.exp t⌋₊ ∧
      |Real.log (Real.log ⌊Real.exp t⌋₊) - Real.log t| ≤ 2 * Real.exp (-t) := by
  have he0 := Real.exp_pos t
  have he3 : 3 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hf := Nat.lt_floor_add_one (Real.exp t)
  have hn : Real.exp t / 2 ≤ (⌊Real.exp t⌋₊ : ℝ) := by linarith
  have hn0 : (0 : ℝ) < ⌊Real.exp t⌋₊ := by linarith
  have hnu : (⌊Real.exp t⌋₊ : ℝ) ≤ Real.exp t := Nat.floor_le he0.le
  have hloglo : t - Real.log 2 ≤ Real.log ⌊Real.exp t⌋₊ := by
    have h := Real.log_le_log (div_pos he0 (by norm_num : (0 : ℝ) < 2)) hn
    rwa [Real.log_div he0.ne' (by norm_num), Real.log_exp] at h
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hhalf : t / 2 ≤ Real.log ⌊Real.exp t⌋₊ := by linarith
  have hL1 : 1 ≤ Real.log ⌊Real.exp t⌋₊ := by linarith
  have hL0 : 0 < Real.log ⌊Real.exp t⌋₊ := by linarith
  have hLu : Real.log ⌊Real.exp t⌋₊ ≤ t := by
    have h := Real.log_le_log hn0 hnu
    rwa [Real.log_exp] at h
  have hgap : t - Real.log ⌊Real.exp t⌋₊ ≤ 1 / (⌊Real.exp t⌋₊ : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (div_pos he0 hn0)
    rw [Real.log_div he0.ne' hn0.ne', Real.log_exp] at h
    have hh : Real.exp t / (⌊Real.exp t⌋₊ : ℝ) - 1 ≤ 1 / (⌊Real.exp t⌋₊ : ℝ) := by
      rw [div_sub_one hn0.ne', div_le_div_iff_of_pos_right hn0]
      linarith
    linarith
  have houter : Real.log t - Real.log (Real.log ⌊Real.exp t⌋₊) ≤
      1 / (⌊Real.exp t⌋₊ : ℝ) := by
    have ht0 : 0 < t := by linarith
    have h := Real.log_le_sub_one_of_pos (div_pos ht0 hL0)
    rw [Real.log_div ht0.ne' hL0.ne'] at h
    have hh : t / Real.log ⌊Real.exp t⌋₊ - 1 ≤ 1 / (⌊Real.exp t⌋₊ : ℝ) := by
      rw [div_sub_one hL0.ne', div_le_iff₀ hL0]
      calc
        _ ≤ 1 / (⌊Real.exp t⌋₊ : ℝ) := hgap
        _ ≤ _ := by nlinarith [one_div_nonneg.mpr hn0.le]
    linarith
  have hrec : 1 / (⌊Real.exp t⌋₊ : ℝ) ≤ 2 * Real.exp (-t) := by
    rw [Real.exp_neg, ← one_div,
      show (2 : ℝ) * (1 / Real.exp t) = 2 / Real.exp t by ring,
      div_le_div_iff₀ hn0 he0]
    linarith
  refine ⟨hhalf, ?_⟩
  rw [abs_of_nonpos (by linarith [Real.log_le_log hL0 hLu])]
  linarith

private theorem tendsto_quadratic_sqrt_exp {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-c * Real.sqrt (t / 2))) atTop (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => c * Real.sqrt (t / 2)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).const_mul_atTop hc
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hu).const_mul
    (4 / c ^ (4 : ℕ))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hs : Real.sqrt (t / 2) ^ (4 : ℕ) = (t / 2) ^ (2 : ℕ) := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
  dsimp only [Function.comp_apply]
  rw [mul_pow, hs, show -(c * Real.sqrt (t / 2)) = -c * Real.sqrt (t / 2) by ring]
  field_simp [hc.ne']
  ring

/-- The actual prime reciprocal remainder vanishes after the quadratic
scaling required by the signed moving-head limit. -/
theorem tendsto_criticalMertensLogError_quadratic_zero :
    Tendsto (fun t : ℝ => t ^ (2 : ℕ) * criticalMertensLogError t) atTop (𝓝 0) := by
  obtain ⟨B, c, hc, hB, hr⟩ := Sieve.exists_mertensS_sub_logLog_sub_const_exp_rate
  have hr' := (tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop).eventually hr
  have hb : ∀ᶠ t : ℝ in atTop, ‖t ^ (2 : ℕ) * criticalMertensLogError t‖ ≤
      t ^ (2 : ℕ) * (B * Real.exp (-c * Real.sqrt (t / 2)) + 2 * Real.exp (-t)) := by
    filter_upwards [hr', eventually_ge_atTop (2 : ℝ)] with t ht ht2
    obtain ⟨hL, hfloor⟩ := logFloor_exp_control ht2
    have hexp : Real.exp (-c * Real.sqrt (Real.log ⌊Real.exp t⌋₊)) ≤
        Real.exp (-c * Real.sqrt (t / 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.sqrt_le_sqrt hL]
    have herror : |criticalMertensLogError t| ≤
        B * Real.exp (-c * Real.sqrt (t / 2)) + 2 * Real.exp (-t) := by
      calc
        _ = |(Sieve.mertensS ⌊Real.exp t⌋₊ - Sieve.logLog ⌊Real.exp t⌋₊ -
            Sieve.meisselMertensConst) +
            (Real.log (Real.log ⌊Real.exp t⌋₊) - Real.log t)| := by
          congr 1
          dsimp [criticalMertensLogError, Sieve.logLog]
          ring
        _ ≤ _ := (abs_add_le _ _).trans
          (add_le_add (ht.trans (mul_le_mul_of_nonneg_left hexp hB)) hfloor)
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)] using
      mul_le_mul_of_nonneg_left herror (sq_nonneg t)
  apply squeeze_zero_norm' hb
  have h := ((tendsto_quadratic_sqrt_exp hc).const_mul B).add
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul 2)
  simp only [mul_zero, add_zero] at h
  convert h using 1
  funext t
  ring

end RHTower
