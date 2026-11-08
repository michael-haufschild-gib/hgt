import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainVKCost
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainVKDilation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Absorption of arithmetic contour losses

Logarithmic width absorbs every fixed polynomial loss. Combining this with
the width dilation estimate preserves the full Vinogradov–Korobov saving.
-/

open RHTower Filter Topology
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Logarithms at the doubled height stay within twice the original logarithm. -/
theorem log_double_add_one_le {L : ℝ} (hL : 3 ≤ L) :
    Real.log (2 * L + 1) ≤ 2 * Real.log L := by
  have hs : 2 * L + 1 ≤ L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 3)]
  have h := Real.log_le_log (show 0 < 2 * L + 1 by linarith only [hL]) hs
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- Every fixed polynomial loss is absorbed by half the arithmetic contour saving. -/
theorem eventually_pow_le_exp_narainVKWidth {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, L ^ k ≤ Real.exp (narainVKWidth δ L * L / 2) := by
  let a : ℝ := min δ 1
  have ha : 0 < a := lt_min hδ zero_lt_one
  have heps : 0 < a / (32 * ((k : ℝ) + 1)) := by positivity
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1) (by norm_num)).bound heps
  filter_upwards [hsmall, eventually_narainVKWidth_ge_inv_log hδ,
    eventually_ge_atTop (3 : ℝ)] with L hs hw hL
  have hL0 : 0 < L := by linarith only [hL]
  have hl : 0 < Real.log L := Real.log_pos (by linarith only [hL])
  have hlg : 0 < Real.log (2 * L + 1) := Real.log_pos (by linarith only [hL])
  have hs' : Real.log L ^ 2 ≤ a / (32 * ((k : ℝ) + 1)) * L := by
    simpa only [Real.rpow_two, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log L)), abs_of_pos hL0] using hs
  have hscaled := mul_le_mul_of_nonneg_left hs'
    (show 0 ≤ 32 * ((k : ℝ) + 1) by positivity)
  have heq : (32 * ((k : ℝ) + 1)) * (a / (32 * ((k : ℝ) + 1)) * L) = a * L := by
    field_simp [ne_of_gt (show 0 < (k : ℝ) + 1 by positivity)]
  rw [heq] at hscaled
  have hpolylog : (k : ℝ) * Real.log L ≤ a * L / (32 * Real.log L) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hscaled, sq_nonneg (Real.log L)]
  have hlog := log_double_add_one_le hL
  have hcost : a * L / (32 * Real.log L) ≤ a * L / (16 * Real.log (2 * L + 1)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith only [hlog]
  have hwidth : a * L / (16 * Real.log (2 * L + 1)) ≤ narainVKWidth δ L * L / 2 := by
    have h := mul_le_mul_of_nonneg_right hw (show 0 ≤ L / 2 by positivity)
    change a / (8 * Real.log (2 * L + 1)) * (L / 2) ≤ _ at h
    calc
      _ = a / (8 * Real.log (2 * L + 1)) * (L / 2) := by ring
      _ ≤ narainVKWidth δ L * (L / 2) := h
      _ = _ := by ring
  calc
    L ^ k = Real.exp ((k : ℝ) * Real.log L) := by
      rw [Real.exp_nat_mul, Real.exp_log hL0]
    _ ≤ _ := Real.exp_le_exp.mpr (hpolylog.trans (hcost.trans hwidth))

/-- The reciprocal arithmetic cost contributes only a fixed polynomial at the logarithmic height. -/
theorem eventually_narainVKCost_polynomial (N : ℕ) :
    ∀ᶠ L : ℝ in atTop, (1 + L) ^ N * narainVKCost L ≤
      (2 ^ N * 3 ^ (7 : ℕ) * 2 ^ (14 : ℕ)) * L ^ (N + 14) := by
  filter_upwards [eventually_narainVKCost_le_log_power, eventually_ge_atTop (3 : ℝ)] with L hQ hL
  have hL0 : 0 < L := by linarith only [hL]
  have hlog : Real.log (2 * L + 1) ≤ 2 * L := by
    have h := Real.log_le_sub_one_of_pos hL0
    exact (log_double_add_one_le hL).trans (by linarith only [h])
  have hlog0 : 0 ≤ Real.log (2 * L + 1) := Real.log_nonneg (by linarith only [hL])
  have hp : (1 + L) ^ N ≤ (2 * L) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hL]) N
  have hq : Real.log (2 * L + 1) ^ (14 : ℕ) ≤ (2 * L) ^ (14 : ℕ) :=
    pow_le_pow_left₀ hlog0 hlog 14
  calc
    _ ≤ (1 + L) ^ N * (3 ^ (7 : ℕ) * Real.log (2 * L + 1) ^ (14 : ℕ)) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    _ ≤ (2 * L) ^ N * (3 ^ (7 : ℕ) * (2 * L) ^ (14 : ℕ)) := by gcongr
    _ = _ := by rw [pow_add, mul_pow, mul_pow]; ring

/-- Polynomial losses and exponential tails preserve the full Vinogradov–Korobov profile. -/
theorem exists_narainVK_saving {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ L : ℝ in atTop,
      (1 + L) ^ N * narainVKCost L *
        (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(Real.pi * L / 4))) ≤
          C * Real.exp (-(c * L * vkHadamardWidth L)) := by
  let D : ℝ := 2 ^ N * 3 ^ (7 : ℕ) * 2 ^ (14 : ℕ)
  have hD : 0 < D := by dsimp only [D]; positivity
  have ha : 0 < min δ 1 := lt_min hδ zero_lt_one
  refine ⟨2 * D, min δ 1 / 128, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_narainVKCost_polynomial N,
    eventually_pow_le_exp_narainVKWidth hδ (N + 14),
    eventually_ge_atTop (Real.exp (Real.exp 1))] with L hcost hpow hL
  have hL0 : 0 < L := (Real.exp_pos _).trans_le hL
  have hwidth := narainVKWidth_ge_profile hδ hL
  have hd8 : narainVKWidth δ L ≤ 1 / 8 := by
    unfold narainVKWidth
    exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right δ 1)) (by norm_num)
  have hQ : 1 ≤ narainVKCost L := one_le_narainVKCost (by linarith only [hL, hL0])
  have htail : Real.exp (-(Real.pi * L / 4)) ≤ Real.exp (-(narainVKWidth δ L * L)) := by
    apply Real.exp_le_exp.mpr
    have hp := Real.pi_gt_three
    nlinarith only [hd8, hp, hL0]
  have hexp : Real.exp (narainVKWidth δ L * L / 2) *
      Real.exp (-(narainVKWidth δ L * L)) = Real.exp (-(narainVKWidth δ L * L / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprofile : Real.exp (-(narainVKWidth δ L * L / 2)) ≤
      Real.exp (-(min δ 1 / 128 * L * vkHadamardWidth L)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hwidth (show 0 ≤ L / 2 by positivity)
    nlinarith only [h]
  change (1 + L) ^ N * narainVKCost L ≤ D * L ^ (N + 14) at hcost
  calc
    _ ≤ (D * L ^ (N + 14)) *
        (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(narainVKWidth δ L * L))) := by gcongr
    _ = 2 * D * L ^ (N + 14) * Real.exp (-(narainVKWidth δ L * L)) := by ring
    _ ≤ 2 * D * Real.exp (narainVKWidth δ L * L / 2) *
        Real.exp (-(narainVKWidth δ L * L)) := by gcongr
    _ = 2 * D * Real.exp (-(narainVKWidth δ L * L / 2)) := by rw [mul_assoc, hexp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hprofile (by positivity)

#print axioms eventually_narainVKCost_polynomial
#print axioms exists_narainVK_saving

#print axioms eventually_pow_le_exp_narainVKWidth
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
