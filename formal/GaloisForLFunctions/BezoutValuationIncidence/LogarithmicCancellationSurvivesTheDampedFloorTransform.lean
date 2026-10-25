import GaloisForLFunctions.BezoutValuationIncidence.HyperbolaCancellationWithDivisorBoundedCoefficients
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic cancellation through the damped floor transform

A cutoff at `n / (log n)^b` keeps the long blocks in the same logarithmic range.
The divisor-square head and the signed reciprocal tail then preserve every
uniform logarithmic saving for the centered damped floor transform.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem eventually_two_mul_log_pow_le_sqrt (b : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2 * Real.log (n : ℝ) ^ b ≤ Real.sqrt n := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ b / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast, Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_rpow_atTop (b : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop)
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h := (div_lt_iff₀ (Real.sqrt_pos.2 hn0)).mp hn
  linarith only [h]

/-- A logarithmic loss in the cutoff preserves its logarithmic scale and leaves it above the square root. -/
theorem eventually_logarithmic_hyperbola_cutoff_bounds (b : ℕ) :
    ∀ᶠ n : ℕ in atTop, let D := ⌊(n : ℝ) / Real.log (n : ℝ) ^ b⌋₊
      1 ≤ D ∧ D ≤ n ∧ Real.sqrt n ≤ (D : ℝ) ∧
        (n : ℝ) / (2 * Real.log (n : ℝ) ^ b) ≤ D ∧
          Real.log (n : ℝ) / 2 ≤ Real.log (D : ℝ) := by
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_two_mul_log_pow_le_sqrt b,
    hloglim.eventually_ge_atTop 1, eventually_ge_atTop 1] with n hsmall hlog hn
  let D := ⌊(n : ℝ) / Real.log (n : ℝ) ^ b⌋₊
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
  have hlp : 0 < Real.log (n : ℝ) ^ b := pow_pos hl b
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hs2 : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt hn0.le
  have hratio : 2 * Real.sqrt (n : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ b := by
    apply (le_div_iff₀ hlp).mpr
    have h := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg (n : ℝ))
    nlinarith only [h, hs2]
  have hfloor := Nat.lt_floor_add_one ((n : ℝ) / Real.log (n : ℝ) ^ b)
  have hsD : Real.sqrt (n : ℝ) ≤ (D : ℝ) := by
    change (n : ℝ) / Real.log (n : ℝ) ^ b < (D : ℝ) + 1 at hfloor
    linarith only [hfloor, hratio, hs1]
  have hhalf : (n : ℝ) / (2 * Real.log (n : ℝ) ^ b) ≤ D := by
    change (n : ℝ) / Real.log (n : ℝ) ^ b < (D : ℝ) + 1 at hfloor
    have heq : (n : ℝ) / (2 * Real.log (n : ℝ) ^ b) =
        ((n : ℝ) / Real.log (n : ℝ) ^ b) / 2 := by ring
    rw [heq]
    linarith only [hfloor, hratio, hs1]
  have hD1 : 1 ≤ D := by exact_mod_cast hs1.trans hsD
  have hDn : D ≤ n := by
    apply Nat.floor_le_of_le
    exact div_le_self hn0.le (one_le_pow₀ hlog)
  refine ⟨hD1, hDn, hsD, hhalf, ?_⟩
  have h := Real.log_le_log (Real.sqrt_pos.2 hn0) hsD
  rw [Real.sqrt_eq_rpow, Real.log_rpow hn0] at h
  linarith only [h]

private theorem logarithmic_cutoff_head_bound {ε C : ℝ} (hε2 : ε ≤ 1 / 2)
    (hC : 0 ≤ C) (q : ℕ) {n D : ℕ} (hlog : 1 ≤ Real.log (n : ℝ)) (hD : 1 ≤ D)
    (hDn : D ≤ n) (hcut : (D : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ (2 * (q + 5))) :
    C * (D : ℝ) ^ (1 - ε) * (1 + Real.log (D : ℝ)) ^ 4 ≤
      16 * C * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (hD.trans hDn)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hl : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
  have hDlog : Real.log (D : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hD0 (by exact_mod_cast hDn)
  have hpoly : (1 + Real.log (D : ℝ)) ^ 4 ≤ 16 * Real.log (n : ℝ) ^ 4 := by
    have h0 : 0 ≤ 1 + Real.log (D : ℝ) := by
      have h := Real.log_nonneg (show (1 : ℝ) ≤ D by exact_mod_cast hD)
      linarith only [h]
    have h := pow_le_pow_left₀ h0 (show 1 + Real.log (D : ℝ) ≤ 2 * Real.log (n : ℝ) by
      linarith only [hDlog, hlog]) 4
    simpa only [mul_pow, show (2 : ℝ) ^ 4 = 16 by norm_num] using h
  have hden : Real.log (n : ℝ) ^ (q + 4) ≤
      (Real.log (n : ℝ) ^ (2 * (q + 5))) ^ (1 - ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hl.le]
    apply Real.rpow_le_rpow_of_exponent_le hlog
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hε2
      (by positivity : 0 ≤ 2 * ((q : ℝ) + 5))]
  have hpower : (D : ℝ) ^ (1 - ε) ≤
      (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ (q + 4) := by
    calc
      _ ≤ ((n : ℝ) / Real.log (n : ℝ) ^ (2 * (q + 5))) ^ (1 - ε) :=
        Real.rpow_le_rpow hD0.le hcut (by linarith only [hε2])
      _ = (n : ℝ) ^ (1 - ε) / (Real.log (n : ℝ) ^ (2 * (q + 5))) ^ (1 - ε) :=
        Real.div_rpow hn0.le (pow_nonneg hl.le _) _
      _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hn0.le _) (pow_pos hl _) hden
  calc
    _ ≤ (C * ((n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ (q + 4))) *
        (16 * Real.log (n : ℝ) ^ 4) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpower hC) hpoly (by positivity) (by positivity)
    _ = _ := by
      rw [pow_add]
      field_simp [hl.ne']

private theorem logarithmic_cutoff_tail_bound {ε B : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hB : 0 ≤ B) (q b : ℕ) {n D : ℕ} (hlog : 1 ≤ Real.log (n : ℝ)) (hn : 1 ≤ n)
    (hD : (n : ℝ) / (2 * Real.log (n : ℝ) ^ b) ≤ D)
    (hlogD : Real.log (n : ℝ) / 2 ≤ Real.log (D : ℝ)) :
    13 / ε * (B / Real.log (D : ℝ) ^ (q + b)) * n * (D : ℝ) ^ (-ε) ≤
      (13 / ε * 2 ^ (q + b + 1) * B) * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
  have hden0 : 0 < 2 * Real.log (n : ℝ) ^ b := by positivity
  have hD0 : (0 : ℝ) < D := (div_pos hn0 hden0).trans_le hD
  have hlogD0 : 0 < Real.log (D : ℝ) := (by positivity : 0 < Real.log (n : ℝ) / 2).trans_le hlogD
  have hL : B / Real.log (D : ℝ) ^ (q + b) ≤
      2 ^ (q + b) * B / Real.log (n : ℝ) ^ (q + b) := by
    calc
      _ ≤ B / (Real.log (n : ℝ) / 2) ^ (q + b) :=
        div_le_div_of_nonneg_left hB (by positivity)
          (pow_le_pow_left₀ (by positivity) hlogD _)
      _ = _ := by rw [div_pow]; field_simp [hl.ne']
  have hDP : (D : ℝ) ^ (-ε) ≤ (n : ℝ) ^ (-ε) * (2 * Real.log (n : ℝ) ^ b) := by
    calc
      _ ≤ ((n : ℝ) / (2 * Real.log (n : ℝ) ^ b)) ^ (-ε) :=
        Real.rpow_le_rpow_of_nonpos (div_pos hn0 hden0) hD (by linarith only [hε])
      _ = (n : ℝ) ^ (-ε) * (2 * Real.log (n : ℝ) ^ b) ^ ε := by
        rw [Real.div_rpow hn0.le hden0.le, div_eq_mul_inv, ← Real.rpow_neg hden0.le, neg_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by
          have hbase : 1 ≤ 2 * Real.log (n : ℝ) ^ b := by
            have := one_le_pow₀ (n := b) hlog
            linarith only [this]
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase
            (by linarith only [hε2] : ε ≤ 1))
        (Real.rpow_nonneg hn0.le _)
  have hnp : (n : ℝ) * (n : ℝ) ^ (-ε) = (n : ℝ) ^ (1 - ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one]
  calc
    _ ≤ (13 / ε * (2 ^ (q + b) * B / Real.log (n : ℝ) ^ (q + b)) * n) *
        ((n : ℝ) ^ (-ε) * (2 * Real.log (n : ℝ) ^ b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL (by positivity)) hn0.le) hDP
          (Real.rpow_nonneg hD0.le _) (by positivity)
    _ = (13 / ε * 2 ^ (q + b + 1) * B) *
        ((n : ℝ) * (n : ℝ) ^ (-ε)) / Real.log (n : ℝ) ^ q := by
      simp only [pow_add, pow_one]
      field_simp [hl.ne']
    _ = _ := by rw [hnp]

/-- Uniform logarithmic cancellation survives the damped floor transform for divisor-square bounded families. -/
theorem exists_uniform_weightCenteredPrefix_dampedSign_log_rate_of_divisor_square
    {ι : Type*} {s : ι → ℕ → ℝ} {ε C : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hC : 0 ≤ C)
    (hs : ∀ a d, 1 ≤ d → |s a d| ≤ C * (d.divisors.card : ℝ) ^ 2)
    (hsum : ∀ a, Summable (fun d : ℕ => dampedSignWeight (s a) ε d / d))
    (hS : ∀ p : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ x : ℕ in atTop, ∀ a,
      |∑ d ∈ Icc 1 x, s a d| ≤ B * x / Real.log (x : ℝ) ^ p) (q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop, ∀ a,
      |weightCenteredPrefix (dampedSignWeight (s a) ε)
        (∑' d : ℕ, dampedSignWeight (s a) ε d / d) n| ≤
          K * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q := by
  let b : ℕ := 2 * (q + 5)
  obtain ⟨B, hB, hSB⟩ := hS (q + b)
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp hSB
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrtlim : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  refine ⟨16 * C + 13 / ε * 2 ^ (q + b + 1) * B, by positivity, ?_⟩
  filter_upwards [eventually_logarithmic_hyperbola_cutoff_bounds b,
    hloglim.eventually_ge_atTop 1, hsqrtlim.eventually_ge_atTop (D₀ : ℝ),
    eventually_ge_atTop 1] with n hcut hlog hstart hn a
  let D := ⌊(n : ℝ) / Real.log (n : ℝ) ^ b⌋₊
  change 1 ≤ D ∧ D ≤ n ∧ Real.sqrt n ≤ (D : ℝ) ∧
    (n : ℝ) / (2 * Real.log (n : ℝ) ^ b) ≤ D ∧
      Real.log (n : ℝ) / 2 ≤ Real.log (D : ℝ) at hcut
  obtain ⟨hD, hDn, hsD, hhalf, hlogD⟩ := hcut
  have hD₀D : D₀ ≤ D := by exact_mod_cast hstart.trans hsD
  have hl : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
  have hld : 0 < Real.log (D : ℝ) := (by positivity : 0 < Real.log (n : ℝ) / 2).trans_le hlogD
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hlinear (x : ℕ) (hx : D ≤ x) :
      |∑ d ∈ Icc 1 x, s a d| ≤ (B / Real.log (D : ℝ) ^ (q + b)) * x := by
    calc
      _ ≤ B * x / Real.log (x : ℝ) ^ (q + b) := hD₀ x (hD₀D.trans hx) a
      _ ≤ B * x / Real.log (D : ℝ) ^ (q + b) :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hld _)
          (pow_le_pow_left₀ hld.le (Real.log_le_log hD0 (by exact_mod_cast hx)) _)
      _ = _ := by ring
  have hbase := abs_weightCenteredPrefix_dampedSign_le_head_of_linear
    (by positivity : 0 ≤ B / Real.log (D : ℝ) ^ (q + b)) hε hε2 (hsum a) hD hDn hlinear
  have hhead := (sum_abs_mul_rpow_le_divisor_square_head
    (by linarith only [hε2] : ε ≤ 1) hC (hs a) hD).trans
      (logarithmic_cutoff_head_bound hε2 hC q hlog hD hDn
        (Nat.floor_le (by positivity : 0 ≤ (n : ℝ) / Real.log (n : ℝ) ^ b)))
  have htail := logarithmic_cutoff_tail_bound hε hε2 hB q b hlog hn hhalf hlogD
  exact hbase.trans ((add_le_add hhead htail).trans_eq (by ring))

end GaloisForLFunctions.BezoutValuationIncidence
