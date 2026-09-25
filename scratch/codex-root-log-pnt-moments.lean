import GaloisForLFunctions.HTGeometry.SubexponentialSqrtSummable
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.HTGeometry

theorem summable_log_pow_exp_neg_sqrt_log_div (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Summable (fun n : ℕ =>
      Real.log (n : ℝ) ^ k *
        Real.exp (-(c * Real.sqrt (Real.log (n : ℝ)))) / (n : ℝ)) := by
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hdecay : Tendsto (fun x : ℝ =>
      x ^ ((2 * k : ℕ) : ℝ) * Real.exp (-(c / 2) * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (by positivity)
  have hsmall := (hdecay.comp hroot).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hbound : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ^ k *
        Real.exp (-(c / 2) * Real.sqrt (Real.log (n : ℝ))) ≤ 1 := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
    have heq : Real.sqrt (Real.log (n : ℝ)) ^ ((2 * k : ℕ) : ℝ) =
        Real.log (n : ℝ) ^ k := by
      rw [Real.rpow_natCast, pow_mul, Real.sq_sqrt hlog]
    simp only [Function.comp_apply] at hn
    rw [heq] at hn
    exact hn.le
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound
  have hbase : Summable (fun n : ℕ =>
      Real.exp (-((c / 2) * Real.sqrt (Real.log (n : ℝ)))) / (n : ℝ)) :=
    summable_exp_neg_sqrt_log_div (by positivity : 0 < c / 2)
  apply (summable_nat_add_iff N).1
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_nat_add_iff N).2 hbase)
  have hn : Real.log ((n + N : ℕ) : ℝ) ^ k *
      Real.exp (-(c / 2) * Real.sqrt (Real.log ((n + N : ℕ) : ℝ))) ≤ 1 :=
    hN (n + N) (by omega)
  have hexp : Real.exp (-(c * Real.sqrt (Real.log ((n + N : ℕ) : ℝ)))) =
      Real.exp (-(c / 2) * Real.sqrt (Real.log ((n + N : ℕ) : ℝ))) *
        Real.exp (-(c / 2) * Real.sqrt (Real.log ((n + N : ℕ) : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hmul := mul_le_mul_of_nonneg_right hn
    (Real.exp_pos (-(c / 2) * Real.sqrt (Real.log ((n + N : ℕ) : ℝ)))).le
  have hden : (0 : ℝ) ≤ (n + N : ℕ) := by positivity
  exact div_le_div_of_nonneg_right (by simpa [mul_assoc] using hmul) hden

end GaloisForLFunctions.HTGeometry

namespace RHTower

theorem summable_psi_error_weight_log_pow (k : ℕ) :
    Summable (fun n : ℕ =>
      |Chebyshev.psi ((n : ℝ) + 1) - ((n : ℝ) + 1)| *
        Real.log ((n : ℝ) + 1) ^ k / (((n : ℝ) + 1) ^ (2 : ℕ))) := by
  obtain ⟨C, c, hc, hC, hbound⟩ := exists_psi_error_eventually
  obtain ⟨X, hX⟩ := eventually_atTop.1 hbound
  obtain ⟨N, hN⟩ := exists_nat_ge (max X 1)
  have hbase := GaloisForLFunctions.HTGeometry.summable_log_pow_exp_neg_sqrt_log_div c hc k
  have hmaj : Summable (fun n : ℕ =>
      C * (Real.log ((n + (N + 1) : ℕ) : ℝ) ^ k *
        Real.exp (-(c * Real.sqrt (Real.log ((n + (N + 1) : ℕ) : ℝ)))) /
          ((n + (N + 1) : ℕ) : ℝ))) :=
    ((summable_nat_add_iff (N + 1)).2 hbase).mul_left C
  apply (summable_nat_add_iff N).1
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · have hxge : (1 : ℝ) ≤ ((n + N : ℕ) : ℝ) + 1 := by
      have hnnonneg : (0 : ℝ) ≤ ((n + N : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    exact div_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (Real.log_nonneg hxge) _))
      (sq_nonneg _)
  set x : ℝ := ((n + (N + 1) : ℕ) : ℝ) with hx
  have hxval : ((n + N : ℕ) : ℝ) + 1 = x := by
    rw [hx]
    push_cast
    ring
  have hxpos : 0 < x := by rw [hx]; positivity
  have hXle : X ≤ x := by
    have h1 : X ≤ max X 1 := le_max_left X 1
    have h2 : max X 1 ≤ (N : ℝ) := hN
    have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [hx]
    push_cast
    linarith
  have hb := hX x hXle
  rw [hxval]
  have hmul := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ Real.log x ^ k / x ^ (2 : ℕ) by positivity)
  have heq : (C * (x * Real.exp (-c * Real.sqrt (Real.log x)))) *
      (Real.log x ^ k / x ^ (2 : ℕ)) =
      C * (Real.log x ^ k * Real.exp (-c * Real.sqrt (Real.log x)) / x) := by
    field_simp
  simpa only [neg_mul, mul_div_assoc] using hmul.trans_eq heq

end RHTower
