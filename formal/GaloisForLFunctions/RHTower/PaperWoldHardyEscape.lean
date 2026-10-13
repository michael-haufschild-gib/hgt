import GaloisForLFunctions.RHTower.PaperWoldHardyContraction
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Power tails escaping every fixed Hardy coordinate

Normalized square-summable power tails supply weakly null tests. Integral
comparison retains the sharp asymptotic constant at every escaping cutoff.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators

def paperWoldHardyPowerTail (a : {a : ℝ // 1 / 2 < a}) (K n : ℕ) : ℝ :=
  if K ≤ n then ((n : ℝ) + 1) ^ (-(a : ℝ)) else 0

theorem paperWoldHardyPowerTail_nonneg (a : {a : ℝ // 1 / 2 < a}) (K n : ℕ) :
    0 ≤ paperWoldHardyPowerTail a K n := by
  unfold paperWoldHardyPowerTail
  split_ifs <;> positivity

theorem paperWoldHardyPowerTail_summable_sq (a : {a : ℝ // 1 / 2 < a}) (K : ℕ) :
    Summable (fun n => paperWoldHardyPowerTail a K n ^ 2) := by
  have hs := (Real.summable_nat_rpow.mpr (show -(a : ℝ) * 2 < -1 by linarith [a.property])).comp_injective
    Nat.succ_injective
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hs
  dsimp [Function.comp_def]
  rw [Nat.cast_succ, Real.rpow_mul (by positivity), Real.rpow_two]
  unfold paperWoldHardyPowerTail
  split_ifs <;> simp [sq_nonneg]

def paperWoldHardyPowerHistory (a : {a : ℝ // 1 / 2 < a}) (K : ℕ) : PaperWoldHistory :=
  ⟨fun n => (paperWoldHardyPowerTail a K n : ℂ), HilbertSchmidt.memℓp_of_sq (by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using paperWoldHardyPowerTail_summable_sq a K)⟩

theorem paperWoldHardyPowerHistory_ne_zero (a : {a : ℝ // 1 / 2 < a}) (K : ℕ) :
    paperWoldHardyPowerHistory a K ≠ 0 := by
  intro h
  have he := congrArg (fun f : PaperWoldHistory => f K) h
  have hp : 0 < ((K : ℝ) + 1) ^ (-(a : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  simp only [paperWoldHardyPowerHistory, paperWoldHardyPowerTail, le_refl, if_true,
    lp.coeFn_zero, Pi.zero_apply, Complex.ofReal_eq_zero] at he
  exact hp.ne' he

def paperWoldHardyPowerUnit (a : {a : ℝ // 1 / 2 < a}) (K : ℕ) : PaperWoldHistory :=
  (‖paperWoldHardyPowerHistory a K‖ : ℂ)⁻¹ • paperWoldHardyPowerHistory a K

theorem paperWoldHardyPowerUnit_norm (a : {a : ℝ // 1 / 2 < a}) (K : ℕ) :
    ‖paperWoldHardyPowerUnit a K‖ = 1 :=
  norm_smul_inv_norm (paperWoldHardyPowerHistory_ne_zero a K)

theorem paperWoldHardyPowerUnit_coord_tendsto (a : {a : ℝ // 1 / 2 < a}) (n : ℕ) :
    Tendsto (fun K => paperWoldHardyPowerUnit a K n) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop n] with K hK
  simp [paperWoldHardyPowerUnit, lp.coeFn_smul, paperWoldHardyPowerHistory,
    paperWoldHardyPowerTail, not_le.mpr hK]

theorem paperWoldHardyPowerUnit_weaklyNull (a : {a : ℝ // 1 / 2 < a}) (z : PaperWoldHistory) :
    Tendsto (fun K => inner ℂ z (paperWoldHardyPowerUnit a K)) atTop (𝓝 0) :=
  tendsto_inner_lp_of_coord (paperWoldHardyPowerUnit a) zero_le_one
    (fun K => (paperWoldHardyPowerUnit_norm a K).le) (paperWoldHardyPowerUnit_coord_tendsto a) z

private theorem power_tail_integral_lower (a : ℝ) (ha : 0 < a) (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ^ (-a) / a ≤ ∑' i : ℕ, ((i + N : ℕ) : ℝ) ^ (-a - 1) := by
  have hs : Summable (fun i : ℕ => (i : ℝ) ^ (-a - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-a - 1)) (Set.Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le (by exact_mod_cast hN) hx) hxy (by linarith)
  have h := hanti.integral_le_tsum_comp_add N hs
    (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans (Nat.cast_pos.mpr hN) hx)) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -a - 1 < -1) (by exact_mod_cast hN),
    show -a - 1 + 1 = -a by ring] at h
  simpa only [neg_div_neg_eq] using h

theorem paperWoldHardyPowerHistory_row_lower (a : {a : ℝ // 1 / 2 < a}) (K n : ℕ)
    (hKn : K ≤ n) :
    ((n : ℝ) + 2) ^ (-(a : ℝ)) / (2 * (a : ℝ)) ≤
      (paperWoldHardyOperator (paperWoldHardyPowerHistory a K) n).re := by
  have ha : 0 < (a : ℝ) := by linarith [a.property]
  have hs : Summable (fun i : ℕ => (i : ℝ) ^ (-(a : ℝ) - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift := hs.comp_injective (show Function.Injective (fun i : ℕ => i + (n + 2)) from
    fun i j h => Nat.add_right_cancel h)
  have hrow := strictHalfHardyKernel_summable_row (paperWoldHardyPowerTail_nonneg a K)
    (paperWoldHardyPowerTail_summable_sq a K) n
  have hle : (1 / 2 : ℝ) * (∑' i : ℕ, ((i + (n + 2) : ℕ) : ℝ) ^ (-(a : ℝ) - 1)) ≤
      ∑' j, strictHalfHardyKernel n j * paperWoldHardyPowerTail a K j := by
    rw [← tsum_mul_left]
    apply Summable.tsum_le_tsum_of_inj (fun i => i + (n + 1))
      (fun i j h => Nat.add_right_cancel h)
      (fun j hj => mul_nonneg (strictHalfHardyKernel_nonneg n j) (paperWoldHardyPowerTail_nonneg a K j))
      (fun i => ?_) (hshift.mul_left (1 / 2)) hrow
    rw [strictHalfHardyKernel, if_pos (by omega), paperWoldHardyPowerTail, if_pos (by omega)]
    dsimp only [Function.comp_def]
    have he : (((i + (n + 2) : ℕ) : ℝ)) = ((i + (n + 1) : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [he, Real.rpow_sub (by positivity), Real.rpow_one]
    exact le_of_eq (by field_simp)
  have hi := mul_le_mul_of_nonneg_left (power_tail_integral_lower (a : ℝ) ha (n + 2) (by omega))
    (by positivity : (0 : ℝ) ≤ 1 / 2)
  have he : (paperWoldHardyOperator (paperWoldHardyPowerHistory a K) n).re =
      ∑' j, strictHalfHardyKernel n j * paperWoldHardyPowerTail a K j := by
    rw [paperWoldHardyOperator_apply]
    simp_rw [paperWoldHardyEntry_eq_strictHalfHardyKernel]
    change (∑' j, (strictHalfHardyKernel n j : ℂ) * (paperWoldHardyPowerTail a K j : ℂ)).re = _
    simp_rw [← Complex.ofReal_mul]
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [he]
  calc
    _ = (1 / 2 : ℝ) * (((n + 2 : ℕ) : ℝ) ^ (-(a : ℝ)) / (a : ℝ)) := by
      push_cast
      ring
    _ ≤ _ := hi.trans hle

end
end RHTower
