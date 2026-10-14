import GaloisForLFunctions.RHTower.PaperLagCayleyCriticalEnergy
import GaloisForLFunctions.RHTower.PrimePowerLogarithmicDensity
import GaloisForLFunctions.HTGeometry.SchattenLogResiduePowerFiniteRank

/-! # Exact critical logarithmic residue of the full lag-source discrepancy

The non-prime-power phase determines the critical coefficient. Prime powers
have zero harmonic logarithmic density, and finite-coordinate energy differs
from singular-value energy by a bounded amount.
-/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Filter _root_.Complex
open scoped Topology

private def bulkPhaseGap (n : ℕ) : ℂ :=
  realCayley (source n - arithmetic n - 1) - realCayley (-1)

private theorem source_gap_tendsto_zero :
    Tendsto (fun n => source n - arithmetic n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using summable_source_discrepancy.tendsto_atTop_zero

private theorem bulkPhaseGap_norm_le (n : ℕ) :
    ‖bulkPhaseGap n‖ ≤ 2 * |source n - arithmetic n| := by
  simpa only [bulkPhaseGap, sub_neg_eq_add, sub_add_cancel] using
    paperRealCayley_norm_sub_le (source n - arithmetic n - 1) (-1)

private theorem bulkPhaseGap_tendsto_zero :
    Tendsto (fun n => ‖bulkPhaseGap n‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _) bulkPhaseGap_norm_le
  simpa only [abs_zero, mul_zero] using source_gap_tendsto_zero.abs.const_mul 2

private theorem bulkPhaseGap_quadratic_tendsto :
    Tendsto (fun n : ℕ => ((n + 3 : ℝ) ^ 2 : ℂ) * bulkPhaseGap n)
      atTop (𝓝 (1 / 6 : ℂ)) := by
  have hd := ((source_gap_tendsto_zero.sub_const 1).ofReal.add_const I).mul_const
    (((-1 : ℝ) : ℂ) + I)
  simp only [zero_sub] at hd
  have h := (source_discrepancy_quadratic_tendsto.ofReal.const_mul (2 * I)).div hd
    (mul_ne_zero (real_add_I_ne_zero (-1)) (real_add_I_ne_zero (-1)))
  have hc : 2 * I * ((-(1 / 6) : ℝ) : ℂ) /
      ((((-1 : ℝ) : ℂ) + I) * (((-1 : ℝ) : ℂ) + I)) = (1 / 6 : ℂ) := by
    norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  rw [hc] at h
  convert! h using 1
  funext n
  change _ = 2 * I * (((n + 3 : ℝ) ^ 2 * (source n - arithmetic n) : ℝ) : ℂ) /
    ((((source n - arithmetic n - 1 : ℝ) : ℂ) + I) * (((-1 : ℝ) : ℂ) + I))
  rw [bulkPhaseGap, paperRealCayley_sub]
  push_cast
  ring

private theorem bulkPhaseGap_sqrt_residue :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, Real.sqrt ‖bulkPhaseGap n‖) /
      Real.log (N + 1)) atTop (𝓝 (1 / Real.sqrt 6)) := by
  have hn : Tendsto (fun n : ℕ => (n + 3 : ℝ) ^ 2 * ‖bulkPhaseGap n‖)
      atTop (𝓝 (1 / 6 : ℝ)) := by
    have h := bulkPhaseGap_quadratic_tendsto.norm
    have hn (n : ℕ) : ‖((n + 3 : ℝ) ^ 2 : ℂ)‖ = (n + 3 : ℝ) ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [norm_mul, hn, norm_div, norm_one, norm_ofNat] using h
  have hs : Tendsto (fun n : ℕ => (n + 3 : ℝ) * Real.sqrt ‖bulkPhaseGap n‖)
      atTop (𝓝 (1 / Real.sqrt 6)) := by
    have he (n : ℕ) : Real.sqrt ((n + 3 : ℝ) ^ 2 * ‖bulkPhaseGap n‖) =
        (n + 3 : ℝ) * Real.sqrt ‖bulkPhaseGap n‖ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    simpa only [he, Real.sqrt_div zero_le_one, Real.sqrt_one] using hn.sqrt
  have hz := bulkPhaseGap_tendsto_zero.sqrt.const_mul 2
  simp only [Real.sqrt_zero, mul_zero] at hz
  have ht := hs.sub hz
  rw [sub_zero] at ht
  apply tendsto_logResidue_succ_of_mul_succ_tendsto
  convert ht using 1
  funext n
  ring

private theorem sqrt_bulkPhaseGap_le (n : ℕ) :
    Real.sqrt ‖bulkPhaseGap n‖ ≤ 22 / (n + 3 : ℝ) := by
  by_cases hn : 9 ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm 9 k]
    have ht : ‖bulkPhaseGap (k + 9)‖ ≤ 1 / (3 * (k + 12 : ℝ) * (k + 11)) := by
      calc
        _ ≤ 2 * |source (k + 9) - arithmetic (k + 9)| := bulkPhaseGap_norm_le _
        _ = 2 * (arithmetic (k + 9) - source (k + 9)) := by
          rw [abs_of_neg (sub_neg.mpr (source_tail_lt_arithmetic k)), neg_sub]
        _ ≤ 2 * (1 / (6 * ((k + 9 : ℕ) + 3 : ℝ) * ((k + 9 : ℕ) + 2))) :=
          mul_le_mul_of_nonneg_left (arithmetic_sub_source_le _) (by norm_num)
        _ = _ := by push_cast; field_simp; ring
    have hs : Real.sqrt ‖bulkPhaseGap (k + 9)‖ ≤ 1 / (k + 12 : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ht.trans ?_⟩
      rw [div_pow, one_pow]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
    push_cast
    rw [show (k : ℝ) + 9 + 3 = k + 12 by ring]
    exact hs.trans (show 1 / (k + 12 : ℝ) ≤ 22 / (k + 12 : ℝ) by gcongr; norm_num)
  · have hn' : (n : ℝ) ≤ 8 := by exact_mod_cast (by omega : n ≤ 8)
    have hb : ‖bulkPhaseGap n‖ ≤ 2 := by
      simpa only [bulkPhaseGap, norm_realCayley, one_add_one_eq_two] using
        norm_sub_le (realCayley (source n - arithmetic n - 1)) (realCayley (-1))
    have hs : Real.sqrt ‖bulkPhaseGap n‖ ≤ 2 := Real.sqrt_le_iff.mpr
      ⟨by norm_num, hb.trans (by norm_num)⟩
    exact hs.trans ((le_div_iff₀ (by positivity)).mpr (by linarith))

private theorem sqrt_gap_difference_le (n : ℕ) :
    |Real.sqrt ‖(phase n : ℂ) - arithmeticPhase n‖ - Real.sqrt ‖bulkPhaseGap n‖| ≤
      44 * (if IsPrimePow (n + 3) then ((n + 3 : ℕ) : ℝ)⁻¹ else 0) := by
  by_cases hn : IsPrimePow (n + 3)
  · rw [if_pos hn]
    have h := abs_sub_le (Real.sqrt ‖(phase n : ℂ) - arithmeticPhase n‖)
      0 (Real.sqrt ‖bulkPhaseGap n‖)
    rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _)] at h
    have h1 := sqrt_phase_discrepancy_le n
    have h2 := sqrt_bulkPhaseGap_le n
    push_cast
    rw [← div_eq_mul_inv]
    calc
      _ ≤ Real.sqrt ‖(phase n : ℂ) - arithmeticPhase n‖ + Real.sqrt ‖bulkPhaseGap n‖ := h
      _ ≤ 22 / (n + 3 : ℝ) + 22 / (n + 3 : ℝ) := add_le_add h1 h2
      _ = _ := by ring
  · have ha : arithmetic n = -1 := by
      simp only [arithmetic, ArithmeticFunction.vonMangoldt_apply, if_neg hn, zero_sub]
    have he : (phase n : ℂ) - arithmeticPhase n = bulkPhaseGap n := by
      change realCayley (source n) - realCayley (arithmetic n) = _
      simp only [bulkPhaseGap, ha, sub_neg_eq_add, add_sub_cancel_right]
    simp only [if_neg hn, mul_zero, he, sub_self, abs_zero, le_refl]

theorem phase_discrepancy_critical_coordinate_residue :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, ‖(phase n : ℂ) - arithmeticPhase n‖ ^ (1 / 2 : ℝ)) /
        Real.log (N + 1)) atTop (𝓝 (1 / Real.sqrt 6)) := by
  have herr : Tendsto (fun N : ℕ =>
      ((∑ n ∈ Finset.range N, Real.sqrt ‖(phase n : ℂ) - arithmeticPhase n‖) -
        ∑ n ∈ Finset.range N, Real.sqrt ‖bulkPhaseGap n‖) / Real.log (N + 1))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hu := (tendsto_primePow_reciprocal_shift_sum_div_log 3).const_mul 44
    rw [mul_zero] at hu
    apply squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hu
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.log_nonneg (by norm_cast; omega)),
      ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_cast; omega))
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun n _ => sqrt_gap_difference_le n)
  have h := bulkPhaseGap_sqrt_residue.add herr
  rw [add_zero] at h
  convert h using 1
  funext N
  simp only [Real.sqrt_eq_rpow, sub_div]
  ring

theorem difference_hasSchattenLogResidue_half :
    HasSchattenLogResidue (1 / 2) (sourceOperator - arithmeticOperator) (1 / Real.sqrt 6) := by
  have h := phase_discrepancy_critical_coordinate_residue.add
    critical_energy_coordinate_log_difference_tendsto_zero
  rw [add_zero] at h
  unfold HasSchattenLogResidue
  convert h using 1
  funext N
  simp only [sub_div]
  ring

theorem difference_sub_prefix_hasSchattenLogResidue_half (N : ℕ) :
    HasSchattenLogResidue (1 / 2)
      ((sourceOperator - arithmeticOperator) - differencePrefix N) (1 / Real.sqrt 6) := by
  have hr : HasRankLE ((sourceOperator - arithmeticOperator) -
      ((sourceOperator - arithmeticOperator) - differencePrefix N)) N := by
    simpa only [sub_sub_cancel] using hasRankLE_differencePrefix N
  exact (hasSchattenLogResidue_iff_of_finiteRank (by norm_num : (0 : ℝ) < 1 / 2)
    hr (1 / Real.sqrt 6)).mp difference_hasSchattenLogResidue_half

theorem difference_sub_prefix_approxNumber_le (N n : ℕ) :
    approxNumber ((sourceOperator - arithmeticOperator) - differencePrefix N) n ≤
      approxNumber (sourceOperator - arithmeticOperator) n := by
  let m : ℕ → ℂ := fun k => if k < N then 0 else 1
  have hm (k : ℕ) : ‖m k‖ ≤ 1 := by simp [m]; split_ifs <;> norm_num
  have he : (sourceOperator - arithmeticOperator) - differencePrefix N =
      (diagonalOperator m hm).comp (sourceOperator - arithmeticOperator) := by
    ext x k
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply,
      ContinuousLinearMap.comp_apply, diagonalOperator_apply, sourceOperator_apply,
      arithmeticOperator_apply, differencePrefix, truncMultiplier, m]
    split_ifs <;> ring
  rw [he]
  exact (approxNumber_comp_le_left _ _ n).trans (by
    simpa using (mul_le_mul_of_nonneg_right (norm_diagonalOperator_le m hm)
      (approxNumber_nonneg (sourceOperator - arithmeticOperator) n)))

theorem difference_sub_prefix_memWeakSchattenClass_half (N : ℕ) :
    MemWeakSchattenClass (1 / 2)
      ((sourceOperator - arithmeticOperator) - differencePrefix N) := by
  obtain ⟨C, hC, hb⟩ := difference_memWeakSchattenClass_half
  exact ⟨C, hC, fun n => (Real.rpow_le_rpow (approxNumber_nonneg _ _)
    (difference_sub_prefix_approxNumber_le N n) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans (hb n)⟩

/-- Changing the boundary curvature leaves the critical residue unchanged. -/
theorem perturbed_difference_hasSchattenLogResidue_half (δ : ℝ) :
    HasSchattenLogResidue (1 / 2)
      (perturbedObservable δ circleCoordinate - arithmeticOperator) (1 / Real.sqrt 6) := by
  have hr : HasRankLE ((perturbedObservable δ circleCoordinate - arithmeticOperator) -
      (sourceOperator - arithmeticOperator)) 1 := by
    have he : (perturbedObservable δ circleCoordinate - arithmeticOperator) -
        (sourceOperator - arithmeticOperator) = perturbedObservable δ circleCoordinate -
          observable circleCoordinate := by
      dsimp only [sourceOperator]
      abel
    rw [he]
    exact hasRankLE_perturbedObservable_sub δ circleCoordinate
  exact (hasSchattenLogResidue_iff_of_finiteRank (by norm_num : (0 : ℝ) < 1 / 2)
    hr (1 / Real.sqrt 6)).mpr difference_hasSchattenLogResidue_half

end
end RHTower.PaperLagCayley
