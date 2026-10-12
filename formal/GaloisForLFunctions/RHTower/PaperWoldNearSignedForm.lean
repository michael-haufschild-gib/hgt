import GaloisForLFunctions.RHTower.PaperWoldNearSpectrum

/-! # Zero ideal cost does not erase the signed Wold interactions

The adjacent composite indices 8 and 9 give a strictly positive matrix entry.
Its symmetric two-coordinate form has both signs, despite compactness and zero
paper ideal cost. The directed operator remains nonzero and quasinilpotent.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal InnerProductSpace

/-- Exact identification with the native absolute near-interaction budget. -/
theorem paperWoldLagCoeff_absolute_row (p : PaperWoldNearParameters) (n : ℕ) :
    (∑ k ∈ Finset.range ⌊((n : ℝ) + 1) ^ p.eta⌋₊, ‖paperWoldLagCoeff p k n‖) =
      ((n : ℝ) + 1) ^ (2 * p.t) *
        ∑ j ∈ Finset.Ioc n (n + ⌊((n : ℝ) + 1) ^ p.eta⌋₊),
          |xiHeatCassiniWoldNatIncrement n * xiHeatCassiniWoldNatIncrement j| := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun k _ => n + k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_range, Finset.mem_Ioc] at *
    omega
  · intro a ha b hb hab
    omega
  · intro j hj
    refine ⟨j - n - 1, ?_, ?_⟩ <;> simp only [Finset.mem_Ioc, Finset.mem_range] at * <;> omega
  · intro k hk
    have hk' : k + 1 ≤ ⌊((n : ℝ) + 1) ^ p.eta⌋₊ := by
      have := Finset.mem_range.mp hk
      omega
    simp only [paperWoldLagCoeff, if_pos hk', Complex.norm_real, Real.norm_eq_abs,
      paperWoldInteraction, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ) + 1) _)]
    ring

theorem paperWoldLagCoeff_absolute_summable (p : PaperWoldNearParameters) (h : 2 * p.t + p.eta < 1) :
    Summable (fun n : ℕ => ∑ k ∈ Finset.range ⌊((n : ℝ) + 1) ^ p.eta⌋₊, ‖paperWoldLagCoeff p k n‖) := by
  simp_rw [paperWoldLagCoeff_absolute_row]
  simpa only [Nat.cast_add, Nat.cast_one] using summable_xiHeatCassiniWoldNatNearIncrementCovariance h

theorem paperWoldNearOperator_single_lower (p : PaperWoldNearParameters) (j n : ℕ) (hjn : j ≤ n) :
    paperWoldNearOperator p (lp.single 2 j (1 : ℂ)) n = 0 := by
  rw [paperWoldNearOperator_apply]
  trans ∑' _ : ℕ, (0 : ℂ)
  · apply tsum_congr
    intro k
    have hne : n + k + 1 ≠ j := by omega
    rw [lp.single_apply_ne 2 j 1 hne, mul_zero]
  · exact tsum_zero

theorem paperWoldNearOperator_single_next (p : PaperWoldNearParameters) (n : ℕ) :
    paperWoldNearOperator p (lp.single 2 (n + 1) (1 : ℂ)) n =
      (paperWoldInteraction p n (n + 1) : ℂ) := by
  rw [paperWoldNearOperator_apply, tsum_eq_single 0 (fun k hk => by
    have hne : n + k + 1 ≠ n + 1 := by omega
    rw [lp.single_apply_ne 2 (n + 1) 1 hne, mul_zero])]
  have hfloor : 1 ≤ ⌊((n : ℝ) + 1) ^ p.eta⌋₊ :=
    Nat.le_floor (by
      simpa using (Real.one_le_rpow
        (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n : ℝ) + 1) p.eta_nonneg))
  simp [paperWoldLagCoeff, hfloor, lp.single_apply]

theorem paperWold_increment_neg_of_composite (n : ℕ) (hn : ¬ (n + 2).Prime) :
    xiHeatCassiniWoldNatIncrement n < 0 := by
  rw [xiHeatCassiniWoldNatIncrement_eq, xiHeatCassiniWoldNatWeight, dif_neg hn]
  have hlog : Real.log ((n : ℝ) + 1) < Real.log ((n : ℝ) + 2) :=
    Real.log_lt_log (by positivity) (by linarith)
  linarith

theorem paperWoldCompositeInteraction_pos (p : PaperWoldNearParameters) :
    0 < paperWoldInteraction p 6 7 := by
  have h8 : ¬ (6 + 2 : ℕ).Prime :=
    Nat.not_prime_of_dvd_of_ne (show (2 : ℕ) ∣ 6 + 2 from ⟨4, rfl⟩) (by norm_num) (by norm_num)
  have h9 : ¬ (7 + 2 : ℕ).Prime :=
    Nat.not_prime_of_dvd_of_ne (show (3 : ℕ) ∣ 7 + 2 from ⟨3, rfl⟩) (by norm_num) (by norm_num)
  have hprod := mul_pos_of_neg_of_neg (paperWold_increment_neg_of_composite 6 h8)
    (paperWold_increment_neg_of_composite 7 h9)
  unfold paperWoldInteraction
  rw [mul_assoc]
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) hprod

theorem paperWoldNearOperator_ne_zero (p : PaperWoldNearParameters) : paperWoldNearOperator p ≠ 0 := by
  intro hz
  have h := paperWoldNearOperator_single_next p 6
  rw [hz] at h
  have hre := congrArg Complex.re h
  simp only [zero_apply, lp.coeFn_zero, Pi.zero_apply, Complex.zero_re,
    Complex.ofReal_re] at hre
  linarith [paperWoldCompositeInteraction_pos p]

theorem paperWoldNearOperator_composite_norm_lower (p : PaperWoldNearParameters) :
    paperWoldInteraction p 6 7 ≤ ‖paperWoldNearOperator p‖ := by
  have he := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (paperWoldNearOperator p (lp.single 2 7 (1 : ℂ))) 6
  rw [paperWoldNearOperator_single_next p 6, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (paperWoldCompositeInteraction_pos p)] at he
  have hn := (paperWoldNearOperator p).le_opNorm (lp.single 2 7 (1 : ℂ))
  rw [lp.norm_single (by norm_num), norm_one, mul_one] at hn
  exact he.trans hn

def paperWoldNearSymmetric (p : PaperWoldNearParameters) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  paperWoldNearOperator p + ContinuousLinearMap.adjoint (paperWoldNearOperator p)

theorem paperWoldNearSymmetric_compact (p : PaperWoldNearParameters) :
    IsCompactOperator (paperWoldNearSymmetric p) :=
  (paperWoldNearOperator_compact p).add
    (isCompactOperator_adjoint_rectangular _ (paperWoldNearOperator_compact p))

theorem paperWoldNearSymmetric_selfAdjoint (p : PaperWoldNearParameters) :
    ContinuousLinearMap.adjoint (paperWoldNearSymmetric p) = paperWoldNearSymmetric p := by
  simp [paperWoldNearSymmetric, add_comm]

theorem paperWoldNearSymmetric_traceCost (p : PaperWoldNearParameters) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldNearSymmetric p) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldNearSymmetric_compact p)

theorem paperWoldNearSymmetric_quadratic (p : PaperWoldNearParameters) (x : PaperWoldHistory) :
    (inner ℂ x (paperWoldNearSymmetric p x)).re =
      2 * (inner ℂ x (paperWoldNearOperator p x)).re := by
  rw [paperWoldNearSymmetric, add_apply, inner_add_right,
    Complex.add_re, ContinuousLinearMap.adjoint_inner_right]
  have hs : (inner ℂ (paperWoldNearOperator p x) x).re =
      (inner ℂ x (paperWoldNearOperator p x)).re :=
    inner_re_symm (𝕜 := ℂ) (paperWoldNearOperator p x) x
  rw [hs]
  ring

theorem paperWoldNearOperator_adjacent_form (p : PaperWoldNearParameters) (n : ℕ) (a b : ℂ) :
    inner ℂ (a • lp.single 2 n (1 : ℂ) + b • lp.single 2 (n + 1) (1 : ℂ))
      (paperWoldNearOperator p (a • lp.single 2 n (1 : ℂ) + b • lp.single 2 (n + 1) (1 : ℂ))) =
      star a * b * (paperWoldInteraction p n (n + 1) : ℂ) := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, starRingEnd_apply,
    paperWoldNearOperator_single_lower p n n le_rfl,
    paperWoldNearOperator_single_lower p n (n + 1) (by omega),
    paperWoldNearOperator_single_lower p (n + 1) (n + 1) le_rfl,
    paperWoldNearOperator_single_next, mul_zero, add_zero, zero_add]
  ring

theorem paperWoldNearSymmetric_adjacent_form (p : PaperWoldNearParameters) (n : ℕ) (a b : ℂ) :
    (inner ℂ (a • lp.single 2 n (1 : ℂ) + b • lp.single 2 (n + 1) (1 : ℂ))
      (paperWoldNearSymmetric p (a • lp.single 2 n (1 : ℂ) + b • lp.single 2 (n + 1) (1 : ℂ)))).re =
      2 * (star a * b).re * paperWoldInteraction p n (n + 1) := by
  rw [paperWoldNearSymmetric_quadratic, paperWoldNearOperator_adjacent_form]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem paperWoldNearSymmetric_both_signs (p : PaperWoldNearParameters) :
    (∃ x : PaperWoldHistory, 0 < (inner ℂ x (paperWoldNearSymmetric p x)).re) ∧
      (∃ y : PaperWoldHistory, (inner ℂ y (paperWoldNearSymmetric p y)).re < 0) := by
  constructor
  · refine ⟨(1 : ℂ) • lp.single 2 6 (1 : ℂ) + (1 : ℂ) • lp.single 2 7 (1 : ℂ), ?_⟩
    rw [paperWoldNearSymmetric_adjacent_form p 6 1 1]
    simpa using mul_pos (by norm_num : (0 : ℝ) < 2) (paperWoldCompositeInteraction_pos p)
  · refine ⟨(1 : ℂ) • lp.single 2 6 (1 : ℂ) + (-1 : ℂ) • lp.single 2 7 (1 : ℂ), ?_⟩
    rw [paperWoldNearSymmetric_adjacent_form p 6 1 (-1)]
    simp only [star_one, one_mul, Complex.neg_re, Complex.one_re]
    nlinarith [paperWoldCompositeInteraction_pos p]

/-- The critical half-power weight with the actual square-root arithmetic window. -/
def paperWoldCriticalNearParameters : PaperWoldNearParameters where
  t := 1 / 2
  eta := 1 / 2
  t_nonneg := by norm_num
  eta_nonneg := by norm_num
  budget := by norm_num

theorem paperWoldCriticalNear_package :
    IsCompactOperator (paperWoldNearOperator paperWoldCriticalNearParameters) ∧
      paperWoldNearOperator paperWoldCriticalNearParameters ≠ 0 ∧
      spectrum ℂ (paperWoldNearOperator paperWoldCriticalNearParameters) ⊆ {0} ∧
      compactOperatorTraceCost PaperWoldHistory (paperWoldNearOperator paperWoldCriticalNearParameters) = 0 ∧
      (∃ x : PaperWoldHistory, 0 < (inner ℂ x (paperWoldNearSymmetric paperWoldCriticalNearParameters x)).re) ∧
      (∃ y : PaperWoldHistory, (inner ℂ y (paperWoldNearSymmetric paperWoldCriticalNearParameters y)).re < 0) :=
  ⟨paperWoldNearOperator_compact _, paperWoldNearOperator_ne_zero _, paperWoldNearOperator_spectrum_subset _,
    paperWoldNearOperator_traceCost _, paperWoldNearSymmetric_both_signs _⟩

end
end RHTower
