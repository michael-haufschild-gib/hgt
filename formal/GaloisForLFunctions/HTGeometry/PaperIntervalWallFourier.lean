import GaloisForLFunctions.HTGeometry.PaperIntervalWallStep

/-! # Fourier reconstruction of the two chambers

The proven Fourier endpoint reconstructs the literal chamber profile on one common
full-measure set, independently of every possible wall value. Symmetric partial sums
are exactly zero at the wall at every depth, by reflection of the integer frequencies.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter Set Topology
open scoped BigOperators ENNReal

theorem paperIntervalWallStep_coefficient_neg (k : ℤ) :
    l2Pair (fourierChar (-k)) (paperIntervalWallStep 0) =
      -l2Pair (fourierChar k) (paperIntervalWallStep 0) := by
  have hs := intervalIntegral.integral_comp_sub_left
    (fun x => (starRingEnd ℂ) (fourierChar k x) * paperIntervalWallStep 0 x)
    (a := (0 : ℝ)) (b := 1) 1
  have h : -l2Pair (fourierChar (-k)) (paperIntervalWallStep 0) =
      l2Pair (fourierChar k) (paperIntervalWallStep 0) := by
    simpa only [l2Pair, sub_self, sub_zero, fourierChar_conj, neg_neg,
      fourierChar_neg_one_sub, paperIntervalWallStep_reflect, mul_neg,
      intervalIntegral.integral_neg] using hs
  simpa only [neg_neg] using congrArg Neg.neg h

/-- The zero frequency has no chamber bias. -/
theorem paperIntervalWallStep_coefficient_zero (w : ℂ) :
    l2Pair (fourierChar 0) (paperIntervalWallStep w) = 0 := by
  rw [paperIntervalWallStep_coefficient w 0]
  have h := paperIntervalWallStep_coefficient_neg 0
  simp only [neg_zero] at h
  linear_combination (1 / 2 : ℂ) * h

/-- Every symmetric cutoff selects the midpoint value, independently of the supplied wall value. -/
theorem paperIntervalWallStep_partialSum_wall (w : ℂ) (N : ℕ) :
    fourierPartialSum (paperIntervalWallStep w) N (1 / 2) = 0 := by
  rw [paperIntervalWallStep_partialSum w 0]
  have hchar (k : ℤ) : fourierChar (-k) (1 / 2) = fourierChar k (1 / 2) := by
    simpa only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num] using
      fourierChar_neg_one_sub k (1 / 2)
  have hs :
      (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        l2Pair (fourierChar (-k)) (paperIntervalWallStep 0) * fourierChar (-k) (1 / 2)) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        l2Pair (fourierChar k) (paperIntervalWallStep 0) * fourierChar k (1 / 2) := by
    apply Finset.sum_bij (fun k _ => -k)
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk j hj h
      exact neg_injective h
    · intro k hk
      refine ⟨-k, ?_, by simp⟩
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk
      rfl
  simp only [paperIntervalWallStep_coefficient_neg, hchar, neg_mul,
    Finset.sum_neg_distrib] at hs
  change -(fourierPartialSum (paperIntervalWallStep 0) N (1 / 2)) =
    fourierPartialSum (paperIntervalWallStep 0) N (1 / 2) at hs
  linear_combination (-1 / 2 : ℂ) * hs

/-- Pointwise Fourier recovery at the wall is possible exactly for its midpoint value. -/
theorem paperIntervalWallStep_recovery_at_wall_iff (w : ℂ) :
    Tendsto (fun N => fourierPartialSum (paperIntervalWallStep w) N (1 / 2))
      atTop (𝓝 (paperIntervalWallStep w (1 / 2))) ↔ w = 0 := by
  simp only [paperIntervalWallStep_partialSum_wall, paperIntervalWallStep_wall]
  constructor
  · intro h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  · rintro rfl
    exact tendsto_const_nhds

/-- One exceptional set works simultaneously for every complex value assigned at the wall. -/
theorem paperIntervalWallStep_common_convergence :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ w : ℂ,
        Tendsto (fun N => fourierPartialSum (paperIntervalWallStep w) N x)
          atTop (𝓝 (paperIntervalWallStep w x)) := by
  classical
  let g := (paperIntervalWallStep_memLp 0).toLp (paperIntervalWallStep 0)
  have hg : g =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] paperIntervalWallStep 0 :=
    (paperIntervalWallStep_memLp 0).coeFn_toLp
  obtain ⟨D, hsub, hDm, hDz⟩ := exists_measurable_superset_of_null (ae_iff.mp hg)
  rw [Measure.restrict_apply hDm] at hDz
  obtain ⟨E, hEm, hEz, hE⟩ := paperUnitIntervalLp_common_span_convergence (fun _ : Unit => g)
  refine ⟨E ∪ (D ∩ Ioc 0 1) ∪ {1 / 2},
    (hEm.union (hDm.inter measurableSet_Ioc)).union (measurableSet_singleton _),
    measure_union_null (measure_union_null hEz hDz) (measure_singleton _), ?_⟩
  intro x hx hxE w
  have hxE' : x ∉ E := fun h => hxE (Or.inl (Or.inl h))
  have hxD : x ∉ D := fun h => hxE (Or.inl (Or.inr ⟨h, hx⟩))
  have hxw : x ≠ 1 / 2 := fun h => hxE (Or.inr h)
  have hgx : g x = paperIntervalWallStep 0 x := by
    by_contra h
    exact hxD (hsub h)
  have hw : paperIntervalWallStep w x = paperIntervalWallStep 0 x := by
    rcases lt_or_gt_of_ne hxw with h | h
    · simp only [paperIntervalWallStep, if_pos h]
    · simp only [paperIntervalWallStep, if_neg (not_lt.mpr h.le), if_pos h]
  have hcoef (k : ℤ) : l2Pair (fourierChar k) g =
      l2Pair (fourierChar k) (paperIntervalWallStep 0) := by
    unfold l2Pair
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [hg] with y hy
    rw [hy]
  have ht := hE x hx hxE' {()} (fun _ => 1)
  simp only [Finset.sum_singleton, one_mul] at ht
  simp only [fourierPartialSum, hcoef, hgx] at ht
  simp_rw [paperIntervalWallStep_partialSum w 0, hw]
  exact ht

end
end GaloisForLFunctions.HTGeometry
