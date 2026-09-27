import GaloisForLFunctions.RHTower.XiCriticalGaussianWeightedFloor

/-!
# The heat rate of the improved independent interpolation floor

Every column of an invertible Vandermonde adjugate is nonzero. Consequently
the sharp cofactor capacity still contains each selected node's heat rate.
The improved lower estimate has a better prefactor, but its exponential rate
remains the largest selected squared height. This concerns the estimate,
not an upper bound on the actual positive energy.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

/-- Each selected node forces its own exponential rate into the interpolation floor. -/
theorem xiCriticalSamplingHeatFloor_node_rate_upper (n : ℕ)
    (γ : {γ : Fin (n + 1) → ℝ // Function.Injective (fun i => (γ i : ℂ) ^ 2)})
    (i : Fin (n + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      xiCriticalSamplingHeatFloor γ.1 t ≤ C * Real.exp (-(γ.1 i ^ 2 * t)) := by
  classical
  let z : Fin (n + 1) → ℂ := fun k => (γ.1 k : ℂ) ^ 2
  let V := Matrix.vandermonde z
  have hdet : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr γ.property
  obtain ⟨j, hj⟩ : ∃ j, V.adjugate j i ≠ 0 := by
    by_contra! hall
    have h := Matrix.det_eq_sum_mul_adjugate_row V i
    simp only [hall, mul_zero, Finset.sum_const_zero] at h
    exact hdet h
  let w : ℝ := ‖V.adjugate j i‖ ^ 2
  let D : ℝ := ‖V.det‖ ^ 2
  have hw : 0 < w := pow_pos (norm_pos_iff.mpr hj) _
  have hD : 0 < D := pow_pos (norm_pos_iff.mpr hdet) _
  refine ⟨2 * D / w, div_pos (mul_pos (by positivity) hD) hw, ?_⟩
  intro t
  have hrow : w * Real.exp (t * γ.1 i ^ 2) ≤
      ∑ k, ‖V.adjugate j k‖ ^ 2 * Real.exp (t * γ.1 k ^ 2) :=
    Finset.single_le_sum (fun k _ => mul_nonneg (sq_nonneg ‖V.adjugate j k‖)
      (Real.exp_pos (t * γ.1 k ^ 2)).le) (Finset.mem_univ i)
  have hcol : (∑ k, ‖V.adjugate j k‖ ^ 2 * Real.exp (t * γ.1 k ^ 2)) ≤
      polynomialSamplingHeatCapacity z (fun k => γ.1 k ^ 2) t :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (sq_nonneg ‖V.adjugate l k‖)
        (Real.exp_pos (t * γ.1 k ^ 2)).le) (Finset.mem_univ j)
  have h := div_le_div_of_nonneg_left (show 0 ≤ 2 * D by positivity)
    (mul_pos hw (Real.exp_pos _)) (hrow.trans hcol)
  change 2 * D / polynomialSamplingHeatCapacity z (fun k => γ.1 k ^ 2) t ≤ _
  calc
    _ ≤ 2 * D / (w * Real.exp (t * γ.1 i ^ 2)) := h
    _ = _ := by
      rw [mul_comm t (γ.1 i ^ 2), Real.exp_neg]
      field_simp

/-- The actual paired interpolation floor is bounded above and below at the same node rate. -/
theorem exists_xiGaussianWeightedFloor_rate_sandwich (n : ℕ) :
    ∃ (γ : Fin (n + 1) → ℝ) (q : Fin (n + 1) → XiZeroCopy)
      (iMax : Fin (n + 1)) (c C : ℝ),
      0 < c ∧ 0 < C ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      (∀ i, γ i ^ 2 ≤ γ iMax ^ 2) ∧
      ∀ t : {t : ℝ // 0 < t},
        c * Real.exp (-(γ iMax ^ 2 * (t : ℝ))) ≤ xiCriticalSamplingHeatFloor γ t ∧
        xiCriticalSamplingHeatFloor γ t ≤ C * Real.exp (-(γ iMax ^ 2 * (t : ℝ))) ∧
        ∀ a : ℕ → ℝ,
          xiCriticalSamplingHeatFloor γ t * (∑ j ∈ Finset.range (n + 1), a j ^ 2) ≤
            xiGaussianRealChannelEnergy
              (∑ j ∈ Finset.range (n + 1), Polynomial.C (a j) * Polynomial.X ^ j) t := by
  obtain ⟨γ, q, iMax, c, hc, hinj, hq, hmax, _, hfloor⟩ :=
    exists_xiGaussianRealChannel_paired_weighted_floor n
  obtain ⟨C, hC, hupper⟩ := xiCriticalSamplingHeatFloor_node_rate_upper n ⟨γ, hinj⟩ iMax
  exact ⟨γ, q, iMax, 2 * c, C, mul_pos (by positivity) hc, hC, hq, hmax,
    fun t => ⟨(hfloor t).2.1, hupper t, (hfloor t).2.2⟩⟩

end RHTower
