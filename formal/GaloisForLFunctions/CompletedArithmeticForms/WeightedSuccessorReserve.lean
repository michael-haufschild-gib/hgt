import GaloisForLFunctions.CompletedArithmeticForms.WeightedCenterTail
import GaloisForLFunctions.CompletedArithmeticForms.PhysicalSuccessorMass

/-!
# An explicit integrated physical reserve for every weighted native tail

The terminal Hermite mass supplies a positive integrable lower density for
the exact tail successor. Testing the complete tail at its own global
minimizer retains this density before integration. The resulting allowance
contains only the literal first-atom mass and source scale; it has no inverse
matrix and includes the entire native source in the comparison theorem.
-/

noncomputable section

open MeasureTheory Matrix Finset Set

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower

/-- The explicit integrated terminal-degree reserve on a complete center tail. -/
def nativeWeightedSuccessorReserve (a R : ℝ) (N : ℕ) : ℝ :=
  ∫ r in Ioi R, r * Real.sinh (a * r) * nativePhysicalSuccessorFloor N (r / 2)

private theorem tail_point_horizon {N : ℕ} {R r : ℝ}
    (hR : 2 * nativeQuadraticRankHorizon (N + 2) ≤ R) (hr : r ∈ Ioi R) :
    nativeQuadraticRankHorizon (N + 1) ≤ r / 2 := by
  have hm := nativeQuadraticRankHorizon_mono (show N + 1 ≤ N + 2 by omega)
  have hr' : R < r := hr
  linarith only [hR, hr', hm]

private theorem tail_endpoint_nonneg {N : ℕ} {R : ℝ}
    (hR : 2 * nativeQuadraticRankHorizon (N + 2) ≤ R) : 0 ≤ R := by
  have hH : 0 ≤ nativeQuadraticRankHorizon (N + 2) := le_max_left _ _
  linarith only [hR, hH]

/-- The explicit reserve density is integrable by domination by the actual native diagonal. -/
theorem integrableOn_nativeWeightedSuccessorReserve {a R : ℝ} {N : ℕ}
    (ha0 : 0 < a) (ha : a < 1 / 2)
    (hR : 2 * nativeQuadraticRankHorizon (N + 2) ≤ R) :
    IntegrableOn (fun r => r * Real.sinh (a * r) * nativePhysicalSuccessorFloor N (r / 2))
      (Ioi R) := by
  have hR0 := tail_endpoint_nonneg hR
  have hU : Ioi R ⊆ Ioi (0 : ℝ) := fun _ h => lt_of_le_of_lt hR0 h
  have hi := (integrableOn_thetaCuspWeightedNativeSignedJet ha0.le ha (2 * N)).mono_set hU
  have hc : Continuous (fun r =>
      r * Real.sinh (a * r) * nativePhysicalSuccessorFloor N (r / 2)) :=
    (continuous_id.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
      ((continuous_nativePhysicalSuccessorFloor N).comp (continuous_id.div_const 2))
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hx := tail_point_horizon hR hr
  have hn := nativeSignedHead_posDef_of_quadratic_rank_horizon N hx
  have hl : nativePhysicalSuccessorFloor N (r / 2) ≤ thetaCuspNativeSignedJet (r / 2) (2 * N) :=
    (nativePhysicalSuccessor_half_bounds_of_horizon N hx).1.le.trans
      (successorSchur_le_terminalMoment hn)
  have hr0 : 0 < r := hU hr
  have hw : 0 < r * Real.sinh (a * r) := mul_pos hr0 (Real.sinh_pos_iff.mpr (mul_pos ha0 hr0))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw.le (nativePhysicalSuccessorFloor_nonneg _ _))]
  exact mul_le_mul_of_nonneg_left hl hw.le

/-- The explicit physical tail allowance is strictly positive at every critical aperture. -/
theorem nativeWeightedSuccessorReserve_pos {a R : ℝ} {N : ℕ}
    (ha0 : 0 < a) (ha : a < 1 / 2)
    (hR : 2 * nativeQuadraticRankHorizon (N + 2) ≤ R) :
    0 < nativeWeightedSuccessorReserve a R N := by
  have hR0 := tail_endpoint_nonneg hR
  have hp (r : ℝ) (hr : r ∈ Ioi R) :
      0 < r * Real.sinh (a * r) * nativePhysicalSuccessorFloor N (r / 2) := by
    have hr0 : 0 < r := lt_of_le_of_lt hR0 hr
    exact mul_pos (mul_pos hr0 (Real.sinh_pos_iff.mpr (mul_pos ha0 hr0)))
      (nativePhysicalSuccessorFloor_pos N (tail_point_horizon hR hr))
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi R)] (fun r =>
      r * Real.sinh (a * r) * nativePhysicalSuccessorFloor N (r / 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (hp r hr).le
  rw [nativeWeightedSuccessorReserve, setIntegral_pos_iff_support_of_nonneg_ae hnn
    (integrableOn_nativeWeightedSuccessorReserve ha0 ha hR)]
  have hs : Ioi R ⊆ Function.support (fun r =>
      r * Real.sinh (a * r) * nativePhysicalSuccessorFloor N (r / 2)) :=
    fun r hr => (hp r hr).ne'
  rw [Set.inter_eq_right.mpr hs]
  exact isOpen_Ioi.measure_pos volume ⟨R + 1, by change R < R + 1; linarith⟩

private theorem native_quadratic_eq {N : ℕ} (x : ℝ) (v : Fin N → ℝ) :
    v ⬝ᵥ finiteHankelMatrix (thetaCuspNativeSignedJet x) N *ᵥ v =
      thetaCuspNativeSignedHankelForm x v := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, finiteHankelMatrix,
    thetaCuspNativeSignedHankelForm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

/-- The exact integrated tail successor pays the explicit physical reserve without an inverse loss. -/
theorem nativeWeightedSuccessorReserve_le_schur {a R : ℝ} {N : ℕ}
    (ha0 : 0 < a) (ha : a < 1 / 2)
    (hR : 2 * nativeQuadraticRankHorizon (N + 2) ≤ R) :
    nativeWeightedSuccessorReserve a R N ≤
      finiteHankelSuccessorSchur (nativeWeightedCenterTailMoment a R) N := by
  have hR0 := tail_endpoint_nonneg hR
  have hU : Ioi R ⊆ Ioi (0 : ℝ) := fun _ h => lt_of_le_of_lt hR0 h
  let v := successorTestVector (nativeWeightedCenterTailMoment a R) N
  have hfull := nativeWeightedCenterTail_posDef (N + 1) ha0 ha hR
  have he : Function.Injective (Fin.castSucc : Fin N → Fin (N + 1)) := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (N + 1) => z.val) hij)
  have hhead : (finiteHankelMatrix (nativeWeightedCenterTailMoment a R) N).PosDef :=
    hfull.submatrix he
  have hi := (integrableOn_thetaCuspWeightedNativeSignedHankelForm ha0.le ha v).mono_set hU
  have hpoint : (fun r => r * Real.sinh (a * r) * nativePhysicalSuccessorFloor N (r / 2)) ≤ᵐ[
      volume.restrict (Ioi R)] (fun r =>
        r * Real.sinh (a * r) * thetaCuspNativeSignedHankelForm (r / 2) v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hx := tail_point_horizon hR hr
    have hn := nativeSignedHead_posDef_of_quadratic_rank_horizon N hx
    have hm := successorSchur_le_monic_energy hn (successorMinimizer (nativeWeightedCenterTailMoment a R) N)
    change finiteHankelSuccessorSchur (thetaCuspNativeSignedJet (r / 2)) N ≤
      v ⬝ᵥ finiteHankelMatrix (thetaCuspNativeSignedJet (r / 2)) (N + 1) *ᵥ v at hm
    rw [native_quadratic_eq] at hm
    have hl := (nativePhysicalSuccessor_half_bounds_of_horizon N hx).1.le.trans hm
    have hr0 : 0 < r := hU hr
    exact mul_le_mul_of_nonneg_left hl
      (mul_pos hr0 (Real.sinh_pos_iff.mpr (mul_pos ha0 hr0))).le
  have hb := integral_mono_ae (integrableOn_nativeWeightedSuccessorReserve ha0 ha hR) hi hpoint
  rw [← nativeWeightedMoment_quadratic_eq_integral ha0.le ha hU v] at hb
  change nativeWeightedSuccessorReserve a R N ≤
    successorTestVector (nativeWeightedCenterTailMoment a R) N ⬝ᵥ
      finiteHankelMatrix (nativeWeightedCenterTailMoment a R) (N + 1) *ᵥ
        successorTestVector (nativeWeightedCenterTailMoment a R) N at hb
  rwa [successorTestVector_energy_eq hhead] at hb

/-- The order-seven center successor has an explicit positive source integral as its tail allowance. -/
theorem centerSeventhSuccessor_explicit_compact_allowance {a R : ℝ}
    (ha0 : 0 < a) (ha : a < 1 / 2)
    (hR : 2 * nativeQuadraticRankHorizon 9 ≤ R) :
    0 < nativeWeightedSuccessorReserve a R 7 ∧
      successorTestVector (thetaCuspCenterMixedSignedJet a) 7 ⬝ᵥ
        finiteHankelMatrix (nativeWeightedCenterBandMoment a R) 8 *ᵥ
          successorTestVector (thetaCuspCenterMixedSignedJet a) 7 +
        nativeWeightedSuccessorReserve a R 7 ≤
          finiteHankelSuccessorSchur (thetaCuspCenterMixedSignedJet a) 7 := by
  refine ⟨nativeWeightedSuccessorReserve_pos ha0 ha hR, ?_⟩
  exact (add_le_add le_rfl (nativeWeightedSuccessorReserve_le_schur ha0 ha hR)).trans
    (centerSeventhSuccessor_compact_allowance ha0 ha hR).2

#print axioms integrableOn_nativeWeightedSuccessorReserve
#print axioms nativeWeightedSuccessorReserve_pos
#print axioms nativeWeightedSuccessorReserve_le_schur
#print axioms centerSeventhSuccessor_explicit_compact_allowance

end GaloisForLFunctions.CompletedArithmeticForms
