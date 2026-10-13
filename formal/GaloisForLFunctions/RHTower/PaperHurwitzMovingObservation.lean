import GaloisForLFunctions.RHTower.PaperHurwitzCompactObservation
import GaloisForLFunctions.HTGeometry.PaperCoordinateCompression

/-! # Exact norms of finite Hurwitz observations

The literal approaching resolvent is observed on its original first `M + 1`
power coordinates. Its distance from the corresponding identity observation
is exactly the defect at the last retained coordinate.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

theorem paperHurwitzApproachPoint_energy_ratio (t : ℝ) (N k : ℕ) :
    paperHurwitzPowerEnergy (paperHurwitzApproachPoint t N) k =
      Real.sinh (((k : ℝ) / ((N : ℝ) + 3)) * Real.log 2) ^ 2 := by
  rw [paperHurwitzPowerEnergy_eq_sinh, paperHurwitzApproachPoint_re]
  congr 2
  ring

theorem paperHurwitzApproachPoint_regularizer_antitone (t : ℝ) (N : ℕ) :
    Antitone (paperHurwitzRegularizer (paperHurwitzApproachPoint t N)) := by
  intro k j hkj
  have harg : (k : ℝ) / ((N : ℝ) + 3) * Real.log 2 ≤
      (j : ℝ) / ((N : ℝ) + 3) * Real.log 2 := by
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    exact div_le_div_of_nonneg_right (by exact_mod_cast hkj) (by positivity)
  have hs := Real.sinh_le_sinh.mpr harg
  have hk : 0 ≤ Real.sinh ((k : ℝ) / ((N : ℝ) + 3) * Real.log 2) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hj : 0 ≤ Real.sinh ((j : ℝ) / ((N : ℝ) + 3) * Real.log 2) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  simp only [paperHurwitzRegularizer, paperHurwitzApproachPoint_energy_ratio, ← one_div]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem paperHurwitzRegularizer_sub_one_norm (rho : ℂ) (k : ℕ) :
    ‖(paperHurwitzRegularizer rho k : ℂ) - 1‖ = 1 - paperHurwitzRegularizer rho k := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (paperHurwitzRegularizer_le_one rho k)), neg_sub]

/-- Error of the actual resolvent on the original prefix through coordinate `M`. -/
def paperHurwitzPrefixDefect (t : ℝ) (N M : ℕ) :
    PaperHurwitzHistory →L[ℂ] PaperHurwitzHistory :=
  (paperHurwitzResolvent (paperHurwitzApproachPoint t N) - 1) ∘L
    paperCoordinateProjection (M + 1)

theorem paperHurwitzPrefixDefect_apply (t : ℝ) (N M : ℕ)
    (f : PaperHurwitzHistory) (k : ℕ) :
    paperHurwitzPrefixDefect t N M f k =
      if k ≤ M then ((paperHurwitzRegularizer (paperHurwitzApproachPoint t N) k : ℂ) - 1) * f k
      else 0 := by
  simp only [paperHurwitzPrefixDefect, ContinuousLinearMap.comp_apply, sub_apply, lp.coeFn_sub,
    Pi.sub_apply,
    paperHurwitzResolvent_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
    paperCoordinateProjection_coordinate, Nat.lt_succ_iff]
  split_ifs <;> ring

theorem paperHurwitzPrefixDefect_single (t : ℝ) (N M : ℕ) :
    paperHurwitzPrefixDefect t N M (lp.single 2 M (1 : ℂ)) =
      lp.single 2 M ((paperHurwitzRegularizer (paperHurwitzApproachPoint t N) M : ℂ) - 1) := by
  ext k
  by_cases hk : k = M
  · subst k
    simp [paperHurwitzPrefixDefect_apply]
  · simp [paperHurwitzPrefixDefect_apply, lp.single_apply, hk]

/-- The final retained coordinate attains the full prefix operator norm. -/
theorem norm_paperHurwitzPrefixDefect (t : ℝ) (N M : ℕ) :
    ‖paperHurwitzPrefixDefect t N M‖ =
      1 - paperHurwitzRegularizer (paperHurwitzApproachPoint t N) M := by
  let rho := paperHurwitzApproachPoint t N
  let c := 1 - paperHurwitzRegularizer rho M
  have hc : 0 ≤ c := sub_nonneg.mpr (paperHurwitzRegularizer_le_one rho M)
  let w : ℕ → ℂ := fun k => if k ≤ M then (paperHurwitzRegularizer rho k : ℂ) - 1 else 0
  have hw : ∀ k, ‖w k‖ ≤ c := by
    intro k
    dsimp [w]
    split_ifs with hk
    · rw [paperHurwitzRegularizer_sub_one_norm]
      exact sub_le_sub_left (paperHurwitzApproachPoint_regularizer_antitone t N hk) 1
    · simpa using hc
  have heq : paperHurwitzPrefixDefect t N M = lpDiagonalCLM w hc hw := by
    ext f k
    simp only [paperHurwitzPrefixDefect_apply, lpDiagonalCLM_apply, w, rho]
    split_ifs <;> simp
  apply le_antisymm
  · rw [heq]
    exact norm_lpDiagonalCLM_le _ _ _
  · have h := (paperHurwitzPrefixDefect t N M).le_opNorm (lp.single 2 M (1 : ℂ))
    simpa only [paperHurwitzPrefixDefect_single, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
      norm_one, mul_one, paperHurwitzRegularizer_sub_one_norm] using h

theorem paperHurwitzPrefixDefect_compact (t : ℝ) (N M : ℕ) :
    IsCompactOperator (paperHurwitzPrefixDefect t N M) := by
  simpa only [paperHurwitzPrefixDefect, ContinuousLinearMap.coe_comp] using
    (isCompactOperator_paperCoordinateProjection (E := ℂ) (M + 1)).clm_comp
      (paperHurwitzResolvent (paperHurwitzApproachPoint t N) - 1)

theorem paperHurwitzPrefixDefect_traceCost (t : ℝ) (N M : ℕ) :
    compactOperatorTraceCost PaperHurwitzHistory (paperHurwitzPrefixDefect t N M) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperHurwitzPrefixDefect_compact t N M)

end
end RHTower
