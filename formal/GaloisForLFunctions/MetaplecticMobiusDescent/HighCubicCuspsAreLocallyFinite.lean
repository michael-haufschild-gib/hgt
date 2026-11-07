import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicQuotientHasASmoothAtlas
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Locally finite high cusps on hyperbolic three-space

A continuous triangular section bounds the four integral coordinates of
any row whose height is at least one. Discreteness gives local finiteness.
The integral norm lower bound gives the height-product obstruction for
distinct cusp directions; upper triangular integral matrices preserve height.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

private def matrixRowOperatorLinear : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ]
    ((Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) where
  toFun M := (Matrix.toLinearMapRight' M).toContinuousLinearMap
  map_add' M N := by
    ext v j
    simp [Matrix.vecMul, dotProduct]
  map_smul' c M := by
    ext v j
    simp [Matrix.vecMul, dotProduct, mul_left_comm, mul_add]

lemma continuous_rowOperator : Continuous rowOperator :=
  matrixRowOperatorLinear.toContinuousLinearMap.continuous.comp continuous_complexSL_coe

lemma continuous_complexSL_inv : Continuous (fun g : SL(2,ℂ) => g⁻¹) := by
  apply Continuous.subtype_mk
  change Continuous (fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ).adjugate)
  exact continuous_complexSL_coe.matrix_adjugate

lemma rowBound_continuous : Continuous rowBound := by
  unfold rowBound
  exact continuous_const.mul (continuous_const.add
    ((continuous_rowOperator.comp continuous_complexSL_inv).norm))

/-- The continuous upper triangular representative of an actual hyperbolic point. -/
def hyperbolicSection (w : HyperbolicSpace) : SL(2,ℂ) :=
  coordinateSection (hyperbolicCoordinates w)

lemma hyperbolicSection_continuous : Continuous hyperbolicSection :=
  continuous_coordinateSection.comp hyperbolicCoordinates_continuous

lemma hyperbolicSection_projects (w : HyperbolicSpace) :
    (hyperbolicSection w : HyperbolicSpace) = w := upperCoordinates_right_inverse w

lemma cosetHeight_section (x : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight x w = (rowEnergy (rowOperator (hyperbolicSection w) (embeddedRow x)))⁻¹ := by
  calc
    cosetHeight x w = cosetHeight x (hyperbolicSection w : HyperbolicSpace) := by
      rw [hyperbolicSection_projects]
    _ = _ := rfl

lemma cosetHeight_pos (x : CuspCosets) (w : HyperbolicSpace) : 0 < cosetHeight x w := by
  rw [cosetHeight_section]
  exact inv_pos.mpr (rowEnergy_pos _
    (rowOperator_ne_zero _ _ (embeddedRow_ne_zero x)))

lemma coordinates_le_inverse_cosetHeight (x : CuspCosets) (w : HyperbolicSpace) :
    ‖rowCoordinates (cosetRow x)‖ ≤
      rowBound (hyperbolicSection w) * Real.sqrt ((cosetHeight x w)⁻¹) := by
  rw [cosetHeight_section, inv_inv]
  exact coordinates_le_transformed_energy (hyperbolicSection w) (cosetRow x)

/-- Locally, only finitely many cusp rows can have height at least one. -/
lemma principal_high_locally_finite (w : HyperbolicSpace) :
    ∃U : Set HyperbolicSpace, IsOpen U ∧ w ∈ U ∧ ∃T : Finset CuspCosets,
      ∀z ∈ U, ∀x ∉ T, cosetHeight x z < 1 := by
  let B := rowBound (hyperbolicSection w) + 1
  let U : Set HyperbolicSpace := {z | rowBound (hyperbolicSection z) < B}
  have hU : IsOpen U := isOpen_lt
    (rowBound_continuous.comp hyperbolicSection_continuous) continuous_const
  have hw : w ∈ U := by change rowBound (hyperbolicSection w) < rowBound (hyperbolicSection w)+1; linarith
  have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
    rowCoordinates_injective.comp cosetRow_injective
  have hfinite : Set.Finite {x : CuspCosets | ‖rowCoordinates (cosetRow x)‖ ≤ B} := by
    have hf : Set.Finite (Metric.closedBall (0 : (Fin 2 × Fin 2) → ℤ) B) :=
      (isCompact_closedBall _ _).finite_of_discrete
    apply (Set.Finite.preimage hinj.injOn hf).subset
    intro x hx
    change rowCoordinates (cosetRow x) ∈ Metric.closedBall 0 B
    simpa only [Metric.mem_closedBall,dist_zero_right] using (show ‖rowCoordinates (cosetRow x)‖ ≤ B from hx)
  refine ⟨U,hU,hw,hfinite.toFinset,?_⟩
  intro z hz x hx
  by_contra hn
  have hh : 1 ≤ cosetHeight x z := le_of_not_gt hn
  have hi : (cosetHeight x z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hh
  have hs : Real.sqrt ((cosetHeight x z)⁻¹) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hi
  have hb : ‖rowCoordinates (cosetRow x)‖ ≤ rowBound (hyperbolicSection z) :=
    (coordinates_le_inverse_cosetHeight x z).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (rowBound_pos _).le)
  apply hx
  rw [Set.Finite.mem_toFinset]
  exact hb.trans (le_of_lt hz)

/-- Distinct integral cusp directions cannot both raise height above one. -/
lemma integral_hyperbolicHeight_mul_le_one (M : SL(2,O)) (hc : M 1 0 ≠ 0)
    (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix M • w) * hyperbolicHeight w ≤ 1 := by
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  have hc1 : 1 ≤ ‖ringComplex (M 1 0)‖^2 := by
    simpa only [Complex.normSq_eq_norm_sq] using one_le_normSq_embedding (M 1 0) hc
  have hd : 0 < ‖ringComplex (M 1 0)*z+ringComplex (M 1 1)‖^2 +
      ‖ringComplex (M 1 0)‖^2*v^2 := by
    have hh := mul_le_mul_of_nonneg_right hc1 (sq_nonneg v)
    nlinarith only [hh, sq_pos_of_pos hv,
      sq_nonneg ‖ringComplex (M 1 0)*z+ringComplex (M 1 1)‖]
  rw [hyperbolicHeight_action_upperPoint,hyperbolicHeight_upperPoint]
  change v / (‖ringComplex (M 1 0)*z+ringComplex (M 1 1)‖^2 +
    ‖ringComplex (M 1 0)‖^2*v^2) * v ≤ 1
  rw [div_mul_eq_mul_div, div_le_one hd]
  nlinarith only [mul_le_mul_of_nonneg_right hc1 (sq_nonneg v),
    sq_nonneg ‖ringComplex (M 1 0)*z+ringComplex (M 1 1)‖]

lemma integral_upper_triangular_height (M : SL(2,O)) (hc : M 1 0 = 0)
    (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicHeight (integralComplexMatrix M • upperPoint z v hv) = v := by
  have hdet : M 0 0 * M 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using M.property
  have ha : M 0 0 ≠ 0 := by intro h; simp [h] at hdet
  have hd : M 1 1 ≠ 0 := by intro h; simp [h] at hdet
  have hprod : Complex.normSq (ringComplex (M 0 0)) *
      Complex.normSq (ringComplex (M 1 1)) = 1 := by
    rw [←Complex.normSq_mul, ←map_mul, hdet, map_one, Complex.normSq_one]
  have hna := one_le_normSq_embedding (M 0 0) ha
  have hnd := one_le_normSq_embedding (M 1 1) hd
  have he : Complex.normSq (ringComplex (M 1 1)) = 1 := by
    nlinarith only [hprod,hna,hnd,
      mul_nonneg (sub_nonneg.mpr hna) (sub_nonneg.mpr hnd)]
  rw [Complex.normSq_eq_norm_sq] at he
  rw [hyperbolicHeight_action_upperPoint]
  change v / (‖ringComplex (M 1 0)*z+ringComplex (M 1 1)‖^2 +
    ‖ringComplex (M 1 0)‖^2*v^2) = v
  simp only [hc, map_zero, zero_mul, zero_add, norm_zero, zero_pow (by decide : 2 ≠ 0),
    add_zero,he,div_one]

#print axioms principal_high_locally_finite
#print axioms integral_hyperbolicHeight_mul_le_one
#print axioms integral_upper_triangular_height
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
