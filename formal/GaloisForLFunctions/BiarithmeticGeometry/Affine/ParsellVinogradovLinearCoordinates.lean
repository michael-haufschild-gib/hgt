import GaloisForLFunctions.BiarithmeticGeometry.Affine.MonomialLinearMapFaithfulness
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovScaledFrames

/-!
# Degree-one coordinates of complete affine moment frames

The degree-one monomials recover all physical coordinates. Faithfulness of
the full moment map extends their physical transformation law to every
ambient vector. Vertical translations disappear from this linear action;
only the horizontal shear and vertical dilation remain.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Linear maps agreeing on the complete moment image agree on the whole ambient space. -/
theorem linearMap_eq_of_horizontalMoment_eq {ι : Type*} (r k : ℕ)
    (T U : AffineAxisSpace r k →ₗ[ℝ] (ι → ℝ))
    (h : ∀ (u : Fin (r + 1) → ℝ) (z : ℝ),
      T (horizontalMoment r k u z) = U (horizontalMoment r k u z)) : T = U := by
  apply linearMap_eq_of_monomial_eq axisMonomialExponent (axisMonomialExponent_injective r k)
  intro x
  have hx : (Fin.cons (x 0) (fun i => x i.succ) : Fin (r + 2) → ℝ) = x :=
    Fin.cons_self_tail x
  change T (canonicalMoment r k x) = U (canonicalMoment r k x)
  simpa only [horizontalMoment, hx] using h (fun i => x i.succ) (x 0)

/-- The ambient moment coordinate corresponding to the physical variable indexed by `i`. -/
def degreeOneIndex (r k : ℕ) (i : Fin (r + 2)) : AffineAxisIndex r (k + 1) :=
  (axisExponentEquiv r (k + 1)).symm ⟨fun j => if j = i then 1 else 0, by simp⟩

theorem axisExponentTuple_degreeOneIndex (r k : ℕ) (i : Fin (r + 2)) :
    axisExponentTuple (degreeOneIndex r k i) = fun j => if j = i then 1 else 0 :=
  congrArg Subtype.val ((axisExponentEquiv r (k + 1)).apply_symm_apply _)

/-- Evaluating a degree-one moment recovers its physical coordinate exactly. -/
theorem canonicalMoment_degreeOneIndex (r k : ℕ) (x : Fin (r + 2) → ℝ) (i : Fin (r + 2)) :
    canonicalMoment r (k + 1) x (degreeOneIndex r k i) = x i := by
  rw [canonicalMoment_product, axisExponentTuple_degreeOneIndex]
  have hp (j : Fin (r + 2)) :
      x j ^ (if j = i then 1 else 0) = if j = i then x j else 1 := by
    by_cases h : j = i <;> simp only [h, if_true, if_false, pow_one, pow_zero]
  simp only [hp, Finset.prod_ite_eq', Finset.mem_univ, if_true]

/-- Projection to the degree-one monomials, with the vertical coordinate first. -/
def degreeOneProjection (r k : ℕ) : AffineAxisSpace r (k + 1) →ₗ[ℝ] (Fin (r + 2) → ℝ) where
  toFun x i := x (degreeOneIndex r k i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem degreeOneProjection_apply (r k : ℕ) (x : AffineAxisSpace r (k + 1)) (i : Fin (r + 2)) :
    degreeOneProjection r k x i = x (degreeOneIndex r k i) := rfl

theorem degreeOneProjection_moment (r k : ℕ) (u : Fin (r + 1) → ℝ) (z : ℝ) :
    degreeOneProjection r k (horizontalMoment r (k + 1) u z) = Fin.cons z u := by
  funext i
  exact canonicalMoment_degreeOneIndex r k (Fin.cons z u) i

/-- The physical shear fixes horizontal coordinates and adds their linear form to the vertical one. -/
def physicalShear (r : ℕ) (δ : Fin (r + 1) → ℝ) :
    (Fin (r + 2) → ℝ) →ₗ[ℝ] (Fin (r + 2) → ℝ) where
  toFun x := Fin.cons (x 0 + ∑ i, δ i * x i.succ) (fun i => x i.succ)
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      ring
    · rfl
  map_smul' c x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change c * x 0 + (∑ j, δ j * (c * x j.succ)) = c * (x 0 + ∑ j, δ j * x j.succ)
      simp only [mul_add, Finset.mul_sum, mul_left_comm]
    · rfl

theorem physicalShear_cons (r : ℕ) (δ u : Fin (r + 1) → ℝ) (z : ℝ) :
    physicalShear r δ (Fin.cons z u) = Fin.cons (z + ∑ i, δ i * u i) u := rfl

/-- Projection of the complete affine frame is the physical shear, independent of its vertical shift. -/
theorem degreeOneProjection_vectorAffine (r k : ℕ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (x : AffineAxisSpace r (k + 1)) :
    degreeOneProjection r k (Matrix.toLin' (vectorAffineMatrix r (k + 1) δ t) x) =
      physicalShear r δ (degreeOneProjection r k x) := by
  have he : (degreeOneProjection r k).comp (Matrix.toLin' (vectorAffineMatrix r (k + 1) δ t)) =
      (physicalShear r δ).comp (degreeOneProjection r k) := by
    apply linearMap_eq_of_horizontalMoment_eq
    intro u z
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, vectorAffineMatrix_moment,
      map_sub, degreeOneProjection_moment, physicalShear_cons]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.sub_apply, Fin.cons_zero]
      ring
    · simp only [Pi.sub_apply, Fin.cons_succ, Pi.zero_apply, sub_zero]
  exact congrArg (fun F : AffineAxisSpace r (k + 1) →ₗ[ℝ] (Fin (r + 2) → ℝ) => F x) he

private theorem degreeOneIndex_vertical_weight (r k : ℕ) :
    (degreeOneIndex r k 0).2.2.val = 1 := by
  simpa only [axisExponentTuple, Fin.cons_zero, if_true] using
    congrFun (axisExponentTuple_degreeOneIndex r k 0) 0

private theorem degreeOneIndex_horizontal_weight (r k : ℕ) (i : Fin (r + 1)) :
    (degreeOneIndex r k i.succ).2.2.val = 0 := by
  have hn : (0 : Fin (r + 2)) ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = i.val + 1 at hv
    omega
  simpa only [axisExponentTuple, Fin.cons_zero, if_neg hn] using
    congrFun (axisExponentTuple_degreeOneIndex r k i.succ) 0

/-- Projecting vertical moment dilation recovers ordinary vertical dilation of physical coordinates. -/
theorem degreeOneProjection_verticalDilation (r k : ℕ) (ε : ℝ) (x : AffineAxisSpace r (k + 1)) :
    degreeOneProjection r k (Matrix.toLin' (verticalDilationMatrix r (k + 1) ε) x) =
      Fin.cons (ε * x (degreeOneIndex r k 0)) (fun i => x (degreeOneIndex r k i.succ)) := by
  funext i
  simp only [degreeOneProjection_apply, Matrix.toLin'_apply, verticalDilationMatrix_mulVec_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [degreeOneIndex_vertical_weight, pow_one, Fin.cons_zero]
  · rw [degreeOneIndex_horizontal_weight, pow_zero, one_mul, Fin.cons_succ]

/-- The projected scaled frame has the same elementary shear formula in every positive degree. -/
theorem degreeOneProjection_scaledAffine (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (x : AffineAxisSpace r (k + 1)) :
    degreeOneProjection r k (Matrix.toLin' (scaledAffineMatrix r (k + 1) ε δ t) x) =
      Fin.cons (ε * (x (degreeOneIndex r k 0) + ∑ i, δ i * x (degreeOneIndex r k i.succ)))
        (fun i => x (degreeOneIndex r k i.succ)) := by
  rw [scaledAffineLinear_apply, degreeOneProjection_vectorAffine,
    degreeOneProjection_verticalDilation, physicalShear_cons]
  simp only [Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

#print axioms linearMap_eq_of_horizontalMoment_eq
#print axioms canonicalMoment_degreeOneIndex
#print axioms degreeOneProjection_moment
#print axioms degreeOneProjection_vectorAffine
#print axioms degreeOneProjection_verticalDilation
#print axioms degreeOneProjection_scaledAffine

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
