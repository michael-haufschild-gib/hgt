import GaloisForLFunctions.HTGeometry.DifferentialOperatorOre
import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# The natural differential-operator module on a differential field

The Ore ring `K[∂; δ]` acts on `K` by applying the corresponding linear differential
operator.  This is the faithful target used to turn homogeneous operator relations into tangent
vectors over a differentially closed field.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

/-- The coefficient action `a ↦ a · δⁿ(x)`. -/
def fieldApplyAux (x : K) (n : ℕ) : K →+ K where
  toFun a := a * differentialJet n x
  map_zero' := zero_mul _
  map_add' a b := add_mul a b _

/-- Natural action of a linear differential operator on its coefficient field. -/
def fieldApply (p : DiffOp K) (x : K) : K :=
  Finsupp.liftAddHom (fieldApplyAux x) (toFinsupp p)

theorem fieldApply_mono (n : ℕ) (a x : K) :
    fieldApply (mono n a) x = a * differentialJet n x := by
  rw [fieldApply, toFinsupp_mono]
  exact Finsupp.liftAddHom_apply_single (fieldApplyAux x) n a

@[simp] theorem fieldApply_zero_op (x : K) : fieldApply 0 x = 0 := by
  rw [fieldApply, toFinsupp_zero, map_zero]

theorem fieldApply_add_op (p q : DiffOp K) (x : K) :
    fieldApply (p + q) x = fieldApply p x + fieldApply q x := by
  rw [fieldApply, fieldApply, fieldApply, toFinsupp_add, map_add]

theorem fieldApply_finset_sum_op {s : Finset ι} (p : ι → DiffOp K) (x : K) :
    fieldApply (∑ i ∈ s, p i) x = ∑ i ∈ s, fieldApply (p i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, fieldApply_add_op, ih, Finset.sum_insert hi]

theorem fieldApply_smul (a : K) (p : DiffOp K) (x : K) :
    fieldApply (a • p) x = a * fieldApply p x := by
  refine induction_linear
    (motive := fun p => fieldApply (a • p) x = a * fieldApply p x) p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [smul_add, fieldApply_add_op, fieldApply_add_op, hp, hq, mul_add]
  · intro n c
    rw [smul_mono, fieldApply_mono, fieldApply_mono, mul_assoc]

theorem fieldApply_dpartial (p : DiffOp K) (x : K) :
    fieldApply (dpartial p) x = Differential.deriv (fieldApply p x) := by
  refine induction_linear
    (motive := fun p => fieldApply (dpartial p) x = Differential.deriv (fieldApply p x))
    p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [dpartial_add, fieldApply_add_op, hp, hq, fieldApply_add_op, map_add]
  · intro n a
    rw [dpartial_mono, fieldApply_add_op, fieldApply_mono, fieldApply_mono,
      fieldApply_mono, Derivation.leibniz, differentialJet_succ]
    ring

theorem fieldApply_dpartial_iterate (n : ℕ) (p : DiffOp K) (x : K) :
    fieldApply (dpartial^[n] p) x = differentialJet n (fieldApply p x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', differentialJet_succ, fieldApply_dpartial, ih]

theorem fieldApply_mul (p q : DiffOp K) (x : K) :
    fieldApply (p * q) x = fieldApply p (fieldApply q x) := by
  refine induction_linear
    (motive := fun p => fieldApply (p * q) x = fieldApply p (fieldApply q x)) p ?_ ?_ ?_
  · rw [zero_mul', fieldApply_zero_op, fieldApply_zero_op]
  · intro p₁ p₂ h₁ h₂
    rw [add_mul', fieldApply_add_op, h₁, h₂, fieldApply_add_op]
  · intro n a
    rw [mono_mul, fieldApply_smul, fieldApply_dpartial_iterate, fieldApply_mono]

@[simp] theorem fieldApply_zero (p : DiffOp K) : fieldApply p 0 = 0 := by
  have hjet : ∀ n : ℕ, differentialJet n (0 : K) = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [differentialJet_succ, ih, map_zero]
  refine induction_linear (motive := fun p => fieldApply p 0 = 0) p ?_ ?_ ?_
  · rw [fieldApply_zero_op]
  · intro p q hp hq
    rw [fieldApply_add_op, hp, hq, add_zero]
  · intro n a
    rw [fieldApply_mono, hjet, mul_zero]

theorem fieldApply_add (p : DiffOp K) (x y : K) :
    fieldApply p (x + y) = fieldApply p x + fieldApply p y := by
  have hjet : ∀ n : ℕ, differentialJet n (x + y)
      = differentialJet n x + differentialJet n y := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [differentialJet_succ, differentialJet_succ,
        differentialJet_succ, ih, map_add]
  refine induction_linear
    (motive := fun p => fieldApply p (x + y) = fieldApply p x + fieldApply p y) p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [fieldApply_add_op, fieldApply_add_op, fieldApply_add_op, hp, hq]
    abel
  · intro n a
    rw [fieldApply_mono, fieldApply_mono, fieldApply_mono, hjet, mul_add]

theorem fieldApply_finset_sum {s : Finset ι} (p : DiffOp K) (x : ι → K) :
    fieldApply p (∑ i ∈ s, x i) = ∑ i ∈ s, fieldApply p (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, fieldApply_add, ih, Finset.sum_insert hi]

@[simp] theorem fieldApply_one (x : K) : fieldApply 1 x = x := by
  rw [one_def, fieldApply_mono]
  simp

/-- Evaluation as a finite sum over any set containing the operator support. -/
theorem fieldApply_eq_sum (p : DiffOp K) (x : K) (T : Finset ℕ)
    (hT : ∀ n ∉ T, coeff p n = 0) :
    fieldApply p x = ∑ n ∈ T, coeff p n * differentialJet n x := by
  classical
  have hsub : (toFinsupp p).support ⊆ T := by
    intro n hn
    by_contra hcon
    exact (Finsupp.mem_support_iff.mp hn) (hT n hcon)
  have hval : fieldApply p x = ∑ n ∈ (toFinsupp p).support,
      coeff p n * differentialJet n x := by
    rw [fieldApply, Finsupp.liftAddHom_apply, Finsupp.sum]
    rfl
  rw [hval]
  refine Finset.sum_subset hsub fun n _ hn => ?_
  rw [show coeff p n = 0 from Finsupp.notMem_support_iff.mp hn, zero_mul]

/-- The coefficient field as a left module over its Ore ring. -/
@[reducible] def fieldModule : Module (DiffOp K) K where
  smul := fieldApply
  one_smul := fieldApply_one
  mul_smul := fieldApply_mul
  smul_zero := fieldApply_zero
  smul_add := fieldApply_add
  add_smul p q x := fieldApply_add_op p q x
  zero_smul := fieldApply_zero_op

instance fieldModuleInstance : Module (DiffOp K) K := fieldModule

theorem field_smul_def (p : DiffOp K) (x : K) : p • x = fieldApply p x := rfl

end

end DiffOp

end GaloisForLFunctions.HTGeometry
