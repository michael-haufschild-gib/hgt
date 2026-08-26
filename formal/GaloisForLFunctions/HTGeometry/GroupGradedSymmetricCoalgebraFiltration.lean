import GaloisForLFunctions.HTGeometry.GroupGradedSymmetricDegree
import GaloisForLFunctions.HTGeometry.AdditivePolynomialCoalgebraFiltration
import GaloisForLFunctions.HTGeometry.CommonHopfSubalgebraTrivial
import GaloisForLFunctions.HTGeometry.SymmetricHopfIdealLinear

/-!
# Coalgebra slices and additive degree in `Sym(V)[M]`

Right-leg contraction of the group-graded symmetric coproduct acts independently at every torus
weight.  Transport through a basis reduces each coefficient slice to the additive polynomial
filtration.  Equal values on group-like constants preserve the top degree; equal values through
the linear additive layer preserve the top two degrees.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace GroupGradedSymmetricCoalgebraFiltration

noncomputable section

open GroupGradedSymmetricDegree
open AdditivePolynomialCoalgebraFiltration

variable {k V ι M : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup M]

/-- Pull a symmetric-algebra functional through the polynomial presentation. -/
noncomputable def polynomialFunctional (basis : Module.Basis ι k V)
    (ψ : SymmetricAlgebra k V →ₗ[k] k) : MvPolynomial ι k →ₗ[k] k :=
  ψ.comp (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap

@[simp] theorem polynomialFunctional_apply (basis : Module.Basis ι k V)
    (ψ : SymmetricAlgebra k V →ₗ[k] k) (P : MvPolynomial ι k) :
    polynomialFunctional basis ψ P =
      ψ ((SymmetricAlgebra.equivMvPolynomial basis).symm P) := rfl

/-- Tensor contraction commutes with the symmetric/polynomial linear equivalence. -/
theorem tensorRightSlice_map_equiv (basis : Module.Basis ι k V)
    (ψ : SymmetricAlgebra k V →ₗ[k] k)
    (t : SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V) :
    tensorRightSlice (polynomialFunctional basis ψ)
        (TensorProduct.map (SymmetricAlgebra.equivMvPolynomial basis).toLinearMap
          (SymmetricAlgebra.equivMvPolynomial basis).toLinearMap t) =
      SymmetricAlgebra.equivMvPolynomial basis (rightSlice ψ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp [tensorRightSlice]
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul x y => simp [tensorRightSlice, rightSlice, polynomialFunctional]

/-- Polynomial presentation of a right slice of symmetric comultiplication. -/
theorem equivMvPolynomial_rightSlice_comul (basis : Module.Basis ι k V)
    (ψ : SymmetricAlgebra k V →ₗ[k] k) (b : SymmetricAlgebra k V) :
    SymmetricAlgebra.equivMvPolynomial basis
        (rightSlice ψ (Coalgebra.comul (R := k) b)) =
      AdditivePolynomialCoalgebraFiltration.rightSlice (polynomialFunctional basis ψ)
        (SymmetricAlgebra.equivMvPolynomial basis b) := by
  have hcom := DFunLike.congr_fun
    (SymmetricHopfIdealLinear.tensorTransport_comul basis) b
  change SymmetricHopfIdealLinear.tensorTransport basis
      (Coalgebra.comul (R := k) b) =
        AdditivePolynomialHopf.addComul
          (SymmetricAlgebra.equivMvPolynomial basis b) at hcom
  rw [AdditivePolynomialCoalgebraFiltration.rightSlice]
  change _ = tensorRightSlice (polynomialFunctional basis ψ)
      ((MvPolynomial.tensorEquivSum k ι ι k).symm
        (AdditivePolynomialHopf.addComul
          (SymmetricAlgebra.equivMvPolynomial basis b)))
  rw [← hcom]
  change _ = tensorRightSlice (polynomialFunctional basis ψ)
      ((MvPolynomial.tensorEquivSum k ι ι k).symm
        ((MvPolynomial.tensorEquivSum k ι ι k)
          (TensorProduct.map (SymmetricAlgebra.equivMvPolynomial basis).toLinearMap
            (SymmetricAlgebra.equivMvPolynomial basis).toLinearMap
            (Coalgebra.comul (R := k) b))))
  rw [AlgEquiv.symm_apply_apply]
  exact (tensorRightSlice_map_equiv basis ψ _).symm

/-- Right contraction cannot increase symmetric polynomial degree. -/
theorem rightSlice_comul_totalDegree_le (basis : Module.Basis ι k V)
    (ψ : SymmetricAlgebra k V →ₗ[k] k) (b : SymmetricAlgebra k V) :
    (SymmetricAlgebra.equivMvPolynomial basis
      (rightSlice ψ (Coalgebra.comul (R := k) b))).totalDegree ≤
      (SymmetricAlgebra.equivMvPolynomial basis b).totalDegree := by
  rw [equivMvPolynomial_rightSlice_comul]
  exact AdditivePolynomialCoalgebraFiltration.rightSlice_totalDegree_le _ _

/-- Functional on one fixed torus-weight coefficient. -/
noncomputable def weightFunctional (ψ :
    AddMonoidAlgebra (SymmetricAlgebra k V) M →ₗ[k] k) (m : M) :
    SymmetricAlgebra k V →ₗ[k] k :=
  ψ.comp (AddMonoidAlgebra.lsingle (R := k) m)

omit [AddCommGroup M] in
@[simp] theorem weightFunctional_apply (ψ :
    AddMonoidAlgebra (SymmetricAlgebra k V) M →ₗ[k] k) (m : M)
    (b : SymmetricAlgebra k V) :
    weightFunctional ψ m b = ψ (AddMonoidAlgebra.single m b) := rfl

/-- Coefficient extraction after diagonally inserting one group weight into both tensor legs. -/
theorem coeff_rightSlice_map_lsingle (ψ :
    AddMonoidAlgebra (SymmetricAlgebra k V) M →ₗ[k] k)
    [DecidableEq M]
    (m a : M) (t : SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V) :
    (rightSlice ψ (TensorProduct.map
      (AddMonoidAlgebra.lsingle (R := k) a)
      (AddMonoidAlgebra.lsingle (R := k) a) t)).coeff m =
      if m = a then rightSlice (weightFunctional ψ m) t else 0 := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => simp [rightSlice]
  | add x y hx hy =>
      rw [map_add, map_add, map_add]
      change ((rightSlice ψ (TensorProduct.map
          (AddMonoidAlgebra.lsingle (R := k) a)
          (AddMonoidAlgebra.lsingle (R := k) a) x)).coeff m) +
        ((rightSlice ψ (TensorProduct.map
          (AddMonoidAlgebra.lsingle (R := k) a)
          (AddMonoidAlgebra.lsingle (R := k) a) y)).coeff m) = _
      rw [hx, hy]
      by_cases hma : m = a <;> simp [hma]
  | tmul x y =>
      by_cases hma : m = a
      · subst a
        simp [rightSlice, weightFunctional]
      · simp [rightSlice, hma]

/-- Right contraction of group-graded comultiplication is coefficientwise symmetric contraction. -/
theorem coeff_rightSlice_comul (ψ :
    AddMonoidAlgebra (SymmetricAlgebra k V) M →ₗ[k] k)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) (m : M) :
    (rightSlice ψ (Coalgebra.comul (R := k) p)).coeff m =
      rightSlice (weightFunctional ψ m)
        (Coalgebra.comul (R := k) (p.coeff m)) := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simpa using congrArg₂ (· + ·) hp hq
  | single a b =>
      rw [AddMonoidAlgebra.comul_single]
      rw [coeff_rightSlice_map_lsingle]
      by_cases ham : m = a
      · subst a
        simp
      · simp [ham]

/-- Counit applied to one fixed group-graded coefficient. -/
noncomputable def weightCounit (m : M) :
    AddMonoidAlgebra (SymmetricAlgebra k V) M →ₗ[k] k where
  toFun p := Coalgebra.counit (R := k) (p.coeff m)
  map_add' p q := by simp
  map_smul' c p := by simp

omit [AddCommGroup M] in
@[simp] theorem weightCounit_apply (m : M)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) :
    weightCounit m p = Coalgebra.counit (R := k) (p.coeff m) := rfl

/-- Slicing any coalgebra comultiplication against its counit is the identity. -/
theorem rightSlice_counit_comul (b : SymmetricAlgebra k V) :
    rightSlice (Coalgebra.counit (R := k))
      (Coalgebra.comul (R := k) b) = b := by
  have h := DFunLike.congr_fun
    (Coalgebra.lTensor_counit_comp_comul
      (R := k) (A := SymmetricAlgebra k V)) b
  change TensorProduct.map
      (LinearMap.id (R := k) (M := SymmetricAlgebra k V))
      (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) b) =
    b ⊗ₜ[k] (1 : k) at h
  simp only [rightSlice, LinearMap.coe_comp, Function.comp_apply]
  rw [h]
  simp

/-- Counit slicing at one weight is the exact homogeneous projection onto that weight. -/
theorem rightSlice_weightCounit_comul (p :
    AddMonoidAlgebra (SymmetricAlgebra k V) M) (m : M) :
    rightSlice (weightCounit m) (Coalgebra.comul (R := k) p) =
      AddMonoidAlgebra.single m (p.coeff m) := by
  classical
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro a
  rw [coeff_rightSlice_comul]
  by_cases ham : a = m
  · subst a
    have hw : weightFunctional (k := k) (V := V) (M := M)
        (weightCounit (k := k) (V := V) (M := M) m) m =
        (Coalgebra.counit (R := k) : SymmetricAlgebra k V →ₗ[k] k) := by
      ext b
      simp [weightFunctional, weightCounit]
    rw [hw, rightSlice_counit_comul]
    simp
  · have hw : weightFunctional (k := k) (V := V) (M := M)
        (weightCounit (k := k) (V := V) (M := M) m) a = 0 := by
      ext b
      simp [weightFunctional, weightCounit, ham]
    rw [hw]
    simp [rightSlice, ham]

/-- Linear coefficient at one fixed group weight, transported through the symmetric basis. -/
noncomputable def weightLinearCoefficient (basis : Module.Basis ι k V)
    (m : M) (i : ι) :
    AddMonoidAlgebra (SymmetricAlgebra k V) M →ₗ[k] k where
  toFun p := AdditivePolynomialCoalgebraFiltration.linearCoefficient (k := k) i
    (coefficientPolynomial basis p m)
  map_add' p q := by simp [coefficientPolynomial]
  map_smul' c p := by simp [coefficientPolynomial]

omit [AddCommGroup M] in
@[simp] theorem weightLinearCoefficient_apply (basis : Module.Basis ι k V)
    (m : M) (i : ι) (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) :
    weightLinearCoefficient basis m i p =
      AdditivePolynomialCoalgebraFiltration.linearCoefficient (k := k) i
        (coefficientPolynomial basis p m) := rfl

/-- Linear-coefficient slicing at one weight differentiates exactly that coefficient. -/
theorem rightSlice_weightLinearCoefficient_comul (basis : Module.Basis ι k V)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) (m : M) (i : ι) :
    rightSlice (weightLinearCoefficient basis m i)
        (Coalgebra.comul (R := k) p) =
      AddMonoidAlgebra.single m
        ((SymmetricAlgebra.equivMvPolynomial basis).symm
          (MvPolynomial.pderiv i (coefficientPolynomial basis p m))) := by
  classical
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro a
  apply (SymmetricAlgebra.equivMvPolynomial basis).injective
  change coefficientPolynomial basis
      (rightSlice (weightLinearCoefficient basis m i)
        (Coalgebra.comul (R := k) p)) a =
      SymmetricAlgebra.equivMvPolynomial basis
        ((AddMonoidAlgebra.single m
          ((SymmetricAlgebra.equivMvPolynomial basis).symm
            (MvPolynomial.pderiv i (coefficientPolynomial basis p m)))).coeff a)
  rw [coefficientPolynomial, coeff_rightSlice_comul,
    equivMvPolynomial_rightSlice_comul]
  by_cases ham : a = m
  · subst a
    have hw : polynomialFunctional basis
        (weightFunctional (weightLinearCoefficient basis m i) m) =
          AdditivePolynomialCoalgebraFiltration.linearCoefficient (k := k) i := by
      ext P
      simp [polynomialFunctional, weightFunctional, weightLinearCoefficient,
        coefficientPolynomial]
    rw [hw, AdditivePolynomialCoalgebraFiltration.rightSlice_linearCoefficient]
    simp [coefficientPolynomial]
  · have hw : polynomialFunctional basis
        (weightFunctional (weightLinearCoefficient basis m i) a) = 0 := by
      ext P
      simp [polynomialFunctional, weightFunctional, weightLinearCoefficient,
        coefficientPolynomial, ham]
    rw [hw]
    simp [AdditivePolynomialCoalgebraFiltration.rightSlice,
      AdditivePolynomialCoalgebraFiltration.tensorRightSlice, ham]

/-- Group-graded right contraction cannot increase maximum additive degree. -/
theorem additiveDegree_rightSlice_comul_le (basis : Module.Basis ι k V)
    (ψ : AddMonoidAlgebra (SymmetricAlgebra k V) M →ₗ[k] k)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) :
    additiveDegree basis (rightSlice ψ (Coalgebra.comul (R := k) p)) ≤
      additiveDegree basis p := by
  classical
  apply Finset.sup_le
  intro m hm
  change (coefficientPolynomial basis
    (rightSlice ψ (Coalgebra.comul (R := k) p)) m).totalDegree ≤ _
  rw [coefficientPolynomial, coeff_rightSlice_comul]
  exact (rightSlice_comul_totalDegree_le basis (weightFunctional ψ m) (p.coeff m)).trans
    (coefficientPolynomial_totalDegree_le basis p m)

/-- If two group-graded functionals agree on every group-like monomial, the difference of their
right contractions has strictly smaller additive degree whenever nonzero. -/
theorem additiveDegree_sub_rightSlice_comul_lt_of_groupLike_eq
    (basis : Module.Basis ι k V)
    (ψ χ : AddMonoidAlgebra (SymmetricAlgebra k V) M →ₗ[k] k)
    (hgroup : ∀ m : M,
      ψ (AddMonoidAlgebra.single m (1 : SymmetricAlgebra k V)) =
        χ (AddMonoidAlgebra.single m 1))
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M)
    (hzero : rightSlice ψ (Coalgebra.comul (R := k) p) -
      rightSlice χ (Coalgebra.comul (R := k) p) ≠ 0) :
    additiveDegree basis
        (rightSlice ψ (Coalgebra.comul (R := k) p) -
          rightSlice χ (Coalgebra.comul (R := k) p)) <
      additiveDegree basis p := by
  classical
  let q := rightSlice ψ (Coalgebra.comul (R := k) p) -
    rightSlice χ (Coalgebra.comul (R := k) p)
  obtain ⟨m, hm, hmdeg⟩ := exists_weight_additiveDegree_eq basis (p := q) hzero
  have hqm : q.coeff m ≠ 0 := Finsupp.mem_support_iff.mp hm
  have hqpoly : coefficientPolynomial basis q m =
      AdditivePolynomialCoalgebraFiltration.rightSlice
          (polynomialFunctional basis (weightFunctional ψ m))
          (coefficientPolynomial basis p m) -
        AdditivePolynomialCoalgebraFiltration.rightSlice
          (polynomialFunctional basis (weightFunctional χ m))
          (coefficientPolynomial basis p m) := by
    unfold q coefficientPolynomial
    rw [AddMonoidAlgebra.coeff_sub]
    change (SymmetricAlgebra.equivMvPolynomial basis)
        ((rightSlice ψ (Coalgebra.comul (R := k) p)).coeff m -
          (rightSlice χ (Coalgebra.comul (R := k) p)).coeff m) = _
    rw [map_sub, coeff_rightSlice_comul, coeff_rightSlice_comul,
      equivMvPolynomial_rightSlice_comul, equivMvPolynomial_rightSlice_comul]
  have hpoly0 :
      AdditivePolynomialCoalgebraFiltration.rightSlice
          (polynomialFunctional basis (weightFunctional ψ m))
          (coefficientPolynomial basis p m) -
        AdditivePolynomialCoalgebraFiltration.rightSlice
          (polynomialFunctional basis (weightFunctional χ m))
          (coefficientPolynomial basis p m) ≠ 0 := by
    intro hz
    apply hqm
    apply (SymmetricAlgebra.equivMvPolynomial basis).injective
    rw [map_zero]
    change coefficientPolynomial basis q m = 0
    rw [hqpoly]
    exact hz
  have hone : polynomialFunctional basis (weightFunctional ψ m) 1 =
      polynomialFunctional basis (weightFunctional χ m) 1 := by
    simpa [polynomialFunctional, weightFunctional] using hgroup m
  have hdrop :=
    AdditivePolynomialCoalgebraFiltration.rightSlice_sub_totalDegree_lt_of_apply_one_eq
      (polynomialFunctional basis (weightFunctional ψ m))
      (polynomialFunctional basis (weightFunctional χ m)) hone
      (coefficientPolynomial basis p m) hpoly0
  rw [← hmdeg]
  change (coefficientPolynomial basis q m).totalDegree < _
  rw [hqpoly]
  exact hdrop.trans_le (coefficientPolynomial_totalDegree_le basis p m)

/-- Agreement through the additive-linear layer makes the contraction difference drop at least
two additive degrees. -/
theorem additiveDegree_sub_rightSlice_comul_add_two_le_of_linear_eq
    (basis : Module.Basis ι k V)
    (ψ χ : AddMonoidAlgebra (SymmetricAlgebra k V) M →ₗ[k] k)
    (hgroup : ∀ m : M,
      ψ (AddMonoidAlgebra.single m (1 : SymmetricAlgebra k V)) =
        χ (AddMonoidAlgebra.single m 1))
    (hlinear : ∀ (m : M) (i : ι),
      ψ (AddMonoidAlgebra.single m (SymmetricAlgebra.ι k V (basis i))) =
        χ (AddMonoidAlgebra.single m (SymmetricAlgebra.ι k V (basis i))))
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M)
    (hzero : rightSlice ψ (Coalgebra.comul (R := k) p) -
      rightSlice χ (Coalgebra.comul (R := k) p) ≠ 0) :
    additiveDegree basis
        (rightSlice ψ (Coalgebra.comul (R := k) p) -
          rightSlice χ (Coalgebra.comul (R := k) p)) + 2 ≤
      additiveDegree basis p := by
  classical
  let q := rightSlice ψ (Coalgebra.comul (R := k) p) -
    rightSlice χ (Coalgebra.comul (R := k) p)
  obtain ⟨m, hm, hmdeg⟩ := exists_weight_additiveDegree_eq basis (p := q) hzero
  have hqm : q.coeff m ≠ 0 := Finsupp.mem_support_iff.mp hm
  have hqpoly : coefficientPolynomial basis q m =
      AdditivePolynomialCoalgebraFiltration.rightSlice
          (polynomialFunctional basis (weightFunctional ψ m))
          (coefficientPolynomial basis p m) -
        AdditivePolynomialCoalgebraFiltration.rightSlice
          (polynomialFunctional basis (weightFunctional χ m))
          (coefficientPolynomial basis p m) := by
    unfold q coefficientPolynomial
    rw [AddMonoidAlgebra.coeff_sub]
    change (SymmetricAlgebra.equivMvPolynomial basis)
        ((rightSlice ψ (Coalgebra.comul (R := k) p)).coeff m -
          (rightSlice χ (Coalgebra.comul (R := k) p)).coeff m) = _
    rw [map_sub, coeff_rightSlice_comul, coeff_rightSlice_comul,
      equivMvPolynomial_rightSlice_comul, equivMvPolynomial_rightSlice_comul]
  have hpoly0 :
      AdditivePolynomialCoalgebraFiltration.rightSlice
          (polynomialFunctional basis (weightFunctional ψ m))
          (coefficientPolynomial basis p m) -
        AdditivePolynomialCoalgebraFiltration.rightSlice
          (polynomialFunctional basis (weightFunctional χ m))
          (coefficientPolynomial basis p m) ≠ 0 := by
    intro hz
    apply hqm
    apply (SymmetricAlgebra.equivMvPolynomial basis).injective
    rw [map_zero]
    change coefficientPolynomial basis q m = 0
    rw [hqpoly]
    exact hz
  have hone : polynomialFunctional basis (weightFunctional ψ m) 1 =
      polynomialFunctional basis (weightFunctional χ m) 1 := by
    simpa [polynomialFunctional, weightFunctional] using hgroup m
  have hX : ∀ i : ι,
      polynomialFunctional basis (weightFunctional ψ m) (MvPolynomial.X i) =
        polynomialFunctional basis (weightFunctional χ m) (MvPolynomial.X i) := by
    intro i
    simpa [polynomialFunctional, weightFunctional] using hlinear m i
  have hdrop :=
    AdditivePolynomialCoalgebraFiltration.rightSlice_sub_totalDegree_add_two_le_of_apply_one_X_eq
      (polynomialFunctional basis (weightFunctional ψ m))
      (polynomialFunctional basis (weightFunctional χ m)) hone hX
      (coefficientPolynomial basis p m) hpoly0
  rw [← hmdeg]
  change (coefficientPolynomial basis q m).totalDegree + 2 ≤ _
  rw [hqpoly]
  exact hdrop.trans (coefficientPolynomial_totalDegree_le basis p m)

end
end GroupGradedSymmetricCoalgebraFiltration
end GaloisForLFunctions.HTGeometry
