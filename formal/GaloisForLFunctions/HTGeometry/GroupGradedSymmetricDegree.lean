import GaloisForLFunctions.HTGeometry.GroupGradedHopfSkewPrimitive

/-!
# Additive degree in group-graded symmetric Hopf algebras

Fixing a basis of `V` identifies every coefficient of `Sym(V)[M]` with a multivariable
polynomial.  This file packages the maximum polynomial degree across the finite torus support.
It is the degree filtration used by the mixed Hopf-kernel argument.
-/

namespace GaloisForLFunctions.HTGeometry
namespace GroupGradedSymmetricDegree

noncomputable section

variable {k V ι M : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup M]

/-- Polynomial representative of one torus-weight coefficient. -/
noncomputable def coefficientPolynomial (basis : Module.Basis ι k V)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) (m : M) :
    MvPolynomial ι k :=
  SymmetricAlgebra.equivMvPolynomial basis (p.coeff m)

@[simp] theorem coefficientPolynomial_zero (basis : Module.Basis ι k V) (m : M) :
    coefficientPolynomial basis (0 : AddMonoidAlgebra (SymmetricAlgebra k V) M) m = 0 := by
  simp [coefficientPolynomial]

/-- Maximum additive polynomial degree among all nonzero torus-weight coefficients. -/
noncomputable def additiveDegree (basis : Module.Basis ι k V)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) : ℕ := by
  classical
  exact p.coeff.support.sup fun m => (coefficientPolynomial basis p m).totalDegree

@[simp] theorem additiveDegree_zero (basis : Module.Basis ι k V) :
    additiveDegree basis (0 : AddMonoidAlgebra (SymmetricAlgebra k V) M) = 0 := by
  classical
  simp [additiveDegree]

omit [AddCommGroup M] in
/-- Every coefficient degree is bounded by the maximum, including coefficients outside support. -/
theorem coefficientPolynomial_totalDegree_le (basis : Module.Basis ι k V)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) (m : M) :
    (coefficientPolynomial basis p m).totalDegree ≤ additiveDegree basis p := by
  classical
  by_cases hm : m ∈ p.coeff.support
  · change (coefficientPolynomial basis p m).totalDegree ≤
      p.coeff.support.sup fun a => (coefficientPolynomial basis p a).totalDegree
    exact Finset.le_sup (α := ℕ)
      (f := fun a => (coefficientPolynomial basis p a).totalDegree) hm
  · have hcoeff : p.coeff m = 0 := Finsupp.notMem_support_iff.mp hm
    simp [coefficientPolynomial, hcoeff]

/-- A nonzero group-graded polynomial has a weight realizing its additive degree. -/
theorem exists_weight_additiveDegree_eq (basis : Module.Basis ι k V)
    {p : AddMonoidAlgebra (SymmetricAlgebra k V) M} (hp : p ≠ 0) :
    ∃ m ∈ p.coeff.support,
      (coefficientPolynomial basis p m).totalDegree = additiveDegree basis p := by
  classical
  have hs : p.coeff.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hp
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro m
    have hm : m ∉ p.coeff.support := by simp [h]
    exact Finsupp.notMem_support_iff.mp hm
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup p.coeff.support hs
    (fun a => (coefficientPolynomial basis p a).totalDegree)
  exact ⟨m, hm, hmax.symm⟩

/-- Additive degree is subadditive with respect to addition. -/
theorem additiveDegree_add_le (basis : Module.Basis ι k V)
    (p q : AddMonoidAlgebra (SymmetricAlgebra k V) M) :
    additiveDegree basis (p + q) ≤ max (additiveDegree basis p) (additiveDegree basis q) := by
  classical
  apply Finset.sup_le
  intro m hm
  change (coefficientPolynomial basis (p + q) m).totalDegree ≤ _
  have hpoly : coefficientPolynomial basis (p + q) m =
      coefficientPolynomial basis p m + coefficientPolynomial basis q m := by
    simp [coefficientPolynomial]
  rw [hpoly]
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le_max (coefficientPolynomial_totalDegree_le basis p m)
      (coefficientPolynomial_totalDegree_le basis q m))

/-- Scalar multiplication cannot increase additive degree. -/
theorem additiveDegree_smul_le (basis : Module.Basis ι k V) (c : k)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) :
    additiveDegree basis (c • p) ≤ additiveDegree basis p := by
  classical
  apply Finset.sup_le
  intro m hm
  change (coefficientPolynomial basis (c • p) m).totalDegree ≤ _
  have hpoly : coefficientPolynomial basis (c • p) m =
      c • coefficientPolynomial basis p m := by
    simp [coefficientPolynomial]
  rw [hpoly]
  exact (MvPolynomial.totalDegree_smul_le c _).trans
    (coefficientPolynomial_totalDegree_le basis p m)

/-- Additive degree of one homogeneous weight is the polynomial degree of its coefficient. -/
theorem additiveDegree_single (basis : Module.Basis ι k V) (m : M)
    (b : SymmetricAlgebra k V) :
    additiveDegree basis (AddMonoidAlgebra.single m b) =
      (SymmetricAlgebra.equivMvPolynomial basis b).totalDegree := by
  classical
  by_cases hb : b = 0
  · subst b
    simp
  · simp [additiveDegree, coefficientPolynomial, hb]

/-- Degree-at-most-`d` elements form a linear subspace. -/
noncomputable def degreeLE (basis : Module.Basis ι k V) (d : ℕ) :
    Submodule k (AddMonoidAlgebra (SymmetricAlgebra k V) M) where
  carrier := {p | additiveDegree basis p ≤ d}
  zero_mem' := by simp
  add_mem' {p q} hp hq :=
    (additiveDegree_add_le basis p q).trans (max_le hp hq)
  smul_mem' c p hp := (additiveDegree_smul_le basis c p).trans hp

@[simp] theorem mem_degreeLE_iff (basis : Module.Basis ι k V) (d : ℕ)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) :
    p ∈ degreeLE basis d ↔ additiveDegree basis p ≤ d := Iff.rfl

/-- Every group-like monomial belongs to additive degree zero. -/
theorem single_one_mem_degreeLE (basis : Module.Basis ι k V) (m : M) :
    AddMonoidAlgebra.single m (1 : SymmetricAlgebra k V) ∈ degreeLE basis 0 := by
  rw [mem_degreeLE_iff, additiveDegree_single]
  simp

/-- A homogeneous basis generator belongs to additive degree one. -/
theorem single_ι_basis_mem_degreeLE_one (basis : Module.Basis ι k V) (m : M) (i : ι) :
    AddMonoidAlgebra.single m (SymmetricAlgebra.ι k V (basis i)) ∈ degreeLE basis 1 := by
  rw [mem_degreeLE_iff, additiveDegree_single]
  simp [SymmetricAlgebra.equivMvPolynomial, MvPolynomial.totalDegree_X]

omit [AddCommGroup M] in
/-- A degree-zero coefficient is a scalar polynomial. -/
theorem coefficientPolynomial_eq_C_of_additiveDegree_eq_zero
    (basis : Module.Basis ι k V)
    {p : AddMonoidAlgebra (SymmetricAlgebra k V) M}
    (hp : additiveDegree basis p = 0) (m : M) :
    coefficientPolynomial basis p m =
      MvPolynomial.C (MvPolynomial.coeff 0 (coefficientPolynomial basis p m)) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  exact Nat.eq_zero_of_le_zero
    ((coefficientPolynomial_totalDegree_le basis p m).trans_eq hp)

/-- Every nonzero subspace contains a nonzero element of least additive degree. -/
theorem Submodule.exists_minimal_additiveDegree_ne_zero
    (basis : Module.Basis ι k V)
    {W : Submodule k (AddMonoidAlgebra (SymmetricAlgebra k V) M)} (hW : W ≠ ⊥) :
    ∃ p : AddMonoidAlgebra (SymmetricAlgebra k V) M,
      p ∈ W ∧ p ≠ 0 ∧
        ∀ ⦃q : AddMonoidAlgebra (SymmetricAlgebra k V) M⦄,
          q ∈ W → q ≠ 0 → additiveDegree basis p ≤ additiveDegree basis q := by
  classical
  have hex : ∃ p : AddMonoidAlgebra (SymmetricAlgebra k V) M, p ∈ W ∧ p ≠ 0 := by
    by_contra h
    apply hW
    ext p
    simp only [Submodule.mem_bot]
    constructor
    · intro hp
      by_contra hp0
      exact h ⟨p, hp, hp0⟩
    · rintro rfl
      exact W.zero_mem
  have hdeg : ∃ d : ℕ, ∃ p : AddMonoidAlgebra (SymmetricAlgebra k V) M,
      p ∈ W ∧ p ≠ 0 ∧ additiveDegree basis p = d := by
    obtain ⟨p, hpW, hp0⟩ := hex
    exact ⟨additiveDegree basis p, p, hpW, hp0, rfl⟩
  obtain ⟨p, hpW, hp0, hpdeg⟩ := Nat.find_spec hdeg
  refine ⟨p, hpW, hp0, ?_⟩
  intro q hqW hq0
  rw [hpdeg]
  exact Nat.find_min' hdeg ⟨q, hqW, hq0, rfl⟩

end
end GroupGradedSymmetricDegree
end GaloisForLFunctions.HTGeometry
