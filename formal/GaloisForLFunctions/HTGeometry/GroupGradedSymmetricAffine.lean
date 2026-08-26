import GaloisForLFunctions.HTGeometry.GroupGradedSymmetricDegree
import GaloisForLFunctions.HTGeometry.SymmetricHopfPrimitive

/-!
# Affine and scalar layers of group-graded symmetric algebras

This file identifies the first two additive-degree layers of `Sym(V)[M]`.  Degree-zero
coefficients are transported back to the scalar group algebra.  A symmetric coefficient of
degree at most one is its constant coefficient plus one canonical degree-one generator.
-/

namespace GaloisForLFunctions.HTGeometry
namespace GroupGradedSymmetricAffine

noncomputable section

open GroupGradedSymmetricDegree

variable {k V ι M : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup M]

/-- Constant polynomial coefficient of a symmetric-algebra element. -/
noncomputable def symmetricConstantCoefficient (basis : Module.Basis ι k V) :
    SymmetricAlgebra k V →ₗ[k] k where
  toFun b := MvPolynomial.coeff 0 (SymmetricAlgebra.equivMvPolynomial basis b)
  map_add' b c := by simp
  map_smul' a b := by simp

@[simp] theorem symmetricConstantCoefficient_apply (basis : Module.Basis ι k V)
    (b : SymmetricAlgebra k V) :
    symmetricConstantCoefficient basis b =
      MvPolynomial.coeff 0 (SymmetricAlgebra.equivMvPolynomial basis b) := rfl

/-- Scalar group-algebra part obtained from constant coefficients at every weight. -/
noncomputable def scalarPart (basis : Module.Basis ι k V)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) : AddMonoidAlgebra k M :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange.linearMap (symmetricConstantCoefficient basis) p.coeff)

omit [AddCommGroup M] in
@[simp] theorem scalarPart_coeff (basis : Module.Basis ι k V)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) (m : M) :
    (scalarPart basis p).coeff m = symmetricConstantCoefficient basis (p.coeff m) := by
  rfl

/-- Embed the scalar group algebra as constant symmetric coefficients. -/
noncomputable def scalarEmbedding : AddMonoidAlgebra k M →ₗ[k]
    AddMonoidAlgebra (SymmetricAlgebra k V) M where
  toFun q := AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange.linearMap (Algebra.linearMap k (SymmetricAlgebra k V)) q.coeff)
  map_add' q r := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro m
    simp
  map_smul' c q := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro m
    simp

omit [AddCommGroup M] in
@[simp] theorem scalarEmbedding_coeff (q : AddMonoidAlgebra k M) (m : M) :
    (scalarEmbedding (k := k) (V := V) q).coeff m =
      algebraMap k (SymmetricAlgebra k V) (q.coeff m) := by
  rfl

omit [AddCommGroup M] in
@[simp] theorem scalarEmbedding_single (m : M) (c : k) :
    scalarEmbedding (V := V) (AddMonoidAlgebra.single m c) =
      AddMonoidAlgebra.single m (algebraMap k (SymmetricAlgebra k V) c) := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro a
  by_cases ham : a = m <;> simp [scalarEmbedding_coeff, ham]

omit [AddCommGroup M] in
/-- Every additive-degree-zero element is exactly its embedded scalar group-algebra part. -/
theorem eq_scalarEmbedding_scalarPart_of_additiveDegree_eq_zero
    (basis : Module.Basis ι k V)
    {p : AddMonoidAlgebra (SymmetricAlgebra k V) M}
    (hp : additiveDegree basis p = 0) :
    p = scalarEmbedding (V := V) (scalarPart basis p) := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro m
  apply (SymmetricAlgebra.equivMvPolynomial basis).injective
  change coefficientPolynomial basis p m =
    SymmetricAlgebra.equivMvPolynomial basis
      ((scalarEmbedding (V := V) (scalarPart basis p)).coeff m)
  rw [coefficientPolynomial_eq_C_of_additiveDegree_eq_zero basis hp m]
  simp [symmetricConstantCoefficient, coefficientPolynomial]

/-- A polynomial of total degree at most one, with zero constant term, scales linearly. -/
private theorem mvScale_two_sub_C_coeff_zero_of_totalDegree_le_one [CharZero k]
    {P : MvPolynomial ι k} (hP : P.totalDegree ≤ 1) :
    SymmetricPrimitive.mvScale (2 : k)
        (P - MvPolynomial.C (MvPolynomial.coeff 0 P)) =
      2 * (P - MvPolynomial.C (MvPolynomial.coeff 0 P)) := by
  classical
  let Q := P - MvPolynomial.C (MvPolynomial.coeff 0 P)
  have hQdeg : Q.totalDegree ≤ 1 := by
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le hP (by simp))
  have hQzero : MvPolynomial.coeff 0 Q = 0 := by
    simp [Q]
  apply MvPolynomial.ext
  intro s
  rw [SymmetricPrimitive.coeff_mvScale]
  rw [show (2 : MvPolynomial ι k) = MvPolynomial.C (2 : k) by
    exact (map_ofNat MvPolynomial.C 2).symm]
  rw [MvPolynomial.coeff_C_mul]
  change MvPolynomial.coeff s Q * 2 ^ (s.sum fun _ n => n) =
    2 * MvPolynomial.coeff s Q
  by_cases hscoeff : MvPolynomial.coeff s Q = 0
  · simp [hscoeff]
  · have hs : s ∈ Q.support := MvPolynomial.mem_support_iff.mpr hscoeff
    have hsumle : s.sum (fun _ n => n) ≤ 1 :=
      (MvPolynomial.le_totalDegree hs).trans hQdeg
    have hs0 : s ≠ 0 := by
      intro hs0
      subst s
      exact hscoeff hQzero
    have hsum0 : s.sum (fun _ n => n) ≠ 0 := by
      intro hzero
      apply hs0
      apply Finsupp.ext
      intro i
      have hi := Finsupp.single_le_sum s (g := fun (_ : ι) (n : ℕ) => n)
        (fun (_ : ι) (n : ℕ) => Nat.zero_le n) i
      have hi0 : s i ≤ 0 := by simpa [hzero] using hi
      exact Nat.eq_zero_of_le_zero hi0
    have hsum : s.sum (fun _ n => n) = 1 := by omega
    simp [hsum, mul_comm]

/-- Exact affine decomposition of a symmetric coefficient of degree at most one. -/
theorem exists_eq_algebraMap_constant_add_ι_of_totalDegree_le_one [CharZero k]
    (basis : Module.Basis ι k V) (b : SymmetricAlgebra k V)
    (hb : (SymmetricAlgebra.equivMvPolynomial basis b).totalDegree ≤ 1) :
    ∃ v : V,
      b = algebraMap k (SymmetricAlgebra k V) (symmetricConstantCoefficient basis b) +
        SymmetricAlgebra.ι k V v := by
  let P := SymmetricAlgebra.equivMvPolynomial basis b
  let Q := P - MvPolynomial.C (MvPolynomial.coeff 0 P)
  have hscale : SymmetricPrimitive.mvScale (2 : k) Q = 2 * Q := by
    exact mvScale_two_sub_C_coeff_zero_of_totalDegree_le_one hb
  obtain ⟨j, hj⟩ := SymmetricPrimitive.eq_finite_linear_sum_of_scale_two hscale
  let v : V := ∑ s : ↥Q.support, MvPolynomial.coeff s.1 Q • basis (j s)
  have hQv : Q = SymmetricAlgebra.equivMvPolynomial basis
      (SymmetricAlgebra.ι k V v) := by
    rw [hj]
    simp [v, Algebra.smul_def, SymmetricAlgebra.equivMvPolynomial]
  refine ⟨v, ?_⟩
  apply (SymmetricAlgebra.equivMvPolynomial basis).injective
  simp only [map_add]
  have hc : SymmetricAlgebra.equivMvPolynomial basis
      (algebraMap k (SymmetricAlgebra k V) (symmetricConstantCoefficient basis b)) =
      MvPolynomial.C (MvPolynomial.coeff 0 P) := by
    simp [symmetricConstantCoefficient, P]
  rw [hc]
  change P = MvPolynomial.C (MvPolynomial.coeff 0 P) +
      SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι k V v)
  rw [← hQv]
  simp [Q]

end
end GroupGradedSymmetricAffine
end GaloisForLFunctions.HTGeometry
