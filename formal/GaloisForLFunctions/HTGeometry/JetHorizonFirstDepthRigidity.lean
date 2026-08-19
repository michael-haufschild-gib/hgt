import Mathlib
import GaloisForLFunctions.HTGeometry.AffineConstantVectorFieldTranslation

/-!
# The gauge group of a first derivative horizon

A map that fixes the first derivatives of the coordinates of a point moves the point by a constant,
and a constant displacement that keeps the point on its own affine locus is a translation symmetry
of that locus.  So the whole gauge freedom of a first derivative horizon is the constant translation
stabilizer of the locus, and it is trivial exactly when the locus is translation rigid.

Both the infinitesimal form — derivations of the ambient differential field killing the first
derivatives — and the finite form — differential embeddings fixing the first derivatives — are
proved.  The mechanism is the same in both: the displacement is a constant tangent vector at a
generic point of the locus, hence the corresponding constant vector field preserves the vanishing
ideal, hence translation by the displacement preserves the locus.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ### Constant displacements that preserve a locus -/

variable {C ι L : Type*} [CommRing C] [CommRing L] [Algebra C L]

/-- A constant vector is a *translation symmetry* of the locus of a point when translating the
point by it preserves every polynomial relation the point satisfies. -/
def IsTranslationSymmetry (z : ι → L) (a : ι → C) : Prop :=
  ∀ P : MvPolynomial ι C, MvPolynomial.aeval z P = 0 →
    MvPolynomial.aeval (fun i => z i + algebraMap C L (a i)) P = 0

/-- A translation symmetry preserves the locus exactly, not only in one direction. -/
theorem IsTranslationSymmetry.aeval_iff [Finite ι] [IsNoetherianRing C]
    {z : ι → L} {a : ι → C} (ha : IsTranslationSymmetry z a) (P : MvPolynomial ι C) :
    MvPolynomial.aeval (fun i => z i + algebraMap C L (a i)) P = 0 ↔
      MvPolynomial.aeval z P = 0 :=
  aeval_add_eq_zero_iff z a ha P

/-! ### The chain rule for a derivation at a point -/

/-- **Chain rule.**  A derivation applied to a polynomial expression is the corresponding constant
vector field applied to the polynomial, provided the derivation moves the coordinates by
constants. -/
theorem derivation_aeval_eq_aeval_constVectorField
    {C : Type*} [Field C] [CharZero C] {ι L : Type*} [CommRing L] [Algebra C L]
    (D : Derivation C L L) (z : ι → L) (a : ι → C)
    (hD : ∀ i, D (z i) = algebraMap C L (a i)) (P : MvPolynomial ι C) :
    D (MvPolynomial.aeval z P) = MvPolynomial.aeval z (constVectorField a P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [constVectorField_C, map_zero, MvPolynomial.aeval_C]
      exact D.map_algebraMap c
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, map_add, map_add]
  | mul_X P i hP =>
      have hleib : constVectorField a (P * MvPolynomial.X i)
          = constVectorField a P * MvPolynomial.X i + MvPolynomial.C (a i) * P := by
        rw [Derivation.leibniz]
        simp only [constVectorField_X, smul_eq_mul]
        ring
      rw [map_mul, Derivation.leibniz, hleib]
      simp only [MvPolynomial.aeval_X, smul_eq_mul, map_add, map_mul, MvPolynomial.aeval_C, hP,
        hD i]
      ring

/-- A constant displacement realized by a derivation is tangent to the locus. -/
theorem constVectorField_mem_ker_of_derivation
    {C : Type*} [Field C] [CharZero C] {ι L : Type*} [CommRing L] [Algebra C L]
    (D : Derivation C L L) (z : ι → L) (a : ι → C)
    (hD : ∀ i, D (z i) = algebraMap C L (a i))
    {P : MvPolynomial ι C} (hP : MvPolynomial.aeval z P = 0) :
    MvPolynomial.aeval z (constVectorField a P) = 0 := by
  rw [← derivation_aeval_eq_aeval_constVectorField D z a hD, hP, map_zero]

/-- **A constant derivation direction is a translation symmetry.**  If a derivation moves the
coordinates of a point by constants, translation by those constants preserves the locus of the
point. -/
theorem isTranslationSymmetry_of_derivation
    {C : Type*} [Field C] [CharZero C] {ι L : Type*} [Finite ι] [CommRing L] [Algebra C L]
    (D : Derivation C L L) (z : ι → L) (a : ι → C)
    (hD : ∀ i, D (z i) = algebraMap C L (a i)) :
    IsTranslationSymmetry z a := by
  classical
  intro P hP
  set I : Ideal (MvPolynomial ι C) :=
    RingHom.ker (MvPolynomial.aeval z : MvPolynomial ι C →ₐ[C] L).toRingHom with hI
  have hmemI : ∀ Q : MvPolynomial ι C, Q ∈ I ↔ MvPolynomial.aeval z Q = 0 := by
    intro Q; rw [hI]; exact RingHom.mem_ker
  have hstab : ∀ Q ∈ I, constVectorField a Q ∈ I := by
    intro Q hQ
    rw [hmemI] at hQ ⊢
    exact constVectorField_mem_ker_of_derivation D z a hD hQ
  have hPI : P ∈ I := (hmemI P).2 hP
  have htrans := mvPolynomialBaseTranslation_mem_of_constVectorField_mem I a hstab hPI
  rw [hmemI, aeval_mvPolynomialBaseTranslation] at htrans
  exact htrans

/-! ### The first derivative horizon -/

variable {F : Type*} [Field F] [Differential F]

/-- **The infinitesimal gauge of a first derivative horizon.**  A derivation of a differential field
over its constants whose value at each coordinate of a point is a constant produces a translation
symmetry of the locus of that point; if the locus is translation rigid the derivation kills the
point. -/
theorem derivation_apply_eq_zero_of_translationRigid
    {C ι : Type*} [Field C] [CharZero C] [Finite ι] [Algebra C F]
    (hconst : ∀ x : F, x′ = 0 → ∃ c : C, algebraMap C F c = x)
    (z : ι → F) (hA : ∀ a : ι → C, IsTranslationSymmetry z a → a = 0)
    (D : Derivation C F F) (hD : ∀ i, (D (z i))′ = 0) (i : ι) :
    D (z i) = 0 := by
  classical
  choose a ha using fun j => hconst (D (z j)) (hD j)
  have hsym : IsTranslationSymmetry z a :=
    isTranslationSymmetry_of_derivation D z a (fun j => (ha j).symm)
  have : a = 0 := hA a hsym
  rw [← ha i, this]
  simp

/-- The same statement for a derivation commuting with the derivation of the field and killing the
first derivatives of the coordinates. -/
theorem derivation_apply_eq_zero_of_translationRigid_of_commutes
    {C ι : Type*} [Field C] [CharZero C] [Finite ι] [Algebra C F]
    (hconst : ∀ x : F, x′ = 0 → ∃ c : C, algebraMap C F c = x)
    (z : ι → F) (hA : ∀ a : ι → C, IsTranslationSymmetry z a → a = 0)
    (D : Derivation C F F) (hcomm : ∀ x : F, D (x′) = (D x)′)
    (hDz : ∀ i, D ((z i)′) = 0) (i : ι) :
    D (z i) = 0 :=
  derivation_apply_eq_zero_of_translationRigid hconst z hA D
    (fun j => by rw [← hcomm, hDz j]) i

/-- **The finite gauge of a first derivative horizon.**  A differential embedding fixing the first
derivatives of the coordinates displaces the point by a constant vector, and that vector is a
translation symmetry of the locus. -/
theorem isTranslationSymmetry_displacement_of_embedding
    {C ι U : Type*} [Field C] [CharZero C] [Finite ι] [Field U] [Differential U] [Algebra C U]
    (hconst : ∀ x : U, x′ = 0 → ∃ c : C, algebraMap C U c = x)
    (z : ι → U) (σ : U →ₐ[C] U) (hcomm : ∀ x : U, σ (x′) = (σ x)′)
    (hfix : ∀ i, σ ((z i)′) = (z i)′) :
    ∃ a : ι → C, (∀ i, σ (z i) = z i + algebraMap C U (a i)) ∧ IsTranslationSymmetry z a := by
  classical
  have hcst : ∀ i, (σ (z i) - z i)′ = 0 := by
    intro i
    rw [map_sub, ← hcomm, hfix i, sub_self]
  choose a ha using fun i => hconst (σ (z i) - z i) (hcst i)
  refine ⟨a, fun i => by rw [ha i]; ring, ?_⟩
  intro P hP
  have hσ : MvPolynomial.aeval (fun i => σ (z i)) P = σ (MvPolynomial.aeval z P) := by
    have := congrArg (fun f : MvPolynomial ι C →ₐ[C] U => f P)
      (MvPolynomial.algHom_ext (f := σ.comp (MvPolynomial.aeval z))
        (g := MvPolynomial.aeval fun i => σ (z i)) (fun i => by simp))
    simpa using this.symm
  have hzero : MvPolynomial.aeval (fun i => σ (z i)) P = 0 := by
    rw [hσ, hP, map_zero]
  have hpt : (fun i => σ (z i)) = fun i => z i + algebraMap C U (a i) := by
    funext i; rw [ha i]; ring
  rwa [hpt] at hzero

end

end GaloisForLFunctions.HTGeometry
