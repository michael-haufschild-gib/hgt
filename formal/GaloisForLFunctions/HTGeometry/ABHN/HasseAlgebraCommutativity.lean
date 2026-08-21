import GaloisForLFunctions.HTGeometry.ABHN.LocalScalarExtension

/-!
# Hasse detection of commutativity in central simple algebras

Scalar extension of a field algebra is commutative exactly when the original algebra is
commutative.  Applied to completions, this makes commutativity a local--global property of a
central simple representative.  This is deliberately stronger than Brauer splitness: a matrix
algebra is split but is generally not commutative.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- A scalar extension of a commutative field algebra is commutative. -/
theorem tensorProduct_mul_comm_of_mul_comm
    {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Ring A] [Algebra K L] [Algebra K A]
    (h : ∀ a b : A, a * b = b * a) :
    ∀ x y : L ⊗[K] A, x * y = y * x := by
  intro x y
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro l a
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp
    · intro m b
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, h a b,
        mul_comm l m]
    · intro y z hy hz
      rw [mul_add, add_mul, hy, hz]
  · intro x z hx hz
    rw [add_mul, mul_add, hx, hz]

/-- Commutativity is reflected by scalar extension along any field extension. -/
theorem tensorProduct_mul_comm_iff
    {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Ring A] [Algebra K L] [Algebra K A] :
    (∀ a b : A, a * b = b * a) ↔ ∀ x y : L ⊗[K] A, x * y = y * x := by
  constructor
  · exact tensorProduct_mul_comm_of_mul_comm
  · intro h a b
    apply Algebra.TensorProduct.includeRight_injective
      (FaithfulSMul.algebraMap_injective K L)
    simpa [Algebra.TensorProduct.includeRight, Algebra.TensorProduct.tmul_mul_tmul]
      using h (1 ⊗ₜ[K] a) (1 ⊗ₜ[K] b)

/-- A commutative central simple algebra is canonically its scalar field. -/
noncomputable def csaAlgEquivScalarOfMulComm {K : Type u} [Field K]
    (A : CSA.{u, u} K) (h : ∀ a b : A.carrier, a * b = b * a) :
    K ≃ₐ[K] A.carrier := by
  letI : IsAzumaya K A.carrier := csa_isAzumaya A
  apply AlgEquiv.ofBijective (Algebra.ofId K A.carrier)
  constructor
  · intro x y hxy
    exact FaithfulSMul.algebraMap_injective K A.carrier hxy
  · intro a
    have ha : a ∈ Subalgebra.center K A.carrier :=
      Subalgebra.mem_center_iff.mpr fun b => h b a
    obtain ⟨k, hk⟩ := (Algebra.IsCentral.mem_center_iff K).mp ha
    exact ⟨k, hk.symm⟩

/-- A commutative central simple algebra represents the split Brauer class. -/
theorem csa_brauerClass_eq_split_of_mul_comm {K : Type u} [Field K]
    (A : CSA.{u, u} K) (h : ∀ a b : A.carrier, a * b = b * a) :
    brauerClass A = brauerSplitClass K := by
  exact brauerClass_eq_of_algEquiv A (scalarCSA K) (csaAlgEquivScalarOfMulComm A h).symm

/-- A central simple algebra over a number field is commutative exactly when every completed
scalar extension is commutative. -/
theorem numberFieldLocalScalarExtensionMap_mul_comm_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) :
    (∀ a b : A.carrier, a * b = b * a) ↔ ∀ p : NumberFieldPlace K,
      ∀ x y : completion K p ⊗[K] A.carrier, x * y = y * x := by
  constructor
  · intro h p
    exact tensorProduct_mul_comm_of_mul_comm h
  · intro h
    exact (tensorProduct_mul_comm_iff (K := K) (L := completion K (witnessPlace K))
      (A := A.carrier)).mpr (h (witnessPlace K))

/-- A central simple algebra over `F(t)` is commutative exactly when every finite and infinite
completed scalar extension is commutative. -/
theorem rationalFunctionLocalScalarExtensionMap_mul_comm_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) :
    (∀ a b : A.carrier, a * b = b * a) ↔ ∀ p : RationalFunctionPlace F,
      ∀ x y : rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier, x * y = y * x := by
  constructor
  · intro h p
    exact tensorProduct_mul_comm_of_mul_comm h
  · intro h
    exact (tensorProduct_mul_comm_iff (K := RatFunc F)
      (L := rationalFunctionCompletion F .infinite) (A := A.carrier)).mpr (h .infinite)

/-- If every completed scalar extension of a same-universe number-field CSA is commutative, its
Brauer class is split. This is a degree-one local--global criterion, not ABHN's criterion by
local Brauer splitness: split matrix algebras of larger degree are noncommutative. -/
theorem numberField_brauerClass_eq_split_of_local_mul_comm
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, u} K)
    (h : ∀ p : NumberFieldPlace K, ∀ x y : completion K p ⊗[K] A.carrier, x * y = y * x) :
    brauerClass A = brauerSplitClass K := by
  apply csa_brauerClass_eq_split_of_mul_comm A
  exact (numberFieldLocalScalarExtensionMap_mul_comm_iff_forall_place K A).mpr h

/-- A non-split same-universe number-field CSA has a concrete noncommuting pair after scalar
extension at some completion. This is a local obstruction certificate, weaker than an ABHN local
invariant and independent of class field theory. -/
theorem numberField_exists_local_noncommuting_of_brauerClass_ne_split
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, u} K)
    (h : brauerClass A ≠ brauerSplitClass K) :
    ∃ p : NumberFieldPlace K, ∃ x y : completion K p ⊗[K] A.carrier, x * y ≠ y * x := by
  by_contra hlocal
  push Not at hlocal
  exact h (numberField_brauerClass_eq_split_of_local_mul_comm K A hlocal)

/-- If every finite and infinite completed scalar extension of a same-universe CSA over `F(t)`
is commutative, its Brauer class is split. As above, this concerns degree one, not general ABHN
splitness. -/
theorem rationalFunction_brauerClass_eq_split_of_local_mul_comm
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, u} (RatFunc F))
    (h : ∀ p : RationalFunctionPlace F,
      ∀ x y : rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier, x * y = y * x) :
    brauerClass A = brauerSplitClass (RatFunc F) := by
  apply csa_brauerClass_eq_split_of_mul_comm A
  exact (rationalFunctionLocalScalarExtensionMap_mul_comm_iff_forall_place F A).mpr h

/-- A non-split same-universe CSA over `F(t)` has a noncommuting pair after scalar extension at
some finite or infinite completion. This is the rational-function-field analogue of the preceding
local obstruction certificate. -/
theorem rationalFunction_exists_local_noncommuting_of_brauerClass_ne_split
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, u} (RatFunc F))
    (h : brauerClass A ≠ brauerSplitClass (RatFunc F)) :
    ∃ p : RationalFunctionPlace F,
      ∃ x y : rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier, x * y ≠ y * x := by
  by_contra hlocal
  push Not at hlocal
  exact h (rationalFunction_brauerClass_eq_split_of_local_mul_comm F A hlocal)

end GaloisForLFunctions.HTGeometry.ABHN
