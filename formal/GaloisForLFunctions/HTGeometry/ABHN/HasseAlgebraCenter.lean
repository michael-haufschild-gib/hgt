import GaloisForLFunctions.HTGeometry.ABHN.LocalScalarExtension

/-!
# Hasse detection of central elements in central simple algebras

A specified element of a central simple algebra is central exactly when its scalar extension is
central at every completion.  The statement concerns global elements embedded into each local
algebra; it does not attempt to descend arbitrary local central elements.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v

/-- Centrality of an element in a central simple algebra over a number field is detected after
scalar extension to every completed place. -/
theorem numberFieldLocalScalarExtensionMap_mem_center_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (a : A.carrier) :
    a ∈ Subalgebra.center K A.carrier ↔ ∀ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p A a ∈
        Subalgebra.center (completion K p) (completion K p ⊗[K] A.carrier) := by
  constructor
  · intro ha p
    rw [Subalgebra.mem_center_iff] at ha ⊢
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [mul_add, add_mul, hx, hy]
    | tmul l b =>
      change (l ⊗ₜ[K] b) * (1 ⊗ₜ[K] a) = (1 ⊗ₜ[K] a) * (l ⊗ₜ[K] b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one, ha b]
  · intro h
    rw [Subalgebra.mem_center_iff]
    intro b
    apply numberFieldLocalScalarExtensionMap_injective K (witnessPlace K) A
    rw [map_mul, map_mul]
    exact Subalgebra.mem_center_iff.mp (h (witnessPlace K))
      (numberFieldLocalScalarExtensionMap K (witnessPlace K) A b)

/-- Centrality of an element in a central simple algebra over `F(t)` is detected after scalar
extension to every finite and infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mem_center_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (a : A.carrier) :
    a ∈ Subalgebra.center (RatFunc F) A.carrier ↔ ∀ p : RationalFunctionPlace F,
      rationalFunctionLocalScalarExtensionMap F p A a ∈
        Subalgebra.center (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier) := by
  constructor
  · intro ha p
    rw [Subalgebra.mem_center_iff] at ha ⊢
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [mul_add, add_mul, hx, hy]
    | tmul l b =>
      change (l ⊗ₜ[RatFunc F] b) * (1 ⊗ₜ[RatFunc F] a) =
        (1 ⊗ₜ[RatFunc F] a) * (l ⊗ₜ[RatFunc F] b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one, ha b]
  · intro h
    rw [Subalgebra.mem_center_iff]
    intro b
    apply rationalFunctionLocalScalarExtensionMap_injective F .infinite A
    rw [map_mul, map_mul]
    exact Subalgebra.mem_center_iff.mp (h .infinite)
      (rationalFunctionLocalScalarExtensionMap F .infinite A b)

/-- Centrality of a fixed number-field CSA element is detected at one completion. -/
theorem numberFieldLocalScalarExtensionMap_mem_center_iff_exists_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (a : A.carrier) :
    a ∈ Subalgebra.center K A.carrier ↔ ∃ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p A a ∈
        Subalgebra.center (completion K p) (completion K p ⊗[K] A.carrier) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldLocalScalarExtensionMap_mem_center_iff_forall_place K A a).mp h
        (witnessPlace K)⟩
  · rintro ⟨p, hp⟩
    rw [Subalgebra.mem_center_iff]
    intro b
    apply numberFieldLocalScalarExtensionMap_injective K p A
    rw [map_mul, map_mul]
    exact Subalgebra.mem_center_iff.mp hp
      (numberFieldLocalScalarExtensionMap K p A b)

/-- Centrality of a fixed rational-function-field CSA element is detected at one finite or
infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mem_center_iff_exists_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (a : A.carrier) :
    a ∈ Subalgebra.center (RatFunc F) A.carrier ↔ ∃ p : RationalFunctionPlace F,
      rationalFunctionLocalScalarExtensionMap F p A a ∈
        Subalgebra.center (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionLocalScalarExtensionMap_mem_center_iff_forall_place F A a).mp h
        .infinite⟩
  · rintro ⟨p, hp⟩
    rw [Subalgebra.mem_center_iff]
    intro b
    apply rationalFunctionLocalScalarExtensionMap_injective F p A
    rw [map_mul, map_mul]
    exact Subalgebra.mem_center_iff.mp hp
      (rationalFunctionLocalScalarExtensionMap F p A b)

end GaloisForLFunctions.HTGeometry.ABHN
