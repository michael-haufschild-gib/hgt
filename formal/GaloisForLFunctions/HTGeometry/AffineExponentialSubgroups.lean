import GaloisForLFunctions.HTGeometry.AffineExponentialGroupHopf
import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Equation-defined subgroups of `Gₐⁿ × Gₘⁿ`

This file passes from the coordinate Hopf algebra to genuine closed affine subgroups.  It proves a
principal Hopf-ideal criterion and applies it to the two equations central to additive-exponential
geometry:

* an additive linear equation `ℓ = 0`, whose coordinate is primitive;
* a torus character equation `χᵐ = 1`, whose coordinate difference is skew-primitive.

The resulting quotients carry kernel-checked Hopf algebra structures.  Thus these equations define
closed subgroup schemes, rather than merely set-theoretic solution sets.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

namespace PrincipalHopfIdeal

noncomputable section

variable {R A : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- A principal ideal is a Hopf ideal when its generator has zero counit, its comultiplication
vanishes in the tensor square of the principal quotient, and its antipode stays in the ideal. -/
theorem isHopfIdeal (g : A)
    (he : Coalgebra.counit (R := R) g = 0)
    (hc : TensorProduct.map
      ((Ideal.span ({g} : Set A)).restrictScalars R).mkQ
      ((Ideal.span ({g} : Set A)).restrictScalars R).mkQ
      (Coalgebra.comul (R := R) g) = 0)
    (hs : HopfAlgebra.antipode R g ∈ Ideal.span ({g} : Set A)) :
    (Ideal.span ({g} : Set A)).IsHopfIdeal R := by
  let I : Ideal A := Ideal.span {g}
  change Bialgebra.counitAlgHom R A g = 0 at he
  change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
    (Bialgebra.comulAlgHom R A g) = 0 at hc
  refine { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_, antipode_mem := ?_ }
  · intro x hx
    change x ∈ Ideal.span ({g} : Set A) at hx
    rw [Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    change Bialgebra.counitAlgHom R A (a * g) = 0
    rw [map_mul, he, mul_zero]
  · intro x hx
    change x ∈ Ideal.span ({g} : Set A) at hx
    rw [Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Bialgebra.comulAlgHom R A (a * g)) = 0
    rw [map_mul, map_mul, hc, mul_zero]
  · intro x hx
    rw [Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [HopfAlgebra.antipode_mul_distrib]
    exact I.mul_mem_left _ hs

end

end PrincipalHopfIdeal

namespace AffineExponentialSubgroups

open AffineExponentialGroup

noncomputable section

variable (k : Type*) [Field k]

/-- An arbitrary additive linear coordinate, embedded in `𝒪(Gₐⁿ × Gₘⁿ)`. -/
noncomputable def additiveLinear {n : ℕ} (v : Fin n → k) :
    CoordinateAlgebra k n :=
  1 ⊗ₜ[k] SymmetricAlgebra.ι k (Fin n → k) v

@[simp]
theorem counit_additiveLinear {n : ℕ} (v : Fin n → k) :
    Coalgebra.counit (R := k) (additiveLinear k v) = 0 := by
  simp [additiveLinear]

@[simp]
theorem comul_additiveLinear {n : ℕ} (v : Fin n → k) :
    Coalgebra.comul (R := k) (additiveLinear k v) =
      additiveLinear k v ⊗ₜ[k] 1 + 1 ⊗ₜ[k] additiveLinear k v := by
  simp [additiveLinear, Algebra.TensorProduct.one_def, TensorProduct.tmul_add]

@[simp]
theorem antipode_additiveLinear {n : ℕ} (v : Fin n → k) :
    HopfAlgebra.antipode k (additiveLinear k v) = -additiveLinear k v := by
  simp [TensorProduct.antipode_def, additiveLinear, TensorProduct.tmul_neg]

/-- Principal ideal cutting out the kernel of one additive linear form. -/
noncomputable def additiveRelationIdeal {n : ℕ} (v : Fin n → k) :
    Ideal (CoordinateAlgebra k n) :=
  Ideal.span {additiveLinear k v}

/-- An additive linear equation cuts out a closed subgroup scheme. -/
theorem additiveRelation_isHopfIdeal {n : ℕ} (v : Fin n → k) :
    (additiveRelationIdeal k v).IsHopfIdeal k := by
  let g := additiveLinear k v
  apply PrincipalHopfIdeal.isHopfIdeal g
  · exact counit_additiveLinear k v
  · let I : Ideal (CoordinateAlgebra k n) := Ideal.span {g}
    change TensorProduct.map (I.restrictScalars k).mkQ (I.restrictScalars k).mkQ
      (Coalgebra.comul (R := k) g) = 0
    rw [comul_additiveLinear]
    have hg : (I.restrictScalars k).mkQ (additiveLinear k v) = 0 := by
      change Submodule.Quotient.mk (p := I.restrictScalars k)
        (additiveLinear k v) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton_self g
    rw [map_add, TensorProduct.map_tmul, TensorProduct.map_tmul, hg,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add]
  · rw [antipode_additiveLinear]
    exact (Ideal.span {g}).neg_mem (Ideal.mem_span_singleton_self g)

/-- Hopf coordinate algebra of an additive-linear kernel subgroup. -/
abbrev AdditiveRelationQuotient {n : ℕ} (v : Fin n → k) :=
  CoordinateAlgebra k n ⧸ additiveRelationIdeal k v

noncomputable instance instAdditiveRelationQuotientHopf {n : ℕ} (v : Fin n → k) :
    HopfAlgebra k (AdditiveRelationQuotient k v) := by
  letI : (additiveRelationIdeal k v).IsHopfIdeal k := additiveRelation_isHopfIdeal k v
  infer_instance

/-- Coordinate equation `χᵐ - 1` for the kernel of a torus character. -/
noncomputable def torusRelation {n : ℕ} (m : Fin n →₀ ℤ) :
    CoordinateAlgebra k n := torusCharacter k m - 1

@[simp]
theorem counit_torusRelation {n : ℕ} (m : Fin n →₀ ℤ) :
    Coalgebra.counit (R := k) (torusRelation k m) = 0 := by
  simp [torusRelation]

/-- Torus character relations are skew-primitive. -/
theorem comul_torusRelation {n : ℕ} (m : Fin n →₀ ℤ) :
    Coalgebra.comul (R := k) (torusRelation k m) =
      torusRelation k m ⊗ₜ[k] torusCharacter k m +
        1 ⊗ₜ[k] torusRelation k m := by
  simp only [torusRelation, map_sub, comul_torusCharacter, Bialgebra.comul_one]
  rw [Algebra.TensorProduct.one_def]
  rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

/-- The antipode of a torus character relation stays in its principal ideal. -/
theorem antipode_torusRelation_mem {n : ℕ} (m : Fin n →₀ ℤ) :
    HopfAlgebra.antipode k (torusRelation k m) ∈ Ideal.span {torusRelation k m} := by
  rw [show HopfAlgebra.antipode k (torusRelation k m) =
      -torusCharacter k (-m) * torusRelation k m by
    rw [show HopfAlgebra.antipode k (torusRelation k m) =
        HopfAlgebra.antipode k (torusCharacter k m) - HopfAlgebra.antipode k 1 by
      exact map_sub (HopfAlgebra.antipode k) _ _]
    rw [AffineExponentialGroup.antipode_torusCharacter, HopfAlgebra.antipode_one]
    have hunit : torusCharacter k (-m) * torusCharacter k m = 1 := by
      rw [← AffineExponentialGroup.torusCharacter_add]
      simp
    unfold torusRelation
    linear_combination hunit]
  exact Ideal.mem_span_singleton'.2 ⟨_, rfl⟩

/-- Principal ideal cutting out the kernel of one torus character. -/
noncomputable def torusRelationIdeal {n : ℕ} (m : Fin n →₀ ℤ) :
    Ideal (CoordinateAlgebra k n) :=
  Ideal.span {torusRelation k m}

/-- A torus character equation cuts out a closed subgroup scheme. -/
theorem torusRelation_isHopfIdeal {n : ℕ} (m : Fin n →₀ ℤ) :
    (torusRelationIdeal k m).IsHopfIdeal k := by
  let g := torusRelation k m
  apply PrincipalHopfIdeal.isHopfIdeal g
  · exact counit_torusRelation k m
  · let I : Ideal (CoordinateAlgebra k n) := Ideal.span {g}
    change TensorProduct.map (I.restrictScalars k).mkQ (I.restrictScalars k).mkQ
      (Coalgebra.comul (R := k) g) = 0
    rw [comul_torusRelation]
    have hg : (I.restrictScalars k).mkQ (torusRelation k m) = 0 := by
      change Submodule.Quotient.mk (p := I.restrictScalars k)
        (torusRelation k m) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton_self g
    rw [map_add, TensorProduct.map_tmul, TensorProduct.map_tmul, hg,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add]
  · exact antipode_torusRelation_mem k m

/-- Hopf coordinate algebra of a torus-character kernel subgroup. -/
abbrev TorusRelationQuotient {n : ℕ} (m : Fin n →₀ ℤ) :=
  CoordinateAlgebra k n ⧸ torusRelationIdeal k m

noncomputable instance instTorusRelationQuotientHopf {n : ℕ} (m : Fin n →₀ ℤ) :
    HopfAlgebra k (TorusRelationQuotient k m) := by
  letI : (torusRelationIdeal k m).IsHopfIdeal k := torusRelation_isHopfIdeal k m
  infer_instance

end


end AffineExponentialSubgroups

end GaloisForLFunctions.HTGeometry
