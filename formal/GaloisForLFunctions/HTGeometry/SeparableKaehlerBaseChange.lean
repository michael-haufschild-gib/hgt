import Mathlib

/-!
# Kähler differentials under a separable base change

A separable field extension is formally étale, and a formally étale extension does not change the
module of Kähler differentials: the canonical map from the base-changed module is an isomorphism.
In characteristic zero every algebraic extension is separable, so passing to a finite extension of
the value field only extends scalars in the differential module.

This is the base-change identification a descent argument needs: a differential relation over the
big field is the extension of one over the small field.
-/

open TensorProduct

namespace GaloisForLFunctions.HTGeometry

universe u

variable (A F K : Type u) [Field A] [Field F] [Field K]
variable [Algebra A F] [Algebra F K] [Algebra A K] [IsScalarTower A F K]

/-- **Separable base change of Kähler differentials.**  For a separable extension `K/F` the
canonical map `K ⊗_F Ω[F/A] → Ω[K/A]` is an isomorphism. -/
noncomputable def kaehlerBaseChangeOfSeparable [Algebra.IsSeparable F K] :
    K ⊗[F] Ω[F⁄A] ≃ₗ[K] Ω[K⁄A] :=
  haveI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A F K

/-- **Characteristic zero.**  Every algebraic extension of the value field only extends scalars in
the differential module. -/
noncomputable def kaehlerBaseChangeOfIsAlgebraic [CharZero F] [Algebra.IsAlgebraic F K] :
    K ⊗[F] Ω[F⁄A] ≃ₗ[K] Ω[K⁄A] :=
  kaehlerBaseChangeOfSeparable A F K

/-- The base-change isomorphism is the canonical map. -/
theorem kaehlerBaseChangeOfSeparable_apply [Algebra.IsSeparable F K] (x : K ⊗[F] Ω[F⁄A]) :
    kaehlerBaseChangeOfSeparable A F K x = KaehlerDifferential.mapBaseChange A F K x := rfl

/-- **The differential of a base element is the extension of its differential.** -/
theorem kaehlerBaseChangeOfSeparable_tmul [Algebra.IsSeparable F K] (c : K) (s : F) :
    kaehlerBaseChangeOfSeparable A F K (c ⊗ₜ KaehlerDifferential.D A F s)
      = c • KaehlerDifferential.D A K (algebraMap F K s) := by
  rw [kaehlerBaseChangeOfSeparable_apply, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.map_D]

/-- **Injectivity of the canonical map.**  A differential relation that vanishes after extension of
scalars already vanishes. -/
theorem mapBaseChange_injective_of_separable [Algebra.IsSeparable F K] :
    Function.Injective (KaehlerDifferential.mapBaseChange A F K) :=
  (kaehlerBaseChangeOfSeparable A F K).injective

/-- **Surjectivity of the canonical map.**  Every differential of the big field is an extension of
differentials of the small one. -/
theorem mapBaseChange_surjective_of_separable [Algebra.IsSeparable F K] :
    Function.Surjective (KaehlerDifferential.mapBaseChange A F K) :=
  (kaehlerBaseChangeOfSeparable A F K).surjective

/-! ## Kernels commute with base change -/

section Kernel

variable {F K N P : Type u} [Field F] [Field K] [Algebra F K]
variable [AddCommGroup N] [Module F N] [AddCommGroup P] [Module F P]

/-- **The kernel over the big field is the extension of the kernel over the small field.**  A field
extension is flat, so base change preserves kernels: every relation over `K` is a `K`-combination of
relations over `F`. -/
theorem ker_lTensor_eq_range_subtype (f : N →ₗ[F] P) :
    LinearMap.ker (AlgebraTensorModule.lTensor K K f)
      = LinearMap.range (AlgebraTensorModule.lTensor K K (LinearMap.ker f).subtype) :=
  Module.Flat.ker_lTensor_eq K K f

/-- The kernel over the big field is the image of the base-changed small kernel; concretely, every
element of it comes from `K ⊗ ker f`. -/
theorem exists_of_mem_ker_lTensor (f : N →ₗ[F] P)
    {v : K ⊗[F] N} (hv : v ∈ LinearMap.ker (AlgebraTensorModule.lTensor K K f)) :
    ∃ w : K ⊗[F] (LinearMap.ker f),
      AlgebraTensorModule.lTensor K K (LinearMap.ker f).subtype w = v := by
  rw [ker_lTensor_eq_range_subtype] at hv
  exact hv

end Kernel

end GaloisForLFunctions.HTGeometry
