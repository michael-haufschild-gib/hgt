import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FlatReductionRelations
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.Module

/-! A finite module flat over the base is flat over a Noetherian algebra if all its
reductions to the fibres are flat. -/

open TensorProduct IsLocalRing
open scoped Pointwise

namespace GlobalTheory.FiniteFibreFlat

private theorem lTensor_map_injective {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    (p : Ideal R) :
    Function.Injective ((p.map (algebraMap R A)).subtype.lTensor M) := by
  let I := p.map (algebraMap R A)
  let c : p →ₗ[R] I :=
    { toFun := fun r => ⟨algebraMap R A r, Ideal.mem_map_of_mem _ r.2⟩
      map_add' := fun r s => Subtype.ext (by simp)
      map_smul' := fun r s => Subtype.ext (by simp [Algebra.smul_def]) }
  let φ : M ⊗[R] p →ₗ[R] M ⊗[A] I :=
    TensorProduct.mapOfCompatibleSMul A R R M I ∘ₗ c.lTensor M
  have hφ (m : M) (r : p) : φ (m ⊗ₜ r) = m ⊗ₜ[A] c r := rfl
  have hsurj : ∀ x, x ∈ LinearMap.range φ := by
    intro x
    induction x with
    | zero => exact zero_mem _
    | add a b ha hb => exact add_mem ha hb
    | tmul m i =>
      obtain ⟨i, hi⟩ := i
      induction hi using Submodule.span_induction generalizing m with
      | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        exact ⟨m ⊗ₜ ⟨r, hr⟩, rfl⟩
      | zero =>
        change m ⊗ₜ[A] (0 : I) ∈ _
        rw [tmul_zero]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        change m ⊗ₜ[A] ((⟨x, hx⟩ : I) + ⟨y, hy⟩) ∈ _
        rw [tmul_add]
        exact add_mem (ihx m) (ihy m)
      | smul a x hx ih =>
        change m ⊗ₜ[A] (a • (⟨x, hx⟩ : I)) ∈ _
        rw [← smul_tmul]
        exact ih _
  have hcomp (y : M ⊗[R] p) :
      TensorProduct.rid A M (I.subtype.lTensor M (φ y)) =
        TensorProduct.rid R M (p.subtype.lTensor M y) := by
    induction y with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul m r => simp [hφ, c]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have h₀ := hcomp y
  rw [hx, map_zero, eq_comm, map_eq_zero_iff _ (TensorProduct.rid R M).injective,
    map_eq_zero_iff _ (Module.Flat.lTensor_preserves_injective_linearMap p.subtype p.injective_subtype)] at h₀
  rw [h₀, map_zero]

private theorem free_of_flat_reduction {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing A] [IsLocalRing A] [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] [Module.Flat R M] [Module.Finite A M]
    (p : Ideal R) (hp : p.map (algebraMap R A) ≤ maximalIdeal A)
    [Module.Flat (A ⧸ p.map (algebraMap R A)) ((A ⧸ p.map (algebraMap R A)) ⊗[A] M)] :
    Module.Free A M := by
  let I := p.map (algebraMap R A)
  letI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := mem_range_lTensor_comap_of_flat_reduction (C := A ⧸ I)
    Ideal.Quotient.mk_surjective Ideal.mk_ker (TensorProduct.mk A (A ⧸ I) M 1)
    (TensorProduct.mk_surjective A M (A ⧸ I) Ideal.Quotient.mk_surjective)
    (LinearMap.ker_tensorProductMk M) (maximalIdeal A).subtype x (by rw [hx]; simp)
  let e := Submodule.comapSubtypeEquivOfLe hp
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ (lTensor_map_injective p)] at hy
  have hy₀ := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [hy₀, map_zero]

/-- Flatness of all field reductions over the base implies flatness of a finite algebra
that is already flat over the base. -/
theorem flat_of_flat_fibres {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsNoetherianRing A] [Module.Finite A B] [Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) :
    Module.Flat A B := by
  refine Module.flat_of_isLocalized_maximal A B (fun P _ => Localization.AtPrime P ⊗[A] B)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) B 1) fun P _ => ?_
  let A' := Localization.AtPrime P
  let p : Ideal R := (maximalIdeal A').comap (algebraMap R A')
  let I := p.map (algebraMap R A')
  haveI : Module.Flat R (B ⊗[A] A') := Module.Flat.trans R B (B ⊗[A] A')
  haveI : Module.Flat R (A' ⊗[A] B) :=
    Module.Flat.of_linearEquiv ((Algebra.TensorProduct.comm A A' B).restrictScalars R).toLinearEquiv
  haveI : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A] B) := by
    let ψ : R →+* A' ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R A')
    have hψ₁ : p ≤ RingHom.ker ψ := fun r hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hψ₂ : p.primeCompl ≤ (IsUnit.submonoid (A' ⧸ I)).comap ψ := by
      intro r hr
      have hu : IsUnit (algebraMap R A' r) := by
        by_contra h
        exact hr h
      exact hu.map (Ideal.Quotient.mk I)
    refine H p.ResidueField (A' ⧸ I) (algebraMap R _) (Ideal.ResidueField.lift p ψ hψ₁ hψ₂) ?_
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p ψ hψ₁ hψ₂ r).symm
  haveI : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange A A' (A' ⧸ I) (A' ⧸ I) B)
  haveI : Module.Free A' (A' ⊗[A] B) := free_of_flat_reduction p Ideal.map_comap_le
  haveI : Module.Flat A' (A' ⊗[A] B) := Module.Flat.of_free
  exact Module.Flat.trans A A' (A' ⊗[A] B)

end GlobalTheory.FiniteFibreFlat
