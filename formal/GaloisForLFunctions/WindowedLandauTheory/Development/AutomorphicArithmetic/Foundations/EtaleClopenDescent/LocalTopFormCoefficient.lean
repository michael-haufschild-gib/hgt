import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalizedDifferentJacobian
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Flat.TorsionFree

/-! In a basis of the local absolute differentials, regular top forms
are exactly the multiples of the basis wedge by local scalars. -/

noncomputable section

open KaehlerDifferential GlobalTheory.SchemeCohomology
open scoped nonZeroDivisors GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

section TopCoefficient

private theorem topWedge_toSpanSingleton_surjective {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {d : ℕ} (b : Module.Basis (Fin d) R M) :
    Function.Surjective (LinearMap.toSpanSingleton R (⋀[R]^d M) (exteriorPower.ιMulti R d b)) := by
  classical
  have hspan (v : Fin d → M) :
      exteriorPower.ιMulti R d v ∈ Submodule.span R {exteriorPower.ιMulti R d b} := by
    let f := b.constr R v
    have hv : (fun j => f (b j)) = v := funext fun j => b.constr_basis R v j
    have he := wedge_image_eq_det_smul b b f
    rw [hv] at he
    exact Submodule.mem_span_singleton.mpr ⟨_, he.symm⟩
  intro z
  have hz : z ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R d (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  exact Submodule.mem_span_singleton.mp ((Submodule.span_le.mpr
    (by rintro _ ⟨v, rfl⟩; exact hspan v)) hz)

variable {k C E : Type*} [CommRing k] [CommRing C] [IsDomain C] [Field E]
  [Algebra k C] [Algebra k E] [Algebra C E] [IsScalarTower k C E] [IsFractionRing C E]

/-- A multiple of the generic image of the top basis wedge comes from
the local chart exactly when its coefficient lies in the local ring. -/
theorem topForm_smul_mem_range_iff {d : ℕ} (b : Module.Basis (Fin d) C Ω[C⁄k]) (x : E) :
    let f := algebraFormPullback k C E d
    let η := f (exteriorPower.ιMulti C d b)
    x • η ∈ LinearMap.range f ↔ x ∈ (algebraMap C E).range := by
  intro f η
  let η₀ := exteriorPower.ιMulti C d b
  letI : Module.Free C Ω[C⁄k] := Module.Free.of_basis b
  letI : Algebra.FormallyEtale C E := .of_isLocalization C⁰
  letI : IsLocalizedModule C⁰ f := (isLocalizedModule_iff_isBaseChange C⁰ E f).mpr
    (algebraFormPullback_isBaseChange k C E d)
  have hf : Function.Injective f := (IsLocalizedModule.injective_iff_isRegular C⁰ f).mpr
    (fun c => by
      change IsSMulRegular (ExteriorDifferentials k C d) (c : C)
      exact Module.Flat.isSMulRegular_of_nonZeroDivisors
        (M := ExteriorDifferentials k C d) c.property)
  have hη₀ : η₀ ≠ 0 := by
    intro h
    let α : ExteriorDifferentials k C d →ₗ[C] C := exteriorPower.alternatingMapLinearEquiv b.det
    have hone : α η₀ = 1 := by
      rw [show α η₀ = b.det b from exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _,
        Module.Basis.det_self]
    rw [h, map_zero] at hone
    exact zero_ne_one hone
  have hη : η ≠ 0 := fun h => hη₀ (hf (h.trans (map_zero f).symm))
  constructor
  · rintro ⟨ω, hω⟩
    obtain ⟨a, rfl⟩ := topWedge_toSpanSingleton_surjective b ω
    refine ⟨a, smul_left_injective E hη ?_⟩
    change algebraMap C E a • η = x • η
    rw [IsScalarTower.algebraMap_smul]
    exact (map_smul f a η₀).symm.trans hω
  · rintro ⟨a, rfl⟩
    exact ⟨a • η₀, (map_smul f a η₀).trans (IsScalarTower.algebraMap_smul E a η).symm⟩

omit [CommRing k] [IsDomain C] [Algebra k C] [Algebra k E]
    [IsScalarTower k C E] [IsFractionRing C E] in
/-- Testing a scalar against all elements of an ideal is equivalent to
testing against a local generator of the extended ideal. -/
theorem mul_mem_range_iff_forall_of_map_ideal {T : Type*} [CommRing T] [Algebra T C]
    [Algebra T E] [IsScalarTower T C E] (I : Ideal T) (J : C)
    (hJ : I.map (algebraMap T C) = Ideal.span {J}) (z : E) :
    z * algebraMap C E J ∈ (algebraMap C E).range ↔
      ∀ a ∈ I, z * algebraMap T E a ∈ (algebraMap C E).range := by
  let N : Ideal C := (LinearMap.range (Algebra.linearMap C E)).comap
    (LinearMap.toSpanSingleton C E z)
  have hn (x : C) : x ∈ N ↔ z * algebraMap C E x ∈ (algebraMap C E).range := by
    change (x • z ∈ LinearMap.range (Algebra.linearMap C E)) ↔ _
    rw [Algebra.smul_def, mul_comm (algebraMap C E x) z]
    rfl
  constructor
  · intro hz a ha
    have hle : I.map (algebraMap T C) ≤ N := by
      rw [hJ, Ideal.span_le, Set.singleton_subset_iff]
      exact (hn J).mpr hz
    have hm := (hn (algebraMap T C a)).mp (hle (Ideal.mem_map_of_mem _ ha))
    rwa [← IsScalarTower.algebraMap_apply T C E] at hm
  · intro h
    have hle : I.map (algebraMap T C) ≤ N := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      apply (hn (algebraMap T C a)).mpr
      rw [← IsScalarTower.algebraMap_apply T C E]
      exact h a ha
    apply (hn J).mp
    exact hle (hJ.symm ▸ Ideal.mem_span_singleton_self J)

end TopCoefficient

section Different

open TensorProduct IsLocalRing

variable {k A T C F E : Type} [CommRing k]
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero (ResidueField A)]
  [CommRing T] [IsDedekindDomain T] [CommRing C] [IsDomain C] [Field F] [Field E]
  [Algebra A F] [Algebra A T] [Algebra A E] [Algebra T E] [Algebra F E]
  [IsScalarTower A F E] [IsScalarTower A T E]
  [IsFractionRing A F] [IsFractionRing T E] [IsIntegralClosure T A E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [Module.Finite A T] [Module.IsTorsionFree A T]
  [Algebra k A] [Algebra k C] [Algebra k E] [Algebra A C] [Algebra T C] [Algebra C E]
  [IsScalarTower k A C] [IsScalarTower A T C] [IsScalarTower k C E]
  [IsScalarTower A C E] [IsScalarTower T C E] [IsFractionRing C E]

include F in
/-- Local regularity of a rational top form with coefficient `z`
is equivalent to local integrality of `z` times the different. -/
theorem coordinateTopForm_regular_iff_different (S : Submonoid T) [IsLocalization S C]
    {d : ℕ} (u : Fin d → A) (a : Module.Basis (Fin d) A Ω[A⁄k]) (ha : ∀ i, a i = D k A (u i))
    (b : Module.Basis (Fin d) C Ω[C⁄k]) (z : E) :
    z • exteriorPower.ιMulti E d (fun i => D k E (algebraMap A E (u i))) ∈
        LinearMap.range (algebraFormPullback k C E d) ↔
      ∀ y ∈ differentIdeal A T, z * algebraMap T E y ∈ (algebraMap C E).range := by
  let J := (LinearMap.toMatrix (a.baseChange C) b (mapBaseChange k A C)).det
  have hJ : (differentIdeal A T).map (algebraMap T C) = Ideal.span {J} :=
    map_differentIdeal_eq_span_kaehler_det (F := F) (E := E) S (a.baseChange C) b
  have hη : algebraFormPullback k C E d (exteriorPower.ιMulti C d b) =
      exteriorPower.ιMulti E d (fun i => KaehlerDifferential.map k k C E (b i)) :=
    exteriorMapOver_ιMulti d _ b
  rw [coordinateWedgeInField_eq_jacobian_smul u a ha b, ← hη, smul_smul]
  exact (topForm_smul_mem_range_iff b (z * algebraMap C E J)).trans
    (mul_mem_range_iff_forall_of_map_ideal _ J hJ z)

end Different

end GlobalTheory.PD
