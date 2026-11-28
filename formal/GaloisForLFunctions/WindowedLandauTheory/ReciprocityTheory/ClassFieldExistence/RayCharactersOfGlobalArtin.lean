import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.CyclicRayArtinExistence
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.GlobalIdelicArtinQuotient
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Cyclic characters of finite idelic quotients factor through global
Artin reciprocity. They separate the points of each finite quotient. -/

noncomputable section

open NumberField IntermediateField GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

local notation "GΩ" => (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω)
local notation "C" => CompactIdeleClassQuotient K

private theorem finite_artin_eq_one_of_global_eq_one
    {E : Type} [Field E] [Algebra K E] [FiniteDimensional K E] [IsAbelianGalois K E]
    (a : C →* GΩ) (ha : MatchesFiniteIdelicArtin K Ω a)
    (f : IdeleGroup K →* Gal(E/K)) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ u : Kˣ, f (diagonal K u) = 1)
    {x : IdeleGroup K} (hx : a (toCompactIdeleClassQuotient K x) = 1) : f x = 1 := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let j : E →ₐ[K] Ω := IsAlgClosed.lift
  let L := j.fieldRange
  let e : E ≃ₐ[K] L := AlgEquiv.ofInjectiveField j
  letI : FiniteDimensional K L := FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  letI : IsAbelianGalois K L := IsAbelianGalois.of_algHom e.symm.toAlgHom
  letI : NumberField E := NumberField.of_module_finite K E
  letI : NumberField L := NumberField.of_module_finite K L
  letI : Algebra E L := e.toAlgHom.toRingHom.toAlgebra
  letI : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  letI : CommGroup Gal(E/K) :=
    { (inferInstance : Group Gal(E/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  letI : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  letI : Fintype Gal(E/K) := Fintype.ofFinite _
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  let V : finiteAbelianExtensions K Ω := ⟨L, inferInstance, inferInstance⟩
  let r := restrictAb L (le_maximalAbelianExtension L)
  let g := r.comp (a.comp (toCompactIdeleClassQuotient K))
  obtain ⟨m, hm, hp⟩ := hf
  obtain ⟨q, hq, hqg⟩ := ha V
  have he := finite_idelic_artin_restrict K E L Gal(E/K) Gal(L/K) m q f g hd
    (fun b => by simp only [g, MonoidHom.comp_apply, toCompactIdeleClassQuotient_diagonal, map_one])
    (fun v hv => not_not.mp fun hu => hv ((hm v).mpr hu))
    (fun v hv => not_not.mp fun hu => hv ((hq v).mpr hu)) hp hqg
  have h := DFunLike.congr_fun he x
  change IsGaloisGroup.restrictHom Gal(L/K) Gal(E/K) K E L
    (r (a (toCompactIdeleClassQuotient K x))) = f x at h
  rw [hx, map_one, map_one] at h
  exact h.symm

private theorem ray_character_eq_one_of_global_eq_one
    {A : Type*} [CommGroup A] {c : ℕ} [NeZero c]
    (a : C →* GΩ) (ha : MatchesFiniteIdelicArtin K Ω a)
    {χ : RayClassGroup (normModulus K c) →* A} (hχ : HasRayArtinFactor χ)
    {z : C} (hz : a z = 1) : χ (compactToRayClass (normModulus K c) z) = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
  obtain ⟨L, _, _, _, _, f, g, -, -, hf, hi, hgf⟩ := hχ
  have hd (u : Kˣ) : f (diagonal K u) = 1 := by
    apply hi
    have h := DFunLike.congr_fun hgf (diagonal K u)
    change g (f (diagonal K u)) = χ (toRayClass (normModulus K c) (diagonal K u)) at h
    rwa [toRayClass_diagonal, map_one, ← map_one g] at h
  have h := DFunLike.congr_fun hgf x
  change g (f x) = χ (toRayClass (normModulus K c) x) at h
  rw [finite_artin_eq_one_of_global_eq_one a ha f hf hd hz, map_one] at h
  exact h.symm

theorem globalArtin_ker_le_open
    (a : C →* GΩ) (ha : MatchesFiniteIdelicArtin K Ω a)
    (N : Subgroup C) (hN : IsOpen (N : Set C)) : a.ker ≤ N := by
  intro x hx
  obtain ⟨c, hc, h⟩ := exists_rationalRay_ker_le_open N hN
  letI := hc
  let m := normModulus K c
  let r := compactToRayClass m
  have hker : r.ker ≤ N := by
    intro y hy
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact h hy
  let P := N.map r
  letI : NeZero (Monoid.exponent (RayClassGroup m)) :=
    ⟨Monoid.exponent_ne_zero_of_finite (G := RayClassGroup m)⟩
  have hP : r x ∈ P := by
    apply (CommGroup.forall_monoidHom_apply_eq_one_iff (M := ℂ) P (r x)).mp
    intro χ _
    let n := Nat.card (RayClassGroup m)
    letI : NeZero n := ⟨Nat.card_pos.ne'⟩
    let A := rootsOfUnity n ℂ
    letI : IsCyclic A := rootsOfUnity.isCyclic ℂ n
    let ψ : RayClassGroup m →* A := χ.codRestrict _ fun q => by
      rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]
    have hexp (y : RayClassGroup m) : ψ y ^ n = 1 :=
      Subtype.ext (ψ y).prop
    have he := ray_character_eq_one_of_global_eq_one a ha
      (hasRayArtinFactor_of_exponent n (NeZero.pos n) ψ hexp) hx
    exact congrArg Subtype.val he
  obtain ⟨y, hy, he⟩ := hP
  have hz : y⁻¹ * x ∈ r.ker :=
    MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, he, inv_mul_cancel])
  simpa only [mul_inv_cancel_left] using N.mul_mem hy (hker hz)

end GlobalTheory.Reciprocity
