import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.TensorProduct.Finite

/-! Exactness on a field fibre gives exactness of the localized complex at
its kernel when the middle modules are finite and the last one is projective. -/

open Function TensorProduct

namespace GlobalTheory

variable {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

private theorem exact_lTensor_of_field_atPrime (p : Ideal R) [p.IsPrime]
    (K : Type) [Field K] [Algebra R K] (hK : RingHom.ker (algebraMap R K) = p)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : Exact (f.lTensor K) (g.lTensor K)) :
    Exact (f.lTensor p.ResidueField) (g.lTensor p.ResidueField) := by
  let k := p.ResidueField
  let e : k →ₐ[R] K := Ideal.ResidueField.liftₐ p (Algebra.ofId R K) hK.ge (by
    intro r hr
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    exact fun hz => hr (hK ▸ hz))
  letI : Algebra k K := e.toRingHom.toAlgebra
  letI : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  have he : Exact (AlgebraTensorModule.lTensor k K f) (AlgebraTensorModule.lTensor k K g) ↔
      Exact ((f.baseChange k).lTensor K) ((g.baseChange k).lTensor K) :=
    Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R k k K A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R k k K B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R k k K C) (by ext; simp) (by ext; simp)
  exact (Module.FaithfullyFlat.lTensor_exact_iff_exact k K (f.baseChange k) (g.baseChange k)).mp (he.mp h)

private theorem exact_of_residue_exact [IsLocalRing R]
    [Module.Finite R B] [Module.Finite R C] [Module.Free R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : Exact (f.lTensor (IsLocalRing.ResidueField R)) (g.lTensor (IsLocalRing.ResidueField R))) :
    Exact f g := by
  let k := IsLocalRing.ResidueField R
  let I := LinearMap.range f
  let l := I.liftQ g (LinearMap.range_le_ker_iff.mpr hfg)
  have hq : l ∘ₗ I.mkQ = g := Submodule.liftQ_mkQ _ _ _
  have hinj : Injective (l.lTensor k) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective k I.mkQ_surjective x
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hq] at hx
    obtain ⟨z, rfl⟩ := (h y).mp hx
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      f.exact_map_mkQ_range.linearMap_comp_eq_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨s, hs⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective l).mpr hinj
  have hl : Injective l := HasLeftInverse.injective ⟨s, LinearMap.congr_fun hs⟩
  intro b
  constructor
  · intro hb
    have hh : l (I.mkQ b) = l 0 := (LinearMap.congr_fun hq b).trans (hb.trans (map_zero l).symm)
    exact (Submodule.Quotient.mk_eq_zero _).mp (hl hh)
  · rintro ⟨a, rfl⟩
    exact LinearMap.congr_fun hfg a

/-- A cycle is a boundary after multiplication by a scalar nonvanishing at
the point where the field fibre is exact. -/
theorem exists_smul_mem_range_of_exact_fibre [Module.Finite R B] [Module.Finite R C]
    [Module.Projective R C] (K : Type) [Field K] [Algebra R K]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : Exact (f.lTensor K) (g.lTensor K)) (b : B) (hb : g b = 0) :
    ∃ r : R, algebraMap R K r ≠ 0 ∧ r • b ∈ LinearMap.range f := by
  let p := RingHom.ker (algebraMap R K)
  letI : p.IsPrime := RingHom.ker_isPrime _
  let O := Localization.AtPrime p
  let k := p.ResidueField
  have h₁ := exact_lTensor_of_field_atPrime p K rfl f g h
  have hc : Exact (AlgebraTensorModule.lTensor O k f) (AlgebraTensorModule.lTensor O k g) ↔
      Exact ((f.baseChange O).lTensor k) ((g.baseChange O).lTensor k) :=
    Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R O O k A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R O O k B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R O O k C) (by ext; simp) (by ext; simp)
  have hfg' : g.baseChange O ∘ₗ f.baseChange O = 0 := by
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_zero]
  letI : Module.Free O (O ⊗[R] C) := Module.free_of_flat_of_isLocalRing
  have hO := exact_of_residue_exact hfg' (hc.mp h₁)
  obtain ⟨x, hx⟩ := (hO ((1 : O) ⊗ₜ[R] b)).mp (by simp [hb])
  obtain ⟨⟨a, u⟩, hu⟩ := IsLocalizedModule.surj p.primeCompl (TensorProduct.mk R O A 1) x
  have he : TensorProduct.mk R O B 1 ((u : R) • b) = TensorProduct.mk R O B 1 (f a) := by
    have z := congrArg (f.lTensor O) hu
    rw [Submonoid.smul_def, map_smul] at z
    have hx' : f.lTensor O x = (1 : O) ⊗ₜ[R] b := hx
    rw [hx'] at z
    simpa using z
  obtain ⟨v, hv⟩ := IsLocalizedModule.exists_of_eq (S := p.primeCompl) he
  refine ⟨(v * u : p.primeCompl), (v * u).2, (v : R) • a, ?_⟩
  rw [map_smul, Submonoid.coe_mul, mul_smul]
  exact hv.symm

end GlobalTheory
