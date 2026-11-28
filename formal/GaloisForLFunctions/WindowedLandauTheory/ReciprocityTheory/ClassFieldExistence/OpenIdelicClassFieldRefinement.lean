import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.OpenIdelicClassField

/-! A class field for an open subgroup contains every finite abelian
subextension whose Artin kernel contains that subgroup. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField Topology
open GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

local notation "A" => finiteAbelianExtensions K Ω
local notation "M" => maximalAbelianExtension K Ω
local notation "C" => CompactIdeleClassQuotient K

private theorem restrictAbPi_apply_of_le {V W : A} (h : (V : IntermediateField K Ω) ≤ W)
    (σ : Gal(M/K)) (x : (V : IntermediateField K Ω)) :
    ((restrictAbPi K Ω σ W ⟨x.val, h x.2⟩ : (W : IntermediateField K Ω)) : Ω) =
      (restrictAbPi K Ω σ V x : Ω) := by
  letI := V.2.2
  letI := W.2.2
  simp only [restrictAbPi, restrictAb_apply]

theorem exists_finite_idelic_artin_of_open_refining
    (V₀ : A) (a : C →* Gal(M/K)) (ha : Continuous a) (hm : MatchesFiniteIdelicArtin K Ω a)
    (N : Subgroup C) (hN : IsOpen (N : Set C))
    (h₀ : ∀ c ∈ N, restrictAbPi K Ω (a c) V₀ = AlgEquiv.refl) :
    ∃ V : A,
      let L := (V : IntermediateField K Ω)
      letI := V.2.1
      ∃ (E : IntermediateField K L) (hE : IsAbelianGalois K E),
        letI := hE
        Nonempty ((V₀ : IntermediateField K Ω) →ₐ[K] E) ∧
        ∃ f : IdeleGroup K →* Gal(E/K), Continuous f ∧ Function.Surjective f ∧
          f.ker = N.comap (toCompactIdeleClassQuotient K) ∧ IsFiniteIdelicArtin f := by
  obtain ⟨V₁, hV₁⟩ := exists_finite_restriction_kernel_le K Ω a ha N hN
    (globalArtin_ker_le_open a hm N hN)
  let L₀ := (V₀ : IntermediateField K Ω)
  let L₁ := (V₁ : IntermediateField K Ω)
  letI := V₀.2.1
  letI := V₀.2.2
  letI := V₁.2.1
  letI := V₁.2.2
  let L := L₀ ⊔ L₁
  have hL : L ≤ M := sup_le (le_maximalAbelianExtension L₀) (le_maximalAbelianExtension L₁)
  letI : IsAbelianGalois K L := isAbelianGalois_of_le_maximalAbelianExtension L hL
  letI : NumberField L := NumberField.of_module_finite K L
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  let V : A := ⟨L, inferInstance, inferInstance⟩
  let q := toCompactIdeleClassQuotient K
  let φ := (restrictAb L (le_maximalAbelianExtension L)).comp (a.comp q)
  let N' := N.comap q
  have hk : φ.ker ≤ N' := by
    intro y hy
    apply hV₁
    have he : restrictAbPi K Ω (a (q y)) V = 1 := hy
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    have h := restrictAbPi_apply_of_le K Ω (V := V₁) (W := V) le_sup_right (a (q y)) x
    rw [he] at h
    exact h.symm
  obtain ⟨m, hr, hp⟩ := hm V
  have hd (x : Kˣ) : φ (diagonal K x) = 1 := by
    simp only [φ, q, MonoidHom.comp_apply, toCompactIdeleClassQuotient_diagonal, map_one]
  let H := N'.map φ
  let E := fixedField H
  letI : IsAbelianGalois K E := IsAbelianGalois.of_algHom E.val
  obtain ⟨f, hc, hs, hfκ, hf⟩ := finite_idelic_artin_fixedField_of_kernel_le m φ hd
    (fun v hv => not_not.mp fun h => hv ((hr v).mpr h)) hp N' hk
  let j := IntermediateField.inclusion (show L₀ ≤ L from le_sup_left)
  have hj (x : L₀) : j x ∈ E := by
    intro σ
    obtain ⟨y, hy, he⟩ := σ.2
    have hres := h₀ (q y) hy
    apply Subtype.ext
    change (σ.val (j x) : Ω) = x.val
    rw [← he]
    have h := restrictAbPi_apply_of_le K Ω (V := V₀) (W := V) le_sup_left (a (q y)) x
    rw [hres] at h
    exact h
  exact ⟨V, E, inferInstance, ⟨j.codRestrict E.toSubalgebra hj⟩, f, hc, hs, hfκ, hf⟩

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_finite_idelic_artin_of_open_refining
