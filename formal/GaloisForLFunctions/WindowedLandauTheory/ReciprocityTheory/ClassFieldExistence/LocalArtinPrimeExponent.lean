import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.OpenIdelicClassFieldRefinement
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinSurjectivityFromPowerKernel
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteDecompositionRestriction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicArtinTowerRestriction

/-! Over a base with the p-th roots of unity, finite Artin reciprocity
surjects onto decomposition at every finite place of an abelian
extension of exponent p. Refine its Artin quotient to detect every
local power class and descend through restriction. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField Topology GaloisForLFunctions
open scoped IsMulCommutative Pointwise

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K E₀ : Type} [Field K] [NumberField K] [Field E₀] [NumberField E₀]
  [Algebra K E₀] [IsAbelianGalois K E₀]

theorem finiteIdelicArtin_range_eq_decomposition_of_prime_exponent
    {p : ℕ} [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity K p]
    (g : IdeleGroup K →* Gal(E₀/K)) (hg : IsFiniteIdelicArtin g)
    (hgd : ∀ a : Kˣ, g (diagonal K a) = 1)
    (hpow : ∀ σ : Gal(E₀/K), σ ^ p = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E₀)) [w.asIdeal.LiesOver v.asIdeal] :
    (g.comp (finiteEmbedding v)).range = MulAction.stabilizer Gal(E₀/K) w.asIdeal := by
  let Ω := AlgebraicClosure K
  let j₀ : E₀ →ₐ[K] Ω := IsAlgClosed.lift
  let F := j₀.fieldRange
  let e := j₀.equivFieldRange
  letI : FiniteDimensional K F := FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  letI : IsAbelianGalois K F := IsAbelianGalois.of_algHom e.symm.toAlgHom
  let V₀ : finiteAbelianExtensions K Ω := ⟨F, inferInstance, inferInstance⟩
  obtain ⟨a, ha, hA, -⟩ := exists_global_idelic_artin K Ω
  let r := (restrictAb F (le_maximalAbelianExtension F)).comp a
  letI : DiscreteTopology Gal(F/K) := krullTopology_discreteTopology_of_finiteDimensional K F
  have hr : Continuous r := (continuous_restrictAb F (le_maximalAbelianExtension F)).comp ha
  have hR : IsOpen (r.ker : Set (CompactIdeleClassQuotient K)) :=
    (isOpen_discrete ({1} : Set Gal(F/K))).preimage hr
  have hpr : compactIdelePowers K p ≤ r.ker := by
    rintro _ ⟨x, rfl⟩
    change r (x ^ p) = 1
    rw [map_pow]
    obtain ⟨σ, hσ⟩ := e.autCongr.surjective (r x)
    rw [← hσ, ← map_pow, hpow, map_one]
  obtain ⟨N, hN, hNp, hNR, hNker⟩ :=
    exists_open_power_subgroup_with_local_comap (n := p) v r.ker hR hpr
  obtain ⟨V, E, hE, ⟨j⟩, f, -, hs, hfk, hf⟩ :=
    exists_finite_idelic_artin_of_open_refining K Ω V₀ a ha hA N hN
      (fun c hc => hNR hc)
  letI : FiniteDimensional K (V : IntermediateField K Ω) := V.2.1
  letI := hE
  letI : NumberField E := NumberField.of_module_finite K E
  have hd (x : Kˣ) : f (diagonal K x) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hfk]
    change toCompactIdeleClassQuotient K (diagonal K x) ∈ N
    rw [toCompactIdeleClassQuotient_diagonal]
    exact one_mem _
  have hp (σ : Gal(E/K)) : σ ^ p = 1 := by
    obtain ⟨y, rfl⟩ := hs σ
    rw [← map_pow]
    apply MonoidHom.mem_ker.mp
    rw [hfk]
    change toCompactIdeleClassQuotient K (y ^ p) ∈ N
    rw [map_pow]
    exact hNp ⟨toCompactIdeleClassQuotient K y, rfl⟩
  have hlocal : (f.comp (finiteEmbedding v)).ker =
      (powMonoidHom p : (v.adicCompletion K)ˣ →* _).range := by
    rw [← MonoidHom.comap_ker, hfk, Subgroup.comap_comap]
    exact hNker
  let j₁ := j.comp e.toAlgHom
  letI : Algebra E₀ E := j₁.toRingHom.toAlgebra
  letI : IsScalarTower K E₀ E := IsScalarTower.of_algebraMap_eq' j₁.comp_algebraMap.symm
  let W := primeAboveSpec (K := E₀) (L := E) w
  letI : W.asIdeal.LiesOver w.asIdeal := primeAbove_liesOver E₀ E w
  letI : W.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans W.asIdeal w.asIdeal v.asIdeal
  have hD := finiteIdelicArtin_range_eq_decomposition_of_power_kernel f hf hd hp v W hlocal
  let s : Gal(E/K) →* Gal(E₀/K) := AlgEquiv.restrictNormalHom E₀
  have he : s.comp f = g := finiteIdelicArtin_restrict_eq K E₀ E f g hf hg hd hgd
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact finiteIdelicArtin_finiteEmbedding_mem_decomposition g hg hgd v w x
  intro τ hτ
  have hτ' : τ ∈ (MulAction.stabilizer Gal(E/K) W.asIdeal).map s := by
    rw [map_stabilizer_restrictNormalHom K E₀ E, under_primeAboveSpec]
    exact hτ
  obtain ⟨σ, hσ, hστ⟩ := hτ'
  obtain ⟨x, hx⟩ : σ ∈ (f.comp (finiteEmbedding v)).range := hD.symm ▸ hσ
  refine ⟨x, ?_⟩
  change g (finiteEmbedding v x) = τ
  rw [← he]
  change s ((f.comp (finiteEmbedding v)) x) = τ
  rw [hx]
  exact hστ

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_range_eq_decomposition_of_prime_exponent
