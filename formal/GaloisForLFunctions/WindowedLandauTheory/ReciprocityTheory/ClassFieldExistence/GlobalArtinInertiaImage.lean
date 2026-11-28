import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FinitePlaceOfAbsoluteValuation
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinDecompositionSurjectivity
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.GlobalIdelicArtinQuotient
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilGroupAtFinitePlace

/-! The absolute inertia image in the maximal abelian Galois group is
the Artin image of the integral units of the local completion. Compact
fibres pass from finite abelian stages to the full group. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField Topology
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

local notation "C" => CompactIdeleClassQuotient K
local notation "M" => maximalAbelianExtension K Ω
local notation "VFA" => finiteAbelianExtensions K Ω
local notation "G" => Gal(M/K)

/-- Restriction of an absolute automorphism to the maximal abelian extension. -/
def toMaxAb : Gal(Ω/K) →* G := AlgEquiv.restrictNormalHom M

theorem continuous_toMaxAb : Continuous (toMaxAb K Ω) :=
  InfiniteGalois.restrictNormalHom_continuous M

theorem restrictAbPi_toMaxAb (V : VFA) (s : Gal(Ω/K)) :
    letI := V.2.2
    restrictAbPi K Ω (toMaxAb K Ω s) V =
      AlgEquiv.restrictNormalHom (V : IntermediateField K Ω) s := by
  let L := (V : IntermediateField K Ω)
  letI := V.2.2
  exact restrictAb_topologicalAbelianizationEquiv L (le_maximalAbelianExtension L) s

/-- Evaluate the global Artin map on ideles and restrict to a finite stage. -/
def finiteStageArtin (a : C →* G) (V : VFA) : IdeleGroup K →* Gal((V : IntermediateField K Ω)/K) :=
  letI := V.2.2
  (restrictAb (V : IntermediateField K Ω) (le_maximalAbelianExtension _)).comp
    (a.comp (toCompactIdeleClassQuotient K))

theorem finiteStageArtin_isFiniteIdelicArtin (a : C →* G) (ha : MatchesFiniteIdelicArtin K Ω a)
    (V : VFA) :
    letI := V.2.1
    letI := V.2.2
    IsFiniteIdelicArtin (finiteStageArtin K Ω a V) := ha V

theorem finiteStageArtin_diagonal (a : C →* G) (V : VFA) (x : Kˣ) :
    finiteStageArtin K Ω a V (diagonal K x) = 1 := by
  simp only [finiteStageArtin, MonoidHom.comp_apply, toCompactIdeleClassQuotient_diagonal, map_one]

variable {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

theorem isCompact_unitsLevel_zero (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (unitsLevel (K := K) v 0 : Set (v.adicCompletion K)ˣ) := by
  rw [unitsLevel_zero]
  exact isCompact_localIntegralUnits v

theorem exists_localUnit_of_all_restrictions_mem_inertia
    (a : C →* G) (hc : Continuous a) (ha : MatchesFiniteIdelicArtin K Ω a)
    (hv : IsPlaceOver A v) (g : G)
    (hg : ∀ V : VFA,
      let L := (V : IntermediateField K Ω)
      letI := V.2.1
      letI := V.2.2
      letI : NumberField L := NumberField.of_module_finite K L
      restrictAbPi K Ω g V ∈ (finitePlaceAtAbsoluteValuation (L := L) A hv).asIdeal.inertia Gal(L/K)) :
    ∃ x ∈ unitsLevel (K := K) v 0, a (toCompactIdeleClassQuotient K (finiteEmbedding v x)) = g := by
  let U := unitsLevel (K := K) v 0
  let h : U → G := fun x => a (toCompactIdeleClassQuotient K (finiteEmbedding v x.val))
  letI : CompactSpace U := isCompact_iff_compactSpace.mp (isCompact_unitsLevel_zero K v)
  have hh : Continuous h := hc.comp
    (QuotientGroup.continuous_mk.comp ((continuous_finiteEmbedding v).comp continuous_subtype_val))
  obtain ⟨x, hx⟩ := exists_eq_of_compact_finite_restrictions K Ω h hh g (fun V => by
    let L := (V : IntermediateField K Ω)
    letI := V.2.1
    letI := V.2.2
    letI : NumberField L := NumberField.of_module_finite K L
    let w := finitePlaceAtAbsoluteValuation (L := L) A hv
    letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A hv
    let f := finiteStageArtin K Ω a V
    have he := finiteIdelicArtin_range_localUnits_eq_inertia f
      (finiteStageArtin_isFiniteIdelicArtin K Ω a ha V) (finiteStageArtin_diagonal K Ω a V) v w
    have hmem : restrictAbPi K Ω g V ∈ w.asIdeal.inertia Gal(L/K) := hg V
    rw [← he] at hmem
    obtain ⟨y, hy, hval⟩ := hmem
    exact ⟨⟨y, hy⟩, hval⟩)
  exact ⟨x.val, x.2, hx⟩

theorem exists_Ine_of_localUnit_artin
    (a : C →* G) (ha : MatchesFiniteIdelicArtin K Ω a)
    (hv : IsPlaceOver A v) (x : (v.adicCompletion K)ˣ) (hx : x ∈ unitsLevel (K := K) v 0) :
    ∃ σ : Ine (F := K) A, toMaxAb K Ω σ.val =
      a (toCompactIdeleClassQuotient K (finiteEmbedding v x)) := by
  let g := a (toCompactIdeleClassQuotient K (finiteEmbedding v x))
  let f : Ine (F := K) A → G := fun σ => toMaxAb K Ω σ.val
  letI : CompactSpace (Ine (F := K) A) := GlobalTheory.WeilDeligne.compactSpace_Ine A
  apply exists_eq_of_compact_finite_restrictions K Ω f
    ((continuous_toMaxAb K Ω).comp continuous_subtype_val) g
  intro V
  let L := (V : IntermediateField K Ω)
  letI := V.2.1
  letI := V.2.2
  letI : NumberField L := NumberField.of_module_finite K L
  let w := finitePlaceAtAbsoluteValuation (L := L) A hv
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A hv
  have hi : restrictAbPi K Ω g V ∈ w.asIdeal.inertia Gal(L/K) :=
    finiteIdelicArtin_finiteEmbedding_mem_inertia (finiteStageArtin K Ω a V)
      (finiteStageArtin_isFiniteIdelicArtin K Ω a ha V) (finiteStageArtin_diagonal K Ω a V) v w x hx
  obtain ⟨σ, hσ⟩ := exists_Ine_restrictNormalHom_eq A hv _ hi
  refine ⟨σ, ?_⟩
  change restrictAbPi K Ω (toMaxAb K Ω σ.val) V = _
  rw [restrictAbPi_toMaxAb K Ω]
  exact hσ

theorem exists_localUnit_of_Ine_artin
    (a : C →* G) (hc : Continuous a) (ha : MatchesFiniteIdelicArtin K Ω a)
    (hv : IsPlaceOver A v) (σ : Ine (F := K) A) :
    ∃ x ∈ unitsLevel (K := K) v 0, a (toCompactIdeleClassQuotient K (finiteEmbedding v x)) =
      toMaxAb K Ω σ.val := by
  refine exists_localUnit_of_all_restrictions_mem_inertia K Ω a hc ha hv (toMaxAb K Ω σ.val) ?_
  intro V
  let L := (V : IntermediateField K Ω)
  letI := V.2.1
  letI := V.2.2
  letI : NumberField L := NumberField.of_module_finite K L
  change restrictAbPi K Ω (toMaxAb K Ω σ.val) V ∈
    (finitePlaceAtAbsoluteValuation (L := L) A hv).asIdeal.inertia Gal(L/K)
  rw [restrictAbPi_toMaxAb K Ω]
  exact restrictNormalHom_mem_inertia_of_mem_Ine A hv σ.2

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_Ine_of_localUnit_artin
#print axioms GlobalTheory.Reciprocity.exists_localUnit_of_Ine_artin
