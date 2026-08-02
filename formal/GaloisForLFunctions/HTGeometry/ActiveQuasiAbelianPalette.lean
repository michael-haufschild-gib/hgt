import GaloisForLFunctions.HTGeometry.QuasiAbelianDampedFactorExtension
import GaloisForLFunctions.HTGeometry.EntireSRRealization

/-!
# Active quasi-Abelian palettes and exact intrinsic dimension

This file gives the action-relative palette an actual Lean type.  Each facet carries its literal
period lattice, quotient group, positive Hermitian-integrality data, compact shadow, faithful
active quotient action, fixed automorphic factor, and finite Abe positive-factor tower.  Thus
all-order jet ampleness is a theorem of the palette data, not an assumed field.

The final dimension theorem isolates only the two already named global geometric operations:
full-HT period extraction and localized Stanley--Reisner/Baire assembly.  The analytic premise of
assembly is discharged internally by fixed-factor all-order jet ampleness.
-/

open Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Integral facet exponent mapped to its complete translation vector. -/
def facetLatticeVector
    {alpha : Type u} [DecidableEq alpha] {d : ℕ}
    (a : alpha → Fin d → ℂ) (F : Finset alpha) :
    (F → ℤ) →+ (Fin d → ℂ) where
  toFun n := ∑ v : F, (n v) • a v.1
  map_zero' := by simp
  map_add' n m := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- One active quasi-Abelian facet in ambient `ℂ^d`. -/
structure ActiveQuasiAbelianFacetPresentation
    (alpha : Type u) [DecidableEq alpha] (F : Finset alpha)
    (d : ℕ) (a : alpha → Fin d → ℂ) where
  Gamma : AddSubgroup (Fin d → ℂ)
  [gammaDiscrete : DiscreteTopology Gamma]
  gammaClosed : IsClosed (Gamma : Set (Fin d → ℂ))
  X : Type u
  [addCommGroupX : AddCommGroup X]
  [topologyX : TopologicalSpace X]
  quotientMap : (Fin d → ℂ) →+ X
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_eq_iff : ∀ x y, quotientMap x = quotientMap y ↔ x - y ∈ Gamma
  quotient_noncompact : ¬ @IsCompact X topologyX Set.univ
  vertex_incidence : ∀ v, a v ∈ Gamma ↔ v ∉ F
  H : (Fin d → ℂ) → (Fin d → ℂ) → ℂ
  H_add_left : ∀ x y z, H (x + y) z = H x z + H y z
  H_smul_left : ∀ c x y, H (c • x) y = c * H x y
  H_hermitian : ∀ x y, H y x = star (H x y)
  H_positive : ∀ x, x ≠ 0 → 0 < (H x x).re
  H_integral_imaginary : ∀ x : Gamma, ∀ y : Gamma,
    ∃ n : ℤ, (H x y).im = n
  compactShadow : AddSubgroup X
  compactShadow_compact : IsCompact (compactShadow : Set X)
  Active : Type u
  [addCommGroupActive : AddCommGroup Active]
  activeQuotient : X →+ Active
  activeQuotient_surjective : Function.Surjective activeQuotient
  activeQuotient_ker : ∀ x, activeQuotient x = 0 ↔ x ∈ compactShadow
  activeFaithful : Function.Injective
    (activeQuotient.comp (quotientMap.comp (facetLatticeVector a F)))
  factor : AutomorphicFactor d Gamma
  positiveTower : AbePositiveFactorTower.{u} d factor

/-- The literal active quotient class of an integral facet exponent. -/
def ActiveQuasiAbelianFacetPresentation.activeClass
    {alpha : Type u} [DecidableEq alpha] {F : Finset alpha}
    {d : ℕ} {a : alpha → Fin d → ℂ}
    (P : ActiveQuasiAbelianFacetPresentation alpha F d a) :
    (F → ℤ) → P.Active :=
  fun n ↦ P.activeQuotient (P.quotientMap (facetLatticeVector a F n))

/-- Active faithfulness is the injectivity of the literal quotient class map. -/
theorem ActiveQuasiAbelianFacetPresentation.activeClass_injective
    {alpha : Type u} [DecidableEq alpha] {F : Finset alpha}
    {d : ℕ} {a : alpha → Fin d → ℂ}
    (P : ActiveQuasiAbelianFacetPresentation alpha F d a) :
    Function.Injective P.activeClass := by
  intro n k hnk
  apply P.activeFaithful
  simpa [ActiveQuasiAbelianFacetPresentation.activeClass, Function.comp_def] using hnk

/-- Every active positive facet factor interpolates arbitrary finite mixed-jet packets. -/
theorem ActiveQuasiAbelianFacetPresentation.jetAmpleEveryFiniteOrder
    {alpha : Type u} [DecidableEq alpha] {F : Finset alpha}
    {d : ℕ} {a : alpha → Fin d → ℂ}
    (P : ActiveQuasiAbelianFacetPresentation alpha F d a) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} P.factor :=
  P.positiveTower.jetAmpleEveryFiniteOrder

/-- Active quasi-Abelian palette for every facet of one finite complex. -/
structure ActiveQuasiAbelianPalette
    (alpha : Type u) [Fintype alpha] [DecidableEq alpha]
    (facets : Finset (Finset alpha)) (d : ℕ) where
  vertex : alpha → Fin d → ℂ
  vertex_independent : LinearIndependent ℚ vertex
  facet : ∀ F : facets,
    ActiveQuasiAbelianFacetPresentation alpha F.1 d vertex

/-- Every facet of an active palette has fixed-factor all-order jet ampleness. -/
theorem ActiveQuasiAbelianPalette.facets_jetAmpleEveryFiniteOrder
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {facets : Finset (Finset alpha)} {d : ℕ}
    (P : ActiveQuasiAbelianPalette alpha facets d) :
    ∀ F : facets,
      AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} (P.facet F).factor :=
  fun F ↦ (P.facet F).jetAmpleEveryFiniteOrder

/-- Active-palette realizability in ambient dimension `d`. -/
def ActiveQuasiAbelianPaletteRealizable
    (alpha : Type u) [Fintype alpha] [DecidableEq alpha]
    (facets : Finset (Finset alpha)) (d : ℕ) : Prop :=
  Nonempty (ActiveQuasiAbelianPalette alpha facets d)

/-- Full hypertranscendental entire realizability in ambient dimension `d`. -/
def FullHTEntireRealizable
    (alpha : Type u) [DecidableEq alpha]
    (facets : Finset (Finset alpha)) (d : ℕ) : Prop :=
  Nonempty (HTEntireSRRealization d facets)

/-- Intrinsic active quasi-Abelian palette dimension. -/
def activeQuasiAbelianPaletteDimension
    (alpha : Type u) [Fintype alpha] [DecidableEq alpha]
    (facets : Finset (Finset alpha)) : ℕ :=
  sInf {d | ActiveQuasiAbelianPaletteRealizable alpha facets d}

/-- Intrinsic full hypertranscendental entire realization dimension. -/
def fullHTEntireDimension
    (alpha : Type u) [DecidableEq alpha]
    (facets : Finset (Finset alpha)) : ℕ :=
  sInf {d | FullHTEntireRealizable alpha facets d}

/-- **Exact active-palette classification.**  Suppose full-HT period extraction returns the
literal active palette above, and the localized Stanley--Reisner/Baire assembly consumes exactly
the all-order facet jet theorem.  Then the two intrinsic dimensions are equal.  Jet ampleness is
discharged internally from each facet's positive Abe tower; it is not an assembly hypothesis. -/
theorem activeQuasiAbelianPaletteDimension_eq_fullHTEntireDimension
    (alpha : Type u) [Fintype alpha] [DecidableEq alpha]
    (facets : Finset (Finset alpha))
    (extract : ∀ d, HTEntireSRRealization d facets →
      ActiveQuasiAbelianPalette alpha facets d)
    (assemble : ∀ d (P : ActiveQuasiAbelianPalette alpha facets d),
      (∀ F : facets,
        AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} (P.facet F).factor) →
      HTEntireSRRealization d facets) :
    activeQuasiAbelianPaletteDimension alpha facets =
      fullHTEntireDimension alpha facets := by
  have hset :
      {d | ActiveQuasiAbelianPaletteRealizable alpha facets d} =
        {d | FullHTEntireRealizable alpha facets d} := by
    ext d
    constructor
    · rintro ⟨P⟩
      exact ⟨assemble d P P.facets_jetAmpleEveryFiniteOrder⟩
    · rintro ⟨R⟩
      exact ⟨extract d R⟩
  rw [activeQuasiAbelianPaletteDimension, fullHTEntireDimension, hset]

/-- Exact six-term dimension hierarchy from the five construction/forgetful reductions and the
active/full equivalence.  This lemma records every inequality direction without attainment or
minimum hypotheses by comparing the actual realizability sets. -/
theorem exact_dimension_hierarchy_of_realizability_reductions
    (PE QA AQA HT PP FFS : ℕ → Prop)
    (hpeqa : ∀ d, QA d → PE d)
    (hqaaqa : ∀ d, AQA d → QA d)
    (haqaht : ∀ d, AQA d ↔ HT d)
    (hhtpp : ∀ d, PP d → HT d)
    (hppffs : ∀ d, FFS d → PP d)
    (hQA : Set.Nonempty {d | QA d})
    (hAQA : Set.Nonempty {d | AQA d})
    (hPP : Set.Nonempty {d | PP d}) (hFFS : Set.Nonempty {d | FFS d}) :
    sInf {d | PE d} ≤ sInf {d | QA d} ∧
    sInf {d | QA d} ≤ sInf {d | AQA d} ∧
    sInf {d | AQA d} = sInf {d | HT d} ∧
    sInf {d | HT d} ≤ sInf {d | PP d} ∧
    sInf {d | PP d} ≤ sInf {d | FFS d} := by
  have hmono (P Q : ℕ → Prop) (hQ : Set.Nonempty {d | Q d})
      (hQP : ∀ d, Q d → P d) : sInf {d | P d} ≤ sInf {d | Q d} := by
    have hdQ : Q (sInf {d | Q d}) := Nat.sInf_mem hQ
    exact Nat.sInf_le (hQP _ hdQ)
  refine ⟨hmono PE QA hQA hpeqa, hmono QA AQA hAQA hqaaqa, ?_,
    hmono HT PP hPP hhtpp, hmono PP FFS hFFS hppffs⟩
  congr 1
  ext d
  exact haqaht d

end

end GaloisForLFunctions.HTGeometry
