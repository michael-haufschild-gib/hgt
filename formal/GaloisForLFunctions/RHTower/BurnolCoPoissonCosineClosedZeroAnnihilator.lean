import GaloisForLFunctions.RHTower.BurnolCoPoissonReciprocalSeedLanding
import GaloisForLFunctions.RHTower.BurnolCoPoissonRawZeroAnnihilator

/-!
# Cosine-closed co-Poisson zero annihilation

The co-Poisson source construction is already closed under the cosine transform
at the level of literal sources: the cosine image of a source is the source
attached to its reciprocal seed.  Hence adjoining cosine images does not
enlarge the closed source space.  This upgrades the raw-source zero
annihilation to Burnol's actual cosine-closed co-Poisson source space.

This is only the source-annihilation component of Burnol's completeness system.
It does not assert aperture completeness, minimality, or a higher zero-jet
statement.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Every generator of the cosine-closed source space is already a literal
raw co-Poisson source: the second branch is the reciprocal-seed source. -/
theorem burnolCoPoissonGeneratorSet_subset_rawSourceSet
    {b : ℝ} (hb : 0 < b) :
    burnolCoPoissonGeneratorSet b ⊆ burnolCoPoissonRawSourceSet b := by
  rintro f ⟨src, rfl | rfl⟩
  · exact ⟨src, rfl⟩
  · refine ⟨src.reciprocal hb, ?_⟩
    simp only [BurnolCoPoissonSource.reciprocal_vector,
      coe_burnolExtendedSoninCosine] 

/-- Conversely, every raw source is a first-branch generator. -/
theorem burnolCoPoissonRawSourceSet_subset_generatorSet {b : ℝ} :
    burnolCoPoissonRawSourceSet b ⊆ burnolCoPoissonGeneratorSet b := by
  rintro f ⟨src, rfl⟩
  exact ⟨src, Or.inl rfl⟩

/-- The algebraic co-Poisson span is unchanged by adjoining cosine images. -/
theorem burnolCoPoissonAlgebraicSourceSpace_eq_raw
    {b : ℝ} (hb : 0 < b) :
    burnolCoPoissonAlgebraicSourceSpace b = burnolCoPoissonRawAlgebraicSourceSpace b := by
  apply le_antisymm
  · rw [burnolCoPoissonAlgebraicSourceSpace, burnolCoPoissonRawAlgebraicSourceSpace]
    exact Submodule.span_mono (burnolCoPoissonGeneratorSet_subset_rawSourceSet hb)
  · rw [burnolCoPoissonAlgebraicSourceSpace, burnolCoPoissonRawAlgebraicSourceSpace]
    exact Submodule.span_mono burnolCoPoissonRawSourceSet_subset_generatorSet

/-- The literal cosine-closed source space and raw source closure coincide. -/
theorem burnolCoPoissonSourceSpace_eq_rawSourceSpace
    {b : ℝ} (hb : 0 < b) :
    burnolCoPoissonSourceSpace b = burnolCoPoissonRawSourceSpace b := by
  rw [burnolCoPoissonSourceSpace, burnolCoPoissonRawSourceSpace,
    burnolCoPoissonAlgebraicSourceSpace_eq_raw hb]

/-- At a right-half-strip zeta zero, the completed Mellin Riesz evaluator
annihilates Burnol's full cosine-closed source space. -/
theorem burnolExtendedSoninEvaluationVector_mem_coPoissonSource_orthogonal
    {b : ℝ} {w : ℂ} (hb : 0 < b) (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (hz : riemannZeta w = 0) :
    (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) ∈
      (burnolCoPoissonSourceSpace b)ᗮ := by
  rw [burnolCoPoissonSourceSpace_eq_rawSourceSpace hb]
  exact burnolExtendedSoninEvaluationVector_mem_rawSource_orthogonal hb hlo hhi hz

end RHTower
