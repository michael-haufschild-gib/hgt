import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaMovableDeficiencyTotality
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilReducingFiniteBlock
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompressionRHCriterion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFirstContactBoundaryRoughness

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform

noncomputable section
namespace RHTower

local instance ccmReducingExceptionalFiniteDimensional
    (a : SuzukiPositiveAperture)
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    FiniteDimensional ℂ C.exterior.orthogonal :=
  C.exceptional_finiteDimensional

local instance ccmReducingExceptionalCompleteSpace
    (a : SuzukiPositiveAperture)
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    CompleteSpace C.exterior.orthogonal :=
  (Submodule.isClosed_orthogonal C.exterior).completeSpace_coe

local instance ccmReducingExceptionalHasOrthogonalProjection
    (a : SuzukiPositiveAperture)
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    C.exterior.orthogonal.HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace C.exterior.orthogonal

local instance ccmReducingExteriorCompleteSpace
    (a : SuzukiPositiveAperture)
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    CompleteSpace C.exterior :=
  C.exterior_isClosed.completeSpace_coe

local instance ccmReducingExteriorHasOrthogonalProjection
    (a : SuzukiPositiveAperture)
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    C.exterior.HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace C.exterior

/-- Exceptional projection before imposing the two pole constraints. -/
def suzukiTaFullReducingExceptionalProjection
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    SuzukiTaHilbert a →L[ℂ] C.exterior.orthogonal :=
  C.exterior.orthogonal.orthogonalProjectionOnto.comp (suzukiTaToFormCLM a)

theorem suzukiTaFullReducingExceptionalProjection_surjective
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    Function.Surjective (suzukiTaFullReducingExceptionalProjection C) := by
  intro y
  refine ⟨suzukiTaFromFormCLM a (y : CCMArchimedeanFormDomain a), ?_⟩
  apply Subtype.ext
  simp [suzukiTaFullReducingExceptionalProjection]

/-- Exceptional coordinate of one actual raw movable completed-covariance response. -/
def suzukiTaMovableFullReducingExceptionalVector
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) (c : ℝ) :
    C.exterior.orthogonal :=
  suzukiTaFullReducingExceptionalProjection C (suzukiTaRawDeficiency a c)

def suzukiTaMovableFullReducingExceptionalSpan
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    Submodule ℂ C.exterior.orthogonal :=
  Submodule.span ℂ (Set.range (suzukiTaMovableFullReducingExceptionalVector C))

theorem suzukiTaMovableFullReducingExceptionalSpan_eq_map
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    suzukiTaMovableFullReducingExceptionalSpan C =
      (suzukiTaRawDeficiencySpan a).map
        (suzukiTaFullReducingExceptionalProjection C).toLinearMap := by
  rw [suzukiTaMovableFullReducingExceptionalSpan,
    suzukiTaRawDeficiencySpan, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨suzukiTaRawDeficiency a c, ⟨c, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩

theorem suzukiTaMovableFullReducingExceptionalSpan_closure_eq_top
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    (suzukiTaMovableFullReducingExceptionalSpan C).topologicalClosure = ⊤ := by
  rw [suzukiTaMovableFullReducingExceptionalSpan_eq_map]
  exact DenseRange.topologicalClosure_map_submodule
    (suzukiTaFullReducingExceptionalProjection_surjective C).denseRange
    (suzukiTaRawDeficiencySpan_closure_eq_top a)

/-- Finite dimensionality upgrades full movable-source density to exact algebraic spanning. -/
theorem suzukiTaMovableFullReducingExceptionalSpan_eq_top
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    suzukiTaMovableFullReducingExceptionalSpan C = ⊤ := by
  have h := suzukiTaMovableFullReducingExceptionalSpan_closure_eq_top C
  simpa only [Submodule.topologicalClosure_eq_self] using h

/-- A finite independent set of actual raw movable sources spans the full exceptional block. -/
theorem exists_finite_suzukiTaMovableFullReducingExceptional_basis
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    ∃ t : Finset C.exterior.orthogonal,
      (t : Set C.exterior.orthogonal) ⊆
          Set.range (suzukiTaMovableFullReducingExceptionalVector C) ∧
        t.card = Module.finrank ℂ C.exterior.orthogonal ∧
        Submodule.span ℂ (t : Set C.exterior.orthogonal) = ⊤ ∧
        LinearIndepOn ℂ id (t : Set C.exterior.orthogonal) := by
  obtain ⟨t, ht, hcard, hspan, hind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℂ
      (Set.range (suzukiTaMovableFullReducingExceptionalVector C))
  have htop :
      Submodule.span ℂ (Set.range (suzukiTaMovableFullReducingExceptionalVector C)) = ⊤ :=
    suzukiTaMovableFullReducingExceptionalSpan_eq_top C
  rw [htop] at hcard hspan
  exact ⟨t, ht, by simpa using hcard, by simpa using hspan, hind⟩

/-- At a nonnegative aperture, every null vector lies entirely in every reducing exceptional
block. The coercive exterior cannot carry any portion of zero energy. -/
theorem mem_reducingExceptional_of_nonnegative_of_null
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a)
    (hnon : ∀ u : CCMArchimedeanFormDomain a,
      0 ≤ (ccmRestrictedWeilForm a u u).re)
    {q : CCMArchimedeanFormDomain a}
    (hq : (ccmRestrictedWeilForm a q q).re = 0) :
    q ∈ C.exterior.orthogonal := by
  let f : C.exterior.orthogonal :=
    C.exterior.orthogonal.orthogonalProjectionOnto q
  let m : C.exterior := C.exterior.orthogonalProjectionOnto q
  have hdecomp : (f : CCMArchimedeanFormDomain a) + m = q := by
    change C.exterior.orthogonal.starProjection q + C.exterior.starProjection q = q
    rw [add_comm]
    exact C.exterior.starProjection_add_starProjection_orthogonal q
  have hfnon := hnon (f : CCMArchimedeanFormDomain a)
  have hsum := C.orthogonal_sum f m
  rw [hdecomp, hq] at hsum
  by_cases hm : m = 0
  · have hfq : (f : CCMArchimedeanFormDomain a) = q := by
      simpa [hm] using hdecomp
    rw [← hfq]
    exact f.property
  · have hmval : (m : CCMArchimedeanFormDomain a) ≠ 0 :=
      fun h => hm (Subtype.ext h)
    have hmpos : 0 < (ccmRestrictedWeilForm a m m).re := by
      have hnorm : 0 < (1 / 2 : ℝ) * ‖m‖ ^ 2 := by positivity
      exact hnorm.trans (C.exterior_coercive m m.property hmval)
    linarith

/-- Exceptional coordinate of a pole-constrained CCM source. -/
def ccmReducingConstrainedExceptionalProjection
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    ccmPolarConstraintSubmodule a →L[ℂ] C.exterior.orthogonal :=
  C.exterior.orthogonal.orthogonalProjectionOnto.comp
    (ccmPolarConstraintSubmodule a).subtypeL

/-- Portion of the finite reducing block seen by literal pole-constrained sources. -/
def ccmReducingConstrainedExceptionalRange
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    Submodule ℂ C.exterior.orthogonal :=
  (ccmReducingConstrainedExceptionalProjection C).range

/-- Exceptional coordinate of one actual orthogonally pole-corrected movable Suzuki source. -/
def suzukiTaMovableReducingExceptionalVector
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) (c : ℝ) :
    ccmReducingConstrainedExceptionalRange C :=
  ⟨ccmReducingConstrainedExceptionalProjection C
      (suzukiTaPolarOrthogonalMovableCCMResponse a c),
    ⟨suzukiTaPolarOrthogonalMovableCCMResponse a c, rfl⟩⟩

def suzukiTaMovableReducingExceptionalSpan
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    Submodule ℂ (ccmReducingConstrainedExceptionalRange C) :=
  Submodule.span ℂ (Set.range (suzukiTaMovableReducingExceptionalVector C))

theorem suzukiTaMovableReducingExceptionalSpan_eq_map
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    suzukiTaMovableReducingExceptionalSpan C =
      (suzukiTaPolarOrthogonalMovableCCMResponseSpan a).map
        (ccmReducingConstrainedExceptionalProjection C).rangeRestrict.toLinearMap := by
  rw [suzukiTaMovableReducingExceptionalSpan,
    suzukiTaPolarOrthogonalMovableCCMResponseSpan, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨suzukiTaPolarOrthogonalMovableCCMResponse a c, ⟨c, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩

theorem suzukiTaMovableReducingExceptionalSpan_closure_eq_top
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    (suzukiTaMovableReducingExceptionalSpan C).topologicalClosure = ⊤ := by
  rw [suzukiTaMovableReducingExceptionalSpan_eq_map]
  have hdense : DenseRange
      (ccmReducingConstrainedExceptionalProjection C).rangeRestrict :=
    (ccmReducingConstrainedExceptionalProjection C).surjective_rangeRestrict.denseRange
  exact DenseRange.topologicalClosure_map_submodule hdense
    (suzukiTaPolarOrthogonalMovableCCMResponseSpan_closure_eq_top a)

/-- Finite dimensionality upgrades movable-source density to exact algebraic spanning. -/
theorem suzukiTaMovableReducingExceptionalSpan_eq_top
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    suzukiTaMovableReducingExceptionalSpan C = ⊤ := by
  have h := suzukiTaMovableReducingExceptionalSpan_closure_eq_top C
  simpa only [Submodule.topologicalClosure_eq_self] using h

/-- A finite linearly independent set of actual movable sources spans the whole constrained
exceptional block. -/
theorem exists_finite_suzukiTaMovableReducingExceptional_basis
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilReducingBlockCertificate a) :
    ∃ t : Finset (ccmReducingConstrainedExceptionalRange C),
      (t : Set (ccmReducingConstrainedExceptionalRange C)) ⊆
          Set.range (suzukiTaMovableReducingExceptionalVector C) ∧
        t.card = Module.finrank ℂ (ccmReducingConstrainedExceptionalRange C) ∧
        Submodule.span ℂ (t : Set (ccmReducingConstrainedExceptionalRange C)) = ⊤ ∧
        LinearIndepOn ℂ id (t : Set (ccmReducingConstrainedExceptionalRange C)) := by
  obtain ⟨t, ht, hcard, hspan, hind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℂ
      (Set.range (suzukiTaMovableReducingExceptionalVector C))
  have htop :
      Submodule.span ℂ (Set.range (suzukiTaMovableReducingExceptionalVector C)) = ⊤ := by
    exact suzukiTaMovableReducingExceptionalSpan_eq_top C
  rw [htop] at hcard hspan
  exact ⟨t, ht, by simpa using hcard, by simpa using hspan, hind⟩

/-- Canonical reducing certificate, selected only after unconditional existence proof. -/
noncomputable def ccmCanonicalReducingBlockCertificate
    (a : SuzukiPositiveAperture) :
    CCMRestrictedWeilReducingBlockCertificate a :=
  Classical.choice (exists_ccmRestrictedWeil_reducingFiniteBlock a)

/-- A boundary-rough first contact represented by exact finite coordinates of actual movable
completed-covariance sources in a reducing exceptional block. -/
def CCMFirstContactFiniteMovableExceptionalCoordinates : Prop :=
  ∃ (a : SuzukiPositiveAperture)
    (C : CCMRestrictedWeilReducingBlockCertificate a),
    ∃ q : C.exterior.orthogonal,
      ccmRestrictedWeilGroundEnergy a = 0 ∧
      (∀ b : SuzukiPositiveAperture, b.1 < a.1 →
        0 < ccmRestrictedWeilGroundEnergy b) ∧
      ccmArchimedeanFormToAperture a (q : CCMArchimedeanFormDomain a) ≠ 0 ∧
      ccmRestrictedWeilSourceQuadratic a (q : CCMArchimedeanFormDomain a) = 0 ∧
      (∀ u : CCMComplexSmoothInteriorSource a,
        u.toCCMFormVector ≠ (q : CCMArchimedeanFormDomain a)) ∧
      ∃ t : Finset C.exterior.orthogonal,
        (t : Set C.exterior.orthogonal) ⊆
            Set.range (suzukiTaMovableFullReducingExceptionalVector C) ∧
        t.card = Module.finrank ℂ C.exterior.orthogonal ∧
        q ∈ Submodule.span ℂ (t : Set C.exterior.orthogonal) ∧
        LinearIndepOn ℂ id (t : Set C.exterior.orthogonal)

/-- Completion-boundary escape at first contact has exact finite actual movable-source
coordinates; no approximation by smooth interior sources is used. -/
theorem ccmFirstContactBoundaryRoughness_implies_finiteMovableExceptionalCoordinates
    (h : CCMFirstContactBoundaryRoughness) :
    CCMFirstContactFiniteMovableExceptionalCoordinates := by
  obtain ⟨a, q, hground, hbefore, hphysical, hnull, hsmooth⟩ := h
  let C := ccmCanonicalReducingBlockCertificate a
  have hnon : ∀ u : CCMArchimedeanFormDomain a,
      0 ≤ (ccmRestrictedWeilForm a u u).re := by
    intro u
    have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u
    rw [hground, zero_mul] at hfloor
    rw [ccmRestrictedWeilForm_self_re_eq_source]
    exact hfloor
  have hqform : (ccmRestrictedWeilForm a q q).re = 0 := by
    rw [ccmRestrictedWeilForm_self_re_eq_source]
    exact hnull
  have hqmem : q ∈ C.exterior.orthogonal :=
    mem_reducingExceptional_of_nonnegative_of_null C hnon hqform
  let qe : C.exterior.orthogonal := ⟨q, hqmem⟩
  obtain ⟨t, ht, hcard, hspan, hind⟩ :=
    exists_finite_suzukiTaMovableFullReducingExceptional_basis C
  refine ⟨a, C, qe, hground, hbefore, hphysical, hnull, hsmooth,
    t, ht, hcard, ?_, hind⟩
  rw [hspan]
  exact Submodule.mem_top

/-- Route-level alternative: RH, or an exact finite actual movable-source realization of its first
completion-boundary obstruction. -/
theorem riemannHypothesis_or_firstContactFiniteMovableExceptionalCoordinates :
    RiemannHypothesis ∨ CCMFirstContactFiniteMovableExceptionalCoordinates := by
  rcases riemannHypothesis_or_ccmFirstContactBoundaryRoughness with hRH | hrough
  · exact Or.inl hRH
  · exact Or.inr
      (ccmFirstContactBoundaryRoughness_implies_finiteMovableExceptionalCoordinates hrough)

/-- RH is exactly positivity on finite-dimensional exceptional coordinates generated by actual
movable Suzuki sources; coercive exterior and all mixed terms have been eliminated exactly. -/
theorem riemannHypothesis_iff_movableReducingExceptional_nonnegative :
    RiemannHypothesis ↔
      ∀ (a : SuzukiPositiveAperture)
        (f : ccmReducingConstrainedExceptionalRange
          (ccmCanonicalReducingBlockCertificate a)),
        0 ≤ ccmRestrictedWeilSourceQuadratic a f.1.1 := by
  constructor
  · intro hRH a f
    exact ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis hRH a f.1.1
  · intro hexceptional
    apply riemannHypothesis_iff_polarGroundEnergy_nonneg.mpr
    intro a
    apply le_ccmRestrictedWeilPolarGroundEnergy_of_floor a
    intro u hu
    simp only [zero_mul]
    let C := ccmCanonicalReducingBlockCertificate a
    let us : ccmPolarConstraintSubmodule a := ⟨u, hu⟩
    let f : C.exterior.orthogonal :=
      C.exterior.orthogonal.orthogonalProjectionOnto u
    let m : C.exterior := C.exterior.orthogonalProjectionOnto u
    let fr : ccmReducingConstrainedExceptionalRange C :=
      ⟨f, ⟨us, rfl⟩⟩
    have hfnon : 0 ≤ (ccmRestrictedWeilForm a f f).re := by
      have := hexceptional a fr
      rw [← ccmRestrictedWeilForm_self_re_eq_source] at this
      exact this
    have hmnon : 0 ≤ (ccmRestrictedWeilForm a m m).re := by
      by_cases hm0 : m = 0
      · rw [hm0]
        simp [ccmRestrictedWeilForm]
      · have hmval : (m : CCMArchimedeanFormDomain a) ≠ 0 :=
          fun h => hm0 (Subtype.ext h)
        exact (mul_nonneg (by norm_num) (sq_nonneg ‖m‖)).trans
          (le_of_lt (C.exterior_coercive m m.property hmval))
    have hdecomp : (f : CCMArchimedeanFormDomain a) + m = u := by
      change C.exterior.orthogonal.starProjection u + C.exterior.starProjection u = u
      rw [add_comm]
      exact C.exterior.starProjection_add_starProjection_orthogonal u
    rw [← ccmRestrictedWeilForm_self_re_eq_source, ← hdecomp,
      C.orthogonal_sum]
    exact add_nonneg hfnon hmnon

end RHTower
