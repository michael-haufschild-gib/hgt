import GaloisForLFunctions.HTGeometry.PointFiniteFacetObservation
import GaloisForLFunctions.HTGeometry.UniversalFiniteConstraintCarrier

/-!
# One fixed source for countable point-finite constraint geometries

The point-finite observation theorem turns every finite structural family on a countable infinite
facet geometry into a genuinely finite polynomial-operator packet.  This module proves that the
same fixed positive prime-log source used for all finite Stanley--Reisner geometries realizes the
exact differential matroid of every such packet.

No completion or infinite analytic sum is introduced: each output is a finite differential-
operator combination of translates of the one universal source.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- Common finite support of a finite family of ordinary `Finsupp` rows. -/
def finsuppOperatorRowSupport
    {P ι κ : Type*} [Semiring P] [Fintype ι] [DecidableEq κ]
    (Q : ι → κ →₀ P) : Finset κ :=
  Finset.univ.biUnion fun i => (Q i).support

/-- Finite source-coordinate type used by one finite family of `Finsupp` rows. -/
abbrev FinsuppOperatorRowIndex
    {P ι κ : Type*} [Semiring P] [Fintype ι] [DecidableEq κ]
    (Q : ι → κ →₀ P) :=
  {q : κ // q ∈ finsuppOperatorRowSupport Q}

/-- Restrict each row to the common finite support without changing any nonzero coefficient. -/
def finsuppOperatorRows
    {P ι κ : Type*} [Semiring P] [Fintype ι] [DecidableEq κ]
    (Q : ι → κ →₀ P) :
    ι → FinsuppOperatorRowIndex Q → P :=
  fun i q => Q i q.1

/-- Every nonzero coefficient occurs in the common finite source support. -/
theorem mem_finsuppOperatorRowSupport_of_ne
    {P ι κ : Type*} [Semiring P] [Fintype ι] [DecidableEq κ]
    (Q : ι → κ →₀ P) {i : ι} {q : κ} (h : Q i q ≠ 0) :
    q ∈ finsuppOperatorRowSupport Q := by
  simp only [finsuppOperatorRowSupport, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, Finsupp.mem_support_iff.mpr h⟩

/-- Restricting a finite family of `Finsupp` rows to its common support preserves and reflects
linear independence. -/
theorem linearIndependent_finsuppOperatorRows_iff
    {P ι κ : Type*} [Ring P] [Fintype ι]
    [DecidableEq ι] [DecidableEq κ]
    (Q : ι → κ →₀ P) :
    LinearIndependent P (finsuppOperatorRows Q) ↔
      LinearIndependent P Q := by
  classical
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h A hrel i
    apply h A
    funext q
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, finsuppOperatorRows]
    have hq := congrArg (fun f : κ →₀ P => f q.1) hrel
    change (Finsupp.lapply (R := P) q.1) (∑ x, A x • Q x) = 0 at hq
    rw [map_sum] at hq
    simpa only [map_smul] using hq
  · intro h A hrel i
    apply h A
    apply Finsupp.ext
    intro q
    by_cases hzero : ∀ j, Q j q = 0
    · simp [hzero]
    · push Not at hzero
      obtain ⟨j, hj⟩ := hzero
      let q' : FinsuppOperatorRowIndex Q :=
        ⟨q, mem_finsuppOperatorRowSupport_of_ne Q hj⟩
      have hq := congrArg (fun f : FinsuppOperatorRowIndex Q → P => f q') hrel
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
        finsuppOperatorRows, q'] at hq
      change (Finsupp.lapply (R := P) q) (∑ x, A x • Q x) = 0
      rw [map_sum]
      simpa only [map_smul] using hq

/-- Acting with finite `Finsupp` polynomial rows on a differentially independent source packet
produces the exact row differential matroid. -/
theorem differentialIndependent_finsuppOperatorRows_iff
    {C K ι κ : Type*}
    [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (Q : ι → κ →₀ Polynomial C)
    (x : FinsuppOperatorRowIndex Q → K)
    (hx : DifferentialIndependent C x) :
    DifferentialIndependent C
        (differentialOperatorRowApply (finsuppOperatorRows Q) x) ↔
      LinearIndependent (Polynomial C) Q := by
  rw [differentialIndependent_differentialOperatorRows_iff
    hconst (finsuppOperatorRows Q) x hx]
  exact linearIndependent_finsuppOperatorRows_iff Q

/-- Embed any countable coordinate type into the fixed universal facet-orbit palette.  The
embedding is only an allocation of collision-free source coordinates; the coherent facet labels
remain present in the row index itself. -/
def countableUniversalFacetOrbitEmbedding (κ : Type*) [Countable κ] :
    κ ↪ UniversalFacetOrbitIndex := by
  letI := Encodable.ofCountable κ
  refine ⟨fun q => ({Encodable.encode q}, 0), ?_⟩
  intro a b h
  have htag := congrArg Prod.fst h
  have hcode : Encodable.encode a = Encodable.encode b := by
    simpa using htag
  exact Encodable.encode_injective hcode

/-- **One-source finite-row universality.**  Every finite family of finitely supported polynomial
operator rows on a countable index set is realized by the same fixed positive prime-log source,
with differential independence exactly equal to polynomial-row independence. -/
theorem universalFacetOrbit_finsuppDifferentialMatroid
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (e : κ ↪ UniversalFacetOrbitIndex)
    (Q : ι → κ →₀ Polynomial ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    let source : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
        universalFacetOrbitGauge (e q.1)
    DifferentialIndependent ℂ
        (differentialOperatorRowApply (finsuppOperatorRows Q) source) ↔
      LinearIndependent (Polynomial ℂ) Q := by
  classical
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let fullSource := boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
    universalFacetOrbitGauge
  let source : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
    fullSource (e q.1)
  have hsourceRat : DifferentialIndependent (RatFunc ℂ) source := by
    have hcomp := universalFacetOrbitGauge_differentialIndependent.comp
      (fun q : FinsuppOperatorRowIndex Q => e q.1)
      (e.injective.comp Subtype.val_injective)
    simpa [source, fullSource, Function.comp_def] using hcomp
  have hsource : DifferentialIndependent ℂ source :=
    differentialIndependent_upperEnd_restrictComplex source hsourceRat
  change DifferentialIndependent ℂ
      (differentialOperatorRowApply (finsuppOperatorRows Q) source) ↔
    LinearIndependent (Polynomial ℂ) Q
  exact differentialIndependent_finsuppOperatorRows_iff
    upperEndMero_deriv_complexConstant Q source hsource

/-- **Countable point-finite constraint completeness.**  Let a countable vertex set carry any
nonempty point-finite family of finite facets.  The one fixed universal positive prime-log source
realizes the exact nonlinear differential matroid of every finite structural family in the
possibly infinite Stanley--Reisner quotient.  Every output is still a finite differential-
operator sum. -/
theorem universalFacetOrbit_countablePointFiniteConstraintDifferentialMatroid
    {α ι : Type*} [Countable α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (facets : Set (Finset α)) (hne : facets.Nonempty)
    (hfacets : PointFiniteFacetFamily facets)
    (P : ι → MvPolynomial α (Polynomial ℂ)) :
    let Q := fun i => pointFiniteFacetRow facets hfacets (P i)
    let e := countableUniversalFacetOrbitEmbedding (PointFiniteFacetIndex facets)
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    let source : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
        universalFacetOrbitGauge (e q.1)
    DifferentialIndependent ℂ
        (differentialOperatorRowApply (finsuppOperatorRows Q) source) ↔
      LinearIndependent (Polynomial ℂ)
        (fun i => Ideal.Quotient.mk
          (setStanleyReisnerIdeal (Polynomial ℂ) facets) (P i)) := by
  classical
  let Q := fun i => pointFiniteFacetRow facets hfacets (P i)
  let e := countableUniversalFacetOrbitEmbedding (PointFiniteFacetIndex facets)
  have hanalytic := universalFacetOrbit_finsuppDifferentialMatroid e Q
  have halgebra := linearIndependent_pointFiniteFacetRow_iff
    facets hne hfacets P
  exact hanalytic.trans halgebra

end

end GaloisForLFunctions.HTGeometry
