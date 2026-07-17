import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# Clock-period commensurability boundary

The differential complexity of Barnes multiple-sine observables is controlled by the arithmetic
geometry of their period lattice, not by a temporal evolution law.  Kurokawa--Wakayama prove
differential algebraicity for rationally commensurable periods; Kato proves
hypertranscendence when some period ratio is non-real.  The positive-real incommensurable regime
is not classified by those results.

This file does not install either external analytic theorem as an axiom.  It formalizes their exact
period-sensitive interface, proves that the two established regimes are disjoint, and derives a
finite-product source theorem: an HT product of multiple-sine one-loop factors must contain a
factor whose clock periods are not rationally commensurable.

Physics provenance: double sines/hyperbolic gamma functions are the building blocks of three-
dimensional supersymmetric partition functions, while triple sines occur in perturbative
partition functions on squashed five-spheres.  The theorem here applies to any exact finite sector
factorization once the corresponding classical differential-algebraic input is supplied.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite clock family is rationally commensurable when every period is a rational multiple of
one nonzero base period.  This is the period condition in the established DA theorems for Barnes
multiple-sine functions. -/
def RationallyCommensurablePeriods {ι : Type*} (ω : ι → ℂ) : Prop :=
  ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ i, ∃ q : ℚ, ω i = (q : ℂ) * Ω

/-- A clock family has a genuinely complex period direction when one ratio with nonzero
denominator has nonzero imaginary part. -/
def HasNonrealPeriodRatio {ι : Type*} (ω : ι → ℂ) : Prop :=
  ∃ i j, ω i ≠ 0 ∧ (ω j / ω i).im ≠ 0

/-- Rational commensurability and a non-real period ratio are disjoint. -/
theorem not_hasNonrealPeriodRatio_of_rationallyCommensurable
    {ι : Type*} {ω : ι → ℂ} (hω : RationallyCommensurablePeriods ω) :
    ¬ HasNonrealPeriodRatio ω := by
  obtain ⟨Ω, hΩ, hcomm⟩ := hω
  rintro ⟨i, j, hi, him⟩
  obtain ⟨qi, hqi⟩ := hcomm i
  obtain ⟨qj, hqj⟩ := hcomm j
  have hqi0 : (qi : ℂ) ≠ 0 := by
    intro hzero
    apply hi
    rw [hqi, hzero, zero_mul]
  have hratio : ω j / ω i = (qj : ℂ) / (qi : ℂ) := by
    rw [hqi, hqj]
    field_simp
  apply him
  rw [hratio]
  simp

/-- The two literature-established period regimes, stated at the exact differential-field
interface needed by the corpus.  Supplying this structure is supplying the classical analytic
theorems; no proposition is asserted merely from the structure's existence. -/
structure MultipleSineDifferentialRegimeInput
    (F E ι : Type*) [Field F] [Field E] [Algebra F E] [Differential E]
    (multipleSine : (ι → ℂ) → E) : Prop where
  commensurable_differentialAlgebraic : ∀ ω,
    RationallyCommensurablePeriods ω → DifferentialAlgebraicOver F (multipleSine ω)
  nonrealRatio_hypertranscendental : ∀ ω,
    HasNonrealPeriodRatio ω → HypertranscendentalOver F (multipleSine ω)

/-- An HT multiple-sine observation cannot come from a rationally commensurable clock lattice. -/
theorem MultipleSineDifferentialRegimeInput.not_rationallyCommensurable_of_hypertranscendental
    {F E ι : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {multipleSine : (ι → ℂ) → E}
    (input : MultipleSineDifferentialRegimeInput F E ι multipleSine)
    {ω : ι → ℂ} (hHT : HypertranscendentalOver F (multipleSine ω)) :
    ¬ RationallyCommensurablePeriods ω := by
  intro hcomm
  exact hHT (input.commensurable_differentialAlgebraic ω hcomm)

/-- A DA multiple-sine observation cannot lie in the established non-real-ratio HT regime. -/
theorem MultipleSineDifferentialRegimeInput.not_hasNonrealPeriodRatio_of_differentialAlgebraic
    {F E ι : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {multipleSine : (ι → ℂ) → E}
    (input : MultipleSineDifferentialRegimeInput F E ι multipleSine)
    {ω : ι → ℂ} (hDA : DifferentialAlgebraicOver F (multipleSine ω)) :
    ¬ HasNonrealPeriodRatio ω := by
  intro hnonreal
  exact input.nonrealRatio_hypertranscendental ω hnonreal hDA

/-- **Finite determinant/partition source localization.**  If an exact finite product of
multiple-sine observables is HT, at least one factor has a noncommensurable period lattice.  Thus
finite multiplication cannot manufacture HT solely from rationally locked clocks. -/
theorem MultipleSineDifferentialRegimeInput.exists_noncommensurable_factor_of_finset_prod
    {F E ι κ : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {multipleSine : (ι → ℂ) → E}
    (input : MultipleSineDifferentialRegimeInput F E ι multipleSine)
    {s : Finset κ} {ω : κ → ι → ℂ}
    (hprod : HypertranscendentalOver F (∏ k ∈ s, multipleSine (ω k))) :
    ∃ k ∈ s, ¬ RationallyCommensurablePeriods (ω k) := by
  obtain ⟨k, hk, hkHT⟩ := exists_hypertranscendental_factor_of_finset_prod hprod
  exact ⟨k, hk, input.not_rationallyCommensurable_of_hypertranscendental hkHT⟩

/-- Exact-factorization form of the finite multiple-sine source theorem. -/
theorem MultipleSineDifferentialRegimeInput.exists_noncommensurable_factor_of_eq_finset_prod
    {F E ι κ : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {multipleSine : (ι → ℂ) → E}
    (input : MultipleSineDifferentialRegimeInput F E ι multipleSine)
    {x : E} {s : Finset κ} {ω : κ → ι → ℂ}
    (hx : HypertranscendentalOver F x)
    (hfactor : x = ∏ k ∈ s, multipleSine (ω k)) :
    ∃ k ∈ s, ¬ RationallyCommensurablePeriods (ω k) := by
  rw [hfactor] at hx
  exact input.exists_noncommensurable_factor_of_finset_prod hx

end

end GaloisForLFunctions.HTGeometry
