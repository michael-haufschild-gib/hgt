import GaloisForLFunctions.HTGeometry.Hypertranscendence
import GaloisForLFunctions.HTGeometry.TorsionFaceExactification
import GaloisForLFunctions.HTGeometry.DATaylorLogRatioResonance

/-!
# Geometric Taylor magnitudes and torsion-language exactification

The analytic confinement theorem for an asymptotically exact geometric Taylor profile is isolated
as an explicit input: differential algebraicity produces one finite locked face, with a nonzero
weight, whose character sum vanishes on every torsion state.  The project-internal Fourier
exactifier then contradicts that nonzero weight.  The exact periodic-profile cascade is assembled
separately from the project-internal polynomial level-vanishing theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The exact output of Mahler normalization, balanced survival, and geometric face confinement
for a torsion-language-universal Taylor phase.  These named analytic parents are data, not axioms. -/
structure GeometricTLULockedFaceInput
    (f : ℂ → ℂ) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  torsionOrder : ℕ
  jetDegree : ℕ
  degree_lt_torsionOrder : jetDegree < torsionOrder
  face : Finset (ι → ℕ)
  weight : (ι → ℕ) → ℂ
  multiplicity_le : ∀ e ∈ face, ∀ i, e i ≤ jetDegree
  nonzeroWeight_of_differentiallyAlgebraic :
    DifferentiallyAlgebraic f → ∃ e ∈ face, weight e ≠ 0
  torsionFaceVanishes_of_differentiallyAlgebraic :
    DifferentiallyAlgebraic f →
      ∀ s : ι → ℂ, (∀ i, s i ^ torsionOrder = 1) →
        ∑ e ∈ face, weight e * ∏ i, s i ^ e i = 0

/-- **Geometric TLU hypertranscendence.**  Once the geometric profile locks every possible ADE to
the finite face supplied by `GeometricTLULockedFaceInput`, torsion Fourier separation forces all
face weights to vanish, contradicting balanced survival. -/
theorem hypertranscendental_of_geometricTLU_lockedFace
    {f : ℂ → ℂ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (input : GeometricTLULockedFaceInput f ι) : Hypertranscendental f := by
  intro hDA
  obtain ⟨e, he, hweight⟩ := input.nonzeroWeight_of_differentiallyAlgebraic hDA
  have hall := GaloisForLFunctions.face_weights_eq_zero
    input.degree_lt_torsionOrder input.face input.multiplicity_le input.weight
    (input.torsionFaceVanishes_of_differentiallyAlgebraic hDA)
  exact hweight (hall e he)

/-- Exact input for all valuation levels of an eventually periodic phase on the exact geometric
profile.  The exponentially separated ADE cascade supplies the convergent level polynomials. -/
structure GeometricPeriodicLevelInput (κ : Type*) where
  levelPolynomial : κ → Polynomial ℂ
  levelSubsequence : κ → ℕ → ℕ
  levelSubsequence_strictMono : ∀ k, StrictMono (levelSubsequence k)
  levelPolynomial_tendsto_zero : ∀ k,
    Tendsto (fun n => (levelPolynomial k).eval
      (((levelSubsequence k n : ℕ) : ℂ))) atTop (nhds 0)

/-- **Level-exactness law.** Every valuation-level polynomial in an exact geometric profile with
eventually periodic phase vanishes identically. -/
theorem geometricPeriodic_everyLevelPolynomial_eq_zero
    {κ : Type*} (input : GeometricPeriodicLevelInput κ) :
    ∀ k, input.levelPolynomial k = 0 := by
  intro k
  exact GaloisForLFunctions.polynomial_eq_zero_of_tendsto_zero
    (input.levelPolynomial k) (input.levelSubsequence k)
    (input.levelSubsequence_strictMono k) (input.levelPolynomial_tendsto_zero k)

/-- A singleton admissible level carrying a nonzero grouped weight is impossible. -/
theorem geometricPeriodic_no_nonzero_level
    {κ : Type*} (input : GeometricPeriodicLevelInput κ) :
    ¬ ∃ k, input.levelPolynomial k ≠ 0 := by
  rintro ⟨k, hk⟩
  exact hk (geometricPeriodic_everyLevelPolynomial_eq_zero input k)

/-- The already checked magnitude-side corollary used by the geometric column: a DA series with a
finite successive log-magnitude ratio greater than one forces that ratio to be algebraic. -/
theorem geometricProfile_da_forces_algebraic_ratio
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ}
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hbpos : ∀ᶠ i in atTop, 0 < b i)
    {lam : ℝ} (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam1 : 1 < lam) (hDA : DifferentiallyAlgebraic f) :
    IsAlgebraic ℤ lam :=
  logRatio_isAlgebraic_of_eventually_differentiallyAlgebraic
    hf hb hbpos hlam hlam1 hDA

end

end GaloisForLFunctions.HTGeometry
