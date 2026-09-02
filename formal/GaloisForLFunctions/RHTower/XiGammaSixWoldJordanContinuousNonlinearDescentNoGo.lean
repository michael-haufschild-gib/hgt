import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanParametricVacuity

/-!
# Continuous nonlinear Wold--Jordan descent no-go

The genuine fixed-left Big--Witt rows all converge to one singular one-leg graph vector, while a
prime-labelled finite reporter reads the row indexed by `p` as its coefficient at `p`.  Continuity
alone therefore forces every such coefficient to be constant.  No linearity, bounded linear
structure, algebra law, or differentiability of the graph reporter is needed.

Applied to the literal Wold--Jordan coefficients `A(q) / p`, arbitrary continuous nonlinear scalar
descent exists exactly when `A(q) = 0`, equivalently when the Xi copy lies on the critical line.
Global continuous nonlinear descent is therefore exactly RH, not an upstream source producer.

RH chain killed: actual Big--Witt source rows -> continuous nonlinear singular scalar reporter ->
Gamma-six horizontal vanishing -> critical-line placement -> RH.  Any surviving Route L descent
must be discontinuous or retain genuinely operator-valued/multifibre output.
-/

open Complex Filter Function Set Topology
open scoped BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Arbitrary continuous, possibly nonlinear scalar descent of a prime-labelled reporter. -/
def PrimeLabelledActualSourceContinuouslyDescends
    (c : Nat.Primes → ℝ) : Prop :=
  ∃ reporter : C(DeningerBigWittCrossPairSingularOneLegGraph, ℂ),
    ∀ a n : ℕ,
      reporter (deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)) =
      primeLabelledEnergyReporter c
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)

/-- Continuous nonlinear scalar descent is possible exactly for prime-constant coefficients. -/
theorem primeLabelledActualSourceContinuouslyDescends_iff
    (c : Nat.Primes → ℝ) :
    PrimeLabelledActualSourceContinuouslyDescends c ↔
      ∃ z : ℝ, ∀ a : ℕ, c (nthPrimeSubtype a) = z := by
  constructor
  · rintro ⟨reporter, hreporter⟩
    have hlimit (a : ℕ) :
        ((c (nthPrimeSubtype a) : ℝ) : ℂ) =
          reporter deningerBigWittCrossPairOneLegGraphSingularVector := by
      have hreported : Tendsto
          (fun n => reporter
            (deningerBigWittCrossPairFiniteOneLegGraphAdmission
              (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)))
          atTop
          (nhds (reporter deningerBigWittCrossPairOneLegGraphSingularVector)) :=
        (reporter.continuous.tendsto
          deningerBigWittCrossPairOneLegGraphSingularVector).comp
            (tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_woldFixedLeftRightEdgeNormalizedPacket a)
      have hreported' : Tendsto
          (fun _n : ℕ => ((c (nthPrimeSubtype a) : ℝ) : ℂ))
          atTop
          (nhds (reporter deningerBigWittCrossPairOneLegGraphSingularVector)) := by
        refine hreported.congr ?_
        intro n
        rw [hreporter,
          primeLabelledEnergyReporter_woldFixedLeftRightEdgeNormalizedPacket]
      exact tendsto_nhds_unique tendsto_const_nhds hreported'
    refine ⟨c (nthPrimeSubtype 0), ?_⟩
    intro a
    have hcomplex :
        ((c (nthPrimeSubtype a) : ℝ) : ℂ) =
          ((c (nthPrimeSubtype 0) : ℝ) : ℂ) :=
      (hlimit a).trans (hlimit 0).symm
    exact_mod_cast hcomplex
  · rintro ⟨z, hz⟩
    refine ⟨⟨fun _ => (z : ℂ), continuous_const⟩, ?_⟩
    intro a n
    rw [primeLabelledEnergyReporter_woldFixedLeftRightEdgeNormalizedPacket,
      hz a]
    rfl

/-- Arbitrary continuous nonlinear descent of literal Wold--Jordan energy. -/
def DeningerBigWittWoldJordanActualSourceContinuousEnergyDescends
    (q : XiZeroCopy) : Prop :=
  ∃ reporter : C(DeningerBigWittCrossPairSingularOneLegGraph, ℂ),
    ∀ a n : ℕ,
      reporter (deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)) =
      deningerBigWittCrossPairFiniteWoldJordanEnergyReporter q
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)

/-- Allowing arbitrary continuous nonlinearity adds no descent power. -/
theorem deningerBigWittWoldJordanActualSourceContinuousEnergyDescends_iff_linear
    (q : XiZeroCopy) :
    DeningerBigWittWoldJordanActualSourceContinuousEnergyDescends q ↔
      DeningerBigWittWoldJordanActualSourceEnergyDescends q := by
  let c : Nat.Primes → ℝ := fun p =>
    thetaGammaSixWoldHorizontalCarrier p q ^ 2
  have hrep :
      deningerBigWittCrossPairFiniteWoldJordanEnergyReporter q =
        primeLabelledEnergyReporter c := by
    simpa only [c] using
      deningerBigWittCrossPairFiniteWoldJordanEnergyReporter_eq q
  constructor
  · rintro ⟨reporter, hreporter⟩
    have hcontinuous : PrimeLabelledActualSourceContinuouslyDescends c := by
      refine ⟨reporter, ?_⟩
      intro a n
      rw [← hrep]
      exact hreporter a n
    have hconstant :=
      (primeLabelledActualSourceContinuouslyDescends_iff c).1 hcontinuous
    have hlinear := (primeLabelledActualSourceDescends_iff c).2 hconstant
    rcases hlinear with ⟨linearReporter, hlinearReporter⟩
    refine ⟨linearReporter, ?_⟩
    intro a n
    rw [hrep]
    exact hlinearReporter a n
  · rintro ⟨reporter, hreporter⟩
    refine ⟨⟨reporter, reporter.continuous⟩, hreporter⟩

/-- At one Xi copy, continuous nonlinear scalar descent is exactly critical-line placement. -/
theorem deningerBigWittWoldJordanActualSourceContinuousEnergyDescends_iff_line
    (q : XiZeroCopy) :
    DeningerBigWittWoldJordanActualSourceContinuousEnergyDescends q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerBigWittWoldJordanActualSourceContinuousEnergyDescends_iff_linear,
    deningerBigWittWoldJordanActualSourceEnergyDescends_iff_line]

/-- Global continuous nonlinear Wold--Jordan descent is exactly RH. -/
theorem everyDeningerBigWittWoldJordanActualSourceContinuousEnergyDescends_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      DeningerBigWittWoldJordanActualSourceContinuousEnergyDescends q) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    rw [← everyDeningerBigWittWoldJordanActualSourceEnergyDescends_iff_riemannHypothesis]
    intro q
    exact
      (deningerBigWittWoldJordanActualSourceContinuousEnergyDescends_iff_linear q).1
        (h q)
  · intro h q
    have hlinear : DeningerBigWittWoldJordanActualSourceEnergyDescends q :=
      (everyDeningerBigWittWoldJordanActualSourceEnergyDescends_iff_riemannHypothesis).2 h q
    exact
      (deningerBigWittWoldJordanActualSourceContinuousEnergyDescends_iff_linear q).2
        hlinear

end

end RHTower.HedenmalmThetaSource
