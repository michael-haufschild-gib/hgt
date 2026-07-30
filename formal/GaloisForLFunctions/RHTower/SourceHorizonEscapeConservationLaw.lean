import GaloisForLFunctions.RHTower.CompactOpenKolchinWardChargeEscape
import GaloisForLFunctions.RHTower.XiSourceCayleyOrderSpaceConservationLaw
import GaloisForLFunctions.RHTower.XiArithmeticSourceMomentTorelli

/-!
# Source-horizon conservation and noncompact Riemann-divisor escape

This module packages the universal source-horizon law with the two
complementary Riemann-divisor facts:

* actual Xi residues are arithmetic-source modes whose canonical-time
  energy has the exact transverse rate `2 Re rho - 1`;
* completed-symmetry countermodels can carry arbitrarily large
  off-critical divisor charge to infinite height while every compact
  holomorphic jet, bounded Ward window, and rational differential
  stratum loses it.

The conjunction identifies these blindness statements as fixed-scale
projections of a source mode that is exactly conserved after inverse-drift
rescaling.
-/

open Complex Filter MeasureTheory Real Set
open scoped Differential Topology

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complete certificate for source-horizon conservation together with
compact-open, differential-algebraic, and Ward-charge escape. -/
structure SourceHorizonEscapeConservationCertificate : Prop where
  generatorClockUniqueness :
    ∀ (b : ℂ) (tau x : ℝ), b ≠ 0 →
      cayleyFockDrift b * x = tau →
        x = coherentGeneratorObservationTime b tau
  generatorDuality :
    ∀ (b : ℂ) (tau : ℝ), b ≠ 0 →
      b * (coherentGeneratorObservationTime b tau : ℂ) =
        (starRingEnd ℂ) (b⁻¹) * (tau : ℂ)
  generatorConservation :
    ∀ (m b : ℂ) (tau : ℝ) (r : ℕ), b ≠ 0 →
      coherentGeneratorObservationTime b tau ^ r / r.factorial *
          ‖coherentExponentialJet m b
            (coherentGeneratorObservationTime b tau) r‖ ^ 2 =
        ‖m‖ ^ 2 *
          Real.exp (coherentGeneratorDualRate b * tau) *
            poissonOrderWeight tau r
  generatorNeutralLineCircle :
    ∀ (b : ℂ), b ≠ 0 →
      (coherentGeneratorDualRate b = 0 ↔ ‖1 + b‖ = 1)
  sourceClockPullback :
    ∀ (c rho : ℂ) (tau : ℝ), rho ≠ c →
      sourceCayleyObservationTime c rho tau =
        coherentGeneratorObservationTime ((rho - c)⁻¹) tau
  finiteCarrierAlgebraic :
    ∀ {n : ℕ} (m rho : Fin n → ℂ) (c : ℂ),
      DifferentiallyAlgebraic
        (finiteCayleyResidueCarrier m rho c)
  finiteCarrierODE :
    ∀ {n : ℕ} (m rho : Fin n → ℂ) (c x : ℂ),
      let lam : Fin n → ℂ := fun j => (rho j - c)⁻¹
      let p := expSumAnnihilator Finset.univ lam
      ∑ j ∈ Finset.range (p.natDegree + 1),
          p.coeff j *
            iteratedDeriv j
              (finiteCayleyResidueCarrier m rho c) x = 0
  finiteCarrierFaithful :
    ∀ {n : ℕ} {m rho : Fin n → ℂ} {c x : ℂ},
      Function.Injective rho → m ≠ 0 →
        ∃ r : Fin n,
          iteratedDeriv (r : ℕ)
            (finiteCayleyResidueCarrier m rho c) x ≠ 0
  sourceInversion :
    ∀ (c rho : ℂ) (tau : ℝ), rho ≠ c →
      (rho - c)⁻¹ *
          (sourceCayleyObservationTime c rho tau : ℂ) =
        (starRingEnd ℂ) (rho - c) * (tau : ℂ)
  sourceHorizon :
    ∀ (c rho : ℂ),
      sourceCayleyTransverseRate c rho = 0 ↔
        rho.re = c.re - 1 / 2
  universalConservation :
    ∀ (m c rho : ℂ) (tau : ℝ) (r : ℕ), rho ≠ c →
      let x := sourceCayleyObservationTime c rho tau
      x ^ r / r.factorial *
          ‖iteratedDeriv r
            (cayleyPoleResidueMode m c rho) (x : ℂ)‖ ^ 2 =
        ‖m‖ ^ 2 *
          Real.exp (sourceCayleyTransverseRate c rho * tau) *
            poissonOrderWeight tau r
  actualXiSourceLaw :
    XiSourceCayleyOrderSpaceConservationCertificate
  arithmeticSourceTomography :
    XiArithmeticSourceMomentTorelliCertificate
  compactEscape :
    ∀ {a : ℝ}, 0 < a → a < 1 / 2 →
      (∀ n, Hypertranscendental (escapingQuartetGaugedXi a n)) ∧
      (∀ n s, AnalyticAt ℂ (escapingQuartetGaugedXi a n) s) ∧
      (∀ n s, escapingQuartetGaugedXi a n (1 - s) =
        escapingQuartetGaugedXi a n s) ∧
      (∀ n s, escapingQuartetGaugedXi a n ((starRingEnd ℂ) s) =
        (starRingEnd ℂ) (escapingQuartetGaugedXi a n s)) ∧
      (∀ n, (quartetPoint a (escapingQuartetHeight n)).re ≠ 1 / 2 ∧
        escapingQuartetGaugedXi a n
          (quartetPoint a (escapingQuartetHeight n)) = 0) ∧
      (∀ j, TendstoLocallyUniformly
        (fun n => iteratedDeriv j (escapingQuartetGaugedXi a n))
        (iteratedDeriv j xi) atTop) ∧
      (∀ R, 0 ≤ R → TendstoUniformlyOn
        (fun n t => quartetWardInfinitesimalDensity a
          (escapingQuartetHeight n) t)
        (fun _ : ℝ => 0) atTop {t : ℝ | |t| ≤ R}) ∧
      (∀ n, ∫⁻ t : ℝ, ENNReal.ofReal
        (quartetWardInfinitesimalDensity a
          (escapingQuartetHeight n) t) =
            ENNReal.ofReal (8 * π))
  unboundedEscape :
    ∀ {a : ℝ}, 0 < a → a < 1 / 2 →
      ∀ N : ℕ, 0 < N →
        (∀ n, Hypertranscendental
          (multiplicityEscapingQuartetGaugedXi a N n)) ∧
        (∀ n s, AnalyticAt ℂ
          (multiplicityEscapingQuartetGaugedXi a N n) s) ∧
        (∀ n s, multiplicityEscapingQuartetGaugedXi a N n (1 - s) =
          multiplicityEscapingQuartetGaugedXi a N n s) ∧
        (∀ n s,
          multiplicityEscapingQuartetGaugedXi a N n
              ((starRingEnd ℂ) s) =
            (starRingEnd ℂ)
              (multiplicityEscapingQuartetGaugedXi a N n s)) ∧
        (∀ n, (quartetPoint a (escapingQuartetHeight n)).re ≠ 1 / 2 ∧
          multiplicityEscapingQuartetGaugedXi a N n
            (quartetPoint a (escapingQuartetHeight n)) = 0) ∧
        (∀ j, TendstoLocallyUniformly
          (fun n => iteratedDeriv j
            (multiplicityEscapingQuartetGaugedXi a N n))
          (iteratedDeriv j xi) atTop) ∧
        (∀ R, 0 ≤ R → TendstoUniformlyOn
          (fun n => multiplicityEscapingQuartetWardDensity a N n)
          (fun _ : ℝ => 0) atTop {t : ℝ | |t| ≤ R}) ∧
        (∀ n, multiplicityEscapingQuartetWardMass a N n =
          N • ENNReal.ofReal (8 * π)) ∧
        (∀ n, meromorphicOrderAt
            (logDeriv (multiplicityEscapingQuartetGauge a N n))
            (quartetPoint a (escapingQuartetHeight n)) =
          ((-1 : ℤ) : WithTop ℤ))

/-- **Source-horizon escape-conservation law.** -/
theorem sourceHorizonEscapeConservation_law :
    SourceHorizonEscapeConservationCertificate := by
  exact {
    generatorClockUniqueness :=
      coherentGenerator_observationTime_unique
    generatorDuality :=
      coherentGenerator_duality
    generatorConservation :=
      coherentGenerator_poisson_conservation
    generatorNeutralLineCircle :=
      coherentGeneratorDualRate_eq_zero_iff_shift_norm_one
    sourceClockPullback :=
      sourceCayleyObservationTime_eq_coherentGeneratorTime
    finiteCarrierAlgebraic :=
      finiteCayleyResidueCarrier_differentiallyAlgebraic
    finiteCarrierODE :=
      finiteCayleyResidueCarrier_ode
    finiteCarrierFaithful :=
      finiteCayleyResidueCarrier_jetFaithful
    sourceInversion :=
      sourceCayley_inverse_observationTime
    sourceHorizon :=
      sourceCayleyTransverseRate_eq_zero_iff
    universalConservation :=
      sourceCayleyResidueMode_horizon_conservation
    actualXiSourceLaw :=
      xiSourceCayleyOrderSpaceConservation_law
    arithmeticSourceTomography :=
      xiArithmeticSourceMomentTorelli_law
    compactEscape :=
      fun ha0 ha1 =>
        compactOpenKolchinWardChargeEscape_law ha0 ha1
    unboundedEscape :=
      fun ha0 ha1 =>
        unboundedCompactOpenKolchinWardChargeEscape_law ha0 ha1 }

end

end RHTower
