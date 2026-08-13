import GaloisForLFunctions.RHTower.XiReflectionIncidenceSchattenSpectrum
import GaloisForLFunctions.RHTower.MarkedHalfCharacterCofinalDiagonalInverseLaw
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster

/-!
# Trace-one source convergence of Xi reflection incidence

The endpoint incidence mass is positive, so ordered convergence over increasing ordinary primes
is already as strong as absolute summability.  This module identifies that ordered series with an
actual rational-adelic source series: the literal trace-one prime cycle is sent through the
completed Xi two-leg landing, its paracyclic residue is read, and the canonical marked comparison
weight is retained.  Prime labels, divisor multiplicity, and both reflection orientations remain
present.

The result is an exact producer interface rather than a convergence assumption hidden inside a
quotient: ordinary convergence of this explicit source residue series is equivalent to endpoint
Schatten-one admission and hence, globally, to RH.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Actual paracyclic residue of the trace-one rational-adelic cycle at the same ordinary-prime
clock and label. -/
def xiReflectionIncidencePrimeTraceOneCyclicResidue
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℂ :=
  ccmRationalAdelicTwoLegCyclicResidue
    (GaloisForLFunctions.HTGeometry.cyclicParacyclicEquivarianceDefect
      ccmRationalAdelicDegreeOneCyclicRotation
      (sourceDaggerNormalizedDegreeOneRotationLinear (p : ℕ) (rho : ℂ))
      (ccmMobiusThetaXiJetTwoLegLanding
        (xiSupportMultiplicity rho) (xiSpectralPointSupport rho))
      (ccmRationalAdelicOrdinaryPrimeCycleAtom p))

/-- Positive, coefficient-faithful source mass.  The multiplicity factor is the literal
reflection-incidence cardinality; the scalar weight is the canonical marked comparison appearing
in the exact Bockstein/residue identity. -/
def xiReflectionIncidencePrimeTraceOneSourceMass
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  ((xiZeroCopyLineReflectionIncidence rho).card : ℝ) *
    markedCofinalComparisonWeight (primeDepthBVWoldXiCenteredRate rho) p *
      ‖xiReflectionIncidencePrimeTraceOneCyclicResidue rho p‖

theorem xiReflectionIncidencePrimeTraceOneSourceMass_nonneg
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    0 ≤ xiReflectionIncidencePrimeTraceOneSourceMass rho p := by
  unfold xiReflectionIncidencePrimeTraceOneSourceMass
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (markedCofinalComparisonWeight_pos
        (primeDepthBVWoldXiCenteredRate rho) p).le)
    (norm_nonneg _)

/-- **Source/incidence identity.**  The actual weighted trace-one cyclic residue is exactly the
endpoint incidence Schatten mass times the norm of the first nonzero Xi jet.  No coefficient is
fitted or divided out. -/
theorem xiReflectionIncidencePrimeTraceOneSourceMass_eq
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    xiReflectionIncidencePrimeTraceOneSourceMass rho p =
      ‖iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)‖ *
        xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho p := by
  have hcomparison :=
    primeGammaBockstein_mul_xiLanding_eq_neg_weight_mul_residue rho p
      (ccmRationalAdelicOrdinaryPrimeCycleAtom p)
  rw [ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one, mul_one] at hcomparison
  rw [thetaInternalJetLeadingSourceCoefficient_eq] at hcomparison
  change
    (primeGammaCofinalBocksteinCoefficient
          (primeDepthBVWoldXiCenteredRate rho) p : ℂ) *
        iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho) =
      -(markedCofinalComparisonWeight
          (primeDepthBVWoldXiCenteredRate rho) p : ℂ) *
        xiReflectionIncidencePrimeTraceOneCyclicResidue rho p at hcomparison
  have hnorm :
      |primeGammaCofinalBocksteinCoefficient
          (primeDepthBVWoldXiCenteredRate rho) p| *
          ‖iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho)‖ =
        markedCofinalComparisonWeight
            (primeDepthBVWoldXiCenteredRate rho) p *
          ‖xiReflectionIncidencePrimeTraceOneCyclicResidue rho p‖ := by
    have := congrArg norm hcomparison
    simpa only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (markedCofinalComparisonWeight_pos
        (primeDepthBVWoldXiCenteredRate rho) p)] using this
  rw [xiReflectionIncidencePrimeTraceOneSourceMass,
    xiZeroCopyLineReflectionPrimeIncidenceSchattenMass,
    primeGammaCofinalBocksteinSchattenMass, Real.rpow_one,
    primeGammaCofinalBocksteinMagnitude]
  calc
    ((xiZeroCopyLineReflectionIncidence rho).card : ℝ) *
          markedCofinalComparisonWeight
            (primeDepthBVWoldXiCenteredRate rho) p *
          ‖xiReflectionIncidencePrimeTraceOneCyclicResidue rho p‖ =
        ((xiZeroCopyLineReflectionIncidence rho).card : ℝ) *
          (markedCofinalComparisonWeight
              (primeDepthBVWoldXiCenteredRate rho) p *
            ‖xiReflectionIncidencePrimeTraceOneCyclicResidue rho p‖) := by ring
    _ =
        ((xiZeroCopyLineReflectionIncidence rho).card : ℝ) *
          (|primeGammaCofinalBocksteinCoefficient
              (primeDepthBVWoldXiCenteredRate rho) p| *
            ‖iteratedDeriv (xiSupportMultiplicity rho) XiC
              (xiSpectralPointSupport rho)‖) := by rw [← hnorm]
    _ = ‖iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho)‖ *
          (((xiZeroCopyLineReflectionIncidence rho).card : ℝ) *
            |primeGammaCofinalBocksteinCoefficient
              (primeDepthBVWoldXiCenteredRate rho) p|) := by ring

/-- Multiplying by the nonzero leading Xi jet does not alter the endpoint summability wall. -/
theorem summable_xiReflectionIncidencePrimeTraceOneSourceMass_iff
    (rho : XiDivisorSupport) :
    Summable (xiReflectionIncidencePrimeTraceOneSourceMass rho) ↔
      Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho) := by
  have hjet :
      ‖iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
  have hfun : xiReflectionIncidencePrimeTraceOneSourceMass rho =
      fun p : Nat.Primes =>
        ‖iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho)‖ *
          xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho p := by
    funext p
    exact xiReflectionIncidencePrimeTraceOneSourceMass_eq rho p
  rw [hfun, summable_mul_left_iff hjet]

/-- Ordered convergence of a nonnegative real series is equivalent to unconditional summability.
This is the exact point at which the one-sign source law removes any conditional-convergence
escape. -/
private theorem exists_tendsto_sum_range_iff_summable_of_nonneg
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    (∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n)
      atTop (nhds L)) ↔ Summable f := by
  constructor
  · rintro ⟨L, hL⟩
    exact ((hasSum_iff_tendsto_nat_of_nonneg hf L).2 hL).summable
  · intro hsum
    refine ⟨∑' n, f n, ?_⟩
    exact (hasSum_iff_tendsto_nat_of_nonneg hf _).1 hsum.hasSum

/-- Ordered increasing-prime convergence of the literal endpoint incidence mass. -/
def XiReflectionIncidencePrimeOrdinaryConvergent
    (rho : XiDivisorSupport) : Prop :=
  ∃ L : ℝ,
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho
          (nthPrimeEquiv n))
      atTop (nhds L)

/-- For positive incidence mass, ordered convergence already is the fixed Schatten-one landing. -/
theorem xiReflectionIncidencePrimeOrdinaryConvergent_iff_summable
    (rho : XiDivisorSupport) :
    XiReflectionIncidencePrimeOrdinaryConvergent rho ↔
      Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho) := by
  let f : ℕ → ℝ := fun n =>
    xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho (nthPrimeEquiv n)
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    dsimp only [f, xiZeroCopyLineReflectionPrimeIncidenceSchattenMass,
      primeGammaCofinalBocksteinSchattenMass]
    rw [Real.rpow_one]
    exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  change
    (∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n)
      atTop (nhds L)) ↔ _
  rw [exists_tendsto_sum_range_iff_summable_of_nonneg f hf]
  change
    Summable
        ((xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho) ∘
          nthPrimeEquiv) ↔
      Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho)
  have henum :
      Summable
          ((xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho) ∘
            nthPrimeEquiv) ↔
        Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho) :=
    nthPrimeEquiv.summable_iff
  exact henum

/-- Ordered convergence of the actual trace-one rational-adelic residue mass. -/
def XiReflectionIncidenceTraceOneSourceOrdinaryConvergent
    (rho : XiDivisorSupport) : Prop :=
  ∃ L : ℝ,
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        xiReflectionIncidencePrimeTraceOneSourceMass rho (nthPrimeEquiv n))
      atTop (nhds L)

/-- The explicit source series converges ordinarily exactly when the endpoint incidence series is
summable. -/
theorem xiReflectionIncidenceTraceOneSourceOrdinaryConvergent_iff_summable
    (rho : XiDivisorSupport) :
    XiReflectionIncidenceTraceOneSourceOrdinaryConvergent rho ↔
      Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho) := by
  let f : ℕ → ℝ := fun n =>
    xiReflectionIncidencePrimeTraceOneSourceMass rho (nthPrimeEquiv n)
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    exact xiReflectionIncidencePrimeTraceOneSourceMass_nonneg rho (nthPrimeEquiv n)
  change
    (∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n)
      atTop (nhds L)) ↔ _
  rw [exists_tendsto_sum_range_iff_summable_of_nonneg f hf]
  change
    Summable
        ((xiReflectionIncidencePrimeTraceOneSourceMass rho) ∘ nthPrimeEquiv) ↔
      Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho)
  have henum' :
      Summable
          ((xiReflectionIncidencePrimeTraceOneSourceMass rho) ∘ nthPrimeEquiv) ↔
        Summable (xiReflectionIncidencePrimeTraceOneSourceMass rho) :=
    nthPrimeEquiv.summable_iff
  exact henum'.trans
    (summable_xiReflectionIncidencePrimeTraceOneSourceMass_iff rho)

/-- Local trace-one source convergence is equivalent to critical-line placement. -/
theorem xiReflectionIncidenceTraceOneSourceOrdinaryConvergent_iff_criticalLine
    (rho : XiDivisorSupport) :
    XiReflectionIncidenceTraceOneSourceOrdinaryConvergent rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [xiReflectionIncidenceTraceOneSourceOrdinaryConvergent_iff_summable,
    summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_one_iff]

/-- Concrete global source producer: every multiplicity-faithful trace-one paracyclic residue
series converges in increasing-prime order without damping. -/
def XiReflectionIncidenceTraceOneSourceOrdinaryLanding : Prop :=
  ∀ rho : XiDivisorSupport,
    XiReflectionIncidenceTraceOneSourceOrdinaryConvergent rho

/-- The ordinary source landing is exactly the endpoint nuclear incidence admission. -/
theorem xiReflectionIncidenceTraceOneSourceOrdinaryLanding_iff_nuclearAdmission :
    XiReflectionIncidenceTraceOneSourceOrdinaryLanding ↔
      XiReflectionIncidenceNuclearSourceAdmission := by
  apply forall_congr'
  intro rho
  exact xiReflectionIncidenceTraceOneSourceOrdinaryConvergent_iff_summable rho

/-- **Frankenstein endpoint.**  Unregularized ordered convergence of the actual trace-one source
residue series for every Xi divisor fibre is equivalent to RH. -/
theorem riemannHypothesis_iff_xiReflectionIncidenceTraceOneSourceOrdinaryLanding :
    RiemannHypothesis ↔
      XiReflectionIncidenceTraceOneSourceOrdinaryLanding :=
  riemannHypothesis_iff_xiReflectionIncidenceNuclearSourceAdmission.trans
    xiReflectionIncidenceTraceOneSourceOrdinaryLanding_iff_nuclearAdmission.symm

end

end RHTower
