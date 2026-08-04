import GaloisForLFunctions.RHTower.PrimeDepthBVWoldPositiveStokesPolarization
import GaloisForLFunctions.RHTower.CCMRationalAdelicPrimeIsotropyStokesRegulator
import GaloisForLFunctions.HTGeometry.StokesCoronaSchurVanishing

/-!
# Route R Rees--corona quotient and the two-lift separation law

The positive resolved BV--Wold frame and the scalar fixed-source frame determine
two different lifts of the same clock-normalized Xi conormal into a two-real-
dimensional corona extension.  The resolved lift is the harmonic graph lift, so
its relative vanishing coordinate is unconditionally zero.  The scalar physical
lift has hidden coordinate zero; its relative coordinate is the normalized
Route-R mixing coefficient, and its corona energy is exactly the fixed-source
Stokes excess.

Consequently resolved source exactness alone does not annihilate the physical
scalar quotient.  Identifying the two lifts is equivalent, on the certified
witness edge and actual nonzero Xi conormal, to critical-line placement.  This
isolates the precise source-to-corona admission theorem still missing from Route R.
-/

open Complex
open GaloisForLFunctions.IrregularStokes

namespace RHTower

noncomputable section

/-! ## Explicit coefficient-faithful Rees--corona model -/

/-- Realification of the one-dimensional complex physical conormal. -/
abbrev PrimeDepthBVWoldReesCoronaCoordinate := Fin 2 → ℝ

/-- Coefficient-faithful realification; coordinate zero is the real part and
coordinate one is the imaginary part. -/
def primeDepthBVWoldReesCoronaRealification
    (c : ℂ) : PrimeDepthBVWoldReesCoronaCoordinate :=
  ![c.re, c.im]

/-- Normalized Route-R off-diagonal coefficient retaining centered rate,
prime/depth edge, and both Wold--Gamma clocks. -/
def primeDepthBVWoldReesCoronaWeight
    (a : ℝ) (i j : PrimeDepthBVWoldCell) : ℝ :=
  a * primeDepthBVWoldConnection i j /
    (xiGammaEulerPrimitivePrimeDepthLogClock i *
      xiGammaEulerPrimitivePrimeDepthLogClock j)

/-- The coefficient-generated corona coupling on the realified physical fibre. -/
def primeDepthBVWoldReesCoronaCoupling
    (a : ℝ) (i j : PrimeDepthBVWoldCell) : Matrix (Fin 2) (Fin 2) ℝ :=
  primeDepthBVWoldReesCoronaWeight a i j • 1

/-- Positive hidden corona metric. -/
def primeDepthBVWoldReesCoronaMetric : Matrix (Fin 2) (Fin 2) ℝ := 1

/-- Fixed same-fibre physical scalar lift: the conormal occupies the boundary
coordinate and has no hidden compensator. -/
def primeDepthBVWoldReesCoronaScalarLift
    (c : ℂ) : PrimeDepthBVWoldReesCoronaCoordinate ×
      PrimeDepthBVWoldReesCoronaCoordinate :=
  (primeDepthBVWoldReesCoronaRealification c, 0)

/-- Positive resolved lift: harmonic extension in the coefficient-generated
corona complex. -/
def primeDepthBVWoldReesCoronaResolvedLift
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
      PrimeDepthBVWoldReesCoronaCoordinate ×
        PrimeDepthBVWoldReesCoronaCoordinate :=
  CoronaSchur.harmonicGraph
    (primeDepthBVWoldReesCoronaCoupling a i j)
    primeDepthBVWoldReesCoronaMetric
    (primeDepthBVWoldReesCoronaRealification c)

/-- Relative vanishing-cycle coordinate of a Route-R corona lift. -/
def primeDepthBVWoldReesCoronaQuotient
    (a : ℝ) (i j : PrimeDepthBVWoldCell) :
      (PrimeDepthBVWoldReesCoronaCoordinate ×
          PrimeDepthBVWoldReesCoronaCoordinate) →ₗ[ℝ]
        PrimeDepthBVWoldReesCoronaCoordinate :=
  CoronaSchur.relativeVanishingMap
    (primeDepthBVWoldReesCoronaCoupling a i j)
    primeDepthBVWoldReesCoronaMetric

/-! ## Exact quotient calculations -/

theorem primeDepthBVWoldReesCoronaCoupling_mulVec
    (a : ℝ) (i j : PrimeDepthBVWoldCell)
    (x : PrimeDepthBVWoldReesCoronaCoordinate) :
    Matrix.mulVec (primeDepthBVWoldReesCoronaCoupling a i j) x =
      primeDepthBVWoldReesCoronaWeight a i j • x := by
  rw [primeDepthBVWoldReesCoronaCoupling, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- The scalar physical lift reports the normalized Route-R mixing coefficient. -/
theorem primeDepthBVWoldReesCoronaQuotient_scalarLift
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    primeDepthBVWoldReesCoronaQuotient a i j
        (primeDepthBVWoldReesCoronaScalarLift c) =
      primeDepthBVWoldReesCoronaWeight a i j •
        primeDepthBVWoldReesCoronaRealification c := by
  simp [primeDepthBVWoldReesCoronaQuotient,
    primeDepthBVWoldReesCoronaScalarLift,
    primeDepthBVWoldReesCoronaMetric, CoronaSchur.relativeVanishingMap,
    CoronaSchur.coronaShift, primeDepthBVWoldReesCoronaCoupling,
    Matrix.smul_mulVec]

/-- Source exactness kills the resolved harmonic lift unconditionally. -/
theorem primeDepthBVWoldReesCoronaQuotient_resolvedLift
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    primeDepthBVWoldReesCoronaQuotient a i j
        (primeDepthBVWoldReesCoronaResolvedLift a i j c) = 0 := by
  apply (CoronaSchur.harmonicGraph_relativeVanishing_exact
    (primeDepthBVWoldReesCoronaCoupling a i j)
    primeDepthBVWoldReesCoronaMetric
    (primeDepthBVWoldReesCoronaResolvedLift a i j c)).2
  exact ⟨primeDepthBVWoldReesCoronaRealification c, rfl⟩

/-- Corona energy of the physical scalar lift is exactly the Route-R positive
Stokes excess, not merely proportional to it. -/
theorem primeDepthBVWoldReesCoronaCorrection_scalarLift_eq_stokesExcess
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    CoronaSchur.coronaCorrection
        (primeDepthBVWoldReesCoronaCoupling a i j)
        primeDepthBVWoldReesCoronaMetric
        (primeDepthBVWoldReesCoronaRealification c) 0 =
      primeDepthBVWoldSourcePolarizationStokesExcess a i j c := by
  rw [primeDepthBVWoldSourcePolarizationStokesExcess_eq]
  simp [CoronaSchur.coronaCorrection, CoronaSchur.coronaShift,
    primeDepthBVWoldReesCoronaMetric,
    primeDepthBVWoldReesCoronaCoupling,
    Matrix.smul_mulVec,
    primeDepthBVWoldReesCoronaWeight,
    primeDepthBVWoldReesCoronaRealification,
    Complex.normSq_apply]
  ring

/-- Two canonical lifts agree exactly when the physical scalar quotient vanishes. -/
theorem primeDepthBVWoldReesCoronaScalarLift_eq_resolvedLift_iff
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    primeDepthBVWoldReesCoronaScalarLift c =
        primeDepthBVWoldReesCoronaResolvedLift a i j c ↔
      primeDepthBVWoldReesCoronaQuotient a i j
        (primeDepthBVWoldReesCoronaScalarLift c) = 0 := by
  constructor
  · intro h
    rw [h]
    exact primeDepthBVWoldReesCoronaQuotient_resolvedLift a i j c
  · intro h
    have hrange :=
      (CoronaSchur.harmonicGraph_relativeVanishing_exact
        (primeDepthBVWoldReesCoronaCoupling a i j)
        primeDepthBVWoldReesCoronaMetric
        (primeDepthBVWoldReesCoronaScalarLift c)).1 h
    obtain ⟨x, hx⟩ := hrange
    have hfirst : x = primeDepthBVWoldReesCoronaRealification c := by
      have := congrArg Prod.fst hx
      simpa [primeDepthBVWoldReesCoronaScalarLift,
        CoronaSchur.harmonicGraph] using this
    subst x
    exact hx.symm

/-- Lift comparison is exactly zero fixed-source excess. -/
theorem primeDepthBVWoldReesCoronaScalarLift_eq_resolvedLift_iff_stokesExcess_zero
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    primeDepthBVWoldReesCoronaScalarLift c =
        primeDepthBVWoldReesCoronaResolvedLift a i j c ↔
      primeDepthBVWoldSourcePolarizationStokesExcess a i j c = 0 := by
  rw [primeDepthBVWoldReesCoronaScalarLift_eq_resolvedLift_iff]
  rw [primeDepthBVWoldReesCoronaQuotient_scalarLift,
    primeDepthBVWoldSourcePolarizationStokesExcess_eq]
  simp [primeDepthBVWoldReesCoronaWeight,
    primeDepthBVWoldReesCoronaRealification,
    Complex.ext_iff]
  tauto

/-! ## Rational-adelic source comparison into the corona complex -/

/-- Coefficient carried from actual rational-adelic relative `H1` by its
period-one Stokes regulator and the first nonzero Xi jet. -/
def ccmRationalAdelicPrimeXiReesCoronaCoefficient
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) : ℂ :=
  ccmRationalAdelicPrimeRelativeH1StokesRegulator p x *
    iteratedDeriv (xiSupportMultiplicity rho) XiC
      (xiSpectralPointSupport rho)

/-- Strict resolved source landing in the harmonic corona graph.  Prime,
depth, divisor, and multiplicity-leading coefficient remain explicit. -/
def ccmRationalAdelicPrimeXiResolvedReesCoronaComparison
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :=
  primeDepthBVWoldReesCoronaResolvedLift
    (primeDepthBVWoldXiCenteredRate rho)
    (ccmRationalAdelicPrimeRelativeXiCellZero p)
    (ccmRationalAdelicPrimeRelativeXiCellOne p)
    (ccmRationalAdelicPrimeXiReesCoronaCoefficient p rho x)

/-- Fixed same-fibre physical landing of the same retained source
coefficient, with hidden compensator set to zero. -/
def ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :=
  primeDepthBVWoldReesCoronaScalarLift
    (ccmRationalAdelicPrimeXiReesCoronaCoefficient p rho x)

/-- The retained source class carries exactly the actual leading Xi jet. -/
theorem ccmRationalAdelicPrimeXiReesCoronaCoefficient_class
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiReesCoronaCoefficient p rho
        (ccmRationalAdelicPrimeRelativeClass p) =
      iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho) := by
  rw [ccmRationalAdelicPrimeXiReesCoronaCoefficient,
    ccmRationalAdelicPrimeRelativeH1StokesRegulator_class, one_mul]

/-- Source `D₁D₀=0` becomes literal zero relative corona coordinate on the
resolved rational-adelic landing. -/
theorem ccmRationalAdelicPrimeXiResolvedReesCoronaComparison_quotient
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    primeDepthBVWoldReesCoronaQuotient
        (primeDepthBVWoldXiCenteredRate rho)
        (ccmRationalAdelicPrimeRelativeXiCellZero p)
        (ccmRationalAdelicPrimeRelativeXiCellOne p)
        (ccmRationalAdelicPrimeXiResolvedReesCoronaComparison p rho x) = 0 := by
  exact primeDepthBVWoldReesCoronaQuotient_resolvedLift _ _ _ _

/-- Exact source-to-physical comparison defect: its quotient is the
coefficient-faithful normalized BV--Wold mixing vector. -/
theorem ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison_quotient
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    primeDepthBVWoldReesCoronaQuotient
        (primeDepthBVWoldXiCenteredRate rho)
        (ccmRationalAdelicPrimeRelativeXiCellZero p)
        (ccmRationalAdelicPrimeRelativeXiCellOne p)
        (ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison p rho x) =
      primeDepthBVWoldReesCoronaWeight
          (primeDepthBVWoldXiCenteredRate rho)
          (ccmRationalAdelicPrimeRelativeXiCellZero p)
          (ccmRationalAdelicPrimeRelativeXiCellOne p) •
        primeDepthBVWoldReesCoronaRealification
          (ccmRationalAdelicPrimeXiReesCoronaCoefficient p rho x) := by
  exact primeDepthBVWoldReesCoronaQuotient_scalarLift _ _ _ _

/-- Every retained ordinary prime supplies a nonzero adjacent-depth
BV--Wold edge, independently of the divisor. -/
theorem ccmRationalAdelicPrimeRelativeXiConnection_pos
    (p : Nat.Primes) :
    0 < primeDepthBVWoldConnection
      (ccmRationalAdelicPrimeRelativeXiCellZero p)
      (ccmRationalAdelicPrimeRelativeXiCellOne p) := by
  have hp0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hp1 : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hinv : (p.1 : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hlog : 0 < Real.log (p.1 : ℝ) := Real.log_pos hp1
  rw [primeDepthBVWoldConnection,
    ccmRationalAdelicPrimeRelativeXiCellZero,
    ccmRationalAdelicPrimeRelativeXiCellOne,
    primeDepthBVFirstTraceDepthWeight_eq,
    primeDepthBVFirstTraceDepthWeight_eq,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply]
  norm_num
  nlinarith [inv_pos.mpr hp0]

/-- On the retained period-one source class, equality of resolved and fixed
physical corona landings is exactly critical-line placement.  This theorem
contains no faithfulness or line premise; it exposes the single remaining
source comparison law at every ordinary prime. -/
theorem ccmRationalAdelicPrimeXiReesCoronaComparisons_eq_iff
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) =
      ccmRationalAdelicPrimeXiResolvedReesCoronaComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison,
    ccmRationalAdelicPrimeXiResolvedReesCoronaComparison,
    ccmRationalAdelicPrimeXiReesCoronaCoefficient_class,
    primeDepthBVWoldReesCoronaScalarLift_eq_resolvedLift_iff_stokesExcess_zero,
    primeDepthBVWoldSourcePolarizationStokesExcess_eq_zero_iff
      (ccmRationalAdelicPrimeRelativeXiConnection_pos p).ne'
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho),
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-! ## Actual Xi landing and the exact remaining admission law -/

/-- On the certified nonzero source edge and actual Xi conormal, identifying
the physical scalar lift with the unconditionally exact resolved lift is
equivalent to critical-line placement. -/
theorem primeDepthBVWoldXiReesCoronaScalarLift_eq_resolvedLift_iff
    (rho : XiDivisorSupport) :
    primeDepthBVWoldReesCoronaScalarLift
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)) =
      primeDepthBVWoldReesCoronaResolvedLift
        (primeDepthBVWoldXiCenteredRate rho)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [primeDepthBVWoldReesCoronaScalarLift_eq_resolvedLift_iff_stokesExcess_zero,
    primeDepthBVWoldXiSourcePolarizationStokesExcess_witness_eq_zero_iff]

/-- The fixed physical Xi conormal lies in the zero corona quotient exactly
on the critical line.  This is the scalar admission statement that cannot be
substituted by resolved exactness. -/
theorem primeDepthBVWoldXiReesCoronaQuotient_scalarLift_eq_zero_iff
    (rho : XiDivisorSupport) :
    primeDepthBVWoldReesCoronaQuotient
        (primeDepthBVWoldXiCenteredRate rho)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        (primeDepthBVWoldReesCoronaScalarLift
          (iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho))) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [← primeDepthBVWoldReesCoronaScalarLift_eq_resolvedLift_iff]
  exact primeDepthBVWoldXiReesCoronaScalarLift_eq_resolvedLift_iff rho

/-- **Resolved-exactness/physical-admission separation.**  The first
conjunct is an unconditional source theorem.  Adding physical corona
admission is nevertheless exactly critical-line placement. -/
theorem primeDepthBVWoldXiResolvedExact_and_physicalCoronaAdmission_iff
    (rho : XiDivisorSupport) :
    (primeDepthBVWoldXiResolvedCovariantD1
          (primeDepthBVWoldXiResolvedCovariantD0
            primeDepthBVWoldXiResolvedLeadingConormal)
          rho primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
            primeDepthBVWoldWitnessTwo = 0 ∧
      primeDepthBVWoldReesCoronaQuotient
          (primeDepthBVWoldXiCenteredRate rho)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          (primeDepthBVWoldReesCoronaScalarLift
            (iteratedDeriv (xiSupportMultiplicity rho) XiC
              (xiSpectralPointSupport rho))) = 0) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [and_iff_right
    (primeDepthBVWoldXiResolvedCovariantD1_comp_D0_leadingConormal rho
      primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
      primeDepthBVWoldWitnessTwo),
    primeDepthBVWoldXiReesCoronaQuotient_scalarLift_eq_zero_iff]

/-- Any hypothetical off-line Xi divisor copy would still satisfy resolved
`D₁D₀ = 0`, while its fixed physical corona coordinate would be nonzero.
This is a direct no-go for deriving scalar admission from resolved exactness
without an independent source-to-physical lift comparison. -/
theorem primeDepthBVWoldXiResolvedExact_but_physicalCoronaNonzero_of_offLine
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    primeDepthBVWoldXiResolvedCovariantD1
          (primeDepthBVWoldXiResolvedCovariantD0
            primeDepthBVWoldXiResolvedLeadingConormal)
          rho primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
            primeDepthBVWoldWitnessTwo = 0 ∧
      primeDepthBVWoldReesCoronaQuotient
          (primeDepthBVWoldXiCenteredRate rho)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          (primeDepthBVWoldReesCoronaScalarLift
            (iteratedDeriv (xiSupportMultiplicity rho) XiC
              (xiSpectralPointSupport rho))) ≠ 0 := by
  exact ⟨
    primeDepthBVWoldXiResolvedCovariantD1_comp_D0_leadingConormal rho
      primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
      primeDepthBVWoldWitnessTwo,
    (primeDepthBVWoldXiReesCoronaQuotient_scalarLift_eq_zero_iff rho).not.mpr
      hoff⟩

/-- Exact source-to-corona admission for the fixed physical lift is RH, while
the resolved harmonic admission above is unconditional. -/
def PrimeDepthBVWoldXiPhysicalCoronaAdmitted : Prop :=
  ∀ rho : XiDivisorSupport,
    primeDepthBVWoldReesCoronaQuotient
        (primeDepthBVWoldXiCenteredRate rho)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        (primeDepthBVWoldReesCoronaScalarLift
          (iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho))) = 0

theorem primeDepthBVWoldXiPhysicalCoronaAdmitted_iff_riemannHypothesis :
    PrimeDepthBVWoldXiPhysicalCoronaAdmitted ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply primeDepthBVWoldXiSourcePolarizationStokesFlat_iff_riemannHypothesis.mp
    intro rho
    rw [← primeDepthBVWoldReesCoronaScalarLift_eq_resolvedLift_iff_stokesExcess_zero]
    exact (primeDepthBVWoldReesCoronaScalarLift_eq_resolvedLift_iff
      (primeDepthBVWoldXiCenteredRate rho)
      primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
      (iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho))).mpr (h rho)
  · intro hRH rho
    have hflat :=
      primeDepthBVWoldXiSourcePolarizationStokesFlat_iff_riemannHypothesis.mpr
        hRH rho
    have hlift :=
      (primeDepthBVWoldReesCoronaScalarLift_eq_resolvedLift_iff_stokesExcess_zero
        (primeDepthBVWoldXiCenteredRate rho)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho))).mpr hflat
    rw [hlift]
    exact primeDepthBVWoldReesCoronaQuotient_resolvedLift
      (primeDepthBVWoldXiCenteredRate rho)
      primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
      (iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho))

end

end RHTower
