import GaloisForLFunctions.RHTower.PrimeDepthBVWoldReesCoronaQuotient
import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinDeterminantTransgression

/-!
# Cofinal Gamma Bockstein to Route-R Rees--corona comparison

The all-prime Gamma Bockstein and the local Rees--corona quotient were
previously constructed from different source presentations.  This file
gives their literal coefficient-faithful comparison.

On every ordinary-prime adjacent-depth edge, the signed Bockstein
coefficient is the negative Rees--corona weight times a nowhere-zero graded
factor.  The factor is defined at neutral grade as one and by the exact
quotient away from neutral grade.  Its nonvanishing is not an assumption:
it follows from the sharp Bockstein and BV--Wold edge classifications.

Consequently the cofinal determinant transgression and the physical corona
microstalk have exactly the same zero radical, before Xi specialization and
without fixed-ideal preservation.  On the retained rational-adelic class,
the comparison carries the actual leading Xi jet with prime, depth, divisor,
and multiplicity provenance intact.
-/

namespace RHTower

noncomputable section

/-- Nowhere-zero graded change of coordinates from the adjacent-depth
Route-R corona weight to the signed cofinal Gamma Bockstein coefficient. -/
def primeGammaBocksteinReesCoronaFactor
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  if t = 0 then 1 else
    -(primeGammaCofinalBocksteinCoefficient t p /
      primeDepthBVWoldReesCoronaWeight t
        (ccmRationalAdelicPrimeRelativeXiCellZero p)
        (ccmRationalAdelicPrimeRelativeXiCellOne p))

private theorem primeDepthBVWoldReesCoronaWeight_adjacent_ne_zero
    {t : ℝ} (p : Nat.Primes) (ht : t ≠ 0) :
    primeDepthBVWoldReesCoronaWeight t
        (ccmRationalAdelicPrimeRelativeXiCellZero p)
        (ccmRationalAdelicPrimeRelativeXiCellOne p) ≠ 0 := by
  rw [primeDepthBVWoldReesCoronaWeight]
  exact div_ne_zero
    (mul_ne_zero ht (ccmRationalAdelicPrimeRelativeXiConnection_pos p).ne')
    (mul_ne_zero
      (xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero
        (ccmRationalAdelicPrimeRelativeXiCellZero p))
      (xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero
        (ccmRationalAdelicPrimeRelativeXiCellOne p)))

/-- The comparison factor never erases a grade or an ordinary-prime edge. -/
theorem primeGammaBocksteinReesCoronaFactor_ne_zero
    (t : ℝ) (p : Nat.Primes) :
    primeGammaBocksteinReesCoronaFactor t p ≠ 0 := by
  by_cases ht : t = 0
  · simp [primeGammaBocksteinReesCoronaFactor, ht]
  · rw [primeGammaBocksteinReesCoronaFactor, if_neg ht]
    exact neg_ne_zero.mpr (div_ne_zero
      ((primeGammaCofinalBocksteinCoefficient_eq_zero_iff t p).not.mpr ht)
      (primeDepthBVWoldReesCoronaWeight_adjacent_ne_zero p ht))

/-- The graded comparison preserves the positive coorientation after the
explicit reflection-odd sign is removed. -/
theorem primeGammaBocksteinReesCoronaFactor_pos
    (t : ℝ) (p : Nat.Primes) :
    0 < primeGammaBocksteinReesCoronaFactor t p := by
  by_cases ht0 : t = 0
  · simp [primeGammaBocksteinReesCoronaFactor, ht0]
  · rw [primeGammaBocksteinReesCoronaFactor, if_neg ht0]
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
    have hdensity : 0 < primeActivationOccupancyFisherDensity p := by
      rw [primeActivationOccupancyFisherDensity_eq]
      positivity
    have hden : 0 <
        xiGammaEulerPrimitivePrimeDepthLogClock
            (ccmRationalAdelicPrimeRelativeXiCellZero p) *
          xiGammaEulerPrimitivePrimeDepthLogClock
            (ccmRationalAdelicPrimeRelativeXiCellOne p) :=
      mul_pos
        (xiGammaEulerPrimitivePrimeDepthLogClock_pos
          (ccmRationalAdelicPrimeRelativeXiCellZero p))
        (xiGammaEulerPrimitivePrimeDepthLogClock_pos
          (ccmRationalAdelicPrimeRelativeXiCellOne p))
    rcases lt_or_gt_of_ne ht0 with htneg | htpos
    · have hpow : (p : ℝ) ^ t < (p : ℝ) ^ (-t) :=
        Real.strictMono_rpow_of_base_gt_one hp1 (by linarith)
      have htwist :
          primeActivationOccupancyFisherTwist t p <
            primeActivationOccupancyFisherTwist (-t) p := by
        rw [primeActivationOccupancyFisherTwist,
          primeActivationOccupancyFisherTwist]
        exact mul_lt_mul_of_pos_right hpow hdensity
      have hbeta : 0 < primeGammaCofinalBocksteinCoefficient t p := by
        rw [primeGammaCofinalBocksteinCoefficient]
        linarith
      have hweight : primeDepthBVWoldReesCoronaWeight t
          (ccmRationalAdelicPrimeRelativeXiCellZero p)
          (ccmRationalAdelicPrimeRelativeXiCellOne p) < 0 := by
        rw [primeDepthBVWoldReesCoronaWeight]
        exact div_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos htneg
            (ccmRationalAdelicPrimeRelativeXiConnection_pos p)) hden
      exact neg_pos.mpr (div_neg_of_pos_of_neg hbeta hweight)
    · have hpow : (p : ℝ) ^ (-t) < (p : ℝ) ^ t :=
        Real.strictMono_rpow_of_base_gt_one hp1 (by linarith)
      have htwist :
          primeActivationOccupancyFisherTwist (-t) p <
            primeActivationOccupancyFisherTwist t p := by
        rw [primeActivationOccupancyFisherTwist,
          primeActivationOccupancyFisherTwist]
        exact mul_lt_mul_of_pos_right hpow hdensity
      have hbeta : primeGammaCofinalBocksteinCoefficient t p < 0 := by
        rw [primeGammaCofinalBocksteinCoefficient]
        linarith
      have hweight : 0 < primeDepthBVWoldReesCoronaWeight t
          (ccmRationalAdelicPrimeRelativeXiCellZero p)
          (ccmRationalAdelicPrimeRelativeXiCellOne p) := by
        rw [primeDepthBVWoldReesCoronaWeight]
        exact div_pos
          (mul_pos htpos
            (ccmRationalAdelicPrimeRelativeXiConnection_pos p)) hden
      exact neg_pos.mpr (div_neg_of_neg_of_pos hbeta hweight)

/-- Exact pre-divisor coefficient comparison.  No critical-line or
fixed-ideal premise enters the identity. -/
theorem primeGammaCofinalBocksteinCoefficient_eq_reesCoronaWeight
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinCoefficient t p =
      -primeGammaBocksteinReesCoronaFactor t p *
        primeDepthBVWoldReesCoronaWeight t
          (ccmRationalAdelicPrimeRelativeXiCellZero p)
          (ccmRationalAdelicPrimeRelativeXiCellOne p) := by
  by_cases ht : t = 0
  · subst t
    simp [primeGammaCofinalBocksteinCoefficient,
      primeDepthBVWoldReesCoronaWeight]
  · rw [primeGammaBocksteinReesCoronaFactor, if_neg ht]
    field_simp [primeDepthBVWoldReesCoronaWeight_adjacent_ne_zero p ht]

/-- **Metric port identification.**  Squared determinant-transgression
energy is exactly a positive graded multiple of the fixed-source Route-R
Stokes excess.  This identifies the cofinal Gamma and Rees--corona physical
rank ports, rather than merely comparing their zero sets. -/
theorem primeGammaCofinalBocksteinEnergy_eq_factor_sq_mul_stokesExcess
    (t : ℝ) (p : Nat.Primes) (c : ℂ) :
    primeGammaCofinalBocksteinCoefficient t p ^ 2 * Complex.normSq c =
      primeGammaBocksteinReesCoronaFactor t p ^ 2 *
        primeDepthBVWoldSourcePolarizationStokesExcess t
          (ccmRationalAdelicPrimeRelativeXiCellZero p)
          (ccmRationalAdelicPrimeRelativeXiCellOne p) c := by
  rw [primeDepthBVWoldSourcePolarizationStokesExcess_eq,
    primeGammaCofinalBocksteinCoefficient_eq_reesCoronaWeight,
    primeDepthBVWoldReesCoronaWeight]
  field_simp
    [xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero
      (ccmRationalAdelicPrimeRelativeXiCellZero p),
     xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero
      (ccmRationalAdelicPrimeRelativeXiCellOne p)]

/-- Equivalent corona form of the metric port identification. -/
theorem primeGammaCofinalBocksteinEnergy_eq_factor_sq_mul_coronaCorrection
    (t : ℝ) (p : Nat.Primes) (c : ℂ) :
    primeGammaCofinalBocksteinCoefficient t p ^ 2 * Complex.normSq c =
      primeGammaBocksteinReesCoronaFactor t p ^ 2 *
        GaloisForLFunctions.IrregularStokes.CoronaSchur.coronaCorrection
          (primeDepthBVWoldReesCoronaCoupling t
            (ccmRationalAdelicPrimeRelativeXiCellZero p)
            (ccmRationalAdelicPrimeRelativeXiCellOne p))
          primeDepthBVWoldReesCoronaMetric
          (primeDepthBVWoldReesCoronaRealification c) 0 := by
  rw [primeDepthBVWoldReesCoronaCorrection_scalarLift_eq_stokesExcess]
  exact primeGammaCofinalBocksteinEnergy_eq_factor_sq_mul_stokesExcess
    t p c

/-- Vector-valued comparison with the literal physical corona microstalk. -/
theorem primeGammaCofinalBocksteinCoefficient_realification_eq_coronaQuotient
    (t : ℝ) (p : Nat.Primes) (c : ℂ) :
    primeGammaCofinalBocksteinCoefficient t p •
        primeDepthBVWoldReesCoronaRealification c =
      -primeGammaBocksteinReesCoronaFactor t p •
        primeDepthBVWoldReesCoronaQuotient t
          (ccmRationalAdelicPrimeRelativeXiCellZero p)
          (ccmRationalAdelicPrimeRelativeXiCellOne p)
          (primeDepthBVWoldReesCoronaScalarLift c) := by
  rw [primeDepthBVWoldReesCoronaQuotient_scalarLift]
  rw [smul_smul]
  exact congrArg
    (fun r : ℝ => r • primeDepthBVWoldReesCoronaRealification c)
    (primeGammaCofinalBocksteinCoefficient_eq_reesCoronaWeight t p)

/-- The Bockstein vector and physical corona quotient have identical zero
radicals because their comparison factor is source-derived and nonzero. -/
theorem primeGammaCofinalBocksteinCoefficient_realification_eq_zero_iff_coronaQuotient
    (t : ℝ) (p : Nat.Primes) (c : ℂ) :
    primeGammaCofinalBocksteinCoefficient t p •
          primeDepthBVWoldReesCoronaRealification c = 0 ↔
      primeDepthBVWoldReesCoronaQuotient t
          (ccmRationalAdelicPrimeRelativeXiCellZero p)
          (ccmRationalAdelicPrimeRelativeXiCellOne p)
          (primeDepthBVWoldReesCoronaScalarLift c) = 0 := by
  rw [primeGammaCofinalBocksteinCoefficient_realification_eq_coronaQuotient]
  constructor
  · intro h
    rcases smul_eq_zero.mp h with hfactor | hquotient
    · exact False.elim
        ((neg_ne_zero.mpr
          (primeGammaBocksteinReesCoronaFactor_ne_zero t p)) hfactor)
    · exact hquotient
  · rintro h
    rw [h]
    exact smul_zero _

/-- On the literal retained rational-adelic class, the comparison carries
the actual first nonzero Xi jet into the fixed physical corona quotient. -/
theorem ccmRationalAdelicPrimeXiGammaBockstein_realification_eq_physicalCorona
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    primeGammaCofinalBocksteinCoefficient
          (primeDepthBVWoldXiCenteredRate rho) p •
        primeDepthBVWoldReesCoronaRealification
          (ccmRationalAdelicPrimeXiReesCoronaCoefficient p rho
            (ccmRationalAdelicPrimeRelativeClass p)) =
      -primeGammaBocksteinReesCoronaFactor
          (primeDepthBVWoldXiCenteredRate rho) p •
        primeDepthBVWoldReesCoronaQuotient
          (primeDepthBVWoldXiCenteredRate rho)
          (ccmRationalAdelicPrimeRelativeXiCellZero p)
          (ccmRationalAdelicPrimeRelativeXiCellOne p)
          (ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison p rho
            (ccmRationalAdelicPrimeRelativeClass p)) := by
  exact primeGammaCofinalBocksteinCoefficient_realification_eq_coronaQuotient
    (primeDepthBVWoldXiCenteredRate rho) p
    (ccmRationalAdelicPrimeXiReesCoronaCoefficient p rho
      (ccmRationalAdelicPrimeRelativeClass p))

end

end RHTower
