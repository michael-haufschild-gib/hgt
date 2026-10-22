import GaloisForLFunctions.RHTower.FrankensteinThetaPluckerIntertwiningAnomaly
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPrimeTranslationAnomaly

/-!
# Theta prime-translation origin of the physical Pluecker carrier

The normalized integer translation of the fixed Hedenmalm source has conormal multiplier
`p^(-s(z))`.  At an actual Xi divisor point `z = xiSpectralPoint q`, its Dirichlet exponent is
literally the divisor point `q`.  The difference between the normalized squared gains at the two
functional-equation orientations is therefore

`p * |p^(-q)|^2 - p * |p^(-(1-conj q))|^2 = p^(-t) - p^t`,

where `t = 2 Re(q) - 1`.  Multiplication by the source-selected Fisher density gives exactly the
signed Gamma Bockstein used by the admitted lower and upper physical Pluecker carriers.

Thus the coefficient in the theta-to-Pluecker anomaly is not a divisor-fitted scalar: it is the
literal energy imbalance of one fixed source translation, observed at the two retained conormal
orientations.  Prime labels and divisor multiplicity remain unsummed.
-/

open Complex

namespace RHTower.HedenmalmThetaSource

noncomputable section

open RHTower.HedenmalmPrimeTranslation

/-! ## Fixed source translation gains -/

/-- At a Xi divisor point, the source conormal Dirichlet exponent is the original divisor point. -/
theorem thetaPrimeTranslation_dirichletExponent_xiSpectralPoint
    (q : RHTower.XiZeroCopy) :
    dirichletExponent (RHTower.xiSpectralPoint q) = (q.1 : ℂ) := by
  rw [dirichletExponent, RHTower.xiSpectralPoint]
  have hI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I]
    ring
  calc
    1 / 2 + Complex.I * (((q.1 : ℂ) - 1 / 2) * (-Complex.I)) =
        1 / 2 + ((q.1 : ℂ) - 1 / 2) * (Complex.I * (-Complex.I)) := by ring
    _ = (q.1 : ℂ) := by rw [hI]; ring

/-- Conormal multiplier of the fixed normalized prime translation on one Xi divisor mode. -/
def frankensteinThetaPrimeTranslationGain
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) : ℂ :=
  ((p : ℂ) ^
    (-(dirichletExponent (RHTower.xiSpectralPoint q))))

/-- The gain is exactly the coefficient supplied by the fixed source translation law, for every
test function.  No horizontal coefficient is inserted here. -/
theorem sourceEvaluation_integerShift_xiSpectralPoint
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) (f : ℝ → ℂ) :
    sourceEvaluation (RHTower.xiSpectralPoint q)
        (integerShift (p : ℕ) f) =
      frankensteinThetaPrimeTranslationGain q p *
        sourceEvaluation (RHTower.xiSpectralPoint q) f := by
  exact sourceEvaluation_integerShift (RHTower.xiSpectralPoint q) f p.2.pos

/-- Prime-normalized squared conormal gain of the fixed source translation. -/
def frankensteinThetaPrimeTranslationEnergy
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) : ℝ :=
  (p : ℝ) * Complex.normSq (frankensteinThetaPrimeTranslationGain q p)

/-- Source translation energy is the negative centered horizontal character. -/
theorem frankensteinThetaPrimeTranslationEnergy_eq
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) :
    frankensteinThetaPrimeTranslationEnergy q p =
      (p : ℝ) ^ (-RHTower.primeDepthBVWoldXiCenteredRate q.1) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [frankensteinThetaPrimeTranslationEnergy,
    frankensteinThetaPrimeTranslationGain,
    thetaPrimeTranslation_dirichletExponent_xiSpectralPoint,
    Complex.normSq_eq_norm_sq]
  change (p : ℝ) *
      ‖((p : ℝ) : ℂ) ^ (-(q.1 : ℂ))‖ ^ 2 =
    (p : ℝ) ^ (-RHTower.primeDepthBVWoldXiCenteredRate q.1)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]
  change (p : ℝ) * ((p : ℝ) ^ (-((q.1 : ℂ).re))) ^ 2 =
    (p : ℝ) ^ (-(2 * (q.1 : ℂ).re - 1))
  calc
    (p : ℝ) * ((p : ℝ) ^ (-((q.1 : ℂ).re))) ^ 2 =
        (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-2 * (q.1 : ℂ).re) := by
      rw [Real.rpow_one]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      congr 1
      norm_num
      ring
    _ = (p : ℝ) ^ ((1 : ℝ) + (-2 * (q.1 : ℂ).re)) := by
      rw [← Real.rpow_add hp]
    _ = (p : ℝ) ^ (-(2 * (q.1 : ℂ).re - 1)) := by
      congr 1
      ring

/-- Functional-equation reflection negates centered horizontal rate. -/
theorem primeDepthBVWoldXiCenteredRate_lineConj
    (q : RHTower.XiZeroCopy) :
    RHTower.primeDepthBVWoldXiCenteredRate
        (RHTower.xiZeroCopyLineConjEquiv q).1 =
      -RHTower.primeDepthBVWoldXiCenteredRate q.1 := by
  rw [RHTower.primeDepthBVWoldXiCenteredRate,
    RHTower.primeDepthBVWoldXiCenteredRate]
  change 2 * (1 - star (q.1 : ℂ)).re - 1 =
    -(2 * (q.1 : ℂ).re - 1)
  simp
  ring

/-- Reflected source translation energy is the positive centered character. -/
theorem frankensteinThetaPrimeTranslationEnergy_lineConj_eq
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) :
    frankensteinThetaPrimeTranslationEnergy
        (RHTower.xiZeroCopyLineConjEquiv q) p =
      (p : ℝ) ^ RHTower.primeDepthBVWoldXiCenteredRate q.1 := by
  rw [frankensteinThetaPrimeTranslationEnergy_eq,
    primeDepthBVWoldXiCenteredRate_lineConj, neg_neg]

/-- The two retained normalized source energies are reciprocal before any scalarization. -/
theorem frankensteinThetaPrimeTranslationEnergy_mul_lineConj
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) :
    frankensteinThetaPrimeTranslationEnergy q p *
        frankensteinThetaPrimeTranslationEnergy
          (RHTower.xiZeroCopyLineConjEquiv q) p = 1 := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [frankensteinThetaPrimeTranslationEnergy_eq,
    frankensteinThetaPrimeTranslationEnergy_lineConj_eq,
    ← Real.rpow_add hp]
  simp

/-- Exact producer reduction: simultaneous contractivity of the two normalized conormal
orientations at one retained prime is equivalent to the critical line.  Reflection supplies
reciprocity unconditionally; the missing source law must supply both inequalities. -/
theorem frankensteinThetaPrimeTranslation_both_energy_le_one_iff
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) :
    (frankensteinThetaPrimeTranslationEnergy q p ≤ 1 ∧
        frankensteinThetaPrimeTranslationEnergy
          (RHTower.xiZeroCopyLineConjEquiv q) p ≤ 1) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  let t := RHTower.primeDepthBVWoldXiCenteredRate q.1
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hmono := Real.strictMono_rpow_of_base_gt_one hp1
  constructor
  · rintro ⟨hforward, hreflected⟩
    rw [frankensteinThetaPrimeTranslationEnergy_eq] at hforward
    rw [frankensteinThetaPrimeTranslationEnergy_lineConj_eq] at hreflected
    have hneg : -t ≤ 0 := (hmono.le_iff_le).mp (by simpa [t] using hforward)
    have hpos : t ≤ 0 := (hmono.le_iff_le).mp (by simpa [t] using hreflected)
    have ht : t = 0 := by linarith
    exact (RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 ht
  · intro hline
    have ht : RHTower.primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    rw [frankensteinThetaPrimeTranslationEnergy_eq,
      frankensteinThetaPrimeTranslationEnergy_lineConj_eq, ht, neg_zero,
      Real.rpow_zero]
    exact ⟨le_rfl, le_rfl⟩

/-- The energy identity remains visible on arbitrary source test functions. -/
theorem prime_mul_normSq_sourceEvaluation_integerShift_xiSpectralPoint
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) (f : ℝ → ℂ) :
    (p : ℝ) * Complex.normSq
        (sourceEvaluation (RHTower.xiSpectralPoint q)
          (integerShift (p : ℕ) f)) =
      frankensteinThetaPrimeTranslationEnergy q p *
        Complex.normSq
          (sourceEvaluation (RHTower.xiSpectralPoint q) f) := by
  rw [sourceEvaluation_integerShift_xiSpectralPoint,
    Complex.normSq_mul, frankensteinThetaPrimeTranslationEnergy]
  ring

/-! ## Exact source imbalance and Pluecker landing -/

/-- Fisher-weighted imbalance of the same prime translation at the two retained conormal
orientations. -/
def frankensteinThetaPrimeTranslationImbalance
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) : ℝ :=
  RHTower.primeActivationOccupancyFisherDensity p *
    (frankensteinThetaPrimeTranslationEnergy q p -
      frankensteinThetaPrimeTranslationEnergy
        (RHTower.xiZeroCopyLineConjEquiv q) p)

/-- The fixed-source conormal energy imbalance is exactly the horizontal Gamma Bockstein. -/
theorem frankensteinThetaPrimeTranslationImbalance_eq_sourceZeroHorizontalPrimeCarrier
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) :
    frankensteinThetaPrimeTranslationImbalance q p =
      RHTower.sourceZeroHorizontalPrimeCarrier q p := by
  rw [frankensteinThetaPrimeTranslationImbalance,
    frankensteinThetaPrimeTranslationEnergy_eq,
    frankensteinThetaPrimeTranslationEnergy_lineConj_eq,
    RHTower.sourceZeroHorizontalPrimeCarrier,
    RHTower.primeGammaCofinalBocksteinCoefficient,
    RHTower.primeActivationOccupancyFisherTwist,
    RHTower.primeActivationOccupancyFisherTwist]
  ring

/-- Source imbalance reverses orientation under critical-line reflection. -/
@[simp] theorem frankensteinThetaPrimeTranslationImbalance_lineConj
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) :
    frankensteinThetaPrimeTranslationImbalance
        (RHTower.xiZeroCopyLineConjEquiv q) p =
      -frankensteinThetaPrimeTranslationImbalance q p := by
  rw [frankensteinThetaPrimeTranslationImbalance_eq_sourceZeroHorizontalPrimeCarrier,
    frankensteinThetaPrimeTranslationImbalance_eq_sourceZeroHorizontalPrimeCarrier,
    RHTower.sourceZeroHorizontalPrimeCarrier_reflection]

/-- One retained prime label detects equality of the two source translation energies exactly on
the critical line. -/
theorem frankensteinThetaPrimeTranslationImbalance_eq_zero_iff
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) :
    frankensteinThetaPrimeTranslationImbalance q p = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [frankensteinThetaPrimeTranslationImbalance_eq_sourceZeroHorizontalPrimeCarrier,
    RHTower.sourceZeroHorizontalPrimeCarrier_eq_zero_iff]

/-- Every lower physical Pluecker coordinate is the literal source translation imbalance times
its positive reporter; there is no divisor-fitted coefficient left in the formula. -/
theorem frankensteinXiLowerPhysicalPluckerHilbertCarrier_apply_eq_primeTranslationImbalance
    (q : RHTower.XiZeroCopy) (z : ℕ × ℕ) :
    frankensteinXiLowerPhysicalPluckerHilbertCarrier q z =
      frankensteinPluckerLowerVertexReporter z.1 1 4 z.2 *
        (frankensteinThetaPrimeTranslationImbalance q
          (RHTower.nthPrimeSubtype z.2) : ℂ) := by
  rw [frankensteinXiLowerPhysicalPluckerHilbertCarrier_apply,
    frankensteinXiLowerPrimeCarrier,
    frankensteinThetaPrimeTranslationImbalance_eq_sourceZeroHorizontalPrimeCarrier]

/-- Same fixed source translation imbalance lands in the upper retained orientation. -/
theorem frankensteinXiUpperPhysicalPluckerHilbertCarrier_apply_eq_primeTranslationImbalance
    (q : RHTower.XiZeroCopy) (z : ℕ × ℕ) :
    frankensteinXiUpperPhysicalPluckerHilbertCarrier q z =
      frankensteinPluckerUpperVertexReporter z.1 4 1 z.2 *
        (frankensteinThetaPrimeTranslationImbalance q
          (RHTower.nthPrimeSubtype z.2) : ℂ) := by
  rw [frankensteinXiUpperPhysicalPluckerHilbertCarrier_apply,
    frankensteinXiUpperPrimeCarrier,
    frankensteinThetaPrimeTranslationImbalance_eq_sourceZeroHorizontalPrimeCarrier]

/-- The previously isolated theta-to-Pluecker anomaly is therefore sourced by the normalized
prime-translation energy imbalance, and its simultaneous vanishing remains exactly the critical
line without discarding either orientation. -/
theorem frankensteinThetaPrimeTranslationBothPluckerAnomalies_eq_zero_iff
    (q : RHTower.XiZeroCopy) :
    (frankensteinThetaXiLowerPluckerIntertwiningAnomaly q
          (RHTower.thetaXiDivisorEigenvector q) = 0 ∧
        frankensteinThetaXiUpperPluckerIntertwiningAnomaly q
          (RHTower.thetaXiDivisorEigenvector q) = 0) ↔
      (q.1 : ℂ).re = 1 / 2 :=
  frankensteinThetaXiBothPluckerIntertwiningAnomalies_eq_zero_iff q

end

end RHTower.HedenmalmThetaSource
