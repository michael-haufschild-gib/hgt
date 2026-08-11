import GaloisForLFunctions.HTGeometry.LogSquaredTailIntegral
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldSchattenAtlasLanding
import GaloisForLFunctions.RHTower.XiHeatCassiniStieltjesOrientationDefect

/-!
# BV--Wold Fisher landing of the Stieltjes--Cassini defect

The depth-one valuation source is not trace class off the critical line, but its centered part is
square summable.  Its exact squared norm is the horizontal Xi rate squared times one universal
positive Wold mass.  The Stieltjes--Cassini orientation defect is the same rate square in a
strictly positive shifted-resolvent gauge.  Consequently the complete Route T/U defect is an
exact positively weighted source Hilbert energy, with no cancellation or RH premise.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Universal squared mass of the depth-one Wold source profile. -/
def woldDepthOneFisherMass : ℝ :=
  ∑' p : Nat.Primes, woldCoeff 1 p ^ 2

/-- Centered physical depth-one relative-log coefficient.  The trace-class seam is subtracted
before taking the source energy. -/
def xiDepthOneCenteredWoldCoefficient
    (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  primeDepthBVWoldXiRelativeLogCoefficient q.1 1 p - woldRemainder p

/-- Squared Hilbert energy of one divisor-labelled centered valuation-one source. -/
def xiDepthOneCenteredWoldEnergy (q : XiZeroCopy) : ℝ :=
  ∑' p : Nat.Primes, xiDepthOneCenteredWoldCoefficient q p ^ 2

/-- Positive gauge transporting centered horizontal source rate into shifted Cassini orientation. -/
def xiHeatCassiniBVWoldTransferGauge (y : ℝ) (q : XiZeroCopy) : ℝ :=
  let D₀ := Complex.normSq ((q.1 : ℂ) - 1 / 2) ^ 2
  let D₁ := Complex.normSq
    (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q)
  (q.1 : ℂ).im ^ 2 /
    ((D₀ * D₁) ^ 2 * (xiShiftedReciprocalSquare y q).re)

/-- Squared depth-one Wold profile is summable although the unsquared profile is not. -/
theorem summable_woldCoeff_one_sq :
    Summable (fun p : Nat.Primes => woldCoeff 1 p ^ 2) := by
  have hmajorant : Summable (fun p : Nat.Primes =>
      (Real.log (p : ℝ) / (p : ℝ)) ^ 2) :=
    GaloisForLFunctions.HTGeometry.summable_logSq_div_sq.comp_injective
      Subtype.val_injective
  apply Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_) hmajorant
  have hp : (2 : ℝ) ≤ (p : ℝ) := two_le_prime_cast p
  have hp0 : 0 < (p : ℝ) := by linarith
  have hf0 : 0 ≤ 1 - 1 / (p : ℝ) := by
    rw [sub_nonneg, div_le_one hp0]
    linarith
  have hf1 : 1 - 1 / (p : ℝ) ≤ 1 := by
    exact sub_le_self _ (div_nonneg zero_le_one hp0.le)
  have hpow : (1 - 1 / (p : ℝ)) ^ 6 ≤ 1 :=
    pow_le_one₀ hf0 hf1
  rw [woldCoeff]
  simp only [pow_one]
  calc
    (((1 - 1 / (p : ℝ)) ^ 3 * Real.log (p : ℝ) / (p : ℝ)) ^ 2) =
        (1 - 1 / (p : ℝ)) ^ 6 *
          (Real.log (p : ℝ) / (p : ℝ)) ^ 2 := by ring
    _ ≤ 1 * (Real.log (p : ℝ) / (p : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
    _ = (Real.log (p : ℝ) / (p : ℝ)) ^ 2 := one_mul _

/-- Universal Wold Fisher mass is strictly positive. -/
theorem woldDepthOneFisherMass_pos :
    0 < woldDepthOneFisherMass := by
  let p₂ : Nat.Primes := ⟨2, Nat.prime_two⟩
  rw [woldDepthOneFisherMass]
  refine Summable.tsum_pos summable_woldCoeff_one_sq (fun p => sq_nonneg _)
    p₂ ?_
  exact sq_pos_of_pos (woldCoeff_pos 1 p₂)

/-- Removing the physical seam exposes exactly centered rate times universal Wold profile. -/
theorem xiDepthOneCenteredWoldCoefficient_eq
    (q : XiZeroCopy) (p : Nat.Primes) :
    xiDepthOneCenteredWoldCoefficient q p =
      primeDepthBVWoldXiCenteredRate q.1 * woldCoeff 1 p := by
  rw [xiDepthOneCenteredWoldCoefficient,
    primeDepthBVWoldXiRelativeLogCoefficient_eq]
  ring

/-- Every divisor-labelled centered Wold source has finite squared energy. -/
theorem summable_xiDepthOneCenteredWoldCoefficient_sq (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes => xiDepthOneCenteredWoldCoefficient q p ^ 2) := by
  have h := summable_woldCoeff_one_sq.mul_left
    (primeDepthBVWoldXiCenteredRate q.1 ^ 2)
  exact h.congr fun p => by
    rw [xiDepthOneCenteredWoldCoefficient_eq]
    ring

/-- Exact source norm: only divisor dependence is centered horizontal rate squared. -/
theorem xiDepthOneCenteredWoldEnergy_eq_rate_sq_mul_mass (q : XiZeroCopy) :
    xiDepthOneCenteredWoldEnergy q =
      primeDepthBVWoldXiCenteredRate q.1 ^ 2 * woldDepthOneFisherMass := by
  rw [xiDepthOneCenteredWoldEnergy, woldDepthOneFisherMass, ← tsum_mul_left]
  exact tsum_congr fun p => by
    rw [xiDepthOneCenteredWoldCoefficient_eq]
    ring

/-- Schwarz conjugation leaves the entire centered valuation-one source vector unchanged. -/
theorem xiDepthOneCenteredWoldCoefficient_copyConj
    (q : XiZeroCopy) (p : Nat.Primes) :
    xiDepthOneCenteredWoldCoefficient (xiZeroCopyConjEquiv q) p =
      xiDepthOneCenteredWoldCoefficient q p := by
  rw [xiDepthOneCenteredWoldCoefficient_eq,
    xiDepthOneCenteredWoldCoefficient_eq]
  congr 1

/-- Schwarz conjugation also leaves centered Wold Hilbert energy unchanged. -/
theorem xiDepthOneCenteredWoldEnergy_copyConj (q : XiZeroCopy) :
    xiDepthOneCenteredWoldEnergy (xiZeroCopyConjEquiv q) =
      xiDepthOneCenteredWoldEnergy q := by
  unfold xiDepthOneCenteredWoldEnergy
  exact tsum_congr fun p => by
    rw [xiDepthOneCenteredWoldCoefficient_copyConj]

/-- Central reciprocal-square imaginary phase is centered horizontal rate times physical height
in a positive denominator. -/
theorem xiZeroCopyReciprocalSquare_im_eq_centeredRate_mul_height_div
    (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im =
      primeDepthBVWoldXiCenteredRate q.1 * (q.1 : ℂ).im /
        Complex.normSq ((q.1 : ℂ) - 1 / 2) ^ 2 := by
  rw [xiZeroCopyReciprocalSquare_eq, xiCentralReciprocalSquare_im]
  unfold primeDepthBVWoldXiCenteredRate
  ring

/-- Shifted Cassini orientation is the same source-rate square in a geometric positive gauge. -/
theorem xiHeatCassiniOrientationTerm_eq_rate_sq_mul_bvWoldGauge
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiHeatCassiniOrientationTerm y q =
      primeDepthBVWoldXiCenteredRate q.1 ^ 2 *
        xiHeatCassiniBVWoldTransferGauge y q := by
  let D₀ : ℝ := Complex.normSq ((q.1 : ℂ) - 1 / 2) ^ 2
  let D₁ : ℝ := Complex.normSq
    (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q)
  have hD₀ : D₀ ≠ 0 := by
    exact pow_ne_zero 2 (Complex.normSq_pos.mpr
      (sub_ne_zero.mpr (xi_divisor_support_ne_half q.1))).ne'
  have hD₁ : D₁ ≠ 0 := by
    exact (Complex.normSq_pos.mpr
      (one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy.le q)).ne'
  have hre : (xiShiftedReciprocalSquare y q).re ≠ 0 := by
    simpa only [xiShiftedResponseMass] using
      (xiShiftedResponseMass_pos hy q).ne'
  rw [xiHeatCassiniOrientationTerm_eq_im_sq_div_re hy,
    xiShiftedReciprocalSquare_im_formula,
    xiZeroCopyReciprocalSquare_im_eq_centeredRate_mul_height_div]
  unfold primeDepthBVWoldXiCenteredRate xiHeatCassiniBVWoldTransferGauge
  dsimp only [D₀, D₁] at hD₀ hD₁ ⊢
  field_simp [hD₀, hD₁, hre]

/-- Transfer gauge is strictly positive on every Xi divisor copy and every positive shift. -/
theorem xiHeatCassiniBVWoldTransferGauge_pos
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 < xiHeatCassiniBVWoldTransferGauge y q := by
  let D₀ : ℝ := Complex.normSq ((q.1 : ℂ) - 1 / 2) ^ 2
  let D₁ : ℝ := Complex.normSq
    (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q)
  have hD₀ : 0 < D₀ := pow_pos
    (Complex.normSq_pos.mpr (sub_ne_zero.mpr (xi_divisor_support_ne_half q.1))) 2
  have hD₁ : 0 < D₁ := Complex.normSq_pos.mpr
    (one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy.le q)
  have hre : 0 < (xiShiftedReciprocalSquare y q).re := by
    simpa only [xiShiftedResponseMass] using xiShiftedResponseMass_pos hy q
  have him : 0 < (q.1 : ℂ).im ^ 2 :=
    sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)
  change 0 < (q.1 : ℂ).im ^ 2 / ((D₀ * D₁) ^ 2 *
    (xiShiftedReciprocalSquare y q).re)
  exact div_pos him (mul_pos (sq_pos_of_pos (mul_pos hD₀ hD₁)) hre)

/-- Existing Suzuki/Hankel transverse charge is exactly one radial norm-square above the
Stieltjes--Cassini Fisher defect. -/
theorem xiShiftedTransverseChargeDensity_eq_normSq_mul_orientation
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiShiftedTransverseChargeDensity y q =
      Complex.normSq (xiShiftedReciprocalSquare y q) *
        xiHeatCassiniOrientationTerm y q := by
  have hre : (xiShiftedReciprocalSquare y q).re ≠ 0 := by
    simpa only [xiShiftedResponseMass] using
      (xiShiftedResponseMass_pos hy q).ne'
  rw [xiHeatCassiniOrientationTerm_eq_im_sq_div_re hy]
  unfold xiShiftedTransverseChargeDensity xiShiftedResponseMass
  field_simp [hre]

/-- Polynomial probe `X` produces the cubic Suzuki charge, not the radially normalized midpoint
defect. -/
theorem xiShiftedApertureTransverseTerm_X_eq_transverseChargeDensity
    (y : ℝ) (q : XiZeroCopy) :
    xiShiftedApertureTransverseTerm y Polynomial.X q =
      xiShiftedTransverseChargeDensity y q := by
  simp [xiShiftedApertureTransverseTerm, xiShiftedTransverseChargeDensity,
    xiShiftedResponseMass, evalRealPolynomial]
  ring

/-- Schwarz conjugation reverses the phase-linear shifted receiver. -/
theorem xiShiftedReciprocalSquare_im_copyConj
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    (xiShiftedReciprocalSquare y (xiZeroCopyConjEquiv q)).im =
      -(xiShiftedReciprocalSquare y q).im := by
  rw [xiShiftedReciprocalSquare_copyConj hy.le]
  simp

/-- **Phase-recovery no-go.**  Off the critical line, no reporter depending only on the complete
centered depth-one Wold coefficient vector can recover the phase-linear shifted reciprocal
coordinate.  Schwarz conjugate divisors have identical source vectors and opposite receiver
orientation. -/
theorem no_centeredWoldVector_reporter_recovers_shiftedIm_of_offLine
    {y : ℝ} (hy : 0 < y) {q : XiZeroCopy}
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬ ∃ F : (Nat.Primes → ℝ) → ℝ, ∀ r : XiZeroCopy,
      F (xiDepthOneCenteredWoldCoefficient r) =
        (xiShiftedReciprocalSquare y r).im := by
  rintro ⟨F, hF⟩
  have hsource : xiDepthOneCenteredWoldCoefficient (xiZeroCopyConjEquiv q) =
      xiDepthOneCenteredWoldCoefficient q := by
    funext p
    exact xiDepthOneCenteredWoldCoefficient_copyConj q p
  have hsame :
      (xiShiftedReciprocalSquare y (xiZeroCopyConjEquiv q)).im =
        (xiShiftedReciprocalSquare y q).im := by
    calc
      (xiShiftedReciprocalSquare y (xiZeroCopyConjEquiv q)).im =
          F (xiDepthOneCenteredWoldCoefficient (xiZeroCopyConjEquiv q)) :=
        (hF (xiZeroCopyConjEquiv q)).symm
      _ = F (xiDepthOneCenteredWoldCoefficient q) := by rw [hsource]
      _ = (xiShiftedReciprocalSquare y q).im := hF q
  have hanti := xiShiftedReciprocalSquare_im_copyConj hy q
  have him : (xiShiftedReciprocalSquare y q).im = 0 := by linarith
  exact hoff ((xiShiftedReciprocalSquare_im_eq_zero_iff_criticalLine hy q).mp him)

/-- Atomwise source/receiver energy conservation. -/
theorem woldMass_mul_xiHeatCassiniOrientationTerm_eq_gauge_mul_sourceEnergy
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    woldDepthOneFisherMass * xiHeatCassiniOrientationTerm y q =
      xiHeatCassiniBVWoldTransferGauge y q *
        xiDepthOneCenteredWoldEnergy q := by
  rw [xiHeatCassiniOrientationTerm_eq_rate_sq_mul_bvWoldGauge hy,
    xiDepthOneCenteredWoldEnergy_eq_rate_sq_mul_mass]
  ring

/-- Weighted source Fisher energies are summable over the complete multiplicity-exact Xi divisor. -/
theorem summable_bvWoldGauge_mul_xiDepthOneCenteredWoldEnergy
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy =>
      xiHeatCassiniBVWoldTransferGauge y q * xiDepthOneCenteredWoldEnergy q) := by
  have h := (summable_xiHeatCassiniOrientationTerm hy).mul_left
    woldDepthOneFisherMass
  exact h.congr fun q =>
    woldMass_mul_xiHeatCassiniOrientationTerm_eq_gauge_mul_sourceEnergy hy q

/-- **Complete BV--Wold Fisher landing.**  Route T/U orientation defect is exactly a positively
weighted Hilbert energy of actual centered valuation-one source coefficients. -/
theorem woldMass_mul_xiHeatCassiniOrientationDefect_eq_sourceFisherEnergy
    {y : ℝ} (hy : 0 < y) :
    woldDepthOneFisherMass * xiHeatCassiniOrientationDefect y =
      ∑' q : XiZeroCopy,
        xiHeatCassiniBVWoldTransferGauge y q * xiDepthOneCenteredWoldEnergy q := by
  rw [xiHeatCassiniOrientationDefect, ← tsum_mul_left]
  exact tsum_congr fun q =>
    woldMass_mul_xiHeatCassiniOrientationTerm_eq_gauge_mul_sourceEnergy hy q

end

end RHTower
