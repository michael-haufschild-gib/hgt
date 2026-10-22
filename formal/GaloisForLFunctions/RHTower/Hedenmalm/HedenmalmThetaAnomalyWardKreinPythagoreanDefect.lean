import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAnomalyWardRealification

/-!
# Positive defect hidden by same-fibre Krein cancellation

The two signed Ward channels cancel on every Xi copy, but their Euclidean energy does not.  This
module proves that both channels have magnitude equal to the P-G123 realification anomaly and that
the raw multiplicative-jet numerator splits orthogonally into realified numerator plus anomaly.

Consequently Euclidean energy of the Krein-null Ward pair is twice anomaly energy, while loss from
raw to realified numerator is exactly one anomaly energy.  Signed conservation is therefore
nontrivial null current off critical line, not flat current.  Positive defect vanishes exactly on
critical line; global vanishing remains equivalent to RH.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-- Multiplicity-scaled compact-theta Ward channel. -/
def thetaXiWardThetaChannel (q : XiZeroCopy) : ℝ :=
  burnolTwoPrimeFrameEnergy (xiSpectralPoint q) *
    (Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q)

/-- Multiplicity-scaled arithmetic jet Ward channel. -/
def thetaXiWardArithmeticChannel (q : XiZeroCopy) : ℝ :=
  (burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q)).im *
    ‖completedXiFirstDividedL2 q.1‖ ^ 2

/-- Raw arithmetic numerator at genuine Xi multiplicity. -/
def thetaXiWardRawNumerator (q : XiZeroCopy) : ℂ :=
  burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q) *
    (‖completedXiFirstDividedL2 q.1‖ ^ 2 : ℂ)

/-- Positive Euclidean energy of two signed Ward channels. -/
def thetaXiWardEuclideanEnergy (q : XiZeroCopy) : ℝ :=
  thetaXiWardThetaChannel q ^ 2 + thetaXiWardArithmeticChannel q ^ 2

/-- Theta Ward channel is radial coordinate times positive Ward mass. -/
theorem thetaXiWardThetaChannel_eq (q : XiZeroCopy) :
    thetaXiWardThetaChannel q =
      (xiSpectralPoint q).im * thetaXiWardRealificationMass q := by
  rw [thetaXiWardThetaChannel, thetaXiRankTwoBoundaryFlux_completedXi_sameFiber,
    thetaXiWardRealificationMass]
  ring

/-- Arithmetic Ward channel has same magnitude and opposite sign. -/
theorem thetaXiWardArithmeticChannel_eq (q : XiZeroCopy) :
    thetaXiWardArithmeticChannel q =
      -(xiSpectralPoint q).im * thetaXiWardRealificationMass q := by
  rw [thetaXiWardArithmeticChannel, burnolMultiplicativeJetConnectionNumerator_eq,
    thetaXiWardRealificationMass]
  simp only [Complex.mul_im, Complex.neg_re, Complex.ofReal_im, mul_zero,
    Complex.neg_im, Complex.ofReal_re, zero_add]
  ring

/-- Raw multiplicity numerator is universal spectral coordinate times positive Ward mass. -/
theorem thetaXiWardRawNumerator_eq (q : XiZeroCopy) :
    thetaXiWardRawNumerator q =
      -xiSpectralPoint q * (thetaXiWardRealificationMass q : ℂ) := by
  rw [thetaXiWardRawNumerator, burnolMultiplicativeJetConnectionNumerator_eq,
    thetaXiWardRealificationMass]
  push_cast
  ring

/-- Signed two-channel Ward current is Krein-null. -/
theorem thetaXiWard_signedChannels_cancel (q : XiZeroCopy) :
    thetaXiWardThetaChannel q + thetaXiWardArithmeticChannel q = 0 := by
  rw [thetaXiWardThetaChannel_eq, thetaXiWardArithmeticChannel_eq]
  ring

/-! ## Pythagorean and Euclidean defect identities -/

/-- **Raw/realified Pythagorean law.**  Raw numerator splits orthogonally into realified numerator
and Ward anomaly. -/
theorem thetaXiWard_raw_realified_anomaly_pythagorean (q : XiZeroCopy) :
    Complex.normSq (thetaXiWardRawNumerator q) =
      Complex.normSq (thetaXiWardRealifiedNumerator q) +
        Complex.normSq (thetaXiWardRealificationAnomaly q) := by
  rw [thetaXiWardRawNumerator_eq, thetaXiWardRealifiedNumerator_eq,
    thetaXiWardRealificationAnomaly_eq]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Ward anomaly energy is squared theta-channel magnitude. -/
theorem thetaXiWard_anomaly_normSq_eq_thetaChannel_sq (q : XiZeroCopy) :
    Complex.normSq (thetaXiWardRealificationAnomaly q) =
      thetaXiWardThetaChannel q ^ 2 := by
  rw [thetaXiWardRealificationAnomaly_eq, thetaXiWardThetaChannel_eq]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Ward anomaly energy is also squared arithmetic-channel magnitude. -/
theorem thetaXiWard_anomaly_normSq_eq_arithmeticChannel_sq (q : XiZeroCopy) :
    Complex.normSq (thetaXiWardRealificationAnomaly q) =
      thetaXiWardArithmeticChannel q ^ 2 := by
  rw [thetaXiWardRealificationAnomaly_eq, thetaXiWardArithmeticChannel_eq]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Krein-to-Euclidean conversion.**  Euclidean energy of signed-null pair is twice anomaly
energy. -/
theorem thetaXiWardEuclideanEnergy_eq_two_mul_anomaly_normSq (q : XiZeroCopy) :
    thetaXiWardEuclideanEnergy q =
      2 * Complex.normSq (thetaXiWardRealificationAnomaly q) := by
  rw [thetaXiWardEuclideanEnergy, ← thetaXiWard_anomaly_normSq_eq_thetaChannel_sq,
    ← thetaXiWard_anomaly_normSq_eq_arithmeticChannel_sq]
  ring

/-- Loss of squared numerator norm under Ward realification is exactly anomaly energy. -/
theorem thetaXiWard_raw_realified_normLoss_eq_anomaly_normSq (q : XiZeroCopy) :
    Complex.normSq (thetaXiWardRawNumerator q) -
        Complex.normSq (thetaXiWardRealifiedNumerator q) =
      Complex.normSq (thetaXiWardRealificationAnomaly q) := by
  rw [thetaXiWard_raw_realified_anomaly_pythagorean]
  ring

/-- Ward realification is norm-contracting on every Xi copy. -/
theorem thetaXiWard_raw_realified_normLoss_nonneg (q : XiZeroCopy) :
    0 ≤ Complex.normSq (thetaXiWardRawNumerator q) -
      Complex.normSq (thetaXiWardRealifiedNumerator q) := by
  rw [thetaXiWard_raw_realified_normLoss_eq_anomaly_normSq]
  exact Complex.normSq_nonneg _

/-! ## Defect boundary -/

/-- Positive Euclidean Ward defect vanishes exactly on critical line. -/
theorem thetaXiWardEuclideanEnergy_eq_zero_iff_line (q : XiZeroCopy) :
    thetaXiWardEuclideanEnergy q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [thetaXiWardEuclideanEnergy_eq_two_mul_anomaly_normSq, mul_eq_zero]
  norm_num
  rw [thetaXiWardRealificationAnomaly_eq_zero_iff, xiSpectralPoint_im_eq]
  constructor <;> intro h <;> linarith

/-- Hypothetical right-half Xi divisor carries strictly positive Euclidean Ward defect despite
exact signed cancellation. -/
theorem thetaXiWardEuclideanEnergy_pos_of_rightHalf
    (q : XiZeroCopy) (h : 1 / 2 < (q.1 : ℂ).re) :
    0 < thetaXiWardEuclideanEnergy q := by
  rw [thetaXiWardEuclideanEnergy_eq_two_mul_anomaly_normSq]
  apply mul_pos two_pos
  apply Complex.normSq_pos.mpr
  intro hzero
  have hline := (thetaXiWardRealificationAnomaly_eq_zero_iff q).mp hzero
  rw [xiSpectralPoint_im_eq] at hline
  linarith

/-- Global Euclidean flatness is an exact RH criterion, not a consequence of signed Ward
conservation. -/
theorem all_thetaXiWardEuclideanEnergy_eq_zero_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, thetaXiWardEuclideanEnergy q = 0) ↔ RiemannHypothesis := by
  rw [← all_thetaXiWardRealifiedConnections_eq_spectral_iff_riemannHypothesis]
  constructor
  · intro h q
    exact (thetaXiWardRealifiedConnection_eq_spectral_iff_line q).mpr
      ((thetaXiWardEuclideanEnergy_eq_zero_iff_line q).mp (h q))
  · intro h q
    exact (thetaXiWardEuclideanEnergy_eq_zero_iff_line q).mpr
      ((thetaXiWardRealifiedConnection_eq_spectral_iff_line q).mp (h q))

end RHTower
