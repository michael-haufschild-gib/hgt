import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAnomalyBurnolMultiplicativeSyzygyQuotient
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceEntropyBoundaryWeld

/-!
# Multiplicative Burnol jet connection

Differentiating the exact completed Burnol syzygy for `6 = 2 * 3` produces a class that no longer
lies in the value-level arithmetic kernel.  Each coefficient jet is spectral coordinate times the
opposite prime cell, with an explicit nonzero arithmetic weight.

Hermitian contraction against the opposite cells and normalization by the nowhere-zero two-prime
frame energy recovers the full spectral coordinate exactly.  On the Xi divisor, the imaginary
part of this arithmetic jet connection is precisely the Gaussian/Gamma horizontal gauge from
P-G115.  Thus that gauge is not an inserted free parameter: it is multiplicative jet curvature.

No vanishing, zero-location, or Riemann-hypothesis premise occurs.
-/

open Complex Real Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Literal derivative of the coefficient carrying the prime-two cell into the six-cell. -/
def burnolTwoToSixCoefficientJet (z : ℂ) : ℂ :=
  -(thetaIntegerShiftScale 6 / thetaIntegerShiftScale 2) *
    ((Real.log 3 / 2 : ℝ) : ℂ) *
      Complex.sin (z * ((Real.log 3 / 2 : ℝ) : ℂ))

/-- Literal derivative of the coefficient carrying the prime-three cell into the six-cell. -/
def burnolThreeToSixCoefficientJet (z : ℂ) : ℂ :=
  -(thetaIntegerShiftScale 6 / thetaIntegerShiftScale 3) *
    ((Real.log 2 / 2 : ℝ) : ℂ) *
      Complex.sin (z * ((Real.log 2 / 2 : ℝ) : ℂ))

theorem hasDerivAt_burnolTwoToSixCoefficient (z : ℂ) :
    HasDerivAt burnolTwoToSixCoefficient (burnolTwoToSixCoefficientJet z) z := by
  have h := (((hasDerivAt_id z).mul_const
    ((Real.log 3 / 2 : ℝ) : ℂ)).ccos).const_mul
      (thetaIntegerShiftScale 6 / thetaIntegerShiftScale 2)
  convert h using 1 <;>
    first | rfl | (rw [burnolTwoToSixCoefficientJet]; simp only [id_eq]; ring)

theorem hasDerivAt_burnolThreeToSixCoefficient (z : ℂ) :
    HasDerivAt burnolThreeToSixCoefficient (burnolThreeToSixCoefficientJet z) z := by
  have h := (((hasDerivAt_id z).mul_const
    ((Real.log 2 / 2 : ℝ) : ℂ)).ccos).const_mul
      (thetaIntegerShiftScale 6 / thetaIntegerShiftScale 3)
  convert h using 1 <;>
    first | rfl | (rw [burnolThreeToSixCoefficientJet]; simp only [id_eq]; ring)

theorem differentiable_burnolCompletedCenteredMultiplier (n : ℕ) :
    Differentiable ℂ (burnolCompletedCenteredMultiplier n) := by
  rw [show burnolCompletedCenteredMultiplier n = centeredMultiplierE n by
    funext z
    exact burnolCompletedCenteredMultiplier_eq_centeredMultiplierE n z]
  exact differentiable_centeredMultiplierE n

/-- Literal first-jet form of the completed `6 = 2 * 3` multiplicative syzygy. -/
theorem deriv_burnolCompletedCenteredMultiplier_six_eq_two_three (z : ℂ) :
    deriv (burnolCompletedCenteredMultiplier 6) z =
      burnolTwoToSixCoefficientJet z * burnolCompletedCenteredMultiplier 2 z +
        burnolTwoToSixCoefficient z * deriv (burnolCompletedCenteredMultiplier 2) z +
      (burnolThreeToSixCoefficientJet z * burnolCompletedCenteredMultiplier 3 z +
        burnolThreeToSixCoefficient z *
          deriv (burnolCompletedCenteredMultiplier 3) z) := by
  have h6 := (differentiable_burnolCompletedCenteredMultiplier 6 z).hasDerivAt
  have h2 := (differentiable_burnolCompletedCenteredMultiplier 2 z).hasDerivAt
  have h3 := (differentiable_burnolCompletedCenteredMultiplier 3 z).hasDerivAt
  have hright :=
    ((hasDerivAt_burnolTwoToSixCoefficient z).mul h2).add
      ((hasDerivAt_burnolThreeToSixCoefficient z).mul h3)
  have heq : (fun w => burnolCompletedCenteredMultiplier 6 w) =ᶠ[nhds z]
      fun w => burnolTwoToSixCoefficient w * burnolCompletedCenteredMultiplier 2 w +
        burnolThreeToSixCoefficient w * burnolCompletedCenteredMultiplier 3 w := by
    filter_upwards with w
    exact burnolCompletedCenteredMultiplier_six_eq_two_three w
  exact (h6.congr_of_eventuallyEq heq.symm).unique hright

/-- Nonzero weight converting the first coefficient jet into spectral coordinate times cell 3. -/
def burnolTwoToSixJetWeight : ℂ :=
  ((thetaIntegerShiftScale 6 / thetaIntegerShiftScale 2) *
      ((Real.log 3 / 2 : ℝ) : ℂ)) /
    (2 * thetaIntegerShiftScale 3)

/-- Nonzero weight converting the second coefficient jet into spectral coordinate times cell 2. -/
def burnolThreeToSixJetWeight : ℂ :=
  ((thetaIntegerShiftScale 6 / thetaIntegerShiftScale 3) *
      ((Real.log 2 / 2 : ℝ) : ℂ)) /
    (2 * thetaIntegerShiftScale 2)

theorem burnolTwoToSixJetWeight_ne_zero : burnolTwoToSixJetWeight ≠ 0 := by
  have hlog : ((Real.log 3 / 2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero (Real.log_pos (by norm_num)).ne' (by norm_num))
  exact div_ne_zero
    (mul_ne_zero
      (div_ne_zero (thetaIntegerShiftScale_ne_zero (by norm_num))
        (thetaIntegerShiftScale_ne_zero (by norm_num))) hlog)
    (mul_ne_zero (by norm_num) (thetaIntegerShiftScale_ne_zero (by norm_num)))

theorem burnolThreeToSixJetWeight_ne_zero : burnolThreeToSixJetWeight ≠ 0 := by
  have hlog : ((Real.log 2 / 2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero (Real.log_pos (by norm_num)).ne' (by norm_num))
  exact div_ne_zero
    (mul_ne_zero
      (div_ne_zero (thetaIntegerShiftScale_ne_zero (by norm_num))
        (thetaIntegerShiftScale_ne_zero (by norm_num))) hlog)
    (mul_ne_zero (by norm_num) (thetaIntegerShiftScale_ne_zero (by norm_num)))

/-- First coefficient jet is division-free spectral multiplication by the opposite prime cell. -/
theorem burnolTwoToSixCoefficientJet_eq_neg_weight_mul_spectral_mul_three (z : ℂ) :
    burnolTwoToSixCoefficientJet z =
      -burnolTwoToSixJetWeight * z * burnolCompletedCenteredMultiplier 3 z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [burnolTwoToSixCoefficientJet]
  · rw [burnolCompletedCenteredMultiplier_eq_scale_sin_div 3 hz]
    rw [burnolTwoToSixCoefficientJet, burnolTwoToSixJetWeight]
    have hs2 : thetaIntegerShiftScale 2 ≠ 0 :=
      thetaIntegerShiftScale_ne_zero (by norm_num)
    have hs3 : thetaIntegerShiftScale 3 ≠ 0 :=
      thetaIntegerShiftScale_ne_zero (by norm_num)
    field_simp [hs2, hs3, hz]
    ring_nf

/-- Second coefficient jet is division-free spectral multiplication by the opposite prime cell. -/
theorem burnolThreeToSixCoefficientJet_eq_neg_weight_mul_spectral_mul_two (z : ℂ) :
    burnolThreeToSixCoefficientJet z =
      -burnolThreeToSixJetWeight * z * burnolCompletedCenteredMultiplier 2 z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [burnolThreeToSixCoefficientJet]
  · rw [burnolCompletedCenteredMultiplier_eq_scale_sin_div 2 hz]
    rw [burnolThreeToSixCoefficientJet, burnolThreeToSixJetWeight]
    have hs2 : thetaIntegerShiftScale 2 ≠ 0 :=
      thetaIntegerShiftScale_ne_zero (by norm_num)
    have hs3 : thetaIntegerShiftScale 3 ≠ 0 :=
      thetaIntegerShiftScale_ne_zero (by norm_num)
    field_simp [hs2, hs3, hz]
    ring_nf

/-- Hermitian contraction of the multiplicative coefficient jets against their opposite cells. -/
def burnolMultiplicativeJetConnectionNumerator (z : ℂ) : ℂ :=
  (burnolTwoToSixCoefficientJet z / burnolTwoToSixJetWeight) *
      (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 3 z) +
    (burnolThreeToSixCoefficientJet z / burnolThreeToSixJetWeight) *
      (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 2 z)

/-- Exact division-free spectral reconstruction identity. -/
theorem burnolMultiplicativeJetConnectionNumerator_eq (z : ℂ) :
    burnolMultiplicativeJetConnectionNumerator z =
      -z * (burnolTwoPrimeFrameEnergy z : ℂ) := by
  rw [burnolMultiplicativeJetConnectionNumerator,
    burnolTwoToSixCoefficientJet_eq_neg_weight_mul_spectral_mul_three,
    burnolThreeToSixCoefficientJet_eq_neg_weight_mul_spectral_mul_two,
    burnolTwoPrimeFrameEnergy]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  field_simp [burnolTwoToSixJetWeight_ne_zero, burnolThreeToSixJetWeight_ne_zero]
  ring

/-- Division-free recovery of the Gaussian/Gamma horizontal gauge from arithmetic jet curvature. -/
theorem thetaXiBurnolGaussianHorizontalGauge_mul_frameEnergy_eq_jetNumerator_im
    (q : XiZeroCopy) :
    (thetaXiBurnolGaussianHorizontalGauge q).re *
        burnolTwoPrimeFrameEnergy (xiSpectralPoint q) =
      2 * (burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q)).im := by
  rw [burnolMultiplicativeJetConnectionNumerator_eq,
    thetaXiBurnolGaussianHorizontalGauge,
    riemannSourceGammaCoPoissonHorizontalParameter,
    riemannReflectedSourceEntropy_xiZeroCopy_eq_two_spectralIm]
  simp only [ofReal_re, neg_re, mul_im, ofReal_re, ofReal_im, mul_zero,
    Complex.neg_im]
  ring

/-- Globally normalized arithmetic multiplicative-jet connection. -/
def burnolMultiplicativeJetSpectralConnection (z : ℂ) : ℂ :=
  -burnolMultiplicativeJetConnectionNumerator z /
    (burnolTwoPrimeFrameEnergy z : ℂ)

/-- The multiplicative-jet connection reconstructs full spectral coordinate at every point. -/
theorem burnolMultiplicativeJetSpectralConnection_eq (z : ℂ) :
    burnolMultiplicativeJetSpectralConnection z = z := by
  rw [burnolMultiplicativeJetSpectralConnection,
    burnolMultiplicativeJetConnectionNumerator_eq]
  have hE : (burnolTwoPrimeFrameEnergy z : ℂ) ≠ 0 := by
    exact_mod_cast (burnolTwoPrimeFrameEnergy_pos z).ne'
  field_simp [hE]

/-- P-G115's Gaussian/Gamma affine gauge is the horizontal part of arithmetic jet curvature. -/
theorem thetaXiBurnolGaussianHorizontalGauge_eq_multiplicativeJetConnection
    (q : XiZeroCopy) :
    thetaXiBurnolGaussianHorizontalGauge q =
      ((-2 * (burnolMultiplicativeJetSpectralConnection
        (xiSpectralPoint q)).im : ℝ) : ℂ) := by
  rw [burnolMultiplicativeJetSpectralConnection_eq,
    thetaXiBurnolGaussianHorizontalGauge,
    riemannSourceGammaCoPoissonHorizontalParameter,
    riemannReflectedSourceEntropy_xiZeroCopy_eq_two_spectralIm]
  push_cast
  ring

/-- Arithmetic jet connection is horizontally real exactly on the critical line. -/
theorem burnolMultiplicativeJetSpectralConnection_im_eq_zero_iff (q : XiZeroCopy) :
    (burnolMultiplicativeJetSpectralConnection (xiSpectralPoint q)).im = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [burnolMultiplicativeJetSpectralConnection_eq, xiSpectralPoint_im_eq]
  constructor <;> intro h <;> linarith

/-- The arithmetic multiplicative-jet connection is a faithful global RH receiver. -/
theorem all_burnolMultiplicativeJetSpectralConnection_im_eq_zero_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      (burnolMultiplicativeJetSpectralConnection (xiSpectralPoint q)).im = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(xiSpectralPoint q).re, Complex.ext ?_ ?_⟩
    · simp
    · have hq := h q
      rw [burnolMultiplicativeJetSpectralConnection_eq] at hq
      simpa using hq
  · intro hRH q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [burnolMultiplicativeJetSpectralConnection_eq, ht]
    simp

end

end RHTower.HedenmalmThetaSource
