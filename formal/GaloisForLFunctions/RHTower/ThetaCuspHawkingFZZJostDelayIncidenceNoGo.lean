import GaloisForLFunctions.RHTower.ThetaCuspHawkingSchwarzschildJostIncidenceNoGo
import GaloisForLFunctions.HTGeometry.FZZCigarScatteringSpectralAsymmetry

/-!
# Theta incidence for the protected FZZ-cigar Jost factor

Ashok--Troost's exact supersymmetric cigar reflection amplitudes expose a protected continuum
spectral asymmetry

`-m / (pi * (p^(2 : ℕ) + m^(2 : ℕ)))`.

This file reconstructs the corresponding reduced charge-sector Jost factor

`R_m(p) = (i p - m) / (i p + m)`

and proves its incidence with the theta/Xi divisor.  Its logarithmic derivative is exactly
`2 pi i` times the protected spectral asymmetry.  Its zero and pole lie at imaginary radial
momenta `-i m` and `+i m`; on physical real momentum it is all-pass.  A positive-frequency theta
divisor representative is therefore neither a charge-sector Jost zero nor a pole.  The dressed
response still vanishes, but only because the theta/Xi source numerator vanishes.

The same protected scattering density has an exact black-hole delay tomography:

`radial continuum --Fourier--> exp(-(n+1)t) --charge sum--> 1/(exp(t)-1)
  --Mellin--> Gamma(s) zeta(s)`.

Thus zeta divisor points are zeros of the completed delay tomography, not zeros or poles of an
individual cigar scattering sector.  This is a positive no-go boundary: mode stability and
sector-local passivity cannot locate the divisor.  A remaining RH-bearing producer must constrain
zeros of the Mellin transform of the protected spectral-shift measure itself, through a genuine
theta-dependent nonlinear black-hole coupling.

`[LITERATURE] [PAPER-PROVED]` The spectral asymmetry and reflection interpretation are from
Ashok--Troost, arXiv:1101.1059.  The Fourier, charge-sum, and Mellin identities are imported from
`FZZCigarScatteringSpectralAsymmetry`.

`[SCOPE]` This is the protected two-dimensional string-black-hole scattering sector.  It is not a
four-dimensional Einstein--Klein--Gordon or Teukolsky determinant.  In this relative sector the
optical identity is all-pass phase scattering; absorption and four-dimensional horizon flux are
handled by the Schwarzschild incidence module imported above.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-! ## Reduced charge-sector Jost factor -/

/-- Numerator of the reduced protected FZZ-cigar charge-sector Jost factor. -/
def fzzCigarChargeJostNumerator (m : ℝ) (p : ℂ) : ℂ :=
  I * p - (m : ℂ)

/-- Denominator of the reduced protected FZZ-cigar charge-sector Jost factor. -/
def fzzCigarChargeJostDenominator (m : ℝ) (p : ℂ) : ℂ :=
  I * p + (m : ℂ)

/-- Minimal meromorphic factor carrying the protected FZZ reflection-phase asymmetry. -/
def fzzCigarChargeJostRatio (m : ℝ) (p : ℂ) : ℂ :=
  fzzCigarChargeJostNumerator m p / fzzCigarChargeJostDenominator m p

/-- The protected charge-sector Jost zero lies on the negative imaginary radial axis. -/
theorem fzzCigarChargeJostNumerator_eq_zero_iff (m : ℝ) (p : ℂ) :
    fzzCigarChargeJostNumerator m p = 0 ↔ p = -I * (m : ℂ) := by
  constructor
  · intro h
    apply Complex.ext
    · have him := congrArg Complex.im h
      simpa [fzzCigarChargeJostNumerator] using him
    · have hre := congrArg Complex.re h
      simp [fzzCigarChargeJostNumerator] at hre ⊢
      linarith
  · intro h
    rw [h]
    rw [fzzCigarChargeJostNumerator]
    calc
      I * (-I * (m : ℂ)) - (m : ℂ) =
          -(I * I) * (m : ℂ) - (m : ℂ) := by ring
      _ = 0 := by rw [I_mul_I]; ring

/-- The protected charge-sector Jost pole lies on the positive imaginary radial axis. -/
theorem fzzCigarChargeJostDenominator_eq_zero_iff (m : ℝ) (p : ℂ) :
    fzzCigarChargeJostDenominator m p = 0 ↔ p = I * (m : ℂ) := by
  constructor
  · intro h
    apply Complex.ext
    · have him := congrArg Complex.im h
      simpa [fzzCigarChargeJostDenominator] using him
    · have hre := congrArg Complex.re h
      simp [fzzCigarChargeJostDenominator] at hre ⊢
      linarith
  · intro h
    rw [h]
    rw [fzzCigarChargeJostDenominator]
    calc
      I * (I * (m : ℂ)) + (m : ℂ) =
          (I * I) * (m : ℂ) + (m : ℂ) := by ring
      _ = 0 := by rw [I_mul_I]; ring

/-- No nonzero real radial momentum is a protected charge-sector Jost zero. -/
theorem fzzCigarChargeJostNumerator_ofReal_ne_zero
    (m : ℝ) {p : ℝ} (hp : p ≠ 0) :
    fzzCigarChargeJostNumerator m (p : ℂ) ≠ 0 := by
  intro hzero
  have h := (fzzCigarChargeJostNumerator_eq_zero_iff m (p : ℂ)).mp hzero
  have hre := congrArg Complex.re h
  simp at hre
  exact hp hre

/-- No nonzero real radial momentum is a protected charge-sector Jost pole. -/
theorem fzzCigarChargeJostDenominator_ofReal_ne_zero
    (m : ℝ) {p : ℝ} (hp : p ≠ 0) :
    fzzCigarChargeJostDenominator m (p : ℂ) ≠ 0 := by
  intro hzero
  have h := (fzzCigarChargeJostDenominator_eq_zero_iff m (p : ℂ)).mp hzero
  have hre := congrArg Complex.re h
  simp at hre
  exact hp hre

/-- A nonzero charge keeps the Jost denominator nonzero on the entire real radial axis. -/
theorem fzzCigarChargeJostDenominator_ofReal_ne_zero_of_charge
    {m : ℝ} (hm : m ≠ 0) (p : ℝ) :
    fzzCigarChargeJostDenominator m (p : ℂ) ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp [fzzCigarChargeJostDenominator] at hre
  exact hm hre

theorem norm_sq_fzzCigarChargeJostNumerator_ofReal (m p : ℝ) :
    ‖fzzCigarChargeJostNumerator m (p : ℂ)‖ ^ (2 : ℕ) = p ^ (2 : ℕ) + m ^ (2 : ℕ) := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [fzzCigarChargeJostNumerator, Complex.normSq_apply]
  ring

theorem norm_sq_fzzCigarChargeJostDenominator_ofReal (m p : ℝ) :
    ‖fzzCigarChargeJostDenominator m (p : ℂ)‖ ^ (2 : ℕ) = p ^ (2 : ℕ) + m ^ (2 : ℕ) := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [fzzCigarChargeJostDenominator, Complex.normSq_apply]
  ring

theorem norm_fzzCigarChargeJostNumerator_eq_denominator_ofReal (m p : ℝ) :
    ‖fzzCigarChargeJostNumerator m (p : ℂ)‖ =
      ‖fzzCigarChargeJostDenominator m (p : ℂ)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_fzzCigarChargeJostNumerator_ofReal,
    norm_sq_fzzCigarChargeJostDenominator_ofReal]

/-- Protected relative scattering is all-pass at physical real radial momentum. -/
theorem norm_fzzCigarChargeJostRatio_ofReal
    {m : ℝ} (hm : m ≠ 0) (p : ℝ) :
    ‖fzzCigarChargeJostRatio m (p : ℂ)‖ = 1 := by
  rw [fzzCigarChargeJostRatio, norm_div,
    norm_fzzCigarChargeJostNumerator_eq_denominator_ofReal]
  apply div_self
  exact norm_ne_zero_iff.mpr
    (fzzCigarChargeJostDenominator_ofReal_ne_zero_of_charge hm p)

/-- Optical-energy share of the protected relative charge sector. -/
def fzzCigarChargeJostOpticalEnergyShare (m p : ℝ) : ℝ :=
  ‖fzzCigarChargeJostRatio m (p : ℂ)‖ ^ (2 : ℕ)

/-- Exact all-pass optical identity for every nonzero protected charge sector. -/
theorem fzzCigarChargeJostOpticalEnergyShare_eq_one
    {m : ℝ} (hm : m ≠ 0) (p : ℝ) :
    fzzCigarChargeJostOpticalEnergyShare m p = 1 := by
  rw [fzzCigarChargeJostOpticalEnergyShare,
    norm_fzzCigarChargeJostRatio_ofReal hm]
  norm_num

/-! ## Logarithmic derivative and exact protected spectral asymmetry -/

/-- Meromorphic logarithmic derivative of the reduced Jost ratio. -/
def fzzCigarChargeJostLogDerivative (m : ℝ) (p : ℂ) : ℂ :=
  I * (I * p - (m : ℂ))⁻¹ - I * (I * p + (m : ℂ))⁻¹

theorem hasDerivAt_fzzCigarChargeJostRatio
    {m : ℝ} {p : ℂ} (hden : fzzCigarChargeJostDenominator m p ≠ 0) :
    HasDerivAt (fzzCigarChargeJostRatio m)
      (2 * I * (m : ℂ) / (fzzCigarChargeJostDenominator m p) ^ (2 : ℕ)) p := by
  have hnum : HasDerivAt (fun q : ℂ => I * q - (m : ℂ)) I p :=
    by simpa using ((hasDerivAt_id p).const_mul I |>.sub_const (m : ℂ))
  have hden' : HasDerivAt (fun q : ℂ => I * q + (m : ℂ)) I p :=
    by simpa using ((hasDerivAt_id p).const_mul I |>.add_const (m : ℂ))
  simp only [fzzCigarChargeJostDenominator] at hden
  unfold fzzCigarChargeJostRatio fzzCigarChargeJostNumerator
    fzzCigarChargeJostDenominator
  have hquot :
      HasDerivAt (fun q : ℂ => (I * q - (m : ℂ)) / (I * q + (m : ℂ)))
        ((I * (I * p + (m : ℂ)) - (I * p - (m : ℂ)) * I) /
          (I * p + (m : ℂ)) ^ (2 : ℕ)) p :=
    hnum.div hden' hden
  have hderiv :
      (I * (I * p + (m : ℂ)) - (I * p - (m : ℂ)) * I) /
          (I * p + (m : ℂ)) ^ (2 : ℕ) =
        2 * I * (m : ℂ) / (I * p + (m : ℂ)) ^ (2 : ℕ) := by
    congr 1
    ring
  rw [hderiv] at hquot
  exact hquot

/-- Away from zero and pole, the analytic derivative divided by the Jost ratio is its declared
logarithmic derivative. -/
theorem fzzCigarChargeJostDerivative_div_ratio_eq_logDerivative
    {m : ℝ} {p : ℂ}
    (hnum : fzzCigarChargeJostNumerator m p ≠ 0)
    (hden : fzzCigarChargeJostDenominator m p ≠ 0) :
    (2 * I * (m : ℂ) / (fzzCigarChargeJostDenominator m p) ^ (2 : ℕ)) /
        fzzCigarChargeJostRatio m p =
      fzzCigarChargeJostLogDerivative m p := by
  simp only [fzzCigarChargeJostNumerator] at hnum
  simp only [fzzCigarChargeJostDenominator] at hden
  unfold fzzCigarChargeJostRatio fzzCigarChargeJostLogDerivative
    fzzCigarChargeJostNumerator fzzCigarChargeJostDenominator
  field_simp [hnum, hden]
  ring

/-- Exact incidence between reduced Jost phase and protected FZZ continuum density. -/
theorem fzzCigarChargeJostLogDerivative_eq_spectralAsymmetry
    (m p : ℝ) :
    fzzCigarChargeJostLogDerivative m (p : ℂ) =
      2 * (Real.pi : ℂ) * I *
        HTGeometry.fzzCigarRightMovingSpectralAsymmetry m p := by
  rw [fzzCigarChargeJostLogDerivative,
    HTGeometry.fzzCigarRightMovingSpectralAsymmetry]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]

/-! ## Theta divisor incidence -/

/-- Theta/Xi source coupled to the protected FZZ charge-sector resolvent denominator. -/
def thetaCuspHawkingFZZChargeJostDressedResponse
    (rho : XiDivisorSupport) (m : ℝ) : ℂ :=
  XiC (xiSpectralPointSupport (thetaCuspHawkingPositiveFrequencySupport rho)) /
    fzzCigarChargeJostDenominator m
      (thetaCuspHawkingPositiveJostFrequency rho : ℂ)

theorem thetaCuspHawkingFZZChargeJostDressedResponse_eq_zero
    (rho : XiDivisorSupport) (m : ℝ) :
    thetaCuspHawkingFZZChargeJostDressedResponse rho m = 0 := by
  rw [thetaCuspHawkingFZZChargeJostDressedResponse,
    XiC_xiSpectralPointSupport_eq_zero_source]
  exact zero_div _

/-- **Exact incidence classification.** A positive-frequency theta divisor representative is a
dark zero of the dressed delay response, but neither a zero nor a pole of any positive protected
FZZ charge sector.  The underlying sector remains all-pass. -/
theorem thetaCuspHawkingXiDivisor_is_FZZ_delay_zero_not_chargeJost_zero_or_pole
    (rho : XiDivisorSupport) {m : ℝ} (hm : 0 < m) :
    thetaCuspHawkingFZZChargeJostDressedResponse rho m = 0 ∧
      fzzCigarChargeJostNumerator m
          (thetaCuspHawkingPositiveJostFrequency rho : ℂ) ≠ 0 ∧
      fzzCigarChargeJostDenominator m
          (thetaCuspHawkingPositiveJostFrequency rho : ℂ) ≠ 0 ∧
      ‖fzzCigarChargeJostRatio m
          (thetaCuspHawkingPositiveJostFrequency rho : ℂ)‖ = 1 := by
  have hp : thetaCuspHawkingPositiveJostFrequency rho ≠ 0 :=
    ne_of_gt (thetaCuspHawkingPositiveJostFrequency_pos rho)
  have hm0 : m ≠ 0 := ne_of_gt hm
  exact ⟨thetaCuspHawkingFZZChargeJostDressedResponse_eq_zero rho m,
    fzzCigarChargeJostNumerator_ofReal_ne_zero m hp,
    fzzCigarChargeJostDenominator_ofReal_ne_zero m hp,
    norm_fzzCigarChargeJostRatio_ofReal hm0 _⟩

/-! ## Discrete-plus-continuum delay tomography -/

/-- Exact radial-continuum Fourier identity together with its discrete positive-charge sum. -/
theorem fzzCigarJost_discretePlusContinuumOpticalDelayIdentity
    {t : ℝ} (ht : 0 < t) :
    (∀ n : ℕ,
      (∫ p : ℝ,
          ((HTGeometry.fzzCigarReflectionDeficit ((n : ℝ) + 1) p : ℝ) : ℂ) *
            Complex.exp (((-(t * p) : ℝ) : ℂ) * I)) =
        ((HTGeometry.fzzCigarChargeDelay n t : ℝ) : ℂ)) ∧
      HasSum (fun n : ℕ => HTGeometry.fzzCigarChargeDelay n t)
        (HTGeometry.fzzCigarContinuumDelay t) := by
  constructor
  · intro n
    exact HTGeometry.fzzCigarChargeDelay_eq_reflectionDeficitFourier n ht
  · exact HTGeometry.hasSum_fzzCigarChargeDelay ht

/-- Exact Mellin completion of the summed protected black-hole delay. -/
theorem fzzCigarJost_continuumMellin_eq_gamma_zeta
    {a : ℝ} (ha : 0 < a) :
    ((HTGeometry.fzzCigarContinuumMellin a : ℝ) : ℂ) =
      Complex.Gamma (((a + 1 : ℝ) : ℂ)) *
        riemannZeta (((a + 1 : ℝ) : ℂ)) :=
  HTGeometry.ofReal_fzzCigarContinuumMellin ha

end RHTower
