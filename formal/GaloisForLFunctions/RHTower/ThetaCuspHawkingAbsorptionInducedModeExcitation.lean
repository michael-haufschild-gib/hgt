import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# Absorption-induced excitation of theta-Hawking resonance modes

Sberna--Bosch--East--Green--Lehner, arXiv:2112.11168, isolate a genuinely
nonlinear black-hole effect: an excited mode is partly absorbed, its quadratic
energy changes the black-hole mass, and the shifted quasinormal spectrum then
re-expands the original mode into the new basis.  This absorption-induced mode
excitation (AIME) is a third-order secular effect, not a KMS or fixed-background
scattering identity.

This file isolates its unavoidable self-frequency component.  Let `x` be mode
intensity, so a sudden absorbed mass has the form `M + absorption * x`.  A
self-similar Schwarzschild quasinormal carrier is

`C(x) = exp(-i * omega * t / (M + absorption * x))`.

Its exact intensity derivative at zero is

`C(0) * i * omega * t * absorption / M^2`.

Multiplication by the original field amplitude makes this the cubic secular
coefficient.  The coefficient respects the physical mirror operation
`omega ↦ -conj(omega)` and is nonzero at nonzero time for every nonzero
frequency and nonzero absorbed mass response.

Every multiplicity-exact Xi spectral point is nonzero.  Consequently AIME
activates every theta/Xi sector, both critical and tilted.  This is a
source-faithful Hawking no-go: universal absorption-induced self-frequency
mixing cannot select RH or force the diagonal-preserving Cayley/Petz cubic
completion.  Any surviving producer must use the cross-mode projection of the
mass-shifted basis, or the fixed-ADM-charge canonical-energy sector, in a way
that distinguishes the critical-line reflection pair.

Physics sources:

* Sberna et al., *Nonlinear effects in the black hole ringdown:
  absorption-induced mode excitation*, arXiv:2112.11168.
* Green et al., *Conserved currents for Kerr and orthogonality of quasinormal
  modes*, arXiv:2210.15935.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-- Self-similar QNM carrier after a quadratic absorbed-energy mass shift. -/
def schwarzschildAbsorptionShiftedQNMCarrier
    (M absorption intensity t : ℝ) (omega : ℂ) : ℂ :=
  Complex.exp
    (-Complex.I * omega * (t : ℂ) /
      ((M + absorption * intensity : ℝ) : ℂ))

/-- Intensity derivative of the shifted carrier.  When intensity is the
square of field amplitude, this is the coefficient of AIME's cubic secular
field response. -/
def schwarzschildAbsorptionInducedCubicCoefficient
    (M absorption t : ℝ) (omega : ℂ) : ℂ :=
  schwarzschildAbsorptionShiftedQNMCarrier M absorption 0 t omega *
    (Complex.I * omega * (t : ℂ) * (absorption : ℂ) / (M : ℂ) ^ 2)

/-- Exact sudden-mass-shift derivation of the AIME cubic coefficient. -/
theorem hasDerivAt_schwarzschildAbsorptionShiftedQNMCarrier_zero
    {M : ℝ} (hM : M ≠ 0) (absorption t : ℝ) (omega : ℂ) :
    HasDerivAt
      (fun intensity : ℝ =>
        schwarzschildAbsorptionShiftedQNMCarrier
          M absorption intensity t omega)
      (schwarzschildAbsorptionInducedCubicCoefficient
        M absorption t omega) 0 := by
  have hdenReal : HasDerivAt
      (fun intensity : ℝ => M + absorption * intensity) absorption 0 := by
    simpa using
      (((hasDerivAt_id 0).const_mul absorption).const_add M)
  have hden : HasDerivAt
      (fun intensity : ℝ =>
        ((M + absorption * intensity : ℝ) : ℂ))
      (absorption : ℂ) 0 := by
    simpa using hdenReal.ofReal_comp
  have hden0 : (((M + absorption * (0 : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    simpa using (show (M : ℂ) ≠ 0 by exact_mod_cast hM)
  have hnum : HasDerivAt
      (fun _ : ℝ => -Complex.I * omega * (t : ℂ)) 0 0 :=
    hasDerivAt_const 0 _
  have hquot := hnum.div hden hden0
  have hexp := hquot.cexp
  unfold schwarzschildAbsorptionInducedCubicCoefficient
    schwarzschildAbsorptionShiftedQNMCarrier
  dsimp only [Pi.div_apply] at hexp ⊢
  convert hexp using 1
  all_goals field_simp [hM]
  all_goals ring_nf

/-- Nonzero absorption gives a nonzero secular self-frequency coefficient for
every nonzero QNM frequency. -/
theorem schwarzschildAbsorptionInducedCubicCoefficient_ne_zero
    {M absorption t : ℝ} (hM : M ≠ 0)
    (habsorption : absorption ≠ 0) (ht : t ≠ 0)
    {omega : ℂ} (homega : omega ≠ 0) :
    schwarzschildAbsorptionInducedCubicCoefficient
      M absorption t omega ≠ 0 := by
  rw [schwarzschildAbsorptionInducedCubicCoefficient]
  apply mul_ne_zero (Complex.exp_ne_zero _)
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero Complex.I_ne_zero homega)
      (by exact_mod_cast ht)) (by exact_mod_cast habsorption)
  · exact pow_ne_zero _ (by exact_mod_cast hM)

/-- The shifted carrier intertwines the QNM mirror operation
`omega ↦ -conj(omega)` with complex conjugation. -/
theorem schwarzschildAbsorptionShiftedQNMCarrier_mirror
    (M absorption intensity t : ℝ) (omega : ℂ) :
    schwarzschildAbsorptionShiftedQNMCarrier
        M absorption intensity t (-starRingEnd ℂ omega) =
      starRingEnd ℂ
        (schwarzschildAbsorptionShiftedQNMCarrier
          M absorption intensity t omega) := by
  rw [schwarzschildAbsorptionShiftedQNMCarrier,
    schwarzschildAbsorptionShiftedQNMCarrier]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, map_neg, conj_I, conj_ofReal]
  ring

/-- AIME's cubic coefficient has the same exact mirror covariance. -/
theorem schwarzschildAbsorptionInducedCubicCoefficient_mirror
    (M absorption t : ℝ) (omega : ℂ) :
    schwarzschildAbsorptionInducedCubicCoefficient
        M absorption t (-starRingEnd ℂ omega) =
      starRingEnd ℂ
        (schwarzschildAbsorptionInducedCubicCoefficient
          M absorption t omega) := by
  rw [schwarzschildAbsorptionInducedCubicCoefficient,
    schwarzschildAbsorptionInducedCubicCoefficient,
    schwarzschildAbsorptionShiftedQNMCarrier_mirror]
  simp only [map_mul, map_div₀, map_pow, conj_I, conj_ofReal]
  ring

/-- AIME coefficient evaluated on one multiplicity-exact theta/Xi spectral
sector. -/
def thetaXiSchwarzschildAIMECubicCoefficient
    (q : XiZeroCopy) (M absorption t : ℝ) : ℂ :=
  schwarzschildAbsorptionInducedCubicCoefficient
    M absorption t (xiSpectralPoint q)

/-- **Hawking-specific all-sector mixing law.**  Universal AIME self-frequency
mixing is nonzero on every Xi divisor sector, without any RH hypothesis. -/
theorem thetaXiSchwarzschildAIMECubicCoefficient_ne_zero
    (q : XiZeroCopy) {M absorption t : ℝ} (hM : M ≠ 0)
    (habsorption : absorption ≠ 0) (ht : t ≠ 0) :
    thetaXiSchwarzschildAIMECubicCoefficient
      q M absorption t ≠ 0 := by
  exact schwarzschildAbsorptionInducedCubicCoefficient_ne_zero
    hM habsorption ht (xiSpectralPoint_ne_zero q)

/-- The critical-line reflection partner carries the conjugate centered
spectral frequency in the same AIME law. -/
theorem thetaXiSchwarzschildAIMECubicCoefficient_lineConj
    (q : XiZeroCopy) (M absorption t : ℝ) :
    thetaXiSchwarzschildAIMECubicCoefficient
        (xiZeroCopyLineConjEquiv q) M absorption t =
      schwarzschildAbsorptionInducedCubicCoefficient
        M absorption t (starRingEnd ℂ (xiSpectralPoint q)) := by
  rw [thetaXiSchwarzschildAIMECubicCoefficient,
    xiSpectralPoint_lineConj]

/-- Packaged unconditional endpoint: every Xi sector is AIME-bright at every
nondegenerate Schwarzschild mass, absorption response, and observation time. -/
theorem thetaXiSchwarzschildAIME_mixesEveryMode
    {M absorption t : ℝ} (hM : M ≠ 0)
    (habsorption : absorption ≠ 0) (ht : t ≠ 0) :
    ∀ q : XiZeroCopy,
      thetaXiSchwarzschildAIMECubicCoefficient
        q M absorption t ≠ 0 :=
  fun q => thetaXiSchwarzschildAIMECubicCoefficient_ne_zero
    q hM habsorption ht

end RHTower
