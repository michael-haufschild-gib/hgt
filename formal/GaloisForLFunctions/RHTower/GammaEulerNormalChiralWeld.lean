import GaloisForLFunctions.HTGeometry.SymmetricChiralShapeLogDeriv
import GaloisForLFunctions.RHTower.FiniteEulerInert

/-!
# Euler normal shifts are Gamma-shape chiral shifts

For an exponential ray of rate `r`, put

`λ = i r / (2π)`,
`E_r(s) = 1 - exp(-rs)`, and
`q_r(s) = rs exp(rs/2) / (4π²)`.

Euler reflection gives the exact endpoint weld

`q_r(s) E_r(s) Γ(λs) Γ(-λs) = 1`.

The finite plaquette law for symmetric/chiral carriers then identifies a spectral normal shift of
the Euler factor with the corresponding Gamma shape shift.  For `r = log p`, this is the local
factor of `ζ(s-α)/ζ(s+α)`.  No zeta zero, analytic continuation, or RH assumption occurs.
-/

noncomputable section

namespace RHTower

open Complex GaloisForLFunctions.HTGeometry

/-- Imaginary Gamma slope attached to an exponential rate. -/
def exponentialRayGammaSlope (rate : ℂ) : ℂ :=
  Complex.I * rate / (2 * (Real.pi : ℂ))

/-- Inverse local Euler factor on one exponential ray. -/
def exponentialRayEulerFactor (rate s : ℂ) : ℂ :=
  1 - Complex.exp (-rate * s)

/-- Explicit DA gauge relating the reciprocal symmetric Gamma endpoint to the Euler factor. -/
def exponentialRayGammaGauge (rate s : ℂ) : ℂ :=
  rate * s * Complex.exp (rate * s / 2) / (4 * (Real.pi : ℂ) ^ (2 : ℕ))

/-- At rate `log p`, the exponential-ray factor is literally the corpus's entire inverse local
Euler factor. -/
theorem exponentialRayEulerFactor_logPrime_eq_eulerInvFactor (p : ℕ) (s : ℂ) :
    exponentialRayEulerFactor (Real.log p : ℂ) s = eulerInvFactor p s := by
  unfold exponentialRayEulerFactor eulerInvFactor
  congr 2
  ring

private theorem gamma_symmetric_endpoint_mul (u : ℂ)
    (hu : u ≠ 0) (hsin : Complex.sin ((Real.pi : ℂ) * u) ≠ 0) :
    u * Complex.sin ((Real.pi : ℂ) * u) *
        (Complex.Gamma u * Complex.Gamma (-u)) = -(Real.pi : ℂ) := by
  have hrec :
      Complex.Gamma (1 - u) = (-u) * Complex.Gamma (-u) := by
    convert Complex.Gamma_add_one (-u) (neg_ne_zero.mpr hu) using 1 ; ring
  have href := Complex.Gamma_mul_Gamma_one_sub u
  rw [hrec] at href
  have href' :
      (Complex.Gamma u * ((-u) * Complex.Gamma (-u))) *
          Complex.sin ((Real.pi : ℂ) * u) = (Real.pi : ℂ) :=
    (eq_div_iff hsin).mp href
  calc
    u * Complex.sin ((Real.pi : ℂ) * u) *
        (Complex.Gamma u * Complex.Gamma (-u)) =
        -((Complex.Gamma u * ((-u) * Complex.Gamma (-u))) *
          Complex.sin ((Real.pi : ℂ) * u)) := by ring
    _ = -(Real.pi : ℂ) := by rw [href']

private theorem sin_exponentialRayGammaSlope (rate s : ℂ) :
    Complex.sin ((Real.pi : ℂ) * exponentialRayGammaSlope rate * s) =
      Complex.I / 2 *
        (Complex.exp (rate * s / 2) - Complex.exp (-(rate * s / 2))) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (Real.pi : ℂ) * exponentialRayGammaSlope rate * s =
      (rate * s / 2) * Complex.I by
    unfold exponentialRayGammaSlope
    field_simp [hpi]]
  rw [Complex.sin_mul_I]
  unfold Complex.sinh
  ring

private theorem gauge_mul_euler_eq_neg_slope_sin_div_pi
    (rate s : ℂ) :
    exponentialRayGammaGauge rate s * exponentialRayEulerFactor rate s =
      -(exponentialRayGammaSlope rate * s *
        Complex.sin ((Real.pi : ℂ) * exponentialRayGammaSlope rate * s)) /
          (Real.pi : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hexp :
      Complex.exp (rate * s / 2) * Complex.exp (-rate * s) =
        Complex.exp (-(rate * s / 2)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [sin_exponentialRayGammaSlope]
  unfold exponentialRayGammaGauge exponentialRayEulerFactor exponentialRayGammaSlope
  calc
    rate * s * Complex.exp (rate * s / 2) / (4 * (Real.pi : ℂ) ^ (2 : ℕ)) *
        (1 - Complex.exp (-rate * s)) =
      rate * s / (4 * (Real.pi : ℂ) ^ (2 : ℕ)) *
        (Complex.exp (rate * s / 2) -
          Complex.exp (rate * s / 2) * Complex.exp (-rate * s)) := by ring
    _ = rate * s / (4 * (Real.pi : ℂ) ^ (2 : ℕ)) *
        (Complex.exp (rate * s / 2) -
          Complex.exp (-(rate * s / 2))) := by rw [hexp]
    _ = -(Complex.I * rate / (2 * (Real.pi : ℂ)) * s *
          (Complex.I / 2 *
            (Complex.exp (rate * s / 2) -
              Complex.exp (-(rate * s / 2))))) /
        (Real.pi : ℂ) := by
      field_simp [hpi]
      rw [Complex.I_sq]
      ring

/-- **Local Euler--Gamma endpoint weld.**  The reciprocal symmetric Gamma endpoint is exactly an
inverse Euler factor times an explicit rational/exponential gauge. -/
theorem exponentialRayGammaGauge_mul_eulerFactor_mul_symmetricEndpoint
    (rate s : ℂ)
    (hu : exponentialRayGammaSlope rate * s ≠ 0)
    (hsin : Complex.sin ((Real.pi : ℂ) *
      (exponentialRayGammaSlope rate * s)) ≠ 0) :
    exponentialRayGammaGauge rate s * exponentialRayEulerFactor rate s *
        symmetricShapeCarrier Complex.Gamma
          (exponentialRayGammaSlope rate) 0 s = 1 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [gauge_mul_euler_eq_neg_slope_sin_div_pi]
  unfold symmetricShapeCarrier
  simp only [zero_add, zero_sub]
  have hend := gamma_symmetric_endpoint_mul
    (exponentialRayGammaSlope rate * s) hu hsin
  calc
    (-(exponentialRayGammaSlope rate * s *
        Complex.sin ((Real.pi : ℂ) * exponentialRayGammaSlope rate * s)) /
          (Real.pi : ℂ)) *
        (Complex.Gamma (exponentialRayGammaSlope rate * s) *
          Complex.Gamma (-(exponentialRayGammaSlope rate * s))) =
        -((exponentialRayGammaSlope rate * s) *
          Complex.sin ((Real.pi : ℂ) * (exponentialRayGammaSlope rate * s)) *
            (Complex.Gamma (exponentialRayGammaSlope rate * s) *
              Complex.Gamma (-(exponentialRayGammaSlope rate * s)))) /
            (Real.pi : ℂ) := by ring
    _ = 1 := by rw [hend]; field_simp [hpi]

/-- Algebraic transport from two endpoint welds to a normal-shift quotient. -/
private theorem endpointWeld_shiftRatio
    (q E M : ℂ → ℂ) (s h : ℂ)
    (hplus : q (s + h) * E (s + h) * M (s + h) = 1)
    (hminus : q (s - h) * E (s - h) * M (s - h) = 1) :
    E (s + h) / E (s - h) =
      q (s - h) / q (s + h) * (M (s - h) / M (s + h)) := by
  have hqEp : q (s + h) * E (s + h) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hplus
    exact zero_ne_one hplus
  have hqEm : q (s - h) * E (s - h) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hminus
    exact zero_ne_one hminus
  have hqMp : q (s + h) * M (s + h) ≠ 0 := by
    intro hz
    have : q (s + h) * E (s + h) * M (s + h) = 0 := by
      calc
        q (s + h) * E (s + h) * M (s + h) =
            E (s + h) * (q (s + h) * M (s + h)) := by ring
        _ = 0 := by rw [hz, mul_zero]
    rw [hplus] at this
    exact one_ne_zero this
  have hqMm : q (s - h) * M (s - h) ≠ 0 := by
    intro hz
    have : q (s - h) * E (s - h) * M (s - h) = 0 := by
      calc
        q (s - h) * E (s - h) * M (s - h) =
            E (s - h) * (q (s - h) * M (s - h)) := by ring
        _ = 0 := by rw [hz, mul_zero]
    rw [hminus] at this
    exact one_ne_zero this
  rcases mul_ne_zero_iff.mp hqEp with ⟨hqp, hEp⟩
  rcases mul_ne_zero_iff.mp hqEm with ⟨hqm, hEm⟩
  rcases mul_ne_zero_iff.mp hqMp with ⟨_, hMp⟩
  rcases mul_ne_zero_iff.mp hqMm with ⟨_, hMm⟩
  have hEplus :
      E (s + h) = 1 / (q (s + h) * M (s + h)) := by
    apply (eq_div_iff hqMp).2
    calc
      E (s + h) * (q (s + h) * M (s + h)) =
          q (s + h) * E (s + h) * M (s + h) := by ring
      _ = 1 := hplus
  have hEminus :
      E (s - h) = 1 / (q (s - h) * M (s - h)) := by
    apply (eq_div_iff hqMm).2
    calc
      E (s - h) * (q (s - h) * M (s - h)) =
          q (s - h) * E (s - h) * M (s - h) := by ring
      _ = 1 := hminus
  rw [hEplus, hEminus]
  field_simp [hqp, hqm, hEp, hEm, hMp, hMm]

/-- **Euler normal shift / Gamma shape shift weld.**  A spectral normal displacement of an
exponential Euler factor is the corresponding chiral Gamma shape displacement, up to the explicit
DA gauge.  At `rate = log p` the left side is one local factor of
`ζ(s-h)/ζ(s+h)`. -/
theorem exponentialRayEulerNormalShift_eq_gammaChiralShapeShift
    (rate s h : ℂ)
    (hup : exponentialRayGammaSlope rate * (s + h) ≠ 0)
    (hum : exponentialRayGammaSlope rate * (s - h) ≠ 0)
    (hsinp : Complex.sin ((Real.pi : ℂ) *
      (exponentialRayGammaSlope rate * (s + h))) ≠ 0)
    (hsinm : Complex.sin ((Real.pi : ℂ) *
      (exponentialRayGammaSlope rate * (s - h))) ≠ 0)
    (hGpp : Complex.Gamma
      (exponentialRayGammaSlope rate * (s + h)) ≠ 0)
    (hGmp : Complex.Gamma
      (-(exponentialRayGammaSlope rate * (s + h))) ≠ 0) :
    exponentialRayEulerFactor rate (s + h) /
        exponentialRayEulerFactor rate (s - h) =
      exponentialRayGammaGauge rate (s - h) /
          exponentialRayGammaGauge rate (s + h) *
        (chiralShapeCarrier Complex.Gamma
            (exponentialRayGammaSlope rate)
            (-(exponentialRayGammaSlope rate * h)) s /
          chiralShapeCarrier Complex.Gamma
            (exponentialRayGammaSlope rate)
            (exponentialRayGammaSlope rate * h) s) := by
  let lam := exponentialRayGammaSlope rate
  let q := exponentialRayGammaGauge rate
  let E := exponentialRayEulerFactor rate
  let M := fun z =>
    symmetricShapeCarrier Complex.Gamma (exponentialRayGammaSlope rate) 0 z
  have hplus : q (s + h) * E (s + h) * M (s + h) = 1 := by
    exact exponentialRayGammaGauge_mul_eulerFactor_mul_symmetricEndpoint
      rate (s + h) hup hsinp
  have hminus : q (s - h) * E (s - h) * M (s - h) = 1 := by
    exact exponentialRayGammaGauge_mul_eulerFactor_mul_symmetricEndpoint
      rate (s - h) hum hsinm
  have hshift := endpointWeld_shiftRatio q E M s h hplus hminus
  have hplaq :
      M (s - h) / M (s + h) =
        chiralShapeCarrier Complex.Gamma
            (exponentialRayGammaSlope rate)
            (-(exponentialRayGammaSlope rate * h)) s /
          chiralShapeCarrier Complex.Gamma
            (exponentialRayGammaSlope rate)
            (exponentialRayGammaSlope rate * h) s := by
    simpa [M, lam] using
      symmetricSpectralShift_ratio_eq_chiralShapeShift_ratio
        Complex.Gamma (exponentialRayGammaSlope rate) 0 s h
          (by simpa only [zero_add] using hGpp)
          (by simpa only [zero_sub] using hGmp)
  simpa [q, E, M, hplaq] using hshift

/-- On the genuine prime ray, positive spectral real part puts the Gamma argument strictly in the
upper half-plane. -/
private theorem im_exponentialRayGammaSlope_logPrime_mul_pos
    {p : ℕ} (hp : 1 < p) {z : ℂ} (hz : 0 < z.re) :
    0 < (exponentialRayGammaSlope (Real.log p : ℂ) * z).im := by
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hslope :
      exponentialRayGammaSlope (Real.log p : ℂ) =
        ((Real.log p / (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    unfold exponentialRayGammaSlope
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hslope]
  simp only [mul_assoc, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, zero_mul, add_zero, one_mul]
  simpa only [zero_add] using mul_pos (div_pos hlog hpi) hz

/-- **Prime-local safe-region form.**  For `p > 1` and both displaced spectral points in the
right half-plane, all nonvanishing premises of the abstract weld follow automatically. -/
theorem eulerInvFactor_normalShift_eq_gammaChiralShapeShift
    (p : ℕ) (hp : 1 < p) (s h : ℂ)
    (hsp : 0 < (s + h).re) (hsm : 0 < (s - h).re) :
    eulerInvFactor p (s + h) / eulerInvFactor p (s - h) =
      exponentialRayGammaGauge (Real.log p : ℂ) (s - h) /
          exponentialRayGammaGauge (Real.log p : ℂ) (s + h) *
        (chiralShapeCarrier Complex.Gamma
            (exponentialRayGammaSlope (Real.log p : ℂ))
            (-(exponentialRayGammaSlope (Real.log p : ℂ) * h)) s /
          chiralShapeCarrier Complex.Gamma
            (exponentialRayGammaSlope (Real.log p : ℂ))
            (exponentialRayGammaSlope (Real.log p : ℂ) * h) s) := by
  let rate : ℂ := (Real.log p : ℂ)
  let lam := exponentialRayGammaSlope rate
  have himp : 0 < (lam * (s + h)).im :=
    im_exponentialRayGammaSlope_logPrime_mul_pos hp hsp
  have himm : 0 < (lam * (s - h)).im :=
    im_exponentialRayGammaSlope_logPrime_mul_pos hp hsm
  have hup : lam * (s + h) ≠ 0 := by
    intro hu
    rw [hu, Complex.zero_im] at himp
    exact (lt_irrefl 0 himp)
  have hum : lam * (s - h) ≠ 0 := by
    intro hu
    rw [hu, Complex.zero_im] at himm
    exact (lt_irrefl 0 himm)
  have hsinp : Complex.sin ((Real.pi : ℂ) * (lam * (s + h))) ≠ 0 := by
    intro hz
    rcases Complex.sin_eq_zero_iff.mp hz with ⟨k, hk⟩
    have harg :
        0 < (((Real.pi : ℂ) * (lam * (s + h))).im) := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_pos Real.pi_pos himp
    have hzero : (((Real.pi : ℂ) * (lam * (s + h))).im) = 0 := by
      rw [hk]
      simp
    exact (ne_of_gt harg) hzero
  have hsinm : Complex.sin ((Real.pi : ℂ) * (lam * (s - h))) ≠ 0 := by
    intro hz
    rcases Complex.sin_eq_zero_iff.mp hz with ⟨k, hk⟩
    have harg :
        0 < (((Real.pi : ℂ) * (lam * (s - h))).im) := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_pos Real.pi_pos himm
    have hzero : (((Real.pi : ℂ) * (lam * (s - h))).im) = 0 := by
      rw [hk]
      simp
    exact (ne_of_gt harg) hzero
  have hGpp : Complex.Gamma (lam * (s + h)) ≠ 0 :=
    Complex.Gamma_ne_zero fun m hm => by
      have hzero : (lam * (s + h)).im = 0 := by
        rw [hm]
        simp
      exact (ne_of_gt himp) hzero
  have hGmp : Complex.Gamma (-(lam * (s + h))) ≠ 0 :=
    Complex.Gamma_ne_zero fun m hm => by
      have himneg : (-(lam * (s + h))).im < 0 := by
        simpa only [Complex.neg_im] using neg_lt_zero.mpr himp
      have hzero : (-(lam * (s + h))).im = 0 := by
        rw [hm]
        simp
      exact (ne_of_lt himneg) hzero
  rw [← exponentialRayEulerFactor_logPrime_eq_eulerInvFactor p (s + h),
    ← exponentialRayEulerFactor_logPrime_eq_eulerInvFactor p (s - h)]
  exact exponentialRayEulerNormalShift_eq_gammaChiralShapeShift
    rate s h hup hum hsinp hsinm hGpp hGmp

end RHTower
