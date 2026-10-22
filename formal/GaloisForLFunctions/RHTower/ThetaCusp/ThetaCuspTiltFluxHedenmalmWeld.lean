import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxSourceWeld
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmExteriorGaussianHankel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedDivisorTomography

/-!
# The scalar theta-tilt flux is the Hedenmalm transverse current

After the rotation `xiCent w = XiC (-I*w)`, the diagonal Bezoutian of the literal theta tilt
source is exactly the zero-safe Hedenmalm transverse current divided by twice the aperture. Within
the theta Fourier strip this is the concrete center-mixed Fourier current divided by `2a`.

The corpus's exterior Hedenmalm theorem then proves every one-mode neutral TTF derivative
nonnegative throughout the full Euler domain `Re w >= 1/2`, unconditionally. Thus the RH-bearing
content of TTF cannot occur in a scalar mode; it begins with cross-mode coherence of a packet.
-/

open Complex Set
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Differential form of the centered-coordinate rotation `xiCent W = XiC (-I*W)`. -/
theorem deriv_xiCent_eq_neg_I_mul_deriv_XiC (W : ℂ) :
    deriv xiCent W = -I * deriv XiC (-I * W) := by
  have h := (XiC_differentiable (-I * W)).hasDerivAt.comp W
    ((hasDerivAt_const W (-I)).mul (hasDerivAt_id W))
  change HasDerivAt (fun z : ℂ => XiC (-I * z))
    (deriv XiC (-I * W) * (0 * W + -I * 1)) W at h
  simp only [zero_mul, zero_add, mul_one] at h
  have hfun : (fun z : ℂ => XiC (-I * z)) = xiCent := by
    funext z
    exact (xiCent_eq_XiC z).symm
  rw [hfun] at h
  rw [h.deriv]
  ring

/-- **Scalar TTF--Hedenmalm weld.** The literal theta-source diagonal Bezoutian is the zero-safe
transverse completed-Xi current divided by the positive Cauchy aperture. -/
theorem sourceBezoutian_thetaCuspTiltSource_self_re_eq_transverseCurrent_div
    {a b : ℝ} (ha : 0 < a) :
    (sourceBezoutian thetaCuspTiltSource
      ((a : ℂ) + (b : ℂ) * I)
      ((a : ℂ) + (b : ℂ) * I)).re =
      xiTransverseEnergyCurrent a b / (2 * a) := by
  let w : ℂ := (a : ℂ) + (b : ℂ) * I
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have hden : w + conj w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
    linarith
  have hz : -I * w = z := by
    apply Complex.ext <;> simp [w, z, Complex.mul_re, Complex.mul_im]
  have hnum :
      (deriv xiCent w * xiCent (conj w) +
        xiCent w * deriv xiCent (conj w)).re =
        xiTransverseEnergyCurrent a b := by
    rw [xiCent_conj, deriv_xiCent_conj,
      deriv_xiCent_eq_neg_I_mul_deriv_XiC,
      xiCent_eq_XiC, hz]
    rw [xiTransverseEnergyCurrent]
    change
      (-I * deriv XiC z * conj (XiC z) +
        XiC z * conj (-I * deriv XiC z)).re =
        2 * (deriv XiC z * conj (XiC z)).im
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [show (a : ℂ) + (b : ℂ) * I = w by rfl,
    sourceBezoutian_thetaCuspTiltSource_eq_xiCentBezoutian hden,
    xiCentBezoutian_eq_div hden, xiCentBezoutianNumerator]
  rw [show w + conj w = ((2 * a : ℝ) : ℂ) by
    apply Complex.ext
    · simp [w]
      ring
    · simp [w]]
  rw [Complex.div_ofReal_re, hnum]

/-- Inside the theta Fourier strip, the scalar TTF diagonal is literally the Hedenmalm
center-mixed Fourier current divided by `2a`. -/
theorem sourceBezoutian_thetaCuspTiltSource_self_re_eq_centerMixedCurrent_div
    {a b : ℝ} (ha : 0 < a) (haOne : a < 1) :
    (sourceBezoutian thetaCuspTiltSource
      ((a : ℂ) + (b : ℂ) * I)
      ((a : ℂ) + (b : ℂ) * I)).re =
      thetaCuspCenterMixedFourierCurrent a
        (by rw [abs_of_pos ha]; exact haOne) b / (2 * a) := by
  rw [sourceBezoutian_thetaCuspTiltSource_self_re_eq_transverseCurrent_div ha]
  rw [thetaCuspCenterMixedFourierCurrent_eq_xiTransverseEnergyCurrent]

/-- The zero-safe transverse current and the pointed Hedenmalm orbit's split Krein value are the
same scalar on every aperture and frequency, without a strip restriction. -/
theorem xiTransverseEnergyCurrent_eq_thetaXiHankelOrbit_kreinForm
    (a b : ℝ) :
    xiTransverseEnergyCurrent a b =
      hedenmalmHankelKreinForm
        (thetaXiHankelOrbitValuePlus a b)
        (thetaXiHankelOrbitTangentPlus a b)
        (thetaXiHankelOrbitValueMinus a b)
        (thetaXiHankelOrbitTangentMinus a b) := by
  rw [thetaXiHankelOrbit_kreinForm_eq]
  simp only [xiTransverseEnergyCurrent, thetaXiHankelOrbitValuePlus,
    thetaXiHankelOrbitTangentPlus]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Every scalar literal-theta TTF Bezoutian is unconditionally nonnegative on and beyond the
Euler boundary. -/
theorem sourceBezoutian_thetaCuspTiltSource_self_nonneg_of_half_le
    {a : ℝ} (ha : 1 / 2 ≤ a) (b : ℝ) :
    0 ≤ (sourceBezoutian thetaCuspTiltSource
      ((a : ℂ) + (b : ℂ) * I)
      ((a : ℂ) + (b : ℂ) * I)).re := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  rw [sourceBezoutian_thetaCuspTiltSource_self_re_eq_transverseCurrent_div ha0]
  apply div_nonneg ?_ (mul_nonneg (by norm_num) ha0.le)
  rw [xiTransverseEnergyCurrent_eq_thetaXiHankelOrbit_kreinForm]
  exact thetaXiHankelOrbit_kreinForm_nonneg_of_half_le ha b

/-- **Rank-one TTF discharge.** Every literal one-mode neutral tilt derivative is nonnegative on
the full closed Euler half-plane. Hence any RH-bearing TTF obstruction needs at least two modes. -/
theorem thetaCuspTiltSource_oneMode_tiltFlux_nonneg
    {w : ℂ} (hw : 1 / 2 ≤ w.re) {D : ℝ}
    (hD : HasDerivAt
      (tiltCorrelation thetaCuspTiltSource
        (fun _ : Fin 1 => 1) (fun _ : Fin 1 => w)) D 0) :
    0 ≤ D := by
  have hw0 : 0 < w.re := lt_of_lt_of_le (by norm_num) hw
  have hcanonical :=
    hasDerivAt_tiltCorrelation thetaCuspTiltSource
      (fun _ : Fin 1 => 1) (fun _ : Fin 1 => w)
      (fun _ => hw0)
  rw [hD.unique hcanonical]
  have hcoord : ((w.re : ℂ) + (w.im : ℂ) * I) = w := by
    apply Complex.ext <;> simp
  simpa [hcoord] using
    sourceBezoutian_thetaCuspTiltSource_self_nonneg_of_half_le
      (a := w.re) hw w.im

end

end RHTower
