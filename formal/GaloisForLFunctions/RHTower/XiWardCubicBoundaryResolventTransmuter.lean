import GaloisForLFunctions.RHTower.XiWardCubicApertureRateChangeConnectionJet

/-!
# Cubic Ward boundary-resolvent transmuter (W-H197)

W-H194--W-H196 force every primitive-to-Xi landing to break aperture covariance with connection
jet `2 (w-z)`.  This module identifies the canonical causal boundary architecture having exactly
that jet.  The Laplace symbol of the generalized radial mode `r exp (-z r)` is `(p+z)⁻²`, so its
scalar transmuter to rate `w` is uniquely

`H_{z,w}(p)=((p+z)/(p+w))²
            =1+2(z-w)/(p+w)+(z-w)²/(p+w)²`.

Thus cubic landing requires exactly two target-resolvent boundary channels, with coefficients
given by the full signed complex spectral gap.  This is a concrete positive architecture, but it
is not passive.  At the target boundary resonance `p=-i Im(w)`, every real rate decrease
`0<Re(w)<Re(z)` forces `|H_{z,w}(p)|>1`.  In particular the primitive-to-strict-right transmuter
has gain above one.  A successful source trace law therefore cannot use this channel as a
standalone contraction; it must retain it inside an augmented pole--Gamma colligation whose
additional signed channel pays the gain.
-/

open Complex

namespace RHTower

noncomputable section

/-- Laplace symbol of the length-two generalized radial mode `r exp (-z r)`. -/
def xiWardCubicLaplaceGeneralizedMode (z p : ℂ) : ℂ :=
  (p + z)⁻¹ ^ 2

/-- Canonical second-order boundary-resolvent scalar changing cubic rate `z` to rate `w`. -/
def xiWardCubicBoundaryResolventTransfer (z w p : ℂ) : ℂ :=
  ((p + z) / (p + w)) ^ 2

/-- Feedthrough, first-resolvent, and second-resolvent decomposition of the transmuter. -/
theorem xiWardCubicBoundaryResolventTransfer_eq_resolventExpansion
    (z w p : ℂ) (h : p + w ≠ 0) :
    xiWardCubicBoundaryResolventTransfer z w p =
      1 + 2 * (z - w) / (p + w) + (z - w) ^ 2 / (p + w) ^ 2 := by
  rw [xiWardCubicBoundaryResolventTransfer]
  field_simp [h]
  ring

/-- Exact Laplace-domain rate transmutation. -/
theorem xiWardCubicBoundaryResolventTransfer_mul_laplaceMode
    (z w p : ℂ) (hz : p + z ≠ 0) (hw : p + w ≠ 0) :
    xiWardCubicBoundaryResolventTransfer z w p *
        xiWardCubicLaplaceGeneralizedMode z p =
      xiWardCubicLaplaceGeneralizedMode w p := by
  rw [xiWardCubicBoundaryResolventTransfer,
    xiWardCubicLaplaceGeneralizedMode, xiWardCubicLaplaceGeneralizedMode]
  field_simp [hz, hw]

/-- Pointwise uniqueness of the scalar Laplace transmuter. -/
theorem xiWardCubicBoundaryResolventTransfer_unique
    (z w p H : ℂ) (hz : p + z ≠ 0) (hw : p + w ≠ 0)
    (hmap : H * xiWardCubicLaplaceGeneralizedMode z p =
      xiWardCubicLaplaceGeneralizedMode w p) :
    H = xiWardCubicBoundaryResolventTransfer z w p := by
  unfold xiWardCubicLaplaceGeneralizedMode at hmap
  unfold xiWardCubicBoundaryResolventTransfer
  field_simp [hz, hw] at hmap ⊢
  exact hmap

/-- At target boundary resonance the target denominator is its horizontal rate. -/
theorem xiWardCubic_targetResonance_add_rate (w : ℂ) :
    -I * (w.im : ℂ) + w = (w.re : ℂ) := by
  apply Complex.ext
  · simp
  · simp

/-- At target boundary resonance the source numerator retains signed ordinate displacement. -/
theorem xiWardCubic_targetResonance_add_source (z w : ℂ) :
    -I * (w.im : ℂ) + z =
      (z.re : ℂ) + I * ((z.im - w.im : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp
    ring

/-- Exact resonant power gain of the two-resolvent transmuter. -/
theorem normSq_xiWardCubicBoundaryResolventTransfer_targetResonance
    (z w : ℂ) :
    Complex.normSq
        (xiWardCubicBoundaryResolventTransfer z w (-I * (w.im : ℂ))) =
      ((z.re ^ 2 + (z.im - w.im) ^ 2) / w.re ^ 2) ^ 2 := by
  rw [xiWardCubicBoundaryResolventTransfer,
    xiWardCubic_targetResonance_add_rate,
    xiWardCubic_targetResonance_add_source]
  rw [pow_two, Complex.normSq_mul, Complex.normSq_div]
  simp [Complex.normSq_apply]
  ring

/-- Every strict real rate decrease forces resonant power gain above one. -/
theorem one_lt_normSq_xiWardCubicBoundaryResolventTransfer_targetResonance
    {z w : ℂ} (hw : 0 < w.re) (hgap : w.re < z.re) :
    1 < Complex.normSq
      (xiWardCubicBoundaryResolventTransfer z w (-I * (w.im : ℂ))) := by
  rw [normSq_xiWardCubicBoundaryResolventTransfer_targetResonance]
  have hz : 0 < z.re := hw.trans hgap
  have hratio :
      1 < (z.re ^ 2 + (z.im - w.im) ^ 2) / w.re ^ 2 := by
    rw [one_lt_div (sq_pos_of_pos hw)]
    nlinarith [sq_nonneg (z.im - w.im),
      sq_lt_sq₀ hw.le hz.le |>.2 hgap]
  have hsum :
      0 < (z.re ^ 2 + (z.im - w.im) ^ 2) / w.re ^ 2 + 1 := by
    linarith
  nlinarith [mul_pos (sub_pos.mpr hratio) hsum]

/-- Equivalent amplitude-gain form. -/
theorem one_lt_norm_xiWardCubicBoundaryResolventTransfer_targetResonance
    {z w : ℂ} (hw : 0 < w.re) (hgap : w.re < z.re) :
    1 < ‖xiWardCubicBoundaryResolventTransfer z w (-I * (w.im : ℂ))‖ := by
  have h :=
    one_lt_normSq_xiWardCubicBoundaryResolventTransfer_targetResonance hw hgap
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg
    (xiWardCubicBoundaryResolventTransfer z w (-I * (w.im : ℂ)))]

/-- **W-H197 active-channel wall.** The canonical cubic boundary-resolvent transmuter from every
primitive Euler mode to every actual strict-right Xi mode has resonant power gain above one. -/
theorem one_lt_normSq_primitive_to_strictRight_boundaryResolventTransfer
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    1 < Complex.normSq
      (xiWardCubicBoundaryResolventTransfer
        (routePPrimitiveBurnolSpectralPoint pe kappa - 1 / 2)
        ((q.1.1 : ℂ) - 1 / 2)
        (-I * ((((q.1.1 : ℂ) - 1 / 2).im : ℝ) : ℂ))) := by
  apply one_lt_normSq_xiWardCubicBoundaryResolventTransfer_targetResonance
  · have h := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half] at h
    exact h
  · have hgap := xiRightCenteredZero_re_lt_primitiveBurnolLogFrequency pe q
    rw [xiRightCenteredZero_eq_support_sub_half] at hgap
    norm_num [Complex.sub_re] at hgap ⊢
    rw [routePPrimitiveBurnolSpectralPoint_re]
    linarith

end

end RHTower
