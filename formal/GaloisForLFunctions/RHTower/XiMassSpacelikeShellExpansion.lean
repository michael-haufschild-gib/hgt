import GaloisForLFunctions.RHTower.XiMassFourierBesselIdentity

/-!
# The linear expansion of the propagation radius on a spacelike shell

On the shell `h = κu + s` with `κ > 1` and `s` in a fixed window, the propagation argument
`τ² + h²` differs from the square of the linear radius

`ζ = q u + (κ s + iσ)/q`,   `q = √(κ²−1)`,

by the *bounded* defect

`σ² + s² − (κ s + iσ)²/(κ²−1)`,

with no dependence on the height `u` at all.  Since both `Re z` and `Re ζ` are at least `q u`, the
elementary identity `z − ζ = (z² − ζ²)/(z + ζ)` turns that bounded defect into

`|z − ζ| ≤ ‖defect‖ / (2 q u)`.

This is the exact form of the principal-root expansion used by the shell analysis: an explicit
`O(1/u)` bound, uniform on every fixed window of `s`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The bounded, height-independent defect of the linear shell approximation. -/
def xiMassShellDefect (sigma kappa s : ℝ) : ℂ :=
  (sigma : ℂ) ^ 2 + (s : ℂ) ^ 2
    - ((kappa : ℂ) * (s : ℂ) + (sigma : ℂ) * I) ^ 2
      / ((Real.sqrt (kappa ^ 2 - 1) : ℝ) : ℂ) ^ 2

/-- The linear shell approximation to the propagation radius. -/
def xiMassShellRadius (sigma kappa u s : ℝ) : ℂ :=
  ((Real.sqrt (kappa ^ 2 - 1) * u : ℝ) : ℂ)
    + ((kappa : ℂ) * (s : ℂ) + (sigma : ℂ) * I)
        / ((Real.sqrt (kappa ^ 2 - 1) : ℝ) : ℂ)

/-- The propagation argument of the shell. -/
def xiMassShellArgument (sigma kappa u s : ℝ) : ℂ :=
  ((sigma : ℂ) + (u : ℂ) * I) ^ 2 + ((kappa * u + s : ℝ) : ℂ) ^ 2

theorem xiMassShellArgument_re (sigma kappa u s : ℝ) :
    (xiMassShellArgument sigma kappa u s).re
      = (kappa ^ 2 - 1) * u ^ 2 + 2 * kappa * u * s + (sigma ^ 2 + s ^ 2) := by
  rw [xiMassShellArgument]
  simp [Complex.add_re, Complex.mul_re, pow_two]
  ring

theorem xiMassShellArgument_re_pos {sigma kappa u s : ℝ} (hkappa : 1 < kappa) (hu : 0 < u)
    (hs : 0 ≤ s) (hsigma : 0 < sigma) : 0 < (xiMassShellArgument sigma kappa u s).re := by
  rw [xiMassShellArgument_re]
  have hk2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  nlinarith [sq_nonneg s, sq_nonneg u, mul_nonneg (mul_nonneg hkappa0.le hu.le) hs]

/-- **The exact defect identity.**  The linear radius reproduces the propagation argument up to a
height-independent constant. -/
theorem xiMassShellArgument_sub_shellRadius_sq {sigma kappa u s : ℝ} (hkappa : 1 < kappa) :
    xiMassShellArgument sigma kappa u s - xiMassShellRadius sigma kappa u s ^ 2
      = xiMassShellDefect sigma kappa s := by
  have hk2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hq : (0 : ℝ) < Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_pos.2 hk2
  have hqsq : Real.sqrt (kappa ^ 2 - 1) ^ 2 = kappa ^ 2 - 1 := Real.sq_sqrt hk2.le
  have hqC : ((Real.sqrt (kappa ^ 2 - 1) : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hq
  have hqsqC : ((Real.sqrt (kappa ^ 2 - 1) : ℝ) : ℂ) ^ 2 = (kappa : ℂ) ^ 2 - 1 := by
    rw [← Complex.ofReal_pow, hqsq]
    push_cast
    ring
  have hk2C : ((kappa : ℂ) ^ 2 - 1) ≠ 0 := by
    rw [← hqsqC]
    exact pow_ne_zero 2 hqC
  have hcast : ((Real.sqrt (kappa ^ 2 - 1) * u : ℝ) : ℂ)
      = ((Real.sqrt (kappa ^ 2 - 1) : ℝ) : ℂ) * (u : ℂ) := by push_cast; ring
  have hcast2 : ((kappa * u + s : ℝ) : ℂ) = (kappa : ℂ) * (u : ℂ) + (s : ℂ) := by push_cast; ring
  rw [xiMassShellArgument, xiMassShellRadius, xiMassShellDefect, hcast, hcast2]
  field_simp
  linear_combination ((u : ℂ) ^ 2 * ((Real.sqrt (kappa ^ 2 - 1) : ℝ) : ℂ) ^ 2) * Complex.I_sq
    - ((u : ℂ) ^ 2 * ((Real.sqrt (kappa ^ 2 - 1) : ℝ) : ℂ) ^ 2) * hqsqC

/-- Both the true and the linear radius have real part at least `q u`. -/
theorem shellRadius_re_ge {sigma kappa u s : ℝ} (hkappa : 1 < kappa) (hs : 0 ≤ s) :
    Real.sqrt (kappa ^ 2 - 1) * u ≤ (xiMassShellRadius sigma kappa u s).re := by
  have hk2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hq : (0 : ℝ) < Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_pos.2 hk2
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hval : (xiMassShellRadius sigma kappa u s).re
      = Real.sqrt (kappa ^ 2 - 1) * u + kappa * s / Real.sqrt (kappa ^ 2 - 1) := by
    rw [xiMassShellRadius]
    simp [Complex.add_re, Complex.div_re, Complex.mul_re, Complex.normSq_apply]
    field_simp
  rw [hval]
  have : 0 ≤ kappa * s / Real.sqrt (kappa ^ 2 - 1) := by positivity
  linarith

theorem csqrt_shellArgument_re_ge {sigma kappa u s : ℝ} (hkappa : 1 < kappa) (hu : 0 < u)
    (hs : 0 ≤ s) (hsigma : 0 < sigma) :
    Real.sqrt (kappa ^ 2 - 1) * u
      ≤ HTGeometry.csqrtRe (xiMassShellArgument sigma kappa u s) := by
  have hpos := xiMassShellArgument_re_pos hkappa hu hs hsigma
  have hk2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hq : (0 : ℝ) < Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_pos.2 hk2
  have hqsq : Real.sqrt (kappa ^ 2 - 1) ^ 2 = kappa ^ 2 - 1 := Real.sq_sqrt hk2.le
  have hle := HTGeometry.re_le_sq_csqrtRe hpos
  have hnn : 0 ≤ HTGeometry.csqrtRe (xiMassShellArgument sigma kappa u s) :=
    HTGeometry.csqrtRe_nonneg _
  rw [xiMassShellArgument_re] at hle
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hlow : (kappa ^ 2 - 1) * u ^ 2
      ≤ HTGeometry.csqrtRe (xiMassShellArgument sigma kappa u s) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hkappa0.le hu.le) hs, sq_nonneg s, sq_nonneg sigma]
  nlinarith [hqsq, mul_nonneg hq.le hu.le]

/-- **The principal-root shell expansion.**  On every fixed window of `s` the principal root of the
propagation argument is within `O(1/u)` of its linear approximation, with an explicit constant. -/
theorem norm_csqrt_shellArgument_sub_shellRadius_le {sigma kappa u s : ℝ} (hkappa : 1 < kappa)
    (hu : 0 < u) (hs : 0 ≤ s) (hsigma : 0 < sigma) :
    ‖HTGeometry.csqrt (xiMassShellArgument sigma kappa u s)
        - xiMassShellRadius sigma kappa u s‖
      ≤ ‖xiMassShellDefect sigma kappa s‖ / (2 * Real.sqrt (kappa ^ 2 - 1) * u) := by
  have hpos := xiMassShellArgument_re_pos hkappa hu hs hsigma
  have hk2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hq : (0 : ℝ) < Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_pos.2 hk2
  set z : ℂ := HTGeometry.csqrt (xiMassShellArgument sigma kappa u s) with hz
  set ζ : ℂ := xiMassShellRadius sigma kappa u s with hζ
  have hzsq : z ^ 2 = xiMassShellArgument sigma kappa u s := HTGeometry.csqrt_sq hpos
  have hdef : z ^ 2 - ζ ^ 2 = xiMassShellDefect sigma kappa s := by
    rw [hzsq, hζ]
    exact xiMassShellArgument_sub_shellRadius_sq hkappa
  have hzre : Real.sqrt (kappa ^ 2 - 1) * u ≤ z.re := by
    rw [hz, HTGeometry.csqrt_re]
    exact csqrt_shellArgument_re_ge hkappa hu hs hsigma
  have hζre : Real.sqrt (kappa ^ 2 - 1) * u ≤ ζ.re := by
    rw [hζ]
    exact shellRadius_re_ge hkappa hs
  have hsum : 2 * (Real.sqrt (kappa ^ 2 - 1) * u) ≤ ‖z + ζ‖ := by
    refine le_trans ?_ (Complex.re_le_norm (z + ζ))
    rw [Complex.add_re]
    linarith
  have hsumpos : (0 : ℝ) < 2 * (Real.sqrt (kappa ^ 2 - 1) * u) := by positivity
  have hne : z + ζ ≠ 0 := by
    intro hzero
    rw [hzero] at hsum
    simp at hsum
    linarith
  have hkey : z - ζ = xiMassShellDefect sigma kappa s / (z + ζ) := by
    rw [← hdef]
    field_simp
    ring
  rw [hkey, norm_div]
  rw [div_le_div_iff₀ (lt_of_lt_of_le hsumpos hsum) (by positivity)]
  have hnn : (0 : ℝ) ≤ ‖xiMassShellDefect sigma kappa s‖ := norm_nonneg _
  calc ‖xiMassShellDefect sigma kappa s‖ * (2 * Real.sqrt (kappa ^ 2 - 1) * u)
      = ‖xiMassShellDefect sigma kappa s‖ * (2 * (Real.sqrt (kappa ^ 2 - 1) * u)) := by ring
    _ ≤ ‖xiMassShellDefect sigma kappa s‖ * ‖z + ζ‖ :=
        mul_le_mul_of_nonneg_left hsum hnn

end

end RHTower
