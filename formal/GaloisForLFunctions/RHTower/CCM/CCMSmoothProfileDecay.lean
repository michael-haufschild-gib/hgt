import GaloisForLFunctions.RHTower.CCM.CCMSmoothTwoEdgeProfile
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Reciprocal-height decay of smooth profile Laplace amplitudes

One integration by parts gives the reciprocal spectral-height bound needed
for absolute summability of the squared Xi-divisor coefficients.
-/

open Complex Filter Function MeasureTheory Set

namespace RHTower

noncomputable section

private def smoothProfileComplex {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (x : ℝ) : ℂ := f x

private def smoothProfileComplexDeriv {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (x : ℝ) : ℂ :=
  ((deriv (fun y : ℝ => (f y : ℝ)) x : ℝ) : ℂ)

/-- The finite `L¹` mass of the first derivative of a fixed smooth
profile. -/
def smoothProfileDerivativeMass {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) : ℝ :=
  ∫ x : ℝ, ‖smoothProfileComplexDeriv f x‖

private theorem continuous_smoothProfileComplex
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) :
    Continuous (smoothProfileComplex f) := by
  unfold smoothProfileComplex
  fun_prop

private theorem continuous_smoothProfileComplexDeriv
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) :
    Continuous (smoothProfileComplexDeriv f) := by
  unfold smoothProfileComplexDeriv
  exact Complex.continuous_ofReal.comp
    (f.contDiff.continuous_deriv (by simp))

private theorem hasCompactSupport_smoothProfileComplex
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) :
    HasCompactSupport (smoothProfileComplex f) := by
  exact f.hasCompactSupport.comp_left rfl

private theorem hasCompactSupport_smoothProfileComplexDeriv
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) :
    HasCompactSupport (smoothProfileComplexDeriv f) := by
  exact f.hasCompactSupport.deriv.comp_left rfl

theorem smoothProfileDerivativeMass_nonneg
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) :
    0 ≤ smoothProfileDerivativeMass f := by
  exact integral_nonneg fun _ => norm_nonneg _

private theorem integrable_smoothProfileComplexDeriv_norm
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) :
    Integrable (fun x => ‖smoothProfileComplexDeriv f x‖) := by
  exact ((continuous_smoothProfileComplexDeriv f).integrable_of_hasCompactSupport
    (hasCompactSupport_smoothProfileComplexDeriv f)).norm

/-- Exact whole-line integration by parts identity for the profile Laplace
amplitude. -/
theorem smoothProfileLaplaceAmplitude_mul
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (w : ℂ) :
    w * smoothProfileLaplaceAmplitude f w =
      ∫ x : ℝ, smoothProfileComplexDeriv f x *
        smoothProfileLaplaceWeight w x := by
  let u : ℝ → ℂ := smoothProfileComplex f
  let u' : ℝ → ℂ := smoothProfileComplexDeriv f
  let v : ℝ → ℂ := smoothProfileLaplaceWeight w
  let v' : ℝ → ℂ := fun x => -w * smoothProfileLaplaceWeight w x
  have hu : ∀ x, HasDerivAt u (u' x) x := by
    intro x
    simpa only [u, u', smoothProfileComplex, smoothProfileComplexDeriv] using!
      ((f.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt).ofReal_comp
  have hv : ∀ x, HasDerivAt v (v' x) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => -(y : ℂ) * w) (-w) x := by
      simpa using!
        (((hasDerivAt_id x).ofReal_comp.neg).mul_const w)
    change HasDerivAt (fun y : ℝ => Complex.exp (-(y : ℂ) * w))
      (-w * Complex.exp (-(x : ℂ) * w)) x
    convert! hlin.cexp using 1
    ring
  have huCont : Continuous u := continuous_smoothProfileComplex f
  have hu'Cont : Continuous u' := continuous_smoothProfileComplexDeriv f
  have hvCont : Continuous v := continuous_smoothProfileLaplaceWeight w
  have hv'Cont : Continuous v' := by
    dsimp only [v']
    exact continuous_const.mul (continuous_smoothProfileLaplaceWeight w)
  have huCompact : HasCompactSupport u := hasCompactSupport_smoothProfileComplex f
  have hu'Compact : HasCompactSupport u' :=
    hasCompactSupport_smoothProfileComplexDeriv f
  have huv : Integrable (u * v) :=
    (huCont.mul hvCont).integrable_of_hasCompactSupport huCompact.mul_right
  have huv' : Integrable (u * v') :=
    (huCont.mul hv'Cont).integrable_of_hasCompactSupport huCompact.mul_right
  have hu'v : Integrable (u' * v) :=
    (hu'Cont.mul hvCont).integrable_of_hasCompactSupport hu'Compact.mul_right
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (v := v) (u' := u') (v' := v')
    (fun x _ => hu x) (fun x _ => hv x) huv' hu'v huv
  have hleft : ∫ x : ℝ, u x * v' x = -w * ∫ x : ℝ, u x * v x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [v']
    ring
  rw [smoothProfileLaplaceAmplitude_eq_integral]
  change w * ∫ x : ℝ, u x * v x = ∫ x : ℝ, u' x * v x
  rw [hleft] at hparts
  apply neg_injective
  simpa only [neg_mul] using hparts

/-- Real profiles make the Laplace amplitude compatible with Schwarz
conjugation. -/
theorem smoothProfileLaplaceAmplitude_conj
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (w : ℂ) :
    (starRingEnd ℂ) (smoothProfileLaplaceAmplitude f w) =
      smoothProfileLaplaceAmplitude f ((starRingEnd ℂ) w) := by
  rw [smoothProfileLaplaceAmplitude_eq_integral,
    smoothProfileLaplaceAmplitude_eq_integral, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp [smoothProfileLaplaceWeight, ← Complex.exp_conj]

/-- On the centered critical strip, one integration by parts bounds the
profile amplitude by an explicit profile-dependent reciprocal height. -/
theorem norm_smoothProfileLaplaceAmplitude_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {w : ℂ} (hw : w ≠ 0)
    (hwre : |w.re| ≤ 1 / 2) :
    ‖smoothProfileLaplaceAmplitude f w‖ ≤
      (Real.exp (L / 2) * smoothProfileDerivativeMass f) / ‖w‖ := by
  have hL : 0 < L := by linarith
  have hderivInt : Integrable (fun x => ‖smoothProfileComplexDeriv f x‖) :=
    integrable_smoothProfileComplexDeriv_norm f
  have hpoint : ∀ x : ℝ,
      ‖smoothProfileComplexDeriv f x * smoothProfileLaplaceWeight w x‖ ≤
        Real.exp (L / 2) * ‖smoothProfileComplexDeriv f x‖ := by
    intro x
    by_cases hdx : smoothProfileComplexDeriv f x = 0
    · simp [hdx]
    · have hxSupp : x ∈ support (smoothProfileComplexDeriv f) := hdx
      have hxT : x ∈ tsupport (fun y : ℝ => f y) := by
        apply support_deriv_subset
        change deriv (fun y : ℝ => (f y : ℝ)) x ≠ 0
        change ((deriv (fun y : ℝ => (f y : ℝ)) x : ℝ) : ℂ) ≠ 0 at hxSupp
        exact_mod_cast hxSupp
      have hxK : x ∈ Icc eta (L - eta) := f.tsupport_subset hxT
      have hx0 : 0 ≤ x := heta.le.trans hxK.1
      have hxUpper : x ≤ L - eta := hxK.2
      have hxL : x ≤ L := by linarith
      rw [norm_mul, smoothProfileLaplaceWeight, Complex.norm_exp]
      have hexponent : (-(x : ℂ) * w).re ≤ L / 2 := by
        rw [Complex.mul_re]
        simp only [neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, zero_mul,
          sub_zero]
        calc
          -x * w.re = x * (-w.re) := by ring
          _ ≤ x * |w.re| :=
            mul_le_mul_of_nonneg_left (neg_le_abs w.re) hx0
          _ ≤ x * (1 / 2) := by gcongr
          _ ≤ L / 2 := by linarith
      calc
        ‖smoothProfileComplexDeriv f x‖ * Real.exp (-(x : ℂ) * w).re ≤
            ‖smoothProfileComplexDeriv f x‖ * Real.exp (L / 2) := by
          gcongr
        _ = Real.exp (L / 2) * ‖smoothProfileComplexDeriv f x‖ := mul_comm _ _
  have hprodNormInt : Integrable (fun x =>
      ‖smoothProfileComplexDeriv f x * smoothProfileLaplaceWeight w x‖) := by
    exact (((continuous_smoothProfileComplexDeriv f).mul
      (continuous_smoothProfileLaplaceWeight w)).integrable_of_hasCompactSupport
        (hasCompactSupport_smoothProfileComplexDeriv f).mul_right).norm
  have hmajorInt : Integrable (fun x =>
      Real.exp (L / 2) * ‖smoothProfileComplexDeriv f x‖) :=
    hderivInt.const_mul _
  have hnormInt :
      ‖∫ x : ℝ, smoothProfileComplexDeriv f x *
          smoothProfileLaplaceWeight w x‖ ≤
        Real.exp (L / 2) * smoothProfileDerivativeMass f := by
    calc
      ‖∫ x : ℝ, smoothProfileComplexDeriv f x *
          smoothProfileLaplaceWeight w x‖ ≤
          ∫ x : ℝ, ‖smoothProfileComplexDeriv f x *
            smoothProfileLaplaceWeight w x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ,
          Real.exp (L / 2) * ‖smoothProfileComplexDeriv f x‖ :=
        integral_mono hprodNormInt hmajorInt hpoint
      _ = Real.exp (L / 2) * smoothProfileDerivativeMass f := by
        rw [integral_const_mul]
        rfl
  have hmul : ‖w‖ * ‖smoothProfileLaplaceAmplitude f w‖ ≤
      Real.exp (L / 2) * smoothProfileDerivativeMass f := by
    rw [← norm_mul, smoothProfileLaplaceAmplitude_mul]
    exact hnormInt
  apply (le_div_iff₀ (norm_pos_iff.mpr hw)).2
  simpa only [mul_comm] using hmul

/-- Squared smooth profile coefficients have the reciprocal-square Xi bound
needed by the Landau carrier. -/
theorem norm_smoothProfileLaplaceAmplitude_sq_xiRight_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (q : XiRightZeroCopy) :
    ‖smoothProfileLaplaceAmplitude f (xiRightCenteredZero q) ^ (2 : ℕ)‖ ≤
      (Real.exp (L / 2) * smoothProfileDerivativeMass f) ^ (2 : ℕ) /
        ‖xiSpectralPoint q.1‖ ^ (2 : ℕ) := by
  rw [norm_pow]
  have hA := norm_smoothProfileLaplaceAmplitude_le heta hwindow f
    (xiRightCenteredZero_ne_zero q)
    (le_of_lt (abs_xiRightCenteredZero_re_lt_half q))
  have hA2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  rw [xiRightCenteredZero, norm_mul, norm_I, one_mul] at hA2
  calc
    ‖smoothProfileLaplaceAmplitude f (xiRightCenteredZero q)‖ ^ (2 : ℕ) ≤
        ((Real.exp (L / 2) * smoothProfileDerivativeMass f) /
          ‖xiSpectralPoint q.1‖) ^ (2 : ℕ) := hA2
    _ = (Real.exp (L / 2) * smoothProfileDerivativeMass f) ^ (2 : ℕ) /
        ‖xiSpectralPoint q.1‖ ^ (2 : ℕ) := by ring

end

end RHTower
