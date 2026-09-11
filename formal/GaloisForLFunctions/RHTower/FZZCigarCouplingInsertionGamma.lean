import GaloisForLFunctions.RHTower.FZZCigarNeutralRadialZeroModeWard
import GaloisForLFunctions.HTGeometry.GammaVerticalDecay

/-!
# Gamma factor of the neutral radial coupling insertion

With `b = exp(v)` and `t(x) = exp(u + b*x)`, the original radial kernel is `exp(-t(x))`.
Its slope-normalized negative logarithmic-coupling derivative is the positive density
`w(x) = b*t(x)*exp(-t(x))`. This module proves integrability, unit mass, and the exact
positive-sign Fourier characteristic

`C(u,v,p) = integral w(x)*exp(i*p*x) dx = exp(-i*p*u/b)*Gamma(1+i*p/b)`.

The change of variables is performed on the actual integral. Gamma nonvanishing also proves
nonvanishing of every characteristic value. Source coupling shifts produce exactly a linear
momentum phase, and the logarithmic coupling Ward law is `d_u C / C = -i*p/b` for every real
momentum. Its derivative vanishes exactly at zero momentum; no stationarity premise is supplied.

This is one neutral radial insertion in the positive effective-coupling chamber. Its Gamma
argument is not identified with the shifted external-BRST arguments. Charged insertions,
continuation outside their Euler-integral chamber, the full nonzero-mode source, replica
coupling, and the integrated vacuum-saturating Ward identity remain separate obligations.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace GaloisForLFunctions.RHTower
noncomputable section

def fzzRadialCouplingDensity (u v x : ℝ) : ℝ :=
  Real.exp v * fzzNeutralRadialCoordinate u v x * fzzNeutralRadialKernel u v x

def fzzRadialCouplingCharacteristic (u v p : ℝ) : ℂ :=
  ∫ x : ℝ, (fzzRadialCouplingDensity u v x : ℂ) *
    Complex.exp (((p * x : ℝ) : ℂ) * Complex.I)

private theorem affine_substitution (u v : ℝ) (g : ℝ → ℂ) :
    (∫ y : ℝ, g y) = ∫ x : ℝ, Real.exp v • g (u + Real.exp v * x) := by
  have hderiv (x : ℝ) : HasDerivAt (fun x => u + Real.exp v * x) (Real.exp v) x := by
    simpa only [mul_one, id_eq] using
      ((hasDerivAt_id x).const_mul (Real.exp v)).const_add u
  have hinj : Function.Injective (fun x : ℝ => u + Real.exp v * x) := by
    intro x y h
    exact mul_left_cancel₀ (Real.exp_ne_zero v) (add_left_cancel h)
  have himg : (fun x : ℝ => u + Real.exp v * x) '' univ = univ := by
    apply Set.eq_univ_of_forall
    intro y
    refine ⟨(y-u)/Real.exp v, Set.mem_univ _, ?_⟩
    dsimp only
    rw [mul_div_cancel₀ _ (Real.exp_ne_zero v)]
    ring
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ) MeasurableSet.univ
    (fun x _ => (hderiv x).hasDerivWithinAt) hinj.injOn g
  simpa only [himg, setIntegral_univ, abs_of_pos (Real.exp_pos v)] using h

theorem fzzRadialCouplingCharacteristic_eq_gamma (u v p : ℝ) :
    fzzRadialCouplingCharacteristic u v p =
      Complex.exp (-(((p * u / Real.exp v : ℝ) : ℂ) * Complex.I)) *
        Complex.Gamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I) := by
  have h := GaloisForLFunctions.Gamma_vertical_eq_fourier (σ := 1) zero_lt_one
    (p / Real.exp v)
  simp only [Complex.ofReal_one, one_mul] at h
  rw [affine_substitution u v] at h
  have hi : (∫ x : ℝ, Real.exp v •
      (Complex.exp (((p / Real.exp v * (u + Real.exp v * x) : ℝ) : ℂ) * Complex.I) *
        (Real.exp (u + Real.exp v * x - Real.exp (u + Real.exp v * x)) : ℂ))) =
      Complex.exp (((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) *
        fzzRadialCouplingCharacteristic u v p := by
    rw [fzzRadialCouplingCharacteristic, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    have he : p / Real.exp v * (u + Real.exp v * x) = p * u / Real.exp v + p * x := by
      field_simp
    rw [he, Complex.ofReal_add, add_mul, Complex.exp_add, Real.exp_sub]
    simp only [Complex.real_smul, fzzRadialCouplingDensity,
      fzzNeutralRadialCoordinate, fzzNeutralRadialKernel, Real.exp_neg,
      Complex.ofReal_mul, div_eq_mul_inv, Complex.ofReal_inv]
    ring
  rw [hi] at h
  rw [h, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

theorem fzzRadialCouplingCharacteristic_ne_zero (u v p : ℝ) :
    fzzRadialCouplingCharacteristic u v p ≠ 0 := by
  rw [fzzRadialCouplingCharacteristic_eq_gamma]
  exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.Gamma_ne_zero_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero]
    exact zero_lt_one))

theorem integrable_fzzRadialCouplingCharacteristic_integrand (u v p : ℝ) :
    Integrable (fun x : ℝ => (fzzRadialCouplingDensity u v x : ℂ) *
      Complex.exp (((p * x : ℝ) : ℂ) * Complex.I)) := by
  by_contra h
  exact fzzRadialCouplingCharacteristic_ne_zero u v p (integral_undef h)

theorem fzzRadialCouplingCharacteristic_zero (u v : ℝ) :
    fzzRadialCouplingCharacteristic u v 0 = 1 := by
  simp [fzzRadialCouplingCharacteristic_eq_gamma, Complex.Gamma_one]

theorem fzzRadialCouplingDensity_mass (u v : ℝ) :
    (∫ x : ℝ, fzzRadialCouplingDensity u v x) = 1 := by
  have h := fzzRadialCouplingCharacteristic_zero u v
  change (∫ x : ℝ, (fzzRadialCouplingDensity u v x : ℂ) *
    Complex.exp (((0 * x : ℝ) : ℂ) * Complex.I)) = 1 at h
  simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one] at h
  exact_mod_cast h

theorem integrable_fzzRadialCouplingDensity (u v : ℝ) :
    Integrable (fzzRadialCouplingDensity u v) := by
  by_contra h
  have hmass := fzzRadialCouplingDensity_mass u v
  rw [integral_undef h] at hmass
  exact zero_ne_one hmass

theorem fzzRadialCouplingDensity_pos (u v x : ℝ) :
    0 < fzzRadialCouplingDensity u v x := by
  unfold fzzRadialCouplingDensity fzzNeutralRadialCoordinate fzzNeutralRadialKernel
  positivity

theorem fzzRadialCouplingDensity_eq_kernel_coupling_deriv (u v x : ℝ) :
    fzzRadialCouplingDensity u v x =
      -Real.exp v * deriv (fun a => fzzNeutralRadialKernel a v x) u := by
  rw [(hasDerivAt_fzzNeutralRadialKernel_logCoupling u v x).deriv]
  unfold fzzRadialCouplingDensity
  ring

theorem fzzRadialCouplingCharacteristic_coupling_shift (u v p h : ℝ) :
    fzzRadialCouplingCharacteristic (u+h) v p =
      Complex.exp (-(((p*h/Real.exp v : ℝ) : ℂ)*Complex.I)) *
        fzzRadialCouplingCharacteristic u v p := by
  simp only [fzzRadialCouplingCharacteristic_eq_gamma]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem hasDerivAt_fzzRadialCouplingCharacteristic_logCoupling (u v p : ℝ) :
    HasDerivAt (fun a => fzzRadialCouplingCharacteristic a v p)
      (-(((p / Real.exp v : ℝ) : ℂ) * Complex.I) *
        fzzRadialCouplingCharacteristic u v p) u := by
  have hr : HasDerivAt (fun a : ℝ => p*a/Real.exp v) (p/Real.exp v) u := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id u).const_mul p).div_const (Real.exp v)
  have hc := ((hr.ofReal_comp.mul_const Complex.I).neg.cexp).mul_const
    (Complex.Gamma (1 + ((p/Real.exp v : ℝ) : ℂ)*Complex.I))
  simp only [Pi.neg_apply] at hc
  simpa only [fzzRadialCouplingCharacteristic_eq_gamma, mul_assoc, mul_left_comm,
    mul_comm] using hc

theorem fzzRadialCouplingCharacteristic_couplingWard (u v p : ℝ) :
    deriv (fun a => fzzRadialCouplingCharacteristic a v p) u /
      fzzRadialCouplingCharacteristic u v p =
        -(((p / Real.exp v : ℝ) : ℂ) * Complex.I) := by
  rw [(hasDerivAt_fzzRadialCouplingCharacteristic_logCoupling u v p).deriv,
    mul_div_cancel_right₀ _ (fzzRadialCouplingCharacteristic_ne_zero u v p)]

theorem fzzRadialCouplingCharacteristic_couplingStationary_iff (u v p : ℝ) :
    deriv (fun a => fzzRadialCouplingCharacteristic a v p) u = 0 ↔ p = 0 := by
  rw [(hasDerivAt_fzzRadialCouplingCharacteristic_logCoupling u v p).deriv]
  simp only [mul_eq_zero, neg_eq_zero, Complex.ofReal_eq_zero,
    Complex.I_ne_zero, or_false, fzzRadialCouplingCharacteristic_ne_zero,
    div_eq_zero_iff, Real.exp_ne_zero]

end
end GaloisForLFunctions.RHTower
