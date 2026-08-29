import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinPoincareRamanujanUnfolding
import GaloisForLFunctions.HTGeometry.BesselOrderIntegral
import GaloisForLFunctions.HTGeometry.ReflectionSplitIntegral
import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.SpectralZetaMellin
import GaloisForLFunctions.HTGeometry.GammaNatShift

/-!
# Exact Gamma--Bessel transform of the Eisenstein Cauchy-power kernel

The primitive-pair Poincare unfolding reduces every fixed-denominator Fourier coefficient to the
Euclidean transform of `(y²+x²)^(-s)`. This module closes that analytic gate for complex `s` in
the actual absolute-convergence chamber `Re(s)>1`.

The proof is source-faithful: a Gamma integral resolves the complex power, product integrability
justifies the Mellin--Gaussian Fubini swap, the corpus Gaussian transform supplies the frequency
factor, and logarithmic substitution identifies the resulting inverse-Gaussian Mellin integral
with the corpus Schlaefli definition of `K_ν`. Both the nonzero Bessel mode and the distinct zero
Gamma mode are proved exactly.

This closes the archimedean transform in the fixed route

`Poincare/Fourier equality -> truncated Stokes -> zero physical defects -> balanced polarized
coefficient -> negative BM leg -> conserved left-QNM coefficient -> HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HC94] [GAMMA--BESSEL FOURIER TRANSFORM]`
-/

open Complex Real Filter MeasureTheory Set Topology
open scoped FourierTransform

namespace RHTower
noncomputable section

open GaloisForLFunctions.HTGeometry

def d4BMExponentialBesselKernel (r : ℝ) (nu : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-(r : ℂ) * Complex.cosh (u : ℂ)) *
    Complex.exp (nu * (u : ℂ))

lemma norm_d4BMExponentialBesselKernel (r : ℝ) (nu : ℂ) (u : ℝ) :
    ‖d4BMExponentialBesselKernel r nu u‖ =
      Real.exp (-r * Real.cosh u + nu.re * u) := by
  rw [d4BMExponentialBesselKernel, norm_mul, Complex.norm_exp, Complex.norm_exp]
  rw [← Real.exp_add]
  congr 1
  simp [← Complex.ofReal_cosh]

theorem integrable_d4BMExponentialBesselKernel
    {r : ℝ} (hr : 0 < r) (nu : ℂ) :
    Integrable (d4BMExponentialBesselKernel r nu) := by
  let B : ℝ → ℝ := fun u =>
    Real.exp (2 * ‖nu‖ ^ 2 / r) * Real.exp (-(r / 8) * u ^ 2)
  have hB : Integrable B := by
    simpa [B] using
      (integrable_exp_neg_mul_sq (div_pos hr (by norm_num : (0 : ℝ) < 8))).const_mul
        (Real.exp (2 * ‖nu‖ ^ 2 / r))
  refine hB.mono' (by unfold d4BMExponentialBesselKernel; fun_prop) ?_
  filter_upwards with u
  rw [norm_d4BMExponentialBesselKernel]
  have hlin : nu.re * u ≤ ‖nu‖ * |u| := by
    calc
      nu.re * u ≤ |nu.re * u| := le_abs_self _
      _ = |nu.re| * |u| := abs_mul _ _
      _ ≤ ‖nu‖ * |u| := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm nu) (abs_nonneg u)
  have hbound := bessel_exponent_bound r ‖nu‖ hr (abs_nonneg u)
  have hcosh : Real.cosh |u| = Real.cosh u := by
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu, Real.cosh_neg]
  have hexp : -r * Real.cosh u + nu.re * u ≤
      2 * ‖nu‖ ^ 2 / r - r / 8 * u ^ 2 := by
    rw [hcosh] at hbound
    nlinarith [sq_abs u]
  calc
    Real.exp (-r * Real.cosh u + nu.re * u) ≤
        Real.exp (2 * ‖nu‖ ^ 2 / r - r / 8 * u ^ 2) := Real.exp_le_exp.mpr hexp
    _ = B u := by
      change Real.exp (2 * ‖nu‖ ^ 2 / r - r / 8 * u ^ 2) =
        Real.exp (2 * ‖nu‖ ^ 2 / r) * Real.exp (-(r / 8) * u ^ 2)
      rw [← Real.exp_add]
      congr 1
      ring

theorem integral_d4BMExponentialBesselKernel_eq
    {r : ℝ} (hr : 0 < r) (nu : ℂ) :
    (∫ u : ℝ, d4BMExponentialBesselKernel r nu u) =
      2 * modifiedBesselKOrder r nu := by
  have hnu := integrable_d4BMExponentialBesselKernel hr nu
  rw [integral_eq_add_reflect hnu]
  have hpos : IntegrableOn (d4BMExponentialBesselKernel r nu) (Ioi 0) := hnu.integrableOn
  have hneg : IntegrableOn (fun u : ℝ => d4BMExponentialBesselKernel r nu (-u)) (Ioi 0) := by
    have hall : Integrable (fun u : ℝ => d4BMExponentialBesselKernel r nu (-u)) := by
      simpa only [Function.comp_def] using hnu.comp_neg
    exact hall.integrableOn
  rw [← MeasureTheory.integral_add hpos hneg]
  rw [modifiedBesselKOrder, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  simp only [d4BMExponentialBesselKernel, besselOrderKernel, Complex.ofReal_neg,
    Complex.cosh_neg, mul_neg]
  rw [← mul_add]
  have hpair : Complex.exp (nu * (u : ℂ)) + Complex.exp (-(nu * (u : ℂ))) =
      2 * Complex.cosh (nu * (u : ℂ)) := by
    rw [Complex.cosh]
    ring
  rw [hpair]
  ring

theorem integral_Ioi_eq_integral_exp_scale_smul
    {q : ℝ} (hq : 0 < q) (g : ℝ → ℂ) :
    (∫ x in Ioi (0 : ℝ), g x) =
      ∫ u : ℝ, (q * Real.exp u) • g (q * Real.exp u) := by
  have himage : (fun u : ℝ => q * Real.exp u) '' Set.univ = Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      exact mul_pos hq (Real.exp_pos u)
    · intro hx
      refine ⟨Real.log (x / q), Set.mem_univ _, ?_⟩
      change q * Real.exp (Real.log (x / q)) = x
      rw [Real.exp_log (div_pos hx hq)]
      field_simp
  rw [← himage]
  simpa only [Measure.restrict_univ, abs_of_pos (mul_pos hq (Real.exp_pos _))] using
    (MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.univ) MeasurableSet.univ
      (fun u _ => ((Real.hasDerivAt_exp u).const_mul q).hasDerivWithinAt)
      (fun _ _ _ _ huv => Real.exp_injective (mul_left_cancel₀ hq.ne' huv)) g)

def d4BMInverseGaussianMellinKernel (a y xi : ℝ) (nu : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (nu - 1) *
    Complex.exp (-(((a * (y ^ 2 * t + xi ^ 2 / t) : ℝ) : ℂ)))

lemma d4BM_ofReal_exp_cpow (u : ℝ) (nu : ℂ) :
    ((Real.exp u : ℝ) : ℂ) ^ nu = Complex.exp (nu * (u : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.exp_ne_zero u)]
  rw [← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  congr 1
  ring

lemma d4BM_inverseGaussian_exp_scale
    {a y xi : ℝ} (ha : 0 < a) (hy : 0 < y) (hxi : 0 < xi) (nu : ℂ) (u : ℝ) :
    ((xi / y) * Real.exp u) •
        d4BMInverseGaussianMellinKernel a y xi nu ((xi / y) * Real.exp u) =
      ((xi / y : ℝ) : ℂ) ^ nu * d4BMExponentialBesselKernel (2 * a * y * xi) nu u := by
  have hq : 0 < xi / y := div_pos hxi hy
  have ht : 0 < (xi / y) * Real.exp u := mul_pos hq (Real.exp_pos u)
  have ht0 : (((xi / y) * Real.exp u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hpow : (((xi / y) * Real.exp u : ℝ) : ℂ) *
      (((xi / y) * Real.exp u : ℝ) : ℂ) ^ (nu - 1) =
      (((xi / y) * Real.exp u : ℝ) : ℂ) ^ nu := by
    calc
      _ = (((xi / y) * Real.exp u : ℝ) : ℂ) ^ (nu - 1) *
          (((xi / y) * Real.exp u : ℝ) : ℂ) ^ (1 : ℂ) := by
            rw [Complex.cpow_one]
            ring
      _ = (((xi / y) * Real.exp u : ℝ) : ℂ) ^ ((nu - 1) + 1) :=
        (Complex.cpow_add _ _ ht0).symm
      _ = _ := by ring_nf
  rw [d4BMInverseGaussianMellinKernel, d4BMExponentialBesselKernel,
    Complex.real_smul, ← mul_assoc, hpow]
  have hcast : (((xi / y) * Real.exp u : ℝ) : ℂ) =
      ((xi / y : ℝ) : ℂ) * ((Real.exp u : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast]
  rw [Complex.mul_cpow_ofReal_nonneg hq.le (Real.exp_pos u).le,
    d4BM_ofReal_exp_cpow]
  have hexp : a * (y ^ 2 * ((xi / y) * Real.exp u) +
      xi ^ 2 / ((xi / y) * Real.exp u)) =
      (2 * a * y * xi) * Real.cosh u := by
    rw [Real.cosh_eq]
    rw [Real.exp_neg]
    field_simp
  rw [hexp]
  push_cast
  ring

theorem integral_d4BMInverseGaussianMellinKernel_eq_bessel
    {a y xi : ℝ} (ha : 0 < a) (hy : 0 < y) (hxi : 0 < xi) (nu : ℂ) :
    (∫ t in Ioi (0 : ℝ), d4BMInverseGaussianMellinKernel a y xi nu t) =
      2 * (((xi / y : ℝ) : ℂ) ^ nu) * modifiedBesselKOrder (2 * a * y * xi) nu := by
  rw [integral_Ioi_eq_integral_exp_scale_smul (div_pos hxi hy)]
  simp_rw [d4BM_inverseGaussian_exp_scale ha hy hxi nu]
  rw [MeasureTheory.integral_const_mul,
    integral_d4BMExponentialBesselKernel_eq
      (mul_pos (mul_pos (mul_pos (by norm_num) ha) hy) hxi)]
  ring

def d4BMCauchyMellinFourierJoint
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (m x u : ℝ) : ℂ :=
  Complex.exp (-(((2 * Real.pi * x * m : ℝ) : ℂ)) * Complex.I) *
    ((u : ℂ) ^ (P.s - 1) *
      Complex.exp (-(Real.pi : ℂ) * (u : ℂ) *
        (((z.y ^ 2 + x ^ 2 : ℝ) : ℂ))))

lemma d4BM_cauchyMellinFourierJoint_norm
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (m x : ℝ)
    {u : ℝ} (hu : 0 < u) :
    ‖d4BMCauchyMellinFourierJoint z P m x u‖ =
      u ^ (P.s.re - 1) * Real.exp (-(Real.pi * (z.y ^ 2 + x ^ 2) * u)) := by
  rw [d4BMCauchyMellinFourierJoint, norm_mul, Complex.norm_exp]
  have hphase : (-(((2 * Real.pi * x * m : ℝ) : ℂ)) * Complex.I).re = 0 := by simp
  rw [hphase, Real.exp_zero, one_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp]
  have hexpre : (-(Real.pi : ℂ) * (u : ℂ) *
      (((z.y ^ 2 + x ^ 2 : ℝ) : ℂ))).re =
      -(Real.pi * (z.y ^ 2 + x ^ 2) * u) := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hexpre, Complex.sub_re, Complex.one_re]

theorem integrable_d4BMCauchyMellinFourierJoint
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (m : ℝ) :
    Integrable (Function.uncurry (d4BMCauchyMellinFourierJoint z P m))
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let F : ℝ → ℝ → ℂ := d4BMCauchyMellinFourierJoint z P m
  have hcont : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ Ioi (0 : ℝ)) := by
    unfold F d4BMCauchyMellinFourierJoint Function.uncurry
    have hx : Continuous (fun p : ℝ × ℝ => (2 * Real.pi * p.1 * m : ℝ)) := by fun_prop
    have hphase : Continuous (fun p : ℝ × ℝ =>
        Complex.exp (-(((2 * Real.pi * p.1 * m : ℝ) : ℂ)) * Complex.I)) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp hx).neg.mul continuous_const)
    have hpow : ContinuousOn (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (P.s - 1))
        (Set.univ ×ˢ Ioi (0 : ℝ)) :=
      (continuousOn_cpow_ofReal (P.s - 1)).comp continuous_snd.continuousOn
        (fun p hp => hp.2)
    have hu : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_snd
    have hqR : Continuous (fun p : ℝ × ℝ => z.y ^ 2 + p.1 ^ 2) := by fun_prop
    have hq : Continuous (fun p : ℝ × ℝ => ((z.y ^ 2 + p.1 ^ 2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hqR
    have hexp : Continuous (fun p : ℝ × ℝ =>
        Complex.exp (-(Real.pi : ℂ) * (p.2 : ℂ) *
          (((z.y ^ 2 + p.1 ^ 2 : ℝ) : ℂ)))) := by
      exact Complex.continuous_exp.comp ((continuous_const.neg.mul hu).mul hq)
    exact hphase.continuousOn.mul (hpow.mul hexp.continuousOn)
  have hAE : AEStronglyMeasurable (Function.uncurry F)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hmeasure : (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) =
        ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          (Set.univ ×ˢ Ioi (0 : ℝ)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hmeasure]
    exact hcont.aestronglyMeasurable (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi)
  have hslice : ∀ᵐ x ∂volume,
      Integrable (fun u => F x u) (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards with x
    have hQ : 0 < z.y ^ 2 + x ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos z.y_pos) (sq_nonneg x)
    have hrate : 0 < Real.pi * (z.y ^ 2 + x ^ 2) := mul_pos Real.pi_pos hQ
    have hrateC : 0 < (((Real.pi * (z.y ^ 2 + x ^ 2) : ℝ) : ℂ)).re := by
      change 0 < Real.pi * (z.y ^ 2 + x ^ 2)
      exact hrate
    have hbase := GaloisForLFunctions.HTGeometry.integrableOn_cpow_mul_exp_neg_mul_Ioi
      (s := P.s) (w := ((Real.pi * (z.y ^ 2 + x ^ 2) : ℝ) : ℂ))
      (by linarith [P.re_gt_one]) hrateC
    have hphase : ‖Complex.exp (-(((2 * Real.pi * x * m : ℝ) : ℂ)) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    refine (hbase.const_mul
      (Complex.exp (-(((2 * Real.pi * x * m : ℝ) : ℂ)) * Complex.I))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    unfold F d4BMCauchyMellinFourierJoint
    congr 2
    congr 1
    push_cast
    ring
  have hnormint : ∀ x : ℝ,
      (∫ u, ‖F x u‖ ∂(volume.restrict (Ioi (0 : ℝ)))) =
        Real.Gamma P.s.re *
          (Real.pi * (z.y ^ 2 + x ^ 2)) ^ (-P.s.re) := by
    intro x
    have hQ : 0 < z.y ^ 2 + x ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos z.y_pos) (sq_nonneg x)
    have hrate : 0 < Real.pi * (z.y ^ 2 + x ^ 2) := mul_pos Real.pi_pos hQ
    rw [show (∫ u, ‖F x u‖ ∂(volume.restrict (Ioi (0 : ℝ)))) =
        ∫ u in Ioi (0 : ℝ),
          u ^ (P.s.re - 1) * Real.exp (-(Real.pi * (z.y ^ 2 + x ^ 2) * u)) by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact d4BM_cauchyMellinFourierJoint_norm z P m x hu]
    have hgamma := GaloisForLFunctions.HTGeometry.DaiYoshikawa.gamma_mul_rpow_neg_eq_integral
      hrate (show 0 < P.s.re by linarith [P.re_gt_one])
    rw [show (∫ u in Ioi (0 : ℝ),
        u ^ (P.s.re - 1) * Real.exp (-(Real.pi * (z.y ^ 2 + x ^ 2) * u))) =
        ∫ u in Ioi (0 : ℝ),
          Real.exp (-(Real.pi * (z.y ^ 2 + x ^ 2) * u)) * u ^ (P.s.re - 1) by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      ring]
    exact hgamma.symm
  have hbound : Integrable (fun x => ∫ u, ‖F x u‖
      ∂(volume.restrict (Ioi (0 : ℝ)))) volume := by
    have hk := (integrable_d4BMCauchyPowerKernel z P).norm.const_mul
      (Real.Gamma P.s.re * Real.pi ^ (-P.s.re))
    refine hk.congr ?_
    filter_upwards with x
    rw [hnormint]
    rw [norm_d4BMCauchyPowerKernel]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hQ : 0 < z.y ^ 2 + x ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos z.y_pos) (sq_nonneg x)
    rw [Real.mul_rpow hpi.le hQ.le]
    rw [Real.rpow_neg hpi.le, Real.rpow_neg hQ.le]
    ring
  exact (integrable_prod_iff hAE).mpr ⟨hslice, hbound⟩

lemma d4BM_fourierPhase_eq_fourierChar (x m : ℝ) :
    Complex.exp (-(((2 * Real.pi * x * m : ℝ) : ℂ)) * Complex.I) =
      ((Real.fourierChar (-(inner ℝ x m)) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply]
  congr 1
  rw [show inner ℝ x m = x * m by simp [mul_comm]]
  push_cast
  ring

theorem integral_d4BMCauchyMellinFourierJoint_x
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (m : ℝ)
    {u : ℝ} (hu : 0 < u) :
    (∫ x : ℝ, d4BMCauchyMellinFourierJoint z P m x u) =
      (u : ℂ) ^ (P.s - 1) *
        Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (z.y : ℂ) ^ 2) *
        (1 / (u : ℂ) ^ (1 / 2 : ℂ) *
          Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (m : ℂ) ^ 2)) := by
  have hfour := congrFun (fourier_gaussianKernel hu) m
  rw [Real.fourier_eq] at hfour
  let C : ℂ := (u : ℂ) ^ (P.s - 1) *
    Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (z.y : ℂ) ^ 2)
  calc
    (∫ x : ℝ, d4BMCauchyMellinFourierJoint z P m x u) =
        ∫ x : ℝ, C * (((Real.fourierChar (-(inner ℝ x m)) : Circle) : ℂ) *
          Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (x : ℂ) ^ 2)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [d4BMCauchyMellinFourierJoint,
        ← d4BM_fourierPhase_eq_fourierChar]
      dsimp [C]
      have hexp : Complex.exp (-(Real.pi : ℂ) * (u : ℂ) *
          (((z.y ^ 2 + x ^ 2 : ℝ) : ℂ))) =
          Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (z.y : ℂ) ^ 2) *
            Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (x : ℂ) ^ 2) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      ring
    _ = C * ∫ x : ℝ, (((Real.fourierChar (-(inner ℝ x m)) : Circle) : ℂ) *
          Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (x : ℂ) ^ 2)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by
      have hfour' : (∫ x : ℝ, (((Real.fourierChar (-(inner ℝ x m)) : Circle) : ℂ) *
          Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (x : ℂ) ^ 2))) =
          1 / (u : ℂ) ^ (1 / 2 : ℂ) *
            Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (m : ℂ) ^ 2) := by
        change (∫ x : ℝ, Real.fourierChar (-(inner ℝ x m)) •
          Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (x : ℂ) ^ 2)) = _
        exact hfour
      rw [hfour']

theorem integral_d4BMCauchyMellinFourierJoint_u
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (m x : ℝ) :
    (∫ u in Ioi (0 : ℝ), d4BMCauchyMellinFourierJoint z P m x u) =
      Complex.exp (-(((2 * Real.pi * x * m : ℝ) : ℂ)) * Complex.I) *
        (Complex.Gamma P.s *
          (((Real.pi * (z.y ^ 2 + x ^ 2) : ℝ) : ℂ)) ^ (-P.s)) := by
  have hQ : 0 < z.y ^ 2 + x ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos z.y_pos) (sq_nonneg x)
  have hrate : 0 < Real.pi * (z.y ^ 2 + x ^ 2) := mul_pos Real.pi_pos hQ
  have hrateC : 0 < (((Real.pi * (z.y ^ 2 + x ^ 2) : ℝ) : ℂ)).re := by
    change 0 < Real.pi * (z.y ^ 2 + x ^ 2)
    exact hrate
  have hbase := GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi
    (s := P.s) (w := ((Real.pi * (z.y ^ 2 + x ^ 2) : ℝ) : ℂ))
    (show 0 < P.s.re by linarith [P.re_gt_one]) hrateC
  let C : ℂ := Complex.exp (-(((2 * Real.pi * x * m : ℝ) : ℂ)) * Complex.I)
  calc
    (∫ u in Ioi (0 : ℝ), d4BMCauchyMellinFourierJoint z P m x u) =
        ∫ u in Ioi (0 : ℝ), C * ((u : ℂ) ^ (P.s - 1) *
          Complex.exp (-(((Real.pi * (z.y ^ 2 + x ^ 2) : ℝ) : ℂ) * (u : ℂ)))) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      rw [d4BMCauchyMellinFourierJoint]
      dsimp [C]
      congr 3
      push_cast
      ring
    _ = C * ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (P.s - 1) *
          Complex.exp (-(((Real.pi * (z.y ^ 2 + x ^ 2) : ℝ) : ℂ) * (u : ℂ))) := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by rw [hbase]

theorem d4BM_gamma_pi_mul_fourier_cauchy_eq_inverseGaussian
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (m : ℝ) :
    Complex.Gamma P.s * (Real.pi : ℂ) ^ (-P.s) *
        𝓕 (d4BMCauchyPowerKernel z P.s) m =
      ∫ u in Ioi (0 : ℝ),
        d4BMInverseGaussianMellinKernel Real.pi z.y |m|
          (P.s - 1 / 2) u := by
  let F : ℝ → ℝ → ℂ := d4BMCauchyMellinFourierJoint z P m
  have hprod := integrable_d4BMCauchyMellinFourierJoint z P m
  have hswap := integral_integral_swap hprod
  have hL : (∫ x : ℝ, ∫ u in Ioi (0 : ℝ), F x u) =
      Complex.Gamma P.s * (Real.pi : ℂ) ^ (-P.s) *
        𝓕 (d4BMCauchyPowerKernel z P.s) m := by
    let C : ℂ := Complex.Gamma P.s * (Real.pi : ℂ) ^ (-P.s)
    rw [show (fun x : ℝ => ∫ u in Ioi (0 : ℝ), F x u) =
        fun x : ℝ => C *
          (((Real.fourierChar (-(inner ℝ x m)) : Circle) : ℂ) *
            d4BMCauchyPowerKernel z P.s x) by
      funext x
      rw [integral_d4BMCauchyMellinFourierJoint_u]
      have hQ : 0 < z.y ^ 2 + x ^ 2 :=
        add_pos_of_pos_of_nonneg (sq_pos_of_pos z.y_pos) (sq_nonneg x)
      have hfactor : (((Real.pi * (z.y ^ 2 + x ^ 2) : ℝ) : ℂ)) ^ (-P.s) =
          (Real.pi : ℂ) ^ (-P.s) *
            (((z.y ^ 2 + x ^ 2 : ℝ) : ℂ)) ^ (-P.s) := by
        rw [show (((Real.pi * (z.y ^ 2 + x ^ 2) : ℝ) : ℂ)) =
            (Real.pi : ℂ) * (((z.y ^ 2 + x ^ 2 : ℝ) : ℂ)) by push_cast; ring,
          Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hQ.le]
      rw [hfactor, ← d4BM_fourierPhase_eq_fourierChar]
      unfold C d4BMCauchyPowerKernel
      ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
  have hR : (∫ u in Ioi (0 : ℝ), ∫ x : ℝ, F x u) =
      ∫ u in Ioi (0 : ℝ),
        d4BMInverseGaussianMellinKernel Real.pi z.y |m|
          (P.s - 1 / 2) u := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change (∫ x : ℝ, d4BMCauchyMellinFourierJoint z P m x u) = _
    rw [integral_d4BMCauchyMellinFourierJoint_x z P m hu]
    unfold d4BMInverseGaussianMellinKernel
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hpow : (u : ℂ) ^ (P.s - 1) * (1 / (u : ℂ) ^ (1 / 2 : ℂ)) =
        (u : ℂ) ^ ((P.s - 1 / 2) - 1) := by
      rw [one_div, ← div_eq_mul_inv, ← Complex.cpow_sub _ _ hu0]
      congr 1
      ring
    calc
      (u : ℂ) ^ (P.s - 1) *
            Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (z.y : ℂ) ^ 2) *
            ((1 / (u : ℂ) ^ (1 / 2 : ℂ)) *
            Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (m : ℂ) ^ 2)) =
          ((u : ℂ) ^ (P.s - 1) * (1 / (u : ℂ) ^ (1 / 2 : ℂ))) *
            (Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (z.y : ℂ) ^ 2) *
              Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (m : ℂ) ^ 2)) := by ring
      _ = (u : ℂ) ^ ((P.s - 1 / 2) - 1) *
          Complex.exp (-(((Real.pi * (z.y ^ 2 * u + |m| ^ 2 / u) : ℝ) : ℂ))) := by
        rw [hpow, ← Complex.exp_add]
        congr 2
        have habs : |m| ^ 2 = m ^ 2 := sq_abs m
        have habsC : (((|m| : ℝ) : ℂ)) ^ 2 = (m : ℂ) ^ 2 := by exact_mod_cast habs
        push_cast
        rw [habsC]
        field_simp
        ring
  rw [← hL, hswap, hR]

theorem fourier_d4BMCauchyPowerKernel_ne_zero
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {m : ℝ} (hm : m ≠ 0) :
    𝓕 (d4BMCauchyPowerKernel z P.s) m =
      (2 * (Real.pi : ℂ) ^ P.s / Complex.Gamma P.s) *
        ((((|m| / z.y : ℝ) : ℂ)) ^ (P.s - 1 / 2)) *
          modifiedBesselKOrder (2 * Real.pi * z.y * |m|) (P.s - 1 / 2) := by
  have hxi : 0 < |m| := abs_pos.mpr hm
  have hinv := integral_d4BMInverseGaussianMellinKernel_eq_bessel
    Real.pi_pos z.y_pos hxi (P.s - 1 / 2)
  have hraw := d4BM_gamma_pi_mul_fourier_cauchy_eq_inverseGaussian z P m
  rw [hinv] at hraw
  have hGamma : Complex.Gamma P.s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    nlinarith [P.re_gt_one, Nat.cast_nonneg (α := ℝ) k]
  have hpi : (Real.pi : ℂ) ^ P.s ≠ 0 := by
    intro hzero
    have hz := (Complex.cpow_eq_zero_iff (Real.pi : ℂ) P.s).mp hzero
    exact (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hz.1
  rw [Complex.cpow_neg] at hraw
  field_simp [hGamma, hpi] at hraw ⊢
  linear_combination hraw

theorem fourier_d4BMCauchyPowerKernel_zero
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    𝓕 (d4BMCauchyPowerKernel z P.s) 0 =
      ((Real.pi : ℂ) ^ P.s / Complex.Gamma P.s) *
        (Complex.Gamma (P.s - 1 / 2) *
          (((Real.pi * z.y ^ 2 : ℝ) : ℂ)) ^ (-(P.s - 1 / 2))) := by
  have hrate : 0 < Real.pi * z.y ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos z.y_pos)
  have hrateC : 0 < (((Real.pi * z.y ^ 2 : ℝ) : ℂ)).re := by
    change 0 < Real.pi * z.y ^ 2
    exact hrate
  have hnu : 0 < (P.s - 1 / 2).re := by
    norm_num [Complex.sub_re, Complex.div_re]
    linarith [P.re_gt_one]
  have hEuler := GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi
    (s := P.s - 1 / 2) (w := ((Real.pi * z.y ^ 2 : ℝ) : ℂ)) hnu hrateC
  have hraw := d4BM_gamma_pi_mul_fourier_cauchy_eq_inverseGaussian z P 0
  have hinv : (∫ u in Ioi (0 : ℝ),
      d4BMInverseGaussianMellinKernel Real.pi z.y |(0 : ℝ)|
        (P.s - 1 / 2) u) =
      Complex.Gamma (P.s - 1 / 2) *
        (((Real.pi * z.y ^ 2 : ℝ) : ℂ)) ^ (-(P.s - 1 / 2)) := by
    rw [show (fun u : ℝ =>
        d4BMInverseGaussianMellinKernel Real.pi z.y |(0 : ℝ)|
          (P.s - 1 / 2) u) =
        fun u : ℝ => (u : ℂ) ^ ((P.s - 1 / 2) - 1) *
          Complex.exp (-(((Real.pi * z.y ^ 2 : ℝ) : ℂ) * (u : ℂ))) by
      funext u
      unfold d4BMInverseGaussianMellinKernel
      simp only [abs_zero]
      congr 2
      push_cast
      ring]
    exact hEuler
  rw [hinv] at hraw
  have hGamma : Complex.Gamma P.s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    nlinarith [P.re_gt_one, Nat.cast_nonneg (α := ℝ) k]
  have hpi : (Real.pi : ℂ) ^ P.s ≠ 0 := by
    intro hzero
    have hz := (Complex.cpow_eq_zero_iff (Real.pi : ℂ) P.s).mp hzero
    exact (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hz.1
  rw [Complex.cpow_neg] at hraw
  field_simp [hGamma, hpi] at hraw ⊢
  linear_combination hraw

end
end RHTower
