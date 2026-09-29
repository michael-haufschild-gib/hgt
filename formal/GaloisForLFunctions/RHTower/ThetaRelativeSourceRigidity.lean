import GaloisForLFunctions.RHTower.ThetaZeroDivisionSource
import GaloisForLFunctions.RHTower.HedenmalmThetaAllShiftedTails
import GaloisForLFunctions.RHTower.XiZeroCountJensenBound
import GaloisForLFunctions.RHTower.XiLogDerivFactorization
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.XiCentralDiscBound
import GaloisForLFunctions.HTGeometry.EntireBezout
import GaloisForLFunctions.HTGeometry.QuotientProximityBound
import GaloisForLFunctions.HTGeometry.MaxModulusCharacteristicBound
import GaloisForLFunctions.HTGeometry.BriotBouquetTwoRootNoGo
import GaloisForLFunctions.HTGeometry.NevanlinnaMaxModulusBridge
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1
import GaloisForLFunctions.HTGeometry.ZetaTailBound
import GaloisForLFunctions.HTGeometry.GammaHorizontalRatio
import GaloisForLFunctions.HTGeometry.SectorPhragmenLindelof

/-!
# Relative-source rigidity for the literal theta source

Let `k` be the completed theta source and `F = XiC` its Fourier transform. If a measurable `u`
obeys `|u| ≤ C k` and its entire transform `H(z) = ∫ e^{-izx} u(x) dx` contains every zero of `F`
with at least the same multiplicity, then `u = c k` almost everywhere.

The quotient `Q = H/F` is entire. Positivity of `k` gives `|H(z)| ≤ C L(Im z)` with
`L(y) = ∫ e^{yx} k(x) dx = |F(i y)|`, so `|Q| ≤ C` on the imaginary axis. Off the zero band,
`L(Im z) = |ξ(Re s)|` with `s = 1/2 + iz`, and the Gauss-product bound for `Γ(a)/|Γ(a + ib)|`
with `|ζ(s) - 1| ≤ 4·2^{-Re s}` gives `|Q(z)| ≤ 3C exp[(|Re z|/2) arctan(|Re z|/(1/2 + |Im z|))]`;
on the rays `arg z = ±(π/2 - δ)` this is `3C e^{(δ/2) r sin δ}`. The Nevanlinna first main theorem
and the Poisson–Jensen bound give `Q` an order-one envelope, and Phragmén–Lindelöf in sectors
and half-planes followed by Liouville make `Q` constant. `L¹` Fourier uniqueness concludes.
Evenness of `u` is not needed.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform

namespace RHTower

noncomputable section

/-! ## Measurable sources with every exponential moment -/

/-- A measurable source with finite exponential moments of every order. -/
structure MeasurableMomentSource (f : ℝ → ℂ) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable f
  moment : ∀ c : ℝ, Integrable (fun x => Real.exp (c * |x|) * ‖f x‖)

namespace MeasurableMomentSource

variable {f : ℝ → ℂ}

theorem integrable_mul (hf : MeasurableMomentSource f) {w : ℝ → ℂ} (hw : Continuous w) {c : ℝ}
    (hwb : ∀ x, ‖w x‖ ≤ Real.exp (c * |x|)) : Integrable (fun x => w x * f x) := by
  refine (hf.moment c).mono' (hw.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hwb x) (norm_nonneg _)

theorem integrable_cexp (hf : MeasurableMomentSource f) (z : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (-I * z * x) * f x) := by
  refine hf.integrable_mul (by fun_prop) (c := |z.im|) fun x => ?_
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have : (-I * z * (x : ℂ)).re = z.im * x := by simp [Complex.mul_re]
  rw [this, ← abs_mul]
  exact le_abs_self _

theorem hasDerivAt_sourceTransform (hf : MeasurableMomentSource f) (w₀ : ℂ) :
    HasDerivAt (sourceTransform f)
      (∫ x : ℝ, (-I * x) * Complex.exp (-I * w₀ * x) * f x) w₀ := by
  set B := |w₀.im| + 1
  have hbound : Integrable (fun x : ℝ => Real.exp ((B + 1) * |x|) * ‖f x‖) := hf.moment _
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (fun x : ℝ => Complex.exp (-I * w * x) * f x) :=
    fun w => (by fun_prop : Continuous fun x : ℝ => Complex.exp (-I * w * x)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  have hdom : ∀ᵐ x : ℝ, ∀ w ∈ Metric.ball w₀ 1,
      ‖(-I * x) * Complex.exp (-I * w * x) * f x‖ ≤ Real.exp ((B + 1) * |x|) * ‖f x‖ := by
    refine Eventually.of_forall fun x w hw => ?_
    have hdist : ‖w - w₀‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
    have him : |w.im| ≤ B := by
      have h1 : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - w₀)
      have h2 := abs_sub_abs_le_abs_sub w.im w₀.im
      dsimp only [B]; linarith
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-I * w * (x : ℂ)).re = w.im * x := by simp [Complex.mul_re]
    rw [hre]
    have hx : |x| ≤ Real.exp |x| := by
      have := Real.add_one_le_exp |x|; linarith
    have hwx : w.im * x ≤ B * |x| := by
      calc w.im * x ≤ |w.im * x| := le_abs_self _
        _ = |w.im| * |x| := abs_mul _ _
        _ ≤ B * |x| := mul_le_mul_of_nonneg_right him (abs_nonneg x)
    have : |x| * Real.exp (w.im * x) ≤ Real.exp ((B + 1) * |x|) := by
      calc |x| * Real.exp (w.im * x) ≤ Real.exp |x| * Real.exp (B * |x|) :=
            mul_le_mul hx (Real.exp_le_exp.mpr hwx) (Real.exp_pos _).le (Real.exp_pos _).le
        _ = Real.exp ((B + 1) * |x|) := by rw [← Real.exp_add]; ring_nf
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hderiv : ∀ᵐ x : ℝ, ∀ w ∈ Metric.ball w₀ 1, HasDerivAt
      (fun w : ℂ => Complex.exp (-I * w * x) * f x) ((-I * x) * Complex.exp (-I * w * x) * f x)
      w := by
    refine Eventually.of_forall fun x w _ => ?_
    have hlin : HasDerivAt (fun w : ℂ => -I * w * x) (-I * x) w := by
      simpa using ((hasDerivAt_id w).const_mul (-I)).mul_const (x : ℂ)
    exact ((Complex.hasDerivAt_exp _).comp w hlin).mul_const (f x) |>.congr_deriv (by ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ one_pos)
    (Eventually.of_forall hmeas) (hf.integrable_cexp w₀)
    ((by fun_prop : Continuous fun x : ℝ =>
      (-I * x) * Complex.exp (-I * w₀ * x)).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    hdom hbound hderiv).2

theorem differentiable_sourceTransform (hf : MeasurableMomentSource f) :
    Differentiable ℂ (sourceTransform f) :=
  fun w => (hf.hasDerivAt_sourceTransform w).differentiableAt

end MeasurableMomentSource

/-! ## Sources bounded relative to the theta source -/

/-- The real Laplace transform `L(y) = ∫ e^{yx} k(x) dx` of the theta source. -/
def thetaSourceLaplace (y : ℝ) : ℝ := ∫ x : ℝ, Real.exp (y * x) * thetaCuspFullSource x

theorem XiC_I_mul (y : ℝ) : XiC (I * y) = (thetaSourceLaplace y : ℂ) := by
  rw [← sourceTransform_thetaSourceC, sourceTransform, thetaSourceLaplace, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [thetaSourceC]
  push_cast
  rw [show -I * (I * (y : ℂ)) * (x : ℂ) = ((y * x : ℝ) : ℂ) by push_cast; ring_nf; simp]
  push_cast; ring

theorem thetaSourceLaplace_pos (y : ℝ) : 0 < thetaSourceLaplace y := by
  have hpos : ∀ x, 0 < Real.exp (y * x) * thetaCuspFullSource x := fun x =>
    mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos x)
  rw [thetaSourceLaplace, integral_pos_iff_support_of_nonneg (fun x => (hpos x).le)
    (HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource y)]
  have : Function.support (fun x : ℝ => Real.exp (y * x) * thetaCuspFullSource x) = univ :=
    Set.eq_univ_of_forall fun x => Function.mem_support.mpr (hpos x).ne'
  rw [this, Measure.measure_univ_pos]
  exact NeZero.ne _

theorem norm_XiC_I_mul (y : ℝ) : ‖XiC (I * y)‖ = thetaSourceLaplace y := by
  rw [XiC_I_mul, Complex.norm_real, Real.norm_of_nonneg (thetaSourceLaplace_pos y).le]

theorem XiC_I_mul_eq_xi (y : ℝ) : XiC (I * y) = xi ((1 / 2 - y : ℝ) : ℂ) := by
  unfold XiC; congr 1; push_cast
  linear_combination (y : ℂ) * Complex.I_mul_I

/-- A measurable source bounded by a multiple of the theta source has every exponential moment. -/
theorem measurableMomentSource_of_le {u : ℝ → ℂ} (hu : AEStronglyMeasurable u) {C : ℝ}
    (hC : ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x) : MeasurableMomentSource u := by
  refine ⟨hu, fun c => ?_⟩
  refine ((expMomentSource_thetaSourceC.moment c).const_mul C).mono'
    ((by fun_prop : Continuous fun x : ℝ => Real.exp (c * |x|)).aestronglyMeasurable.mul
      hu.norm) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, norm_norm, thetaSourceC,
    Complex.norm_real, Real.norm_of_nonneg (thetaCuspFullSource_pos x).le]
  calc Real.exp (c * |x|) * ‖u x‖ ≤ Real.exp (c * |x|) * (C * thetaCuspFullSource x) :=
        mul_le_mul_of_nonneg_left (hC x) (Real.exp_pos _).le
    _ = C * (Real.exp (c * |x|) * thetaCuspFullSource x) := by ring

/-- **The relative transform bound.** If `|u| ≤ C k` then `|H(z)| ≤ C L(Im z) = C |F(i Im z)|`. -/
theorem norm_sourceTransform_le {u : ℝ → ℂ} {C : ℝ}
    (hC : ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x) (z : ℂ) :
    ‖sourceTransform u z‖ ≤ C * thetaSourceLaplace z.im := by
  have hint := HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource z.im
  rw [sourceTransform, thetaSourceLaplace, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x => norm_nonneg _) (hint.const_mul C)
    (Eventually.of_forall fun x => ?_))
  dsimp only
  rw [norm_mul, Complex.norm_exp]
  have hre : (-I * z * (x : ℂ)).re = z.im * x := by simp [Complex.mul_re]
  rw [hre]
  calc Real.exp (z.im * x) * ‖u x‖ ≤ Real.exp (z.im * x) * (C * thetaCuspFullSource x) :=
        mul_le_mul_of_nonneg_left (hC x) (Real.exp_pos _).le
    _ = C * (Real.exp (z.im * x) * thetaCuspFullSource x) := by ring

/-! ## The xi ratio on vertical rays -/

theorem norm_riemannZeta_le_of_three_le {s : ℂ} (hs : 3 ≤ s.re) : ‖riemannZeta s‖ ≤ 3 / 2 := by
  have h := GaloisForLFunctions.HTGeometry.norm_riemannZeta_sub_one_le_rpow (s := s) (by linarith)
  have h2 : (2 : ℝ) ^ (-s.re) ≤ 1 / 8 := by
    calc (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-(3 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 8 := by norm_num
  calc ‖riemannZeta s‖ = ‖(riemannZeta s - 1) + 1‖ := by ring_nf
    _ ≤ ‖riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 3 / 2 := by rw [norm_one]; linarith

theorem one_half_le_norm_riemannZeta {s : ℂ} (hs : 3 ≤ s.re) : 1 / 2 ≤ ‖riemannZeta s‖ := by
  have h := GaloisForLFunctions.HTGeometry.norm_riemannZeta_sub_one_le_rpow (s := s) (by linarith)
  have h2 : (2 : ℝ) ^ (-s.re) ≤ 1 / 8 := by
    calc (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-(3 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 8 := by norm_num
  have h3 := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  rw [norm_one, sub_sub_cancel, norm_sub_rev] at h3
  linarith

/-- **The xi ratio on a vertical line.** For `Re s ≥ 3`,
`|ξ(Re s)| ≤ 3 e^{B(Re s/2, Im s/2)} |ξ(s)|`. -/
theorem norm_xi_re_le {s : ℂ} (hs : 3 ≤ s.re) :
    ‖xi (s.re : ℂ)‖ ≤ 3 * Real.exp (HTGeometry.gammaRatioBound (s.re / 2) (s.im / 2)) * ‖xi s‖ := by
  have hσ1 : 1 < s.re := by linarith
  have hr : 1 < ((s.re : ℂ)).re := by simpa using hσ1
  rw [xi_eq_four_factors hr, xi_eq_four_factors hσ1]
  have hΓ := HTGeometry.Gamma_le_norm_Gamma_mul_exp (a := s.re / 2) (by linarith) (s.im / 2)
  have hs2 : (((s.re / 2 : ℝ)) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * I = s / 2 := by
    conv_rhs => rw [← Complex.re_add_im s]
    push_cast; ring
  rw [hs2] at hΓ
  have hΓr : Complex.Gamma ((s.re : ℂ) / 2) = ((Real.Gamma (s.re / 2) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hπ : ∀ w : ℂ, ‖(Real.pi : ℂ) ^ (-w / 2)‖ = Real.pi ^ (-w.re / 2) := by
    intro w
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1; simp
  have hζ1 := norm_riemannZeta_le_of_three_le (s := (s.re : ℂ)) (by simpa using hs)
  have hζ2 := one_half_le_norm_riemannZeta hs
  have hpoly : ‖(s.re : ℂ) * ((s.re : ℂ) - 1) / 2‖ ≤ ‖s * (s - 1) / 2‖ := by
    rw [norm_div, norm_div, norm_mul, norm_mul]
    refine div_le_div_of_nonneg_right (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
      (by positivity)
    · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      exact Complex.re_le_norm s
    · rw [show (s.re : ℂ) - 1 = ((s.re - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
      simpa using Complex.re_le_norm (s - 1)
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hπ, hπ, hΓr, Complex.norm_real,
    Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by linarith)).le, Complex.ofReal_re]
  have hGpos : 0 < Real.Gamma (s.re / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hπpos : 0 < Real.pi ^ (-s.re / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  set P := ‖s * (s - 1) / 2‖
  set G := ‖Complex.Gamma (s / 2)‖
  set E := Real.exp (HTGeometry.gammaRatioBound (s.re / 2) (s.im / 2))
  have hE : 0 < E := Real.exp_pos _
  calc ‖(s.re : ℂ) * ((s.re : ℂ) - 1) / 2‖ * (Real.pi ^ (-s.re / 2) *
        (Real.Gamma (s.re / 2) * ‖riemannZeta (s.re : ℂ)‖))
      ≤ P * (Real.pi ^ (-s.re / 2) * ((G * E) * (3 / 2))) := by
        refine mul_le_mul hpoly (mul_le_mul_of_nonneg_left (mul_le_mul hΓ hζ1 (norm_nonneg _)
          (by positivity)) hπpos.le) (by positivity) (norm_nonneg _)
    _ = 3 * E * (P * (Real.pi ^ (-s.re / 2) * (G * (1 / 2)))) := by ring
    _ ≤ 3 * E * (P * (Real.pi ^ (-s.re / 2) * (G * ‖riemannZeta s‖))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hζ2 (norm_nonneg _)) hπpos.le)
          (norm_nonneg _)) (by positivity)

/-! ## Bounds for the quotient `Q = H/F` -/

theorem gammaRatioBound_abs (a b : ℝ) :
    HTGeometry.gammaRatioBound a |b| = HTGeometry.gammaRatioBound a b := by
  simp [HTGeometry.gammaRatioBound, sq_abs, abs_abs]

theorem thetaSourceLaplace_neg (y : ℝ) : thetaSourceLaplace (-y) = thetaSourceLaplace y := by
  rw [← norm_XiC_I_mul, ← norm_XiC_I_mul, show I * ((-y : ℝ) : ℂ) = -(I * y) by push_cast; ring,
    XiC_even]

theorem thetaSourceLaplace_le_mul_norm_XiC_of_nonpos {z : ℂ} (hz : 5 / 2 ≤ |z.im|)
    (h : z.im ≤ 0) :
    thetaSourceLaplace z.im ≤ 3 * Real.exp (HTGeometry.gammaRatioBound ((1 / 2 + |z.im|) / 2)
      (|z.re| / 2)) * ‖XiC z‖ := by
  have habs : |z.im| = -z.im := abs_of_nonpos h
  set s : ℂ := 1 / 2 + z * I with hs
  have hsre : s.re = 1 / 2 + |z.im| := by rw [habs, hs]; simp
  have hsim : s.im = z.re := by rw [hs]; simp
  have hs3 : 3 ≤ s.re := by rw [hsre]; linarith
  have key := norm_xi_re_le hs3
  rw [hsre, hsim] at key
  rw [← gammaRatioBound_abs, abs_div, abs_two] at key
  rw [← norm_XiC_I_mul, XiC_I_mul_eq_xi, show XiC z = xi s from rfl]
  convert key using 3
  rw [habs]; push_cast; ring

/-- **Away from the zero band**, `L(Im z) ≤ 3 e^{B} |F(z)|` with
`B = B((1/2 + |Im z|)/2, |Re z|/2)`. -/
theorem thetaSourceLaplace_le_mul_norm_XiC {z : ℂ} (hz : 5 / 2 ≤ |z.im|) :
    thetaSourceLaplace z.im ≤ 3 * Real.exp (HTGeometry.gammaRatioBound ((1 / 2 + |z.im|) / 2)
      (|z.re| / 2)) * ‖XiC z‖ := by
  rcases le_or_gt z.im 0 with h | h
  · exact thetaSourceLaplace_le_mul_norm_XiC_of_nonpos hz h
  · have h' := thetaSourceLaplace_le_mul_norm_XiC_of_nonpos (z := -z) (by simpa using hz)
      (by simp; linarith)
    simpa [thetaSourceLaplace_neg, XiC_even] using h'

variable {u : ℝ → ℂ} {C : ℝ} {q : ℂ → ℂ}

/-- The quotient is bounded by `C` on the imaginary axis. -/
theorem norm_quotient_imag_le (hC : ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x)
    (hq : ∀ z, sourceTransform u z = q z * XiC z) (y : ℝ) : ‖q (y * I)‖ ≤ C := by
  have h := norm_sourceTransform_le hC (y * I)
  rw [hq, norm_mul, show XiC ((y : ℂ) * I) = XiC (I * y) by ring_nf, norm_XiC_I_mul] at h
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero] at h
  exact le_of_mul_le_mul_right h (thetaSourceLaplace_pos y)

/-- **The quotient off the zero band.** For `|Im z| ≥ 5/2`,
`|Q(z)| ≤ 3C exp[(|Re z|/2) arctan(|Re z|/(1/2 + |Im z|))]`. -/
theorem norm_le_of_band_of_eq_mul (hC : ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x) {z : ℂ}
    (hz : 5 / 2 ≤ |z.im|) {w : ℂ} (hw : sourceTransform u z = w * XiC z) :
    ‖w‖ ≤ 3 * C * Real.exp (|z.re| / 2 * Real.arctan (|z.re| / (1 / 2 + |z.im|))) := by
  have hC0 : 0 ≤ C := by
    have := hC 0
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) (thetaCuspFullSource_pos 0)
  have h1 := norm_sourceTransform_le hC z
  have h2 := thetaSourceLaplace_le_mul_norm_XiC hz
  have hB := HTGeometry.gammaRatioBound_le (a := (1 / 2 + |z.im|) / 2) (b := |z.re| / 2)
    (by linarith [abs_nonneg z.im])
  rw [abs_div, abs_abs, abs_two, div_div_div_cancel_right₀ (two_ne_zero)] at hB
  have hF : 0 < ‖XiC z‖ := by
    by_contra hF
    push Not at hF
    have := thetaSourceLaplace_pos z.im
    nlinarith [Real.exp_pos (HTGeometry.gammaRatioBound ((1 / 2 + |z.im|) / 2) (|z.re| / 2)),
      norm_nonneg (XiC z)]
  rw [hw, norm_mul] at h1
  have h3 : ‖w‖ * ‖XiC z‖ ≤ 3 * C * Real.exp (|z.re| / 2 * Real.arctan (|z.re| / (1 / 2 + |z.im|)))
      * ‖XiC z‖ := by
    calc ‖w‖ * ‖XiC z‖ ≤ C * thetaSourceLaplace z.im := h1
      _ ≤ C * (3 * Real.exp (HTGeometry.gammaRatioBound ((1 / 2 + |z.im|) / 2) (|z.re| / 2)) *
          ‖XiC z‖) := mul_le_mul_of_nonneg_left h2 hC0
      _ ≤ C * (3 * Real.exp (|z.re| / 2 * Real.arctan (|z.re| / (1 / 2 + |z.im|))) * ‖XiC z‖) := by
          gcongr
      _ = _ := by ring
  exact le_of_mul_le_mul_right h3 hF

theorem norm_quotient_le_of_band (hC : ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x)
    (hq : ∀ z, sourceTransform u z = q z * XiC z) {z : ℂ} (hz : 5 / 2 ≤ |z.im|) :
    ‖q z‖ ≤ 3 * C * Real.exp (|z.re| / 2 * Real.arctan (|z.re| / (1 / 2 + |z.im|))) :=
  norm_le_of_band_of_eq_mul hC hz (hq z)

theorem norm_ofReal_mul_cexp (r β : ℝ) (hr : 0 ≤ r) : ‖(r : ℂ) * cexp (β * I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

/-- **Ray bounds from a band bound.**  A continuous `q` with
`|q(z)| ≤ C(1+|z|)^N exp[(|Re z|/2) arctan(|Re z|/(1/2 + |Im z|))]` for `|Im z| ≥ 5/2` has, for
every `η > 0`, the four ray bounds `|q| ≤ A(1+r)^N e^{η r cos α}` on `±r e^{±iα}`,
`α = π/2 - δ`, `δ = min(2η, 1)`. -/
theorem rays_of_band_bound {q : ℂ → ℂ} (hqc : Continuous q) {C : ℝ} (hC0 : 0 ≤ C) (N : ℕ)
    (hband : ∀ z : ℂ, 5 / 2 ≤ |z.im| → ‖q z‖ ≤
      C * (1 + ‖z‖) ^ N * Real.exp (|z.re| / 2 * Real.arctan (|z.re| / (1 / 2 + |z.im|)))) :
    ∀ η > 0, ∃ α ∈ Ioo 0 (Real.pi / 2), ∃ A : ℝ, ∀ r : ℝ, 0 ≤ r →
      ‖q (r * cexp (α * I))‖ ≤ A * (1 + r) ^ N * Real.exp (η * r * Real.cos α) ∧
        ‖q (r * cexp (-α * I))‖ ≤ A * (1 + r) ^ N * Real.exp (η * r * Real.cos α) ∧
        ‖q (-(r * cexp (α * I)))‖ ≤ A * (1 + r) ^ N * Real.exp (η * r * Real.cos α) ∧
        ‖q (-(r * cexp (-α * I)))‖ ≤ A * (1 + r) ^ N * Real.exp (η * r * Real.cos α) := by
  intro η hη
  have hπ := Real.pi_gt_three
  set δ := min (2 * η) 1 with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδη : δ ≤ 2 * η := min_le_left _ _
  have hcos : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ0.le (by linarith)
  set α := Real.pi / 2 - δ with hαdef
  have hcα : Real.cos α = Real.sin δ := Real.cos_pi_div_two_sub δ
  have hsα : Real.sin α = Real.cos δ := Real.sin_pi_div_two_sub δ
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (5 / (2 * Real.cos δ))).exists_bound_of_continuousOn
    hqc.continuousOn
  refine ⟨α, ⟨by linarith, by linarith⟩, max C M, fun r hr => ?_⟩
  have hpt : ∀ w : ℂ, |w.re| = r * Real.sin δ → |w.im| = r * Real.cos δ → ‖w‖ = r →
      ‖q w‖ ≤ max C M * (1 + r) ^ N * Real.exp (η * r * Real.cos α) := by
    intro w hre him hnorm
    have hexp1 : 1 ≤ Real.exp (η * r * Real.cos α) :=
      Real.one_le_exp (by rw [hcα]; positivity)
    have hpow1 : 1 ≤ (1 + r) ^ N := one_le_pow₀ (by linarith)
    have hA0 : 0 ≤ max C M := le_max_of_le_left hC0
    rcases le_or_gt (5 / 2) (r * Real.cos δ) with hband' | hsmall
    · have h := hband w (by rw [him]; exact hband')
      rw [hre, him, hnorm] at h
      have hr0 : 0 < r := by
        by_contra h0; push Not at h0
        have : r * Real.cos δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 hcos.le
        linarith
      have hratio : r * Real.sin δ / (1 / 2 + r * Real.cos δ) ≤ Real.tan δ := by
        rw [Real.tan_eq_sin_div_cos, div_le_div_iff₀ (by positivity) hcos]
        nlinarith [mul_nonneg hr hsin]
      have harc : Real.arctan (r * Real.sin δ / (1 / 2 + r * Real.cos δ)) ≤ δ := by
        calc Real.arctan (r * Real.sin δ / (1 / 2 + r * Real.cos δ)) ≤ Real.arctan (Real.tan δ) :=
              Real.arctan_strictMono.monotone hratio
          _ = δ := Real.arctan_tan (by linarith) (by linarith)
      have hexp : r * Real.sin δ / 2 * Real.arctan (r * Real.sin δ / (1 / 2 + r * Real.cos δ)) ≤
          η * r * Real.cos α := by
        rw [hcα]
        have h1 := mul_le_mul_of_nonneg_left harc (by positivity : (0 : ℝ) ≤ r * Real.sin δ / 2)
        have h2 : r * Real.sin δ / 2 * δ ≤ η * r * Real.sin δ := by
          nlinarith [mul_nonneg hr hsin]
        linarith
      calc ‖q w‖ ≤ C * (1 + r) ^ N * Real.exp (r * Real.sin δ / 2 *
            Real.arctan (r * Real.sin δ / (1 / 2 + r * Real.cos δ))) := h
        _ ≤ max C M * (1 + r) ^ N * Real.exp (η * r * Real.cos α) := by
            gcongr
            exact le_max_left _ _
    · have hw : w ∈ Metric.closedBall (0 : ℂ) (5 / (2 * Real.cos δ)) := by
        rw [mem_closedBall_zero_iff, hnorm, le_div_iff₀ (by positivity)]
        linarith
      calc ‖q w‖ ≤ M := hM w hw
        _ ≤ max C M := le_max_right _ _
        _ ≤ max C M * (1 + r) ^ N * Real.exp (η * r * Real.cos α) := by
            rw [mul_assoc]
            exact le_mul_of_one_le_right hA0 (one_le_mul_of_one_le_of_one_le hpow1 hexp1)
  have hre1 : ((r : ℂ) * cexp (α * I)).re = r * Real.cos α := by
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him1 : ((r : ℂ) * cexp (α * I)).im = r * Real.sin α := by
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hre2 : ((r : ℂ) * cexp (-α * I)).re = r * Real.cos α := by
    rw [show (-(α : ℂ)) = ((-α : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have him2 : ((r : ℂ) * cexp (-α * I)).im = -(r * Real.sin α) := by
    rw [show (-(α : ℂ)) = ((-α : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im, Real.sin_neg, mul_neg]
  have hn1 : ‖(r : ℂ) * cexp (α * I)‖ = r := norm_ofReal_mul_cexp r α hr
  have hn2 : ‖(r : ℂ) * cexp (-α * I)‖ = r := by
    rw [show (-(α : ℂ)) = ((-α : ℝ) : ℂ) by push_cast; ring]; exact norm_ofReal_mul_cexp r (-α) hr
  have habs1 : |r * Real.cos α| = r * Real.sin δ := by
    rw [hcα, abs_of_nonneg (mul_nonneg hr hsin)]
  have habs2 : |r * Real.sin α| = r * Real.cos δ := by
    rw [hsα, abs_of_nonneg (mul_nonneg hr hcos.le)]
  refine ⟨hpt _ (by rw [hre1, habs1]) (by rw [him1, habs2]) hn1,
    hpt _ (by rw [hre2, habs1]) (by rw [him2, abs_neg, habs2]) hn2,
    hpt _ (by rw [Complex.neg_re, abs_neg, hre1, habs1]) (by rw [Complex.neg_im, abs_neg, him1, habs2])
      (by rw [norm_neg, hn1]),
    hpt _ (by rw [Complex.neg_re, abs_neg, hre2, habs1])
      (by rw [Complex.neg_im, abs_neg, him2, abs_neg, habs2]) (by rw [norm_neg, hn2])⟩

/-- **Ray bounds for the quotient.** For every `η > 0` the four rays `±r e^{±iα}`,
`α = π/2 - δ`, `δ = min(2η, 1)`, carry `|Q| ≤ A e^{η r cos α}`. -/
theorem quotient_rays (hC : ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x)
    (hq : ∀ z, sourceTransform u z = q z * XiC z) (hqc : Continuous q) :
    ∀ η > 0, ∃ α ∈ Ioo 0 (Real.pi / 2), ∃ A : ℝ, ∀ r : ℝ, 0 ≤ r →
      ‖q (r * cexp (α * I))‖ ≤ A * Real.exp (η * r * Real.cos α) ∧
        ‖q (r * cexp (-α * I))‖ ≤ A * Real.exp (η * r * Real.cos α) ∧
        ‖q (-(r * cexp (α * I)))‖ ≤ A * Real.exp (η * r * Real.cos α) ∧
        ‖q (-(r * cexp (-α * I)))‖ ≤ A * Real.exp (η * r * Real.cos α) := by
  have hC0 : 0 ≤ C := by
    have := hC 0
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) (thetaCuspFullSource_pos 0)
  simpa using rays_of_band_bound hqc (C := 3 * C) (by linarith) 0
    (fun z hz => by simpa using norm_quotient_le_of_band hC hq hz)

/-! ## The order-one envelope of the quotient -/

theorem shape_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (1 + s) * Real.log (2 + s) ≤ (1 + t) * Real.log (2 + t) :=
  mul_le_mul (by linarith) (Real.log_le_log (by linarith) (by linarith))
    (Real.log_nonneg (by linarith)) (by linarith)

theorem log_le_two_mul_log {r c : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) (hc4 : c ≤ 4 + 4 * r + r ^ 2 - 2 - r) :
    Real.log (2 + r + c) ≤ 2 * Real.log (2 + r) := by
  have h2 : 2 * Real.log (2 + r) = Real.log ((2 + r) ^ 2) := by rw [Real.log_pow]; norm_num
  rw [h2]
  exact Real.log_le_log (by linarith) (by nlinarith)

theorem posLog_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.posLog (Real.exp x) = x := by
  rw [Real.posLog_eq_log (by rw [abs_of_pos (Real.exp_pos _)]; exact Real.one_le_exp hx),
    Real.log_exp]

/-- The order-one envelope of `F = XiC`. -/
theorem exists_norm_XiC_le_exp :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ z, ‖XiC z‖ ≤ Real.exp (K₀ * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  obtain ⟨C₀, hC₀, hxi⟩ := orderOneEnvelope_xi
  refine ⟨4 * C₀, by positivity, fun z => ?_⟩
  have h := hxi (1 / 2 + z * I)
  rw [GaloisForLFunctions.HTGeometry.orderOneWeight] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hr := norm_nonneg z
  have hs : ‖(1 / 2 : ℂ) + z * I‖ ≤ 1 / 2 + ‖z‖ := by
    calc _ ≤ ‖(1 / 2 : ℂ)‖ + ‖z * I‖ := norm_add_le _ _
      _ = 1 / 2 + ‖z‖ := by rw [norm_mul, Complex.norm_I, mul_one]; norm_num
  have h1 := shape_mono (norm_nonneg _) hs
  have hlog : Real.log (2 + ‖z‖ + 1 / 2) ≤ 2 * Real.log (2 + ‖z‖) :=
    log_le_two_mul_log hr (by norm_num) (by nlinarith)
  have hl0 : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith)
  have h2 : (1 + (1 / 2 + ‖z‖)) * Real.log (2 + (1 / 2 + ‖z‖)) ≤
      4 * ((1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    rw [show 2 + (1 / 2 + ‖z‖) = 2 + ‖z‖ + 1 / 2 by ring]
    have hl1 : 0 ≤ Real.log (2 + ‖z‖ + 1 / 2) := Real.log_nonneg (by linarith)
    nlinarith
  calc C₀ * (1 + ‖1 / 2 + z * I‖) * Real.log (2 + ‖1 / 2 + z * I‖) =
        C₀ * ((1 + ‖1 / 2 + z * I‖) * Real.log (2 + ‖1 / 2 + z * I‖)) := by ring
    _ ≤ C₀ * (4 * ((1 + ‖z‖) * Real.log (2 + ‖z‖))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hC₀.le
    _ = 4 * C₀ * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by ring

theorem meromorphicOrderAt_ne_top_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ z, f z ≠ 0) (w : ℂ) : meromorphicOrderAt f w ≠ ⊤ := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hA : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have h0 : analyticOrderAt f z₀ ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hz₀)]; exact ENat.zero_ne_top
  have hw := hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z₀)
    (mem_univ w) h0
  rw [(hf.analyticAt w).meromorphicOrderAt_eq]
  intro h
  exact hw (by simpa using h)

/-- **Order-one envelope of an entire quotient.**  If `G = q F` with `q` entire and `G` entire,
nonzero, with `|G(z)| ≤ C exp(K₀(1+|z|) log(2+|z|))`, then `q` has such an envelope too.  Via the
Nevanlinna first main theorem the proximity of `q` is bounded by those of `G` and `F`, and the
Poisson–Jensen bound converts it to a pointwise envelope. -/
theorem exists_quotient_envelope_of_bound {G : ℂ → ℂ} (hGd : Differentiable ℂ G) {K₀ : ℝ}
    (hC0 : 0 ≤ C)
    (hGenv : ∀ z, ‖G z‖ ≤ C * Real.exp (K₀ * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hq : ∀ z, G z = q z * XiC z) (hqd : Differentiable ℂ q) (hG : ∃ z, G z ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z, ‖q z‖ ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  obtain ⟨KX, hKX, hX0⟩ := exists_norm_XiC_le_exp
  set K₁ := max KX K₀
  have hK₁ : 0 ≤ K₁ := le_max_of_le_left hKX
  have hshape0 : ∀ z : ℂ, 0 ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun z => by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + ‖z‖ by linarith [norm_nonneg z]); positivity
  have hmono : ∀ {a : ℝ}, a ≤ K₁ → ∀ z : ℂ, a * (1 + ‖z‖) * Real.log (2 + ‖z‖) ≤
      K₁ * (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun ha z => by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right ha (hshape0 z)
  have hX : ∀ z, ‖XiC z‖ ≤ Real.exp (K₁ * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := fun z =>
    (hX0 z).trans (Real.exp_le_exp.mpr (hmono (le_max_left _ _) z))
  have hHenv : ∀ z, ‖G z‖ ≤ C * Real.exp (K₁ * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := fun z =>
    (hGenv z).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (hmono (le_max_right _ _) z)) hC0)
  have hA : ∀ f : ℂ → ℂ, Differentiable ℂ f → AnalyticOnNhd ℂ f univ :=
    fun f hf z _ => hf.analyticAt z
  have hqne : ∃ z, q z ≠ 0 := by
    obtain ⟨z₀, hz₀⟩ := hG
    exact ⟨z₀, fun h => hz₀ (by rw [hq, h, zero_mul])⟩
  obtain ⟨K, hK⟩ := GaloisForLFunctions.QuotientProximity.proximity_quotient_le
    (F := XiC) (G := G) (H := q) (hA _ XiC_differentiable) (hA _ hGd) (hA _ hqd)
    (meromorphicOrderAt_ne_top_of_differentiable XiC_differentiable ⟨0, XiC_ne_zero_of_norm_le_one
      (by simp)⟩)
    (meromorphicOrderAt_ne_top_of_differentiable hGd hG) hq
  have hprox : ∀ r : ℝ, 1 ≤ r → ValueDistribution.proximity q ⊤ r ≤
      Real.posLog C + 2 * (K₁ * (1 + r) * Real.log (2 + r)) + K := by
    intro r hr
    have hr0 : 0 ≤ r := by linarith
    have hshape : 0 ≤ K₁ * (1 + r) * Real.log (2 + r) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + r by linarith); positivity
    have hmX := GaloisForLFunctions.HTGeometry.proximity_top_le_posLog_of_norm (f := XiC) hr0
      (fun z _ => (XiC_differentiable.analyticAt z).meromorphicAt)
      (M := Real.exp (K₁ * (1 + r) * Real.log (2 + r))) (fun z hz => by rw [← hz]; exact hX z)
    rw [posLog_exp_of_nonneg hshape] at hmX
    have hmH := GaloisForLFunctions.HTGeometry.proximity_top_le_posLog_of_norm
      (f := G) hr0 (fun z _ => (hGd.analyticAt z).meromorphicAt)
      (M := C * Real.exp (K₁ * (1 + r) * Real.log (2 + r))) (fun z hz => by rw [← hz]; exact hHenv z)
    have hpl := Real.posLog_mul (x := C) (y := Real.exp (K₁ * (1 + r) * Real.log (2 + r)))
    rw [posLog_exp_of_nonneg hshape] at hpl
    have := hK r hr
    linarith
  set K₂ := max |Real.log ‖q 0‖| |Real.log ‖meromorphicTrailingCoeffAt q 0‖|
  have hK₂ : 0 ≤ K₂ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcpos : 0 ≤ 6 * (Real.posLog C + |K|) + 3 * K₂ := by
    have := Real.posLog_nonneg (x := C)
    have := abs_nonneg K
    linarith
  refine ⟨72 * K₁ + (6 * (Real.posLog C + |K|) + 3 * K₂) / Real.log 2,
    add_nonneg (by linarith) (div_nonneg hcpos hl2.le), fun w => ?_⟩
  set ρ := ‖w‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg w
  have hmain := GaloisForLFunctions.HTGeometry.posLog_norm_le_characteristic hqd
    (meromorphicOrderAt_ne_top_of_differentiable hqd hqne) (R := 2 * ρ + 2) (r := ρ)
    (by linarith) hρ0 (by linarith) le_rfl
  rw [GaloisForLFunctions.Nevanlinna.characteristic_top_eq_proximity_of_analyticOnNhd (hA _ hqd)]
    at hmain
  have hpR := hprox (2 * ρ + 2) (by linarith)
  have hnn : 0 ≤ ValueDistribution.proximity q ⊤ (2 * ρ + 2) :=
    GaloisForLFunctions.QuotientProximity.proximity_nonneg_of_entire (hA _ hqd) (by linarith)
  have hfac : (2 * ρ + 2 + ρ) / (2 * ρ + 2 - ρ) ≤ 3 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hfac0 : 0 ≤ (2 * ρ + 2 + ρ) / (2 * ρ + 2 - ρ) := div_nonneg (by linarith) (by linarith)
  have hl0 : Real.log 2 ≤ Real.log (2 + ρ) := Real.log_le_log (by norm_num) (by linarith)
  have hS0 : Real.log 2 ≤ (1 + ρ) * Real.log (2 + ρ) := by nlinarith
  have hR : (1 + (2 * ρ + 2)) * Real.log (2 + (2 * ρ + 2)) ≤ 6 * ((1 + ρ) * Real.log (2 + ρ)) := by
    have hlog : Real.log (2 + ρ + (ρ + 2)) ≤ 2 * Real.log (2 + ρ) :=
      log_le_two_mul_log hρ0 (by linarith) (by nlinarith)
    rw [show 2 + (2 * ρ + 2) = 2 + ρ + (ρ + 2) by ring]
    have hl1 : 0 ≤ Real.log (2 + ρ + (ρ + 2)) := Real.log_nonneg (by linarith)
    have hl2' : 0 ≤ Real.log (2 + ρ) := Real.log_nonneg (by linarith)
    nlinarith
  have hbound : Real.posLog ‖q w‖ ≤
      (72 * K₁ + (6 * (Real.posLog C + |K|) + 3 * K₂) / Real.log 2) * (1 + ρ) * Real.log (2 + ρ) := by
    have hX2 : 0 ≤ 2 * ValueDistribution.proximity q ⊤ (2 * ρ + 2) + K₂ := by linarith
    have h1 : Real.posLog ‖q w‖ ≤ 3 * (2 * ValueDistribution.proximity q ⊤ (2 * ρ + 2) + K₂) :=
      hmain.trans (mul_le_mul_of_nonneg_right hfac hX2)
    have hKabs := le_abs_self K
    have hpC : 0 ≤ Real.posLog C := Real.posLog_nonneg
    have hc : (6 * (Real.posLog C + |K|) + 3 * K₂) ≤
        (6 * (Real.posLog C + |K|) + 3 * K₂) / Real.log 2 * ((1 + ρ) * Real.log (2 + ρ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hS0 (by positivity)
    have hk6 : K₁ * (1 + (2 * ρ + 2)) * Real.log (2 + (2 * ρ + 2)) ≤
        K₁ * (6 * ((1 + ρ) * Real.log (2 + ρ))) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hR hK₁
    nlinarith
  calc ‖q w‖ ≤ Real.exp (Real.posLog ‖q w‖) :=
        GaloisForLFunctions.HTGeometry.le_exp_posLog (norm_nonneg _)
    _ ≤ _ := Real.exp_le_exp.mpr hbound


/-- **The quotient has an order-one envelope.** Via the Nevanlinna first main theorem the
proximity of `Q = H/F` is bounded by those of `H` and `F`; the Poisson–Jensen bound then gives
`|Q(z)| ≤ exp(K(1+|z|) log(2+|z|))`. -/
theorem exists_quotient_envelope (hu : AEStronglyMeasurable u)
    (hC : ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x) (hq : ∀ z, sourceTransform u z = q z * XiC z)
    (hqd : Differentiable ℂ q) (hH : ∃ z, sourceTransform u z ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z, ‖q z‖ ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  obtain ⟨K₀, hK₀, hX⟩ := exists_norm_XiC_le_exp
  have hC0 : 0 ≤ C := by
    have := hC 0
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) (thetaCuspFullSource_pos 0)
  refine exists_quotient_envelope_of_bound (K₀ := K₀)
    (measurableMomentSource_of_le hu hC).differentiable_sourceTransform hC0 (fun z => ?_) hq
    hqd hH
  refine (norm_sourceTransform_le hC z).trans (mul_le_mul_of_nonneg_left ?_ hC0)
  rw [← norm_XiC_I_mul]
  refine (hX _).trans (Real.exp_le_exp.mpr ?_)
  have hn : ‖I * (z.im : ℂ)‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact Complex.abs_im_le_norm z
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (shape_mono (norm_nonneg _) hn) hK₀

/-! ## Relative-source rigidity -/

theorem fourier_eq_sourceTransform (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = sourceTransform f (2 * Real.pi * ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, sourceTransform]
  congr 1
  funext v
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- `L¹` Fourier uniqueness in the `XiC` normalization. -/
theorem ae_eq_zero_of_sourceTransform_eq_zero {f : ℝ → ℂ} (hf : Integrable f)
    (h : ∀ z : ℂ, sourceTransform f z = 0) : f =ᵐ[volume] 0 :=
  HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hf fun ξ => by
    rw [fourier_eq_sourceTransform]; exact h _

/-- **Relative-source rigidity.** Let `u` be measurable with `|u| ≤ C k` for the literal theta source
`k`, and suppose its entire Fourier transform `H(z) = ∫ e^{-izx} u(x) dx` contains every zero of
`F = XiC` with at least the same multiplicity. Then `u = c k` almost everywhere for a constant
`c`. No evenness is needed. -/
theorem relativeSource_rigidity (hu : AEStronglyMeasurable u)
    (hC : ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x)
    (hdiv : ∀ z, analyticOrderAt XiC z ≤ analyticOrderAt (sourceTransform u) z) :
    ∃ c : ℂ, u =ᵐ[volume] fun x => c * thetaCuspFullSource x := by
  have hms := measurableMomentSource_of_le hu hC
  have hHd := hms.differentiable_sourceTransform
  have hint_u : Integrable u := (hms.moment 0).mono' hu (Eventually.of_forall fun x => by simp)
  by_cases hH : ∀ z, sourceTransform u z = 0
  · refine ⟨0, ?_⟩
    filter_upwards [ae_eq_zero_of_sourceTransform_eq_zero hint_u hH] with x hx
    simpa using hx
  push Not at hH
  obtain ⟨q, hqd, hq⟩ := GaloisForLFunctions.HTGeometry.exists_entire_quotient hHd
    XiC_differentiable ⟨0, XiC_ne_zero_of_norm_le_one (by simp)⟩ hdiv
  obtain ⟨K, hK, henv⟩ := exists_quotient_envelope hu hC hq hqd hH
  have hconst := HTGeometry.eq_const_of_imag_of_rays hqd hK henv (norm_quotient_imag_le hC hq)
    (quotient_rays hC hq hqd.continuous)
  refine ⟨q 0, ?_⟩
  have hw : Integrable (fun x => u x - q 0 * thetaSourceC x) :=
    hint_u.sub (expMomentSource_thetaSourceC.integrable.const_mul _)
  have hzero : ∀ z, sourceTransform (fun x => u x - q 0 * thetaSourceC x) z = 0 := by
    intro z
    have h1 := hms.integrable_cexp z
    have h2 := (expMomentSource_thetaSourceC.integrable_cexp z).const_mul (q 0)
    have hsplit : sourceTransform (fun x => u x - q 0 * thetaSourceC x) z =
        sourceTransform u z - q 0 * sourceTransform thetaSourceC z := by
      rw [sourceTransform, sourceTransform, sourceTransform, ← integral_const_mul, ← integral_sub h1 h2]
      congr 1; funext x; ring
    rw [hsplit, hq, hconst z, sourceTransform_thetaSourceC, sub_self]
  filter_upwards [ae_eq_zero_of_sourceTransform_eq_zero hw hzero] with x hx
  simp only [Pi.zero_apply, sub_eq_zero] at hx
  rw [hx, thetaSourceC]

/-- **Relative-source rigidity, real form (card statement).** A real, even, measurable `u` with
`|u| ≤ C k` whose transform carries the complete Xi divisor is `c k` a.e. for a real `c`. -/
theorem relativeSource_rigidity_real {v : ℝ → ℝ} (hv : AEStronglyMeasurable v)
    (hC : ∀ x, |v x| ≤ C * thetaCuspFullSource x)
    (hdiv : ∀ z, analyticOrderAt XiC z ≤ analyticOrderAt (sourceTransform fun x => (v x : ℂ)) z) :
    ∃ c : ℝ, v =ᵐ[volume] fun x => c * thetaCuspFullSource x := by
  obtain ⟨c, hc⟩ := relativeSource_rigidity (u := fun x => (v x : ℂ))
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hv)
    (fun x => by simpa [Complex.norm_real] using hC x) hdiv
  refine ⟨c.re, ?_⟩
  filter_upwards [hc] with x hx
  have hre := congrArg Complex.re hx
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
  exact hre

/-- For continuous `u` the rigidity holds pointwise. -/
theorem relativeSource_rigidity_of_continuous (hu : Continuous u)
    (hC : ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x)
    (hdiv : ∀ z, analyticOrderAt XiC z ≤ analyticOrderAt (sourceTransform u) z) :
    ∃ c : ℂ, ∀ x, u x = c * thetaCuspFullSource x := by
  obtain ⟨c, hc⟩ := relativeSource_rigidity hu.aestronglyMeasurable hC hdiv
  refine ⟨c, fun x => ?_⟩
  have := (hu.ae_eq_iff_eq volume (continuous_const.mul
    expMomentSource_thetaSourceC.continuous)).mp hc
  exact congrFun this x

end

end RHTower
