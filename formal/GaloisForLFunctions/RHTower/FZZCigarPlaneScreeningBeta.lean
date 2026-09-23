import GaloisForLFunctions.HTGeometry.HalfLineBetaKernel
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.SpectralZetaMellin
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The original two-puncture plane screening integral

The original kernel `|z|^(-2a) |z-1|^(-2b)` is integrable on the whole
complex plane for `0 < a,b < 1 < a+b`. Its integral is

`pi Gamma(a+b-1) Gamma(1-a) Gamma(1-b) /
  (Gamma(a) Gamma(b) Gamma(2-a-b))`.

This is derived from positive Gamma parameters and a translated plane Gaussian.
A one-dimensional rescaling of the second Gamma parameter gives a half-line Beta
integral. Product integrability is proved before every Fubini interchange. The
original Gamma representation is used almost everywhere, retaining both
punctures and the tail at infinity.

The public positive exponential chart covers the entire convergence chamber.
Its variables are independent continuation exponents, not physical levels or
replica deficits. This proves the convergent-chamber identity corresponding to
arXiv:2310.02313, section 4.1, equation (60), at arguments `(-a,-b)`.

No analytic continuation, physical cutoff matching, marked logarithmic integral,
higher screening depth, complete Ward identity or RH statement is asserted.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private theorem rate_gamma {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), t^(s-1)*Real.exp (-(r*t))) = Real.Gamma s*r^(-s) := by
  simp_rw [mul_comm ( _ ^ (s-1))]
  exact (HTGeometry.DaiYoshikawa.gamma_mul_rpow_neg_eq_integral hr hs).symm

private theorem rate_gamma_integrable {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t^(s-1)*Real.exp (-(r*t))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [rate_gamma hr hs]
  exact ne_of_gt (mul_pos (Real.Gamma_pos_of_pos hs) (Real.rpow_pos_of_pos hr _))

private theorem beta_ray {w c : ℝ} (hw : 0 < w) (hc : w < c) :
    (∫ y in Ioi (0 : ℝ), y^(w-1)*(1+y)^(-c)) =
      Real.Gamma w * Real.Gamma (c-w) / Real.Gamma c := by
  have h := HTGeometry.integral_halfLine_beta (w := (w : ℂ)) (c := (c : ℂ)) hw hc
  have he : ∀ y ∈ Ioi (0 : ℝ),
      (y : ℂ)^((w : ℂ)-1)*(1+(y : ℂ))^(-(c : ℂ)) =
        ((y^(w-1)*(1+y)^(-c) : ℝ) : ℂ) := by
    intro y hy
    have hy0 : 0 < y := hy
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt hy),
      Complex.ofReal_cpow (by linarith : 0 ≤ 1+y)]
    push_cast
    rfl
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_complex_ofReal] at h
  rw [← Complex.ofReal_sub, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_div] at h
  exact_mod_cast h

private theorem beta_ray_integrable {w c : ℝ} (hw : 0 < w) (hc : w < c) :
    IntegrableOn (fun y : ℝ => y^(w-1)*(1+y)^(-c)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [beta_ray hw hc]
  exact ne_of_gt (div_pos (mul_pos (Real.Gamma_pos_of_pos hw)
    (Real.Gamma_pos_of_pos (sub_pos.mpr hc))) (Real.Gamma_pos_of_pos (hw.trans hc)))

private theorem gaussian_square {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (z : ℂ) :
    -t*‖z‖^(2 : ℕ)-u*‖z-1‖^(2 : ℕ) =
      -(t*u/(t+u)) + (-(t+u)*‖z-((u/(t+u) : ℝ) : ℂ)‖^(2 : ℕ)) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero]
  field_simp
  ring

private theorem plane_gaussian {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    (∫ z : ℂ, Real.exp (-t*‖z‖^(2 : ℕ)-u*‖z-1‖^(2 : ℕ))) =
      Real.pi/(t+u)*Real.exp (-(t*u/(t+u))) := by
  simp_rw [gaussian_square ht hu, Real.exp_add]
  rw [integral_const_mul, integral_sub_right_eq_self (f := fun z : ℂ => Real.exp (-(t+u)*‖z‖^(2 : ℕ)))]
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (add_pos ht hu)]
  simp only [Complex.finrank_real_complex]
  norm_num
  ring

private theorem plane_gaussian_integrable {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    Integrable (fun z : ℂ => Real.exp (-t*‖z‖^(2 : ℕ)-u*‖z-1‖^(2 : ℕ))) := by
  apply Integrable.of_integral_ne_zero
  rw [plane_gaussian ht hu]
  exact ne_of_gt (mul_pos (div_pos Real.pi_pos (add_pos ht hu)) (Real.exp_pos _))


private def rescaledPair (a b t y : ℝ) : ℝ :=
  y^(b-1)/(1+y) * (t^((a+b-1)-1) * Real.exp (-(y/(1+y)*t)))

private theorem rescaledPair_nonneg {a b t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    0 ≤ rescaledPair a b t y := by
  unfold rescaledPair
  positivity

private theorem rescaledPair_inner_integrable {a b y : ℝ} (hab : 1 < a+b) (hy : 0 < y) :
    IntegrableOn (fun t => rescaledPair a b t y) (Ioi 0) := by
  exact (rate_gamma_integrable (div_pos hy (by linarith)) (by linarith : 0 < a+b-1)).const_mul _

private theorem rescaledPair_inner {a b y : ℝ} (hab : 1 < a+b) (hy : 0 < y) :
    (∫ t in Ioi (0 : ℝ), rescaledPair a b t y) =
      Real.Gamma (a+b-1) * (y^(-a)*(1+y)^(a+b-2)) := by
  unfold rescaledPair
  rw [integral_const_mul, rate_gamma (div_pos hy (by linarith)) (by linarith : 0 < a+b-1),
    Real.div_rpow hy.le (by linarith : 0 ≤ 1+y),
    Real.rpow_neg (by linarith : 0 ≤ 1+y), div_inv_eq_mul]
  have hyprod : y^(b-1)*y^(-(a+b-1)) = y^(-a) := by
    rw [← Real.rpow_add hy]
    congr 1
    ring
  have hone : (1+y)^(a+b-1)/(1+y) = (1+y)^(a+b-2) := by
    have h := Real.rpow_sub (by linarith : 0 < 1+y) (a+b-1) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  calc
    _ = Real.Gamma (a+b-1) * ((y^(b-1)*y^(-(a+b-1))) * ((1+y)^(a+b-1)/(1+y))) := by ring
    _ = _ := by rw [hyprod, hone]

private theorem ray_weight_integrable {a b : ℝ} (ha : a < 1) (hb : b < 1) :
    IntegrableOn (fun y : ℝ => y^(-a)*(1+y)^(a+b-2)) (Ioi 0) := by
  have h := beta_ray_integrable (w := 1-a) (c := 2-a-b) (by linarith) (by linarith)
  simpa only [show 1-a-1 = -a by ring, show -(2-a-b) = a+b-2 by ring] using h

private theorem ray_weight_integral {a b : ℝ} (ha : a < 1) (hb : b < 1) :
    (∫ y in Ioi (0 : ℝ), y^(-a)*(1+y)^(a+b-2)) =
      Real.Gamma (1-a)*Real.Gamma (1-b)/Real.Gamma (2-a-b) := by
  have h := beta_ray (w := 1-a) (c := 2-a-b) (by linarith) (by linarith)
  simpa only [show 1-a-1 = -a by ring, show -(2-a-b) = a+b-2 by ring,
    show 2-a-b-(1-a) = 1-b by ring] using h

private theorem rescaledPair_integrable {a b : ℝ} (ha : a < 1) (hb : b < 1)
    (hab : 1 < a+b) :
    Integrable (fun q : ℝ × ℝ => rescaledPair a b q.1 q.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  apply (integrable_prod_iff' (by unfold rescaledPair; fun_prop)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact rescaledPair_inner_integrable hab hy
  · apply ((ray_weight_integrable ha hb).const_mul (Real.Gamma (a+b-1))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [← rescaledPair_inner hab hy]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (Real.norm_of_nonneg (rescaledPair_nonneg ht hy)).symm

private theorem rescaledPair_integral {a b : ℝ} (ha : a < 1) (hb : b < 1)
    (hab : 1 < a+b) :
    (∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), rescaledPair a b t y) =
      Real.Gamma (a+b-1)*(Real.Gamma (1-a)*Real.Gamma (1-b)/Real.Gamma (2-a-b)) := by
  rw [integral_integral_swap (rescaledPair_integrable ha hb hab)]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => rescaledPair_inner hab hy),
    integral_const_mul, ray_weight_integral ha hb]


private def gaussianPair (a b t u : ℝ) : ℝ :=
  t^(a-1)*u^(b-1)/(t+u)*Real.exp (-(t*u/(t+u)))

private theorem gaussianPair_nonneg {a b t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    0 ≤ gaussianPair a b t u := by
  unfold gaussianPair
  positivity

private theorem gaussianPair_rescale {a b t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    t * gaussianPair a b t (t*y) = rescaledPair a b t y := by
  unfold gaussianPair rescaledPair
  have hsum : t+t*y = t*(1+y) := by ring
  have he : t*(t*y)/(t+t*y) = y/(1+y)*t := by
    rw [hsum]
    field_simp
  rw [he, Real.mul_rpow ht.le hy.le, hsum]
  have hp : t^(a-1)*t^(b-1) = t^((a+b-1)-1) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  calc
    _ = (t^(a-1)*t^(b-1)) * y^(b-1)/(1+y)*Real.exp (-(y/(1+y)*t)) := by
      field_simp
    _ = _ := by rw [hp]; ring

private theorem gaussianPair_inner_integral {a b t : ℝ} (ht : 0 < t) :
    (∫ u in Ioi (0 : ℝ), gaussianPair a b t u) =
      ∫ y in Ioi (0 : ℝ), rescaledPair a b t y := by
  have hs := integral_comp_mul_left_Ioi (gaussianPair a b t) 0 ht
  simp only [mul_zero, smul_eq_mul] at hs
  calc
    _ = t * ∫ y in Ioi (0 : ℝ), gaussianPair a b t (t*y) := by rw [hs]; field_simp
    _ = _ := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun y hy => gaussianPair_rescale ht hy)

private theorem gaussianPair_inner_integrable {a b t : ℝ} (ht : 0 < t)
    (hi : IntegrableOn (fun y => rescaledPair a b t y) (Ioi 0)) :
    IntegrableOn (gaussianPair a b t) (Ioi 0) := by
  have hs : IntegrableOn (fun y => gaussianPair a b t (t*y)) (Ioi 0) := by
    apply (hi.const_mul t⁻¹).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [← gaussianPair_rescale ht hy]
    field_simp
  simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff (gaussianPair a b t) 0 ht).mp hs

private theorem gaussianPair_integrable {a b : ℝ} (ha : a < 1) (hb : b < 1)
    (hab : 1 < a+b) :
    Integrable (fun q : ℝ × ℝ => gaussianPair a b q.1 q.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hF := rescaledPair_integrable ha hb hab
  apply (integrable_prod_iff (by unfold gaussianPair; fun_prop)).mpr
  constructor
  · filter_upwards [hF.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with t ht ht0
    exact gaussianPair_inner_integrable ht0 ht
  · apply hF.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [← gaussianPair_inner_integral ht]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (Real.norm_of_nonneg (gaussianPair_nonneg ht hu)).symm

private theorem gaussianPair_integral {a b : ℝ} (ha : a < 1) (hb : b < 1)
    (hab : 1 < a+b) :
    (∫ q : ℝ × ℝ, gaussianPair a b q.1 q.2
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      Real.Gamma (a+b-1)*(Real.Gamma (1-a)*Real.Gamma (1-b)/Real.Gamma (2-a-b)) := by
  rw [integral_prod _ (gaussianPair_integrable ha hb hab)]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => gaussianPair_inner_integral ht)]
  exact rescaledPair_integral ha hb hab


private abbrev pairMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))

private theorem pair_positive : ∀ᵐ q ∂pairMeasure, 0 < q.1 ∧ 0 < q.2 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact ⟨ht, hu⟩

private def laplacePair (a b : ℝ) (q : ℝ × ℝ) (z : ℂ) : ℝ :=
  q.1^(a-1)*q.2^(b-1)*Real.exp (-q.1*‖z‖^(2 : ℕ)-q.2*‖z-1‖^(2 : ℕ))

private theorem laplacePair_plane {a b t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    (∫ z : ℂ, laplacePair a b (t,u) z) = Real.pi*gaussianPair a b t u := by
  unfold laplacePair gaussianPair
  rw [integral_const_mul, plane_gaussian ht hu]
  ring

private theorem laplacePair_integrable {a b : ℝ} (ha : a < 1) (hb : b < 1)
    (hab : 1 < a+b) :
    Integrable (fun r : (ℝ × ℝ) × ℂ => laplacePair a b r.1 r.2) (pairMeasure.prod volume) := by
  apply (integrable_prod_iff (by unfold laplacePair; fun_prop)).mpr
  constructor
  · filter_upwards [pair_positive] with q hq
    exact (plane_gaussian_integrable hq.1 hq.2).const_mul _
  · apply ((gaussianPair_integrable ha hb hab).const_mul Real.pi).congr
    filter_upwards [pair_positive] with q hq
    rw [← laplacePair_plane hq.1 hq.2]
    apply integral_congr_ae
    filter_upwards with z
    symm
    apply Real.norm_of_nonneg
    unfold laplacePair
    obtain ⟨ht, hu⟩ := hq
    positivity

private theorem laplacePair_parameter {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    (∫ q, laplacePair a b q z ∂pairMeasure) =
      (Real.Gamma a*Real.Gamma b)*(‖z‖^(-2*a)*‖z-1‖^(-2*b)) := by
  have he : (fun q => laplacePair a b q z) = fun q : ℝ × ℝ =>
      (q.1^(a-1)*Real.exp (-(‖z‖^(2 : ℕ)*q.1))) *
        (q.2^(b-1)*Real.exp (-(‖z-1‖^(2 : ℕ)*q.2))) := by
    funext q
    unfold laplacePair
    rw [show -q.1*‖z‖^(2 : ℕ)-q.2*‖z-1‖^(2 : ℕ) = -(‖z‖^(2 : ℕ)*q.1) + -(‖z-1‖^(2 : ℕ)*q.2) by ring,
      Real.exp_add]
    ring
  rw [he, pairMeasure, integral_prod_mul
    (fun t : ℝ => t^(a-1)*Real.exp (-(‖z‖^(2 : ℕ)*t)))
    (fun u : ℝ => u^(b-1)*Real.exp (-(‖z-1‖^(2 : ℕ)*u))),
    rate_gamma (sq_pos_of_pos (norm_pos_iff.mpr hz)) ha,
    rate_gamma (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz1))) hb]
  have hp (w : ℂ) (d : ℝ) : (‖w‖^(2 : ℕ))^(-d) = ‖w‖^(-2*d) := by
    rw [← Real.rpow_natCast ‖w‖ 2, ← Real.rpow_mul (norm_nonneg w)]
    congr 1
    ring
  rw [hp, hp]
  ring

private theorem plane_kernel_integrable {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a < 1) (hb : b < 1) (hab : 1 < a+b) :
    Integrable (fun z : ℂ => ‖z‖^(-2*a)*‖z-1‖^(-2*b)) := by
  have hP := laplacePair_integrable ha hb hab
  apply (hP.integral_prod_right.const_mul (Real.Gamma a*Real.Gamma b)⁻¹).congr
  filter_upwards [volume.ae_ne (0 : ℂ), volume.ae_ne (1 : ℂ)] with z hz hz1
  rw [laplacePair_parameter ha0 hb0 hz hz1]
  have hg : Real.Gamma a*Real.Gamma b ≠ 0 :=
    ne_of_gt (mul_pos (Real.Gamma_pos_of_pos ha0) (Real.Gamma_pos_of_pos hb0))
  field_simp

private theorem plane_kernel_integral {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a < 1) (hb : b < 1) (hab : 1 < a+b) :
    (∫ z : ℂ, ‖z‖^(-2*a)*‖z-1‖^(-2*b)) =
      Real.pi*Real.Gamma (a+b-1)*Real.Gamma (1-a)*Real.Gamma (1-b) /
        (Real.Gamma a*Real.Gamma b*Real.Gamma (2-a-b)) := by
  have hP := laplacePair_integrable ha hb hab
  have hswap := integral_integral_swap (f := fun q z => laplacePair a b q z) hP
  have hleft : (∫ q, (∫ z : ℂ, laplacePair a b q z) ∂pairMeasure) =
      Real.pi*(Real.Gamma (a+b-1)*(Real.Gamma (1-a)*Real.Gamma (1-b)/Real.Gamma (2-a-b))) := by
    calc
      _ = ∫ q, Real.pi*gaussianPair a b q.1 q.2 ∂pairMeasure := by
        apply integral_congr_ae
        filter_upwards [pair_positive] with q hq
        exact laplacePair_plane hq.1 hq.2
      _ = _ := by rw [integral_const_mul, gaussianPair_integral ha hb hab]
  have hright : (∫ z : ℂ, ∫ q, laplacePair a b q z ∂pairMeasure) =
      (Real.Gamma a*Real.Gamma b)*(∫ z : ℂ, ‖z‖^(-2*a)*‖z-1‖^(-2*b)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [volume.ae_ne (0 : ℂ), volume.ae_ne (1 : ℂ)] with z hz hz1
    exact laplacePair_parameter ha0 hb0 hz hz1
  rw [hleft, hright] at hswap
  have hga := (Real.Gamma_pos_of_pos ha0).ne'
  have hgb := (Real.Gamma_pos_of_pos hb0).ne'
  have hgc := (Real.Gamma_pos_of_pos (by linarith : 0 < 2-a-b)).ne'
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero hga hgb) hgc)).mpr
  field_simp at hswap
  simp only [show -(a*2) = -2*a by ring, show -(b*2) = -2*b by ring] at hswap
  linear_combination -hswap


/-- First independent exponent in the ordinary convergence chamber. -/
def fzzScreeningBetaA (x y : ℝ) : ℝ :=
  (1+Real.exp x)/(1+Real.exp x+Real.exp y)

/-- Second independent exponent in the ordinary convergence chamber. -/
def fzzScreeningBetaB (x y : ℝ) : ℝ :=
  (1+Real.exp y)/(1+Real.exp x+Real.exp y)

/-- Both punctures and the tail satisfy their strict convergence bounds. -/
theorem fzzScreeningBeta_chamber (x y : ℝ) :
    0 < fzzScreeningBetaA x y ∧ fzzScreeningBetaA x y < 1 ∧
    0 < fzzScreeningBetaB x y ∧ fzzScreeningBetaB x y < 1 ∧
    1 < fzzScreeningBetaA x y+fzzScreeningBetaB x y := by
  have hx := Real.exp_pos x
  have hy := Real.exp_pos y
  have hd : 0 < 1+Real.exp x+Real.exp y := by positivity
  unfold fzzScreeningBetaA fzzScreeningBetaB
  refine ⟨div_pos (by positivity) hd, ?_, div_pos (by positivity) hd, ?_, ?_⟩
  · rw [div_lt_one hd]
    linarith
  · rw [div_lt_one hd]
    linarith
  · rw [← add_div, one_lt_div hd]
    linarith

/-- The positive chart covers the entire triangular convergence chamber. -/
theorem fzzScreeningBeta_chart_iff (a b : ℝ) :
    (∃ x y : ℝ, fzzScreeningBetaA x y = a ∧ fzzScreeningBetaB x y = b) ↔
      0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 ∧ 1 < a+b := by
  constructor
  · rintro ⟨x,y,rfl,rfl⟩
    exact fzzScreeningBeta_chamber x y
  · rintro ⟨ha0,ha,hb0,hb,hab⟩
    have hd : 0 < a+b-1 := by linarith
    have hx : 0 < (1-b)/(a+b-1) := div_pos (by linarith) hd
    have hy : 0 < (1-a)/(a+b-1) := div_pos (by linarith) hd
    refine ⟨Real.log ((1-b)/(a+b-1)), Real.log ((1-a)/(a+b-1)), ?_, ?_⟩
    · unfold fzzScreeningBetaA
      rw [Real.exp_log hx, Real.exp_log hy]
      field_simp
      ring
    · unfold fzzScreeningBetaB
      rw [Real.exp_log hx, Real.exp_log hy]
      field_simp
      ring

/-- The original position integral includes the whole complex plane. -/
def fzzScreeningBetaIntegral (x y : ℝ) : ℝ :=
  ∫ z : ℂ, ‖z‖^(-2*fzzScreeningBetaA x y)*‖z-1‖^(-2*fzzScreeningBetaB x y)

/-- Ordinary absolute convergence of the original two-puncture source. -/
theorem fzzScreeningBetaKernel_integrable (x y : ℝ) :
    Integrable (fun z : ℂ =>
      ‖z‖^(-2*fzzScreeningBetaA x y)*‖z-1‖^(-2*fzzScreeningBetaB x y)) := by
  obtain ⟨ha0,ha,hb0,hb,hab⟩ := fzzScreeningBeta_chamber x y
  exact plane_kernel_integrable ha0 hb0 ha hb hab

/-- The Gamma ratio is derived from the original plane integral by integrable Fubini. -/
theorem fzzScreeningBetaIntegral_eq_gamma (x y : ℝ) :
    fzzScreeningBetaIntegral x y =
      Real.pi*Real.Gamma (fzzScreeningBetaA x y+fzzScreeningBetaB x y-1)*
        Real.Gamma (1-fzzScreeningBetaA x y)*Real.Gamma (1-fzzScreeningBetaB x y) /
          (Real.Gamma (fzzScreeningBetaA x y)*Real.Gamma (fzzScreeningBetaB x y)*
            Real.Gamma (2-fzzScreeningBetaA x y-fzzScreeningBetaB x y)) := by
  obtain ⟨ha0,ha,hb0,hb,hab⟩ := fzzScreeningBeta_chamber x y
  exact plane_kernel_integral ha0 hb0 ha hb hab

/-- Positivity belongs to this ordinary convergence chamber. -/
theorem fzzScreeningBetaIntegral_pos (x y : ℝ) : 0 < fzzScreeningBetaIntegral x y := by
  rw [fzzScreeningBetaIntegral_eq_gamma]
  obtain ⟨ha0,ha,hb0,hb,hab⟩ := fzzScreeningBeta_chamber x y
  have hs : 0 < fzzScreeningBetaA x y+fzzScreeningBetaB x y-1 := by linarith
  have h1a : 0 < 1-fzzScreeningBetaA x y := by linarith
  have h1b : 0 < 1-fzzScreeningBetaB x y := by linarith
  have h2 : 0 < 2-fzzScreeningBetaA x y-fzzScreeningBetaB x y := by linarith
  exact div_pos
    (mul_pos (mul_pos (mul_pos Real.pi_pos (Real.Gamma_pos_of_pos hs))
      (Real.Gamma_pos_of_pos h1a)) (Real.Gamma_pos_of_pos h1b))
    (mul_pos (mul_pos (Real.Gamma_pos_of_pos ha0) (Real.Gamma_pos_of_pos hb0))
      (Real.Gamma_pos_of_pos h2))

end GaloisForLFunctions.RHTower
