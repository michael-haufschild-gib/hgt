import GaloisForLFunctions.ThetaCuspSections.TheSharpCurrentTail
import GaloisForLFunctions.ThetaCuspSections.ExplicitCurrentCore
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The coupled analytic current tail

The product `Ξ(b-iz)Ξ(b+iz)` is even and bounded on a fixed aperture circle.
Subtracting its two Cauchy derivative formulas retains the aperture factor
before taking norms. This pays a factor of thirty-two in the complete tail.
-/

open Complex MeasureTheory Set Metric Filter
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
open _root_.RHTower

/-- An even entire function retains its vanishing derivative in the Cauchy estimate. -/
theorem norm_deriv_even_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (heven : ∀ z, f (-z) = f z) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z ∈ sphere (0 : ℂ) (3 / 2), ‖f z‖ ≤ B)
    {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    ‖deriv f a‖ ≤ 9 / 8 * B * ‖a‖ := by
  have hball : a ∈ ball (0 : ℂ) (3 / 2) := by
    rw [mem_ball, dist_zero_right]
    linarith only [ha]
  have hballneg : -a ∈ ball (0 : ℂ) (3 / 2) := by
    simpa only [mem_ball, dist_zero_right, norm_neg] using hball
  have hneg : deriv f (-a) = -deriv f a := by
    have hd := ((hf (-a)).hasDerivAt.comp a (hasDerivAt_id a).neg)
    have hd' : HasDerivAt f (deriv f (-a) * -1) a := by
      convert hd using 1
      funext z
      exact (heven z).symm
    have hh := hd'.unique (hf a).hasDerivAt
    linear_combination -hh
  let K : ℂ → ℂ → ℂ := fun u z => ((z - u) ^ 2)⁻¹ * f z
  have hint {u : ℂ} (hu : u ∈ ball (0 : ℂ) (3 / 2)) :
      CircleIntegrable (K u) 0 (3 / 2) := by
    apply ContinuousOn.circleIntegrable (by norm_num : (0 : ℝ) ≤ 3 / 2)
    refine (ContinuousOn.inv₀ ((continuous_id.sub continuous_const).pow 2).continuousOn
      (fun z hz => ?_)).mul hf.continuous.continuousOn
    intro hzero
    exact sphere_disjoint_ball.ne_of_mem hz hu (sub_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  have hformula {u : ℂ} (hu : u ∈ ball (0 : ℂ) (3 / 2)) :
      (2 * Real.pi * I : ℂ)⁻¹ • (∮ z in C(0, 3 / 2), K u z) = deriv f u := by
    exact two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      isOpen_univ (subset_univ _) hf.differentiableOn hu
  have hdiff : (2 * Real.pi * I : ℂ)⁻¹ •
      (∮ z in C(0, 3 / 2), K a z - K (-a) z) = 2 * deriv f a := by
    rw [circleIntegral.integral_sub (hint hball) (hint hballneg), smul_sub,
      hformula hball, hformula hballneg, hneg]
    ring
  have hkernel (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (3 / 2)) :
      ‖K a z - K (-a) z‖ ≤ 3 / 2 * B * ‖a‖ := by
    have hzN : ‖z‖ = 3 / 2 := by simpa only [mem_sphere, dist_zero_right] using hz
    have hD : 2 ≤ ‖z ^ 2 - a ^ 2‖ := by
      have hh := norm_sub_norm_le (z ^ 2) (a ^ 2)
      rw [norm_pow, norm_pow, hzN] at hh
      have ha2 := pow_le_pow_left₀ (norm_nonneg a) ha 2
      norm_num at ha2 hh
      linarith only [ha2, hh]
    have hza : z - a ≠ 0 := sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hball)
    have hzna : z + a ≠ 0 := by
      simpa only [sub_neg_eq_add] using
        sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hballneg)
    have hD0 : z ^ 2 - a ^ 2 ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hD
      norm_num at hD
    have he : K a z - K (-a) z = (4 * a * z / (z ^ 2 - a ^ 2) ^ 2) * f z := by
      dsimp only [K]
      rw [sub_neg_eq_add]
      field_simp [hza, hzna, hD0] <;> ring
    rw [he, norm_mul, norm_div, norm_mul, norm_mul, norm_pow, norm_ofNat, hzN]
    have hquot : 4 * ‖a‖ * (3 / 2) / ‖z ^ 2 - a ^ 2‖ ^ 2 ≤ 3 / 2 * ‖a‖ := by
      rw [div_le_iff₀ (by positivity : 0 < ‖z ^ 2 - a ^ 2‖ ^ 2)]
      have hd2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hD 2
      nlinarith only [mul_le_mul_of_nonneg_left hd2 (norm_nonneg a)]
    calc
      _ ≤ (3 / 2 * ‖a‖) * B := mul_le_mul hquot (hbound z hz) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hh := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (by norm_num : (0 : ℝ) ≤ 3 / 2) hkernel
  rw [hdiff, norm_mul, norm_ofNat] at hh
  nlinarith only [hh]

/-- The two opposite aperture shifts retain a common decay envelope. -/
def coupledXiProduct (b : ℝ) (z : ℂ) : ℂ :=
  XiC ((b : ℂ) - z * I) * XiC ((b : ℂ) + z * I)

theorem coupledXiProduct_differentiable (b : ℝ) : Differentiable ℂ (coupledXiProduct b) :=
  (XiC_differentiable.comp (by fun_prop)).mul (XiC_differentiable.comp (by fun_prop))

theorem coupledXiProduct_even (b : ℝ) (z : ℂ) :
    coupledXiProduct b (-z) = coupledXiProduct b z := by
  simp only [coupledXiProduct, neg_mul, sub_neg_eq_add, add_neg_eq_sub, mul_comm]

/-- The complete coupled product has no loss from the common contour phase. -/
theorem norm_coupledXiProduct_le {z : ℂ} (hz : ‖z‖ ≤ 3 / 2) (b : ℝ) :
    ‖coupledXiProduct b z‖ ≤ 1000000 * Real.exp (-(7 / 5 * |b|)) := by
  have hre : |z.re| ≤ 3 / 2 := (abs_re_le_norm z).trans hz
  have hm : (b : ℂ) - z * I = ((b + z.im : ℝ) : ℂ) + ((-z.re : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  have hp : (b : ℂ) + z * I = ((b - z.im : ℝ) : ℂ) + (z.re : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  have h1 := norm_XiC_le_wide (b + z.im) (-z.re) (by rwa [abs_neg])
  have h2 := norm_XiC_le_wide (b - z.im) z.re hre
  have habs : 2 * |b| ≤ |b + z.im| + |b - z.im| := by
    have hh := abs_add_le (b + z.im) (b - z.im)
    rw [show b + z.im + (b - z.im) = 2 * b by ring, abs_mul] at hh
    norm_num at hh
    exact hh
  rw [coupledXiProduct, norm_mul, hm, hp]
  calc
    _ ≤ (1000 * Real.exp (-(7 / 10 * |b + z.im|))) *
        (1000 * Real.exp (-(7 / 10 * |b - z.im|))) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 1000000 * Real.exp (-(7 / 10 * (|b + z.im| + |b - z.im|))) := by
      rw [show -(7 / 10 * (|b + z.im| + |b - z.im|)) =
        -(7 / 10 * |b + z.im|) + -(7 / 10 * |b - z.im|) by ring, Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      linarith only [habs]

theorem coupledXiProduct_real (a b : ℝ) :
    (coupledXiProduct b (a : ℂ)).re = normSq (XiC ((b : ℂ) - (a : ℂ) * I)) := by
  have he : (b : ℂ) + (a : ℂ) * I = (starRingEnd ℂ) ((b : ℂ) - (a : ℂ) * I) := by
    simp
  rw [coupledXiProduct, he, XiC_conj, Complex.mul_conj, Complex.ofReal_re]

theorem deriv_coupledXiProduct_re (a b : ℝ) :
    (deriv (coupledXiProduct b) (a : ℂ)).re = current a b := by
  have hh := ((coupledXiProduct_differentiable b (a : ℂ)).hasDerivAt).real_of_complex
  have he : (fun x : ℝ => (coupledXiProduct b (x : ℂ)).re) =
      (fun x : ℝ => normSq (XiC ((b : ℂ) - (x : ℂ) * I))) :=
    funext fun x => coupledXiProduct_real x b
  rw [he] at hh
  exact hh.unique (hasDerivAt_normSq_XiC a b)

/-- The complete current tail retains the aperture factor before taking norms. -/
theorem abs_current_le_coupled {a : ℝ} (ha : |a| ≤ 1 / 2) (b : ℝ) :
    |current a b| ≤ 1125000 * |a| * Real.exp (-(7 / 5 * |b|)) := by
  have hh := norm_deriv_even_le (coupledXiProduct_differentiable b)
    (coupledXiProduct_even b)
    (by positivity : 0 ≤ 1000000 * Real.exp (-(7 / 5 * |b|)))
    (fun z hz => norm_coupledXiProduct_le
      (le_of_eq (by simpa only [mem_sphere, dist_zero_right] using hz)) b)
    (a := (a : ℂ)) (by simpa only [norm_real, Real.norm_eq_abs] using ha)
  rw [norm_real, Real.norm_eq_abs] at hh
  rw [← deriv_coupledXiProduct_re a b]
  exact (abs_re_le_norm _).trans (hh.trans_eq (by ring))

#print axioms norm_deriv_even_le
#print axioms abs_current_le_coupled

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
