import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic

/-!
# A Cauchy estimate retaining evenness

Subtracting derivative formulas at opposite points preserves the vanishing
aperture factor. The resulting bound is uniform on the inner half-radius disk.
-/

open Complex Set Metric Filter
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar

/-- An even entire function retains its vanishing derivative in the Cauchy estimate. -/
theorem norm_deriv_even_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (heven : ∀ z, f (-z) = f z) {B : ℝ}
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
      exact hd.congr_of_eventuallyEq (Eventually.of_forall fun z => (heven z).symm)
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
      field_simp [hza, hzna, hD0]
      ring
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

#print axioms norm_deriv_even_le

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
