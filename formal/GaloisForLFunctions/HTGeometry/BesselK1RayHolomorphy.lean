import GaloisForLFunctions.HTGeometry.BesselK1RayRepresentation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The ray representation is holomorphic in the spectral parameter

On the open right half plane the base `1 + u/(2z)` of the ray integrand has real part at least one,
so the integrand is bounded by a Gamma integrand and its derivative in `z` by another; differentiating
under the integral sign therefore makes the ray integral holomorphic there.
-/

open MeasureTheory Set Complex Filter Metric

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section RayGeometry

theorem re_ray_frac_nonneg {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ ((u : ℂ) / (2 * z)).re := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hns : (0 : ℝ) < Complex.normSq (2 * z) := by
    rw [Complex.normSq_pos]
    exact mul_ne_zero two_ne_zero hzne
  rw [Complex.div_re]
  have hre : ((2 : ℂ) * z).re = 2 * z.re := by simp
  rw [Complex.ofReal_re, Complex.ofReal_im, hre, zero_mul, zero_div, add_zero]
  exact div_nonneg (by nlinarith) hns.le

theorem one_le_re_ray_base {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ (1 + (u : ℂ) / (2 * z)).re := by
  have h := re_ray_frac_nonneg hz hu
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem one_le_norm_ray_base {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ ‖1 + (u : ℂ) / (2 * z)‖ :=
  le_trans (one_le_re_ray_base hz hu) (Complex.re_le_norm _)

theorem ray_base_mem_slitPlane {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) :
    1 + (u : ℂ) / (2 * z) ∈ slitPlane :=
  Or.inl (lt_of_lt_of_le zero_lt_one (one_le_re_ray_base hz hu))

theorem norm_ray_base_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖1 + (u : ℂ) / (2 * z)‖ ≤ 1 + u / (2 * ‖z‖) := by
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_one, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  simp

theorem norm_rayShellPow_le_one {z : ℂ} (hz : 0 < z.re) {u α : ℝ} (hu : 0 ≤ u) (hα : α ≤ 0) :
    ‖rayShellPow z u α‖ ≤ 1 := by
  rw [rayShellPow, Complex.norm_cpow_real]
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_norm_ray_base hz hu) hα

theorem norm_rayShellPow_half_le {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) :
    ‖rayShellPow z u (1 / 2)‖ ≤ 1 + u / (2 * ‖z‖) := by
  rw [rayShellPow, Complex.norm_cpow_real]
  have h1 := one_le_norm_ray_base hz hu
  calc ‖1 + (u : ℂ) / (2 * z)‖ ^ ((1 : ℝ) / 2)
      ≤ ‖1 + (u : ℂ) / (2 * z)‖ ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ = ‖1 + (u : ℂ) / (2 * z)‖ := Real.rpow_one _
    _ ≤ 1 + u / (2 * ‖z‖) := norm_ray_base_le z hu

theorem norm_besselK1RayIntegrand_le {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) :
    ‖besselK1RayIntegrand z u‖
      ≤ Real.exp (-u) / Real.sqrt u * (3 + u / ‖z‖) := by
  have hA := norm_rayShellPow_half_le hz hu
  have hB := norm_rayShellPow_le_one (z := z) (u := u) (α := -1 / 2) hz hu (by norm_num)
  have hcoef : ‖((Real.exp (-u) / Real.sqrt u : ℝ) : ℂ)‖ = Real.exp (-u) / Real.sqrt u := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [besselK1RayIntegrand, norm_mul, hcoef]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hstep : 2 * ‖rayShellPow z u (1 / 2)‖ ≤ 2 * (1 + u / (2 * ‖z‖)) := by linarith
  have hkey : 2 * (1 + u / (2 * ‖z‖)) + 1 = 3 + u / ‖z‖ := by
    rcases eq_or_ne ‖z‖ 0 with h | h
    · rw [h]
      norm_num
    · field_simp
      ring
  linarith [hstep, hB, hkey]

end RayGeometry

section Integrability

theorem integrableOn_rayBound (z : ℂ) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) / Real.sqrt u * (3 + u / ‖z‖)) (Ioi 0) := by
  have h1 := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 3 / 2)
  have hsum : IntegrableOn (fun u : ℝ =>
      3 * (Real.exp (-u) * u ^ ((1 : ℝ) / 2 - 1))
        + ‖z‖⁻¹ * (Real.exp (-u) * u ^ ((3 : ℝ) / 2 - 1))) (Ioi 0) :=
    (h1.const_mul 3).add (h2.const_mul ‖z‖⁻¹)
  refine hsum.congr_fun ?_ measurableSet_Ioi
  intro u hu
  have hu0 : (0 : ℝ) < u := hu
  have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  have e1 : u ^ ((1 : ℝ) / 2 - 1) = (Real.sqrt u)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hu0.le]
    congr 1
    norm_num
  have e2 : u ^ ((3 : ℝ) / 2 - 1) = Real.sqrt u := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hd : u * (Real.sqrt u)⁻¹ = Real.sqrt u := by
    field_simp
    exact (Real.sq_sqrt hu0.le).symm
  dsimp only
  rw [e1, e2, div_eq_mul_inv (Real.exp (-u)), div_eq_mul_inv u]
  calc 3 * (Real.exp (-u) * (Real.sqrt u)⁻¹) + ‖z‖⁻¹ * (Real.exp (-u) * Real.sqrt u)
      = 3 * (Real.exp (-u) * (Real.sqrt u)⁻¹)
        + ‖z‖⁻¹ * (Real.exp (-u) * (u * (Real.sqrt u)⁻¹)) := by rw [hd]
    _ = Real.exp (-u) * (Real.sqrt u)⁻¹ * (3 + u * ‖z‖⁻¹) := by ring

theorem continuousOn_besselK1RayIntegrand {z : ℂ} (hz : 0 < z.re) :
    ContinuousOn (besselK1RayIntegrand z) (Ioi 0) := by
  intro u hu
  have hu0 : (0 : ℝ) < u := hu
  have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  refine ContinuousAt.continuousWithinAt ?_
  have hcoef : ContinuousAt (fun t : ℝ => ((Real.exp (-t) / Real.sqrt t : ℝ) : ℂ)) u := by
    have : ContinuousAt (fun t : ℝ => Real.exp (-t) / Real.sqrt t) u := by
      exact (Real.continuous_exp.comp continuous_neg).continuousAt.div
        (Real.continuous_sqrt.continuousAt) (ne_of_gt hsu)
    exact Complex.continuous_ofReal.continuousAt.comp this
  have hbase : ContinuousAt (fun t : ℝ => 1 + (t : ℂ) / (2 * z)) u := by fun_prop
  have hpow : ∀ α : ℝ, ContinuousAt (fun t : ℝ => rayShellPow z t α) u := by
    intro α
    have hc : ContinuousAt (fun w : ℂ => w ^ ((α : ℝ) : ℂ)) (1 + (u : ℂ) / (2 * z)) :=
      continuousAt_cpow_const (ray_base_mem_slitPlane hz hu0.le)
    have hcomp : ContinuousAt ((fun w : ℂ => w ^ ((α : ℝ) : ℂ))
        ∘ (fun t : ℝ => 1 + (t : ℂ) / (2 * z))) u :=
      ContinuousAt.comp (g := fun w : ℂ => w ^ ((α : ℝ) : ℂ))
        (f := fun t : ℝ => 1 + (t : ℂ) / (2 * z)) hc hbase
    exact hcomp
  exact hcoef.mul ((continuousAt_const.mul (hpow (1 / 2))).sub (hpow (-1 / 2)))

theorem integrableOn_besselK1RayIntegrand {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (besselK1RayIntegrand z) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_rayBound z)
    ((continuousOn_besselK1RayIntegrand hz).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_besselK1RayIntegrand_le hz (le_of_lt hu)

end Integrability

section Derivative

/-- The derivative in the spectral parameter of a shell power on the ray. -/
def rayShellPowDeriv (z : ℂ) (u α : ℝ) : ℂ :=
  ((α : ℝ) : ℂ) * (1 + (u : ℂ) / (2 * z)) ^ (((α : ℝ) : ℂ) - 1)
    * (-((u : ℂ) * 2 / (2 * z) ^ 2))

theorem ne_zero_of_re_pos' {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro h
  rw [h] at hz
  simp at hz

theorem hasDerivAt_rayBase {z : ℂ} (hz : z ≠ 0) (u : ℝ) :
    HasDerivAt (fun w : ℂ => 1 + (u : ℂ) / (2 * w)) (-((u : ℂ) * 2 / (2 * z) ^ 2)) z := by
  have hd : HasDerivAt (fun w : ℂ => 2 * w) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have hne : (2 : ℂ) * z ≠ 0 := mul_ne_zero two_ne_zero hz
  have hdiv := (hasDerivAt_const z ((u : ℂ))).div hd hne
  have hval : ((0 : ℂ) * (2 * z) - (u : ℂ) * 2) / (2 * z) ^ 2
      = -((u : ℂ) * 2 / (2 * z) ^ 2) := by ring
  rw [hval] at hdiv
  simpa using hdiv.const_add (1 : ℂ)

theorem hasDerivAt_rayShellPow {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) (α : ℝ) :
    HasDerivAt (fun w : ℂ => rayShellPow w u α) (rayShellPowDeriv z u α) z :=
  (hasDerivAt_rayBase (ne_zero_of_re_pos' hz) u).cpow_const (ray_base_mem_slitPlane hz hu)

theorem norm_rayShellPowDeriv_le {z : ℂ} (hz : 0 < z.re) {u α : ℝ} (hu : 0 ≤ u) (hα : α ≤ 1) :
    ‖rayShellPowDeriv z u α‖ ≤ |α| * u / (2 * ‖z‖ ^ 2) := by
  have hexp : ((α : ℝ) : ℂ) - 1 = (((α - 1 : ℝ)) : ℂ) := by push_cast; ring
  have hbase : ‖(1 + (u : ℂ) / (2 * z)) ^ (((α - 1 : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_cpow_real]
    exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_norm_ray_base hz hu) (by linarith)
  have hlast : ‖(-((u : ℂ) * 2 / (2 * z) ^ 2))‖ = u / (2 * ‖z‖ ^ 2) := by
    rw [norm_neg, norm_div, norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    rcases eq_or_ne ‖z‖ 0 with h | h
    · rw [h]
      simp
    · field_simp
  rw [rayShellPowDeriv, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hexp, hlast]
  have hn : (0 : ℝ) ≤ u / (2 * ‖z‖ ^ 2) := by positivity
  have habs : (0 : ℝ) ≤ |α| := abs_nonneg α
  calc |α| * ‖(1 + (u : ℂ) / (2 * z)) ^ (((α - 1 : ℝ)) : ℂ)‖ * (u / (2 * ‖z‖ ^ 2))
      ≤ |α| * 1 * (u / (2 * ‖z‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase habs) hn
    _ = |α| * u / (2 * ‖z‖ ^ 2) := by ring

/-- The derivative in the spectral parameter of the ray integrand. -/
def besselK1RayIntegrandDeriv (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (-u) / Real.sqrt u : ℝ) : ℂ)
    * (2 * rayShellPowDeriv z u (1 / 2) - rayShellPowDeriv z u (-1 / 2))

theorem hasDerivAt_besselK1RayIntegrand {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun w : ℂ => besselK1RayIntegrand w u) (besselK1RayIntegrandDeriv z u) z := by
  have hA := hasDerivAt_rayShellPow hz hu (1 / 2)
  have hB := hasDerivAt_rayShellPow hz hu (-1 / 2)
  have hsub := (hA.const_mul (2 : ℂ)).sub hB
  exact hsub.const_mul (((Real.exp (-u) / Real.sqrt u : ℝ) : ℂ))

theorem norm_besselK1RayIntegrandDeriv_le {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) :
    ‖besselK1RayIntegrandDeriv z u‖
      ≤ Real.exp (-u) / Real.sqrt u * (3 * u / (4 * ‖z‖ ^ 2)) := by
  have hA := norm_rayShellPowDeriv_le (z := z) (u := u) (α := 1 / 2) hz hu (by norm_num)
  have hB := norm_rayShellPowDeriv_le (z := z) (u := u) (α := -1 / 2) hz hu (by norm_num)
  have hcoef : ‖((Real.exp (-u) / Real.sqrt u : ℝ) : ℂ)‖ = Real.exp (-u) / Real.sqrt u := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [besselK1RayIntegrandDeriv, norm_mul, hcoef]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
  have habs1 : |(1 : ℝ) / 2| = 1 / 2 := by norm_num
  have habs2 : |(-1 : ℝ) / 2| = 1 / 2 := by norm_num
  rw [habs1] at hA
  rw [habs2] at hB
  have hkey : 2 * (1 / 2 * u / (2 * ‖z‖ ^ 2)) + 1 / 2 * u / (2 * ‖z‖ ^ 2)
      = 3 * u / (4 * ‖z‖ ^ 2) := by
    rcases eq_or_ne ‖z‖ 0 with h | h
    · rw [h]
      simp
    · field_simp
      ring
  linarith [hA, hB, hkey]

end Derivative

section Holomorphy

theorem integrableOn_expSqrt : IntegrableOn (fun u : ℝ => Real.exp (-u) * Real.sqrt u) (Ioi 0) := by
  have h2 := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 3 / 2)
  refine h2.congr_fun ?_ measurableSet_Ioi
  intro u _
  dsimp only
  rw [show ((3 : ℝ) / 2 - 1) = (1 : ℝ) / 2 by norm_num, ← Real.sqrt_eq_rpow]

theorem integrableOn_rayDerivBound (R : ℝ) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) / Real.sqrt u * (3 * u / (4 * R ^ 2))) (Ioi 0) := by
  have h : IntegrableOn
      (fun u : ℝ => 3 / (4 * R ^ 2) * (Real.exp (-u) * Real.sqrt u)) (Ioi 0) :=
    integrableOn_expSqrt.const_mul _
  refine h.congr_fun ?_ measurableSet_Ioi
  intro u hu
  have hu0 : (0 : ℝ) < u := hu
  have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hd : Real.sqrt u = u / Real.sqrt u := by
    rw [eq_div_iff (ne_of_gt hsu)]
    exact Real.mul_self_sqrt hu0.le
  calc 3 / (4 * R ^ 2) * (Real.exp (-u) * Real.sqrt u)
      = 3 / (4 * R ^ 2) * (Real.exp (-u) * (u / Real.sqrt u)) := by rw [← hd]
    _ = Real.exp (-u) / Real.sqrt u * (3 * u / (4 * R ^ 2)) := by ring

theorem hasDerivAt_besselK1Ray {z₀ : ℂ} (hz : 0 < z₀.re) :
    HasDerivAt besselK1Ray (∫ u in Ioi (0 : ℝ), besselK1RayIntegrandDeriv z₀ u) z₀ := by
  have hR : (0 : ℝ) < z₀.re / 2 := by linarith
  have hball : ∀ z ∈ ball z₀ (z₀.re / 2), z₀.re / 2 < z.re ∧ z₀.re / 2 < ‖z‖ := by
    intro z hz'
    have h1 : ‖z - z₀‖ < z₀.re / 2 := by rwa [mem_ball, dist_eq_norm] at hz'
    have h2 : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
    have h3 : (z - z₀).re = z.re - z₀.re := by simp
    rw [h3] at h2
    have h4 := abs_lt.mp (lt_of_le_of_lt h2 h1)
    have h5 : z₀.re / 2 < z.re := by linarith [h4.1]
    exact ⟨h5, lt_of_lt_of_le h5 (Complex.re_le_norm z)⟩
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w : ℂ => fun u : ℝ => besselK1RayIntegrand w u)
    (F' := fun w : ℂ => fun u : ℝ => besselK1RayIntegrandDeriv w u)
    (bound := fun u : ℝ => Real.exp (-u) / Real.sqrt u * (3 * u / (4 * (z₀.re / 2) ^ 2)))
    (μ := volume.restrict (Ioi (0 : ℝ))) (x₀ := z₀)
    (ball_mem_nhds z₀ hR)
    (Filter.eventually_of_mem (ball_mem_nhds z₀ hR) fun w hw =>
      (continuousOn_besselK1RayIntegrand (lt_trans hR (hball w hw).1)).aestronglyMeasurable
        measurableSet_Ioi)
    (integrableOn_besselK1RayIntegrand hz)
    (by
      have hcont : ContinuousOn (besselK1RayIntegrandDeriv z₀) (Ioi 0) := by
        intro u hu
        have hu0 : (0 : ℝ) < u := hu
        refine ContinuousAt.continuousWithinAt ?_
        have hcoef : ContinuousAt (fun t : ℝ => ((Real.exp (-t) / Real.sqrt t : ℝ) : ℂ)) u := by
          have hs : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
          have : ContinuousAt (fun t : ℝ => Real.exp (-t) / Real.sqrt t) u :=
            (Real.continuous_exp.comp continuous_neg).continuousAt.div
              Real.continuous_sqrt.continuousAt (ne_of_gt hs)
          exact Complex.continuous_ofReal.continuousAt.comp this
        have hbase : ContinuousAt (fun t : ℝ => 1 + (t : ℂ) / (2 * z₀)) u := by fun_prop
        have hpow : ∀ α : ℝ, ContinuousAt (fun t : ℝ => rayShellPowDeriv z₀ t α) u := by
          intro α
          have hc : ContinuousAt (fun w : ℂ => w ^ (((α : ℝ) : ℂ) - 1))
              (1 + (u : ℂ) / (2 * z₀)) :=
            continuousAt_cpow_const (ray_base_mem_slitPlane hz hu0.le)
          have hcomp : ContinuousAt ((fun w : ℂ => w ^ (((α : ℝ) : ℂ) - 1))
              ∘ (fun t : ℝ => 1 + (t : ℂ) / (2 * z₀))) u :=
            ContinuousAt.comp (g := fun w : ℂ => w ^ (((α : ℝ) : ℂ) - 1))
              (f := fun t : ℝ => 1 + (t : ℂ) / (2 * z₀)) hc hbase
          have hlast : ContinuousAt
              (fun t : ℝ => -((t : ℂ) * 2 / (2 * z₀) ^ 2)) u := by fun_prop
          exact (continuousAt_const.mul hcomp).mul hlast
        exact hcoef.mul ((continuousAt_const.mul (hpow (1 / 2))).sub (hpow (-1 / 2)))
      exact hcont.aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro w hw
      have hu0 : (0 : ℝ) < u := hu
      obtain ⟨hwre, hwn⟩ := hball w hw
      have hwre0 : 0 < w.re := lt_trans hR hwre
      refine le_trans (norm_besselK1RayIntegrandDeriv_le hwre0 hu0.le) ?_
      have hpos : (0 : ℝ) ≤ Real.exp (-u) / Real.sqrt u := by positivity
      refine mul_le_mul_of_nonneg_left ?_ hpos
      have hsq : (z₀.re / 2) ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [hwn, hR]
      have hR2 : (0 : ℝ) < (z₀.re / 2) ^ 2 := by positivity
      gcongr)
    (integrableOn_rayDerivBound (z₀.re / 2))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro w hw
      have hu0 : (0 : ℝ) < u := hu
      have hwre0 : 0 < w.re := lt_trans hR (hball w hw).1
      exact hasDerivAt_besselK1RayIntegrand hwre0 hu0.le)
  exact hmain.2

end Holomorphy

section Continuation

/-- The model the ray integral matches: the Schläfli integral with its deep-time factors removed. -/
def besselK1RayModel (z : ℂ) : ℂ :=
  Complex.exp z * (2 * z) ^ (((1 : ℝ) / 2 : ℝ) : ℂ) * _root_.HTGeometry.besselK1C z

theorem two_mul_mem_slitPlane {z : ℂ} (hz : 0 < z.re) : (2 : ℂ) * z ∈ slitPlane := by
  refine Or.inl ?_
  have h : ((2 : ℂ) * z).re = 2 * z.re := by simp
  rw [h]
  linarith

theorem differentiableAt_besselK1RayModel {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ besselK1RayModel z := by
  have hexp : DifferentiableAt ℂ Complex.exp z := Complex.differentiable_exp z
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (2 * w) ^ (((1 : ℝ) / 2 : ℝ) : ℂ)) z :=
    (hlin.cpow_const (two_mul_mem_slitPlane hz)).differentiableAt
  have hK : DifferentiableAt ℂ _root_.HTGeometry.besselK1C z :=
    (_root_.HTGeometry.hasDerivAt_besselK1C hz).differentiableAt
  exact (hexp.mul hpow).mul hK

theorem besselK1Ray_ofReal_eq_model {b : ℝ} (hb : 0 < b) :
    besselK1Ray (b : ℂ) = besselK1RayModel (b : ℂ) := by
  have h2b : (0 : ℝ) ≤ 2 * b := by linarith
  have hs2b : (0 : ℝ) < Real.sqrt (2 * b) := Real.sqrt_pos.2 (by linarith)
  have hcpow : ((2 : ℂ) * (b : ℂ)) ^ (((1 : ℝ) / 2 : ℝ) : ℂ)
      = ((Real.sqrt (2 * b) : ℝ) : ℂ) := by
    have hcast : ((2 : ℂ) * (b : ℂ)) = (((2 * b : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_cpow h2b, Real.sqrt_eq_rpow]
  have hrep := besselK1C_ofReal_eq_ray hb
  have hne : ((Real.sqrt (2 * b) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs2b
  have hexp1 : Complex.exp ((b : ℂ)) * Complex.exp (-(b : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [besselK1RayModel, hcpow, hrep]
  calc besselK1Ray (b : ℂ)
      = Complex.exp ((b : ℂ)) * Complex.exp (-(b : ℂ))
          * (((Real.sqrt (2 * b) : ℝ) : ℂ) * ((Real.sqrt (2 * b) : ℝ) : ℂ)⁻¹)
          * besselK1Ray (b : ℂ) := by
        rw [hexp1, mul_inv_cancel₀ hne]
        ring
    _ = Complex.exp ((b : ℂ)) * ((Real.sqrt (2 * b) : ℝ) : ℂ)
          * (Complex.exp (-(b : ℂ)) * ((Real.sqrt (2 * b) : ℝ) : ℂ)⁻¹
            * besselK1Ray (b : ℂ)) := by ring

/-- **The ray representation on the whole right half plane.** -/
theorem besselK1Ray_eq_model {z : ℂ} (hz : 0 < z.re) :
    besselK1Ray z = besselK1RayModel z := by
  have hUopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected {w : ℂ | 0 < w.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hd1 : DifferentiableOn ℂ besselK1Ray {w : ℂ | 0 < w.re} :=
    fun w hw => (hasDerivAt_besselK1Ray hw).differentiableAt.differentiableWithinAt
  have hd2 : DifferentiableOn ℂ besselK1RayModel {w : ℂ | 0 < w.re} :=
    fun w hw => (differentiableAt_besselK1RayModel hw).differentiableWithinAt
  have h1 : AnalyticOnNhd ℂ besselK1Ray {w : ℂ | 0 < w.re} := hd1.analyticOnNhd hUopen
  have h2 : AnalyticOnNhd ℂ besselK1RayModel {w : ℂ | 0 < w.re} := hd2.analyticOnNhd hUopen
  have hone : (1 : ℂ) ∈ {w : ℂ | 0 < w.re} := by
    simp
  have hmap : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 1 {(1 : ℝ)}ᶜ)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      exact ht (by exact_mod_cast h)
  have hev : ∀ᶠ t : ℝ in nhdsWithin 1 {(1 : ℝ)}ᶜ,
      besselK1Ray ((t : ℝ) : ℂ) = besselK1RayModel ((t : ℝ) : ℂ) := by
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht
    exact besselK1Ray_ofReal_eq_model ht
  exact h1.eqOn_of_preconnected_of_frequently_eq h2 hUconn hone (hmap.frequently hev.frequently) hz

/-- **The order-one Schläfli integral in ray form**, on the whole right half plane. -/
theorem besselK1C_eq_ray {z : ℂ} (hz : 0 < z.re) :
    _root_.HTGeometry.besselK1C z
      = Complex.exp (-z) * (((2 * z) ^ (((1 : ℝ) / 2 : ℝ) : ℂ))⁻¹ * besselK1Ray z) := by
  have hne : ((2 : ℂ) * z) ^ (((1 : ℝ) / 2 : ℝ) : ℂ) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr ?_
    left
    intro h
    have : ((2 : ℂ) * z).re = 0 := by rw [h]; simp
    have h2 : ((2 : ℂ) * z).re = 2 * z.re := by simp
    rw [h2] at this
    linarith
  have hexp1 : Complex.exp (-z) * Complex.exp z = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [besselK1Ray_eq_model hz, besselK1RayModel]
  calc _root_.HTGeometry.besselK1C z
      = Complex.exp (-z) * Complex.exp z
          * ((((2 : ℂ) * z) ^ (((1 : ℝ) / 2 : ℝ) : ℂ))⁻¹
            * (((2 : ℂ) * z) ^ (((1 : ℝ) / 2 : ℝ) : ℂ)))
          * _root_.HTGeometry.besselK1C z := by
        rw [hexp1, inv_mul_cancel₀ hne]
        ring
    _ = Complex.exp (-z) * ((((2 : ℂ) * z) ^ (((1 : ℝ) / 2 : ℝ) : ℂ))⁻¹
          * (Complex.exp z * (((2 : ℂ) * z) ^ (((1 : ℝ) / 2 : ℝ) : ℂ))
            * _root_.HTGeometry.besselK1C z)) := by ring

end Continuation

end

end GaloisForLFunctions.HTGeometry
