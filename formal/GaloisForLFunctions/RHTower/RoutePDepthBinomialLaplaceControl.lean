import GaloisForLFunctions.RHTower.RoutePPrimitiveDepthRadialGraphCollapse
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Positive-slope control of the primitive depth packet Laplace transform

The undamped binomial cutoff has nonnegative derivative. Integration by parts therefore
bounds its transform on every positive half-plane by a Cauchy factor times one real
Laplace budget. That budget tends to zero with the packet order. These are source-native
estimates for the literal depth packet, independent of any hypothesis on Xi zeros or primes.
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower
noncomputable section

def routePDepthCutoff (lam : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  t * (1 - Real.exp (-lam * t)) ^ N

def routePDepthCutoffSlope (lam : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (1 - Real.exp (-lam * t)) ^ N +
    t * N * (1 - Real.exp (-lam * t)) ^ (N - 1) * (lam * Real.exp (-lam * t))

def routePDepthLaplace (lam : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, Complex.exp (-(z * (t : ℂ))) * (routePDepthCutoff lam N t : ℂ)

def routePDepthRealBudget (lam : ℝ) (N : ℕ) (a : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, Real.exp (-a * t) * routePDepthCutoff lam N t

private theorem cutoff_base {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-lam * t) ∧ 1 - Real.exp (-lam * t) < 1 := by
  have h := Real.exp_le_one_iff.mpr (show -lam * t ≤ 0 by nlinarith)
  constructor
  · linarith
  · linarith [Real.exp_pos (-lam * t)]

theorem routePDepthCutoff_bounds {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) (N : ℕ) :
    0 ≤ routePDepthCutoff lam N t ∧ routePDepthCutoff lam N t ≤ t := by
  have h := cutoff_base hlam ht
  exact ⟨mul_nonneg ht (pow_nonneg h.1 N),
    mul_le_of_le_one_right ht (pow_le_one₀ h.1 h.2.le)⟩

theorem routePDepthCutoffSlope_bounds {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) (N : ℕ) :
    0 ≤ routePDepthCutoffSlope lam N t ∧
      routePDepthCutoffSlope lam N t ≤ 1 + (N : ℝ) * lam * t := by
  have h := cutoff_base hlam ht
  have hp : (1 - Real.exp (-lam * t)) ^ N ≤ 1 := pow_le_one₀ h.1 h.2.le
  have hm : (1 - Real.exp (-lam * t)) ^ (N - 1) ≤ 1 := pow_le_one₀ h.1 h.2.le
  have he : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  unfold routePDepthCutoffSlope
  constructor
  · positivity
  · have hh : t * N * (1 - Real.exp (-lam * t)) ^ (N - 1) *
        (lam * Real.exp (-lam * t)) ≤ t * N * 1 * (lam * 1) := by gcongr
    nlinarith

theorem hasDerivAt_routePDepthCutoff (lam : ℝ) (N : ℕ) (t : ℝ) :
    HasDerivAt (routePDepthCutoff lam N) (routePDepthCutoffSlope lam N t) t := by
  have he := ((hasDerivAt_id t).const_mul (-lam)).exp
  have hq := (hasDerivAt_const t (1 : ℝ)).sub he
  have hg := (hasDerivAt_id t).mul (hq.pow N)
  convert hg using 1 <;> first | rfl | (dsimp [routePDepthCutoff, routePDepthCutoffSlope]; ring)

private theorem norm_exp_mul_real (z : ℂ) (t v : ℝ) :
    ‖Complex.exp (-(z * (t : ℂ))) * (v : ℂ)‖ = Real.exp (-z.re * t) * |v| := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  simp [Complex.mul_re, neg_mul]

private theorem integrable_linear_exp {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * t) (Ioi 0) := by
  simpa only [Real.rpow_one, mul_comm] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := a)
      (by norm_num) le_rfl ha

theorem integrable_routePDepthLaplace {lam : ℝ} (hlam : 0 < lam) (N : ℕ)
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) *
      (routePDepthCutoff lam N t : ℂ)) (Ioi 0) := by
  apply (integrable_linear_exp hz).mono'
  · have hc : Continuous (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) *
        (routePDepthCutoff lam N t : ℂ)) := by unfold routePDepthCutoff; fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [norm_exp_mul_real, abs_of_nonneg (routePDepthCutoff_bounds hlam ht.le N).1]
    exact mul_le_mul_of_nonneg_left (routePDepthCutoff_bounds hlam ht.le N).2
      (Real.exp_pos _).le

theorem integrable_routePDepthSlopeLaplace {lam : ℝ} (hlam : 0 < lam) (N : ℕ)
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) *
      (routePDepthCutoffSlope lam N t : ℂ)) (Ioi 0) := by
  have h0 := integrableOn_exp_mul_Ioi (show -z.re < 0 by linarith) 0
  have h1 := (integrable_linear_exp hz).const_mul ((N : ℝ) * lam)
  have hi : IntegrableOn
      (fun t : ℝ => Real.exp (-z.re * t) * (1 + (N : ℝ) * lam * t)) (Ioi 0) := by
    have heq : (fun t : ℝ => Real.exp (-z.re * t) * (1 + (N : ℝ) * lam * t)) =
        (fun t : ℝ => Real.exp (-z.re * t) + (N : ℝ) * lam *
          (Real.exp (-z.re * t) * t)) := by funext t; ring
    rw [heq]
    exact h0.add h1
  apply hi.mono'
  · have hc : Continuous (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) *
        (routePDepthCutoffSlope lam N t : ℂ)) := by unfold routePDepthCutoffSlope; fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [norm_exp_mul_real, abs_of_nonneg (routePDepthCutoffSlope_bounds hlam ht.le N).1]
    exact mul_le_mul_of_nonneg_left (routePDepthCutoffSlope_bounds hlam ht.le N).2
      (Real.exp_pos _).le

private theorem laplace_boundary_zero {lam : ℝ} (hlam : 0 < lam) (N : ℕ)
    {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) *
      (routePDepthCutoff lam N t : ℂ)) atTop (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hlim : Tendsto (fun t : ℝ => Real.exp (-z.re * t) * t) atTop (nhds 0) := by
    simpa only [Real.rpow_one, mul_comm] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 z.re hz
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [norm_exp_mul_real, abs_of_nonneg (routePDepthCutoff_bounds hlam ht N).1]
  exact mul_le_mul_of_nonneg_left (routePDepthCutoff_bounds hlam ht N).2
    (Real.exp_pos _).le

theorem integral_routePDepthSlopeLaplace {lam : ℝ} (hlam : 0 < lam) (N : ℕ)
    {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-(z * (t : ℂ))) *
      (routePDepthCutoffSlope lam N t : ℂ)) = z * routePDepthLaplace lam N z := by
  let u : ℝ → ℂ := fun t => Complex.exp (-(z * (t : ℂ)))
  let u' : ℝ → ℂ := fun t => -z * Complex.exp (-(z * (t : ℂ)))
  let v : ℝ → ℂ := fun t => (routePDepthCutoff lam N t : ℂ)
  let v' : ℝ → ℂ := fun t => (routePDepthCutoffSlope lam N t : ℂ)
  have hu (t : ℝ) (_ht : t ∈ Ioi (0 : ℝ)) : HasDerivAt u (u' t) t := by
    have h := ((hasDerivAt_id t).ofReal_comp.const_mul (-z)).cexp
    simpa only [u, u', id_eq, Complex.ofReal_one, mul_one, neg_mul, mul_neg,
      mul_comm (Complex.exp (-(z * (t : ℂ)))) z] using h
  have hv (t : ℝ) (_ht : t ∈ Ioi (0 : ℝ)) : HasDerivAt v (v' t) t :=
    (hasDerivAt_routePDepthCutoff lam N t).ofReal_comp
  have hiv : IntegrableOn (u * v') (Ioi 0) := integrable_routePDepthSlopeLaplace hlam N hz
  have hiu : IntegrableOn (u' * v) (Ioi 0) := by
    refine ((integrable_routePDepthLaplace hlam N hz).const_mul (-z)).congr ?_
    filter_upwards with t
    dsimp [u', v]
    ring
  have hzero : Tendsto (u * v) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hc : Continuous (u * v) := by dsimp [u, v, routePDepthCutoff]; fun_prop
    simpa [u, v, routePDepthCutoff] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto (u * v) atTop (nhds 0) := laplace_boundary_zero hlam N hz
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hiv hiu hzero hinfty
  have hi : (∫ t : ℝ in Ioi 0, u' t * v t) = -z * routePDepthLaplace lam N z := by
    rw [routePDepthLaplace, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [u', v]
    ring
  rw [hi] at h
  simpa only [u, v', sub_zero, zero_sub, neg_mul, neg_neg] using h

private theorem real_integrand_cast (a t v : ℝ) :
    ((Real.exp (-a * t) * v : ℝ) : ℂ) =
      Complex.exp (-((a : ℂ) * (t : ℂ))) * (v : ℂ) := by
  push_cast
  rw [neg_mul]

theorem routePDepthLaplace_real (lam : ℝ) (N : ℕ) (a : ℝ) :
    routePDepthLaplace lam N (a : ℂ) = (routePDepthRealBudget lam N a : ℂ) := by
  unfold routePDepthLaplace routePDepthRealBudget
  simp_rw [← real_integrand_cast]
  exact integral_complex_ofReal

theorem integrable_routePDepthRealBudget {lam : ℝ} (hlam : 0 < lam) (N : ℕ)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * routePDepthCutoff lam N t) (Ioi 0) := by
  have h := integrable_routePDepthLaplace hlam N (z := (a : ℂ)) (by simpa using ha)
  simp_rw [← real_integrand_cast] at h
  exact h.re

private theorem integrable_real_slope {lam : ℝ} (hlam : 0 < lam) (N : ℕ)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * routePDepthCutoffSlope lam N t) (Ioi 0) := by
  have h := integrable_routePDepthSlopeLaplace hlam N (z := (a : ℂ)) (by simpa using ha)
  simp_rw [← real_integrand_cast] at h
  exact h.re

theorem routePDepthRealBudget_nonneg {lam : ℝ} (hlam : 0 < lam) (N : ℕ) (a : ℝ) :
    0 ≤ routePDepthRealBudget lam N a := by
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.exp_pos _).le (routePDepthCutoff_bounds hlam ht.le N).1

theorem tendsto_routePDepthRealBudget {lam : ℝ} (hlam : 0 < lam) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N => routePDepthRealBudget lam N a) atTop (nhds 0) := by
  have hm (N : ℕ) : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-a * t) * routePDepthCutoff lam N t)
      (volume.restrict (Ioi 0)) := by
    have hc : Continuous (fun t : ℝ => Real.exp (-a * t) * routePDepthCutoff lam N t) := by
      unfold routePDepthCutoff
      fun_prop
    exact hc.aestronglyMeasurable
  have hb (N : ℕ) : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖Real.exp (-a * t) * routePDepthCutoff lam N t‖ ≤ Real.exp (-a * t) * t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (routePDepthCutoff_bounds hlam ht.le N).1)]
    exact mul_le_mul_of_nonneg_left (routePDepthCutoff_bounds hlam ht.le N).2 (Real.exp_pos _).le
  have ht : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun N => Real.exp (-a * t) * routePDepthCutoff lam N t) atTop (nhds (0 : ℝ)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hq := cutoff_base hlam ht.le
    simpa only [routePDepthCutoff, mul_assoc, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq.1 hq.2).const_mul (Real.exp (-a * t) * t)
  have h := tendsto_integral_of_dominated_convergence
    (fun t : ℝ => Real.exp (-a * t) * t) hm (integrable_linear_exp ha) hb ht
  simpa only [integral_zero, routePDepthRealBudget] using h

private theorem integral_real_slope {lam : ℝ} (hlam : 0 < lam) (N : ℕ)
    {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, Real.exp (-a * t) * routePDepthCutoffSlope lam N t) =
      a * routePDepthRealBudget lam N a := by
  have h := integral_routePDepthSlopeLaplace hlam N (z := (a : ℂ)) (by simpa using ha)
  simp_rw [← real_integrand_cast] at h
  rw [integral_complex_ofReal, routePDepthLaplace_real] at h
  exact_mod_cast h

/-- Positivity of the undamped source slope supplies a Cauchy factor uniformly in packet order.
The factor multiplying it is the single real budget, which tends to zero. -/
theorem norm_routePDepthLaplace_le {lam a : ℝ} (hlam : 0 < lam) (ha : 0 < a)
    (N : ℕ) {z : ℂ} (haz : a ≤ z.re) :
    ‖routePDepthLaplace lam N z‖ ≤ a * routePDepthRealBudget lam N a / ‖z‖ := by
  have hz : 0 < z.re := ha.trans_le haz
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have h : ‖z‖ * ‖routePDepthLaplace lam N z‖ ≤ a * routePDepthRealBudget lam N a := by
    calc
      _ = ‖z * routePDepthLaplace lam N z‖ := (norm_mul _ _).symm
      _ = ‖∫ t : ℝ in Ioi 0, Complex.exp (-(z * (t : ℂ))) *
          (routePDepthCutoffSlope lam N t : ℂ)‖ := by
        rw [integral_routePDepthSlopeLaplace hlam N hz]
      _ ≤ ∫ t : ℝ in Ioi 0, ‖Complex.exp (-(z * (t : ℂ))) *
          (routePDepthCutoffSlope lam N t : ℂ)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ in Ioi 0, Real.exp (-a * t) * routePDepthCutoffSlope lam N t := by
        apply integral_mono_ae (integrable_routePDepthSlopeLaplace hlam N hz).norm
          (integrable_real_slope hlam N ha)
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have hg := (routePDepthCutoffSlope_bounds hlam ht.le N).1
        rw [norm_exp_mul_real, abs_of_nonneg hg]
        apply mul_le_mul_of_nonneg_right _ hg
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (neg_le_neg haz) ht.le
      _ = _ := integral_real_slope hlam N ha
  exact (le_div_iff₀ (norm_pos_iff.mpr hz0)).mpr (by simpa only [mul_comm] using h)

end
end RHTower
