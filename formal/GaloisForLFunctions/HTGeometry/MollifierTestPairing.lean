import GaloisForLFunctions.HTGeometry.CompactKernelL2Convolution
import GaloisForLFunctions.HTGeometry.CompactSupportIntegrationByParts

/-!
# Pairing a mollified profile against a test function

Three facts drive the identification step of a weak-limit argument.

* **Transposition.**  `∫ (g ⋆ V) φ = ∫ V(t) (∫ g(u) φ(t+u) du) dt`: the convolution moves off the
  square-integrable profile and onto the test function, by one Fubini exchange over a compactly
  supported region.
* **Integration by parts.**  `∫ g′(u) φ(t+u) du = −∫ g(u) φ′(t+u) du`: the derivative moves from
  the kernel onto the test function.
* **Uniform approximation.**  For a unit-mass kernel supported within `ε` of the origin, the
  transported test `∫ g(u) φ(t+u) du` differs from `φ(t)` by at most the modulus of `φ` at
  scale `ε`, uniformly in `t`.

Together: pairing the mollified weak derivative against a smooth compactly supported test
converges to pairing the distributional derivative, which is what identifies a weak `L²` limit.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The kernel-flip form of the line convolution. -/
theorem lineConvolution_flip (g V : ℝ → ℝ) (x : ℝ) :
    lineConvolution g V x = ∫ t, g (x - t) * V t := by
  rw [lineConvolution]
  have h := integral_sub_left_eq_self (fun τ => g τ * V (x - τ)) volume x
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show g (x - t) * V (x - (x - t)) = g (x - t) * V t
  rw [show x - (x - t) = t from by ring]

/-- **Transposition.**  The convolution pairing against a compactly supported continuous test
moves onto the test side. -/
theorem integral_lineConvolution_mul_test {g V φ : ℝ → ℝ}
    (hgc : Continuous g) (hgsupp : HasCompactSupport g)
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ 2))
    (hφc : Continuous φ) (hφsupp : HasCompactSupport φ) :
    (∫ x, lineConvolution g V x * φ x) = ∫ t, V t * ∫ u, g u * φ (t + u) := by
  have hVm : AEStronglyMeasurable V volume := hVmm.aestronglyMeasurable
  have hg2 : Integrable (fun u => g u ^ 2) :=
    (hgc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hgsupp)
  have hφint : Integrable φ := hφc.integrable_of_hasCompactSupport hφsupp
  set F : ℝ × ℝ → ℝ := fun p => g (p.1 - p.2) * V p.2 * φ p.1 with hF
  have hFm : AEStronglyMeasurable F ((volume : Measure ℝ).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    exact ((hgc.measurable.comp (measurable_fst.sub measurable_snd)).mul
      (hVmm.comp measurable_snd)).mul (hφc.measurable.comp measurable_fst)
  -- slicewise integrability and the mass bound
  have hslice : ∀ x : ℝ, Integrable (fun t => F (x, t)) := by
    intro x
    have hker : Integrable (fun t => g (x - t) * V t) :=
      integrable_mul_of_sq_integrable (aestronglyMeasurable_comp_sub hgc.aestronglyMeasurable x)
        hVm (integrable_sq_comp_sub hg2 x) hV2
    have := hker.mul_const (φ x)
    refine this.congr ?_
    filter_upwards with t
    rw [hF]
  have hCg : ∀ x : ℝ, (∫ t, |g (x - t) * V t|) ^ 2 ≤ (∫ u, g u ^ 2) * ∫ t, V t ^ 2 := by
    intro x
    have hgabsm : AEStronglyMeasurable (fun t => |g (x - t)|) volume :=
      ((hgc.comp (continuous_const.sub continuous_id)).abs).aestronglyMeasurable
    have hVabsm : AEStronglyMeasurable (fun t => |V t|) volume :=
      (continuous_abs.measurable.comp hVmm).aestronglyMeasurable
    have hgabs2 : Integrable (fun t => |g (x - t)| ^ 2) := by
      refine (integrable_sq_comp_sub hg2 x).congr ?_
      filter_upwards with t
      show g (x - t) ^ 2 = |g (x - t)| ^ 2
      rw [sq_abs]
    have hVabs2 : Integrable (fun t => |V t| ^ 2) := by
      refine hV2.congr ?_
      filter_upwards with t
      show V t ^ 2 = |V t| ^ 2
      rw [sq_abs]
    have habs := sq_integral_mul_le (μ := (volume : Measure ℝ)) hgabsm hVabsm hgabs2 hVabs2
    have heq1 : (∫ t, |g (x - t)| * |V t|) = ∫ t, |g (x - t) * V t| := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show |g (x - t)| * |V t| = |g (x - t) * V t|
      rw [abs_mul]
    have heq2 : (∫ t, |g (x - t)| ^ 2) = ∫ u, g u ^ 2 := by
      have h1 : (∫ t, |g (x - t)| ^ 2) = ∫ t, g (x - t) ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show |g (x - t)| ^ 2 = g (x - t) ^ 2
        rw [sq_abs]
      rw [h1, integral_sq_comp_sub]
    have heq3 : (∫ t, |V t| ^ 2) = ∫ t, V t ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show |V t| ^ 2 = V t ^ 2
      rw [sq_abs]
    rw [heq1, heq2, heq3] at habs
    exact habs
  have hCgnn : (0 : ℝ) ≤ (∫ u, g u ^ 2) * ∫ t, V t ^ 2 :=
    mul_nonneg (integral_nonneg fun u => sq_nonneg _) (integral_nonneg fun t => sq_nonneg _)
  set Cg : ℝ := Real.sqrt ((∫ u, g u ^ 2) * ∫ t, V t ^ 2) with hCgdef
  have hmass : ∀ x : ℝ, (∫ t, |g (x - t) * V t|) ≤ Cg := by
    intro x
    have hnn : (0 : ℝ) ≤ ∫ t, |g (x - t) * V t| := integral_nonneg fun t => abs_nonneg _
    rw [hCgdef, ← Real.sqrt_sq hnn]
    exact Real.sqrt_le_sqrt (hCg x)
  -- joint integrability
  have hFint : Integrable F ((volume : Measure ℝ).prod volume) := by
    rw [integrable_prod_iff hFm]
    constructor
    · filter_upwards with x
      exact hslice x
    · have hmaj : Integrable (fun x => |φ x| * Cg) := (hφint.abs.mul_const Cg)
      have haesm : AEStronglyMeasurable (fun x => ∫ t, ‖F (x, t)‖) volume :=
        hFm.norm.integral_prod_right'
      refine Integrable.mono' hmaj haesm ?_
      filter_upwards with x
      have h1 : (∫ t, ‖F (x, t)‖) = |φ x| * ∫ t, |g (x - t) * V t| := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show ‖g (x - t) * V t * φ x‖ = |φ x| * |g (x - t) * V t|
        rw [Real.norm_eq_abs, abs_mul]
        ring
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _), h1]
      exact mul_le_mul_of_nonneg_left (hmass x) (abs_nonneg _)
  -- the exchange
  have hswap := integral_integral_swap
    (f := fun x t => F (x, t)) (μ := (volume : Measure ℝ)) (ν := volume)
    (by
      refine hFint.congr ?_
      filter_upwards with p
      rfl)
  have hLHS : (∫ x, lineConvolution g V x * φ x) = ∫ x, ∫ t, F (x, t) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show lineConvolution g V x * φ x = ∫ t, F (x, t)
    rw [lineConvolution_flip, ← integral_mul_const]
  have hRHS : (∫ t, ∫ x, F (x, t)) = ∫ t, V t * ∫ u, g u * φ (t + u) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have hpull : (∫ x, F (x, t)) = V t * ∫ x, g (x - t) * φ x := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show g (x - t) * V t * φ x = V t * (g (x - t) * φ x)
      ring
    have hsub : (∫ x, g (x - t) * φ x) = ∫ u, g u * φ (t + u) := by
      have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun x => g (x - t) * φ x) t
      rw [← h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      show g (u + t - t) * φ (u + t) = g u * φ (t + u)
      rw [show u + t - t = u from by ring, show u + t = t + u from by ring]
    show (∫ x, F (x, t)) = V t * ∫ u, g u * φ (t + u)
    rw [hpull, hsub]
  rw [hLHS, hswap, hRHS]

/-- **Integration by parts.**  The derivative moves from the compactly supported kernel onto the
test function. -/
theorem integral_deriv_kernel_test {ρ φ : ℝ → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hρsupp : HasCompactSupport ρ)
    (hφ : ContDiff ℝ 1 φ) (t : ℝ) :
    (∫ u, deriv ρ u * φ (t + u)) = -∫ u, ρ u * deriv φ (t + u) := by
  have hρd : ∀ u, HasDerivAt ρ (deriv ρ u) u := fun u =>
    ((hρ.differentiable one_ne_zero) u).hasDerivAt
  have hφd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
    ((hφ.differentiable one_ne_zero) x).hasDerivAt
  have hρ'c : Continuous (deriv ρ) := hρ.continuous_deriv le_rfl
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  set h : ℝ → ℝ := fun u => ρ u * φ (t + u) with hh
  set h' : ℝ → ℝ := fun u => deriv ρ u * φ (t + u) + ρ u * deriv φ (t + u) with hh'
  have hd : ∀ u, HasDerivAt h (h' u) u := by
    intro u
    have hshift : HasDerivAt (fun u : ℝ => φ (t + u)) (deriv φ (t + u)) u := by
      have hb : HasDerivAt (fun u : ℝ => t + u) 1 u := by
        simpa using (hasDerivAt_id u).const_add t
      have hcomp : HasDerivAt (φ ∘ fun u : ℝ => t + u) (deriv φ (t + u) * 1) u :=
        HasDerivAt.comp u (hφd (t + u)) hb
      have hcomp' : HasDerivAt (fun u : ℝ => φ (t + u)) (deriv φ (t + u) * 1) u := hcomp
      simpa using hcomp'
    have := (hρd u).mul hshift
    refine this.congr_deriv ?_
    rw [hh']
  have hh'c : Continuous h' := by
    rw [hh']
    exact ((hρ'c.mul (hφ.continuous.comp (continuous_const.add continuous_id)))).add
      ((hρ.continuous.mul (hφ'c.comp (continuous_const.add continuous_id))))
  have hhc : HasCompactSupport h := by
    rw [hh]
    exact hρsupp.mul_right
  have hzero := integral_deriv_eq_zero_of_hasCompactSupport hd hh'c hhc
  have hint1 : Integrable (fun u => deriv ρ u * φ (t + u)) :=
    Continuous.integrable_of_hasCompactSupport
      (hρ'c.mul (hφ.continuous.comp (continuous_const.add continuous_id)))
      (hρsupp.deriv.mul_right)
  have hint2 : Integrable (fun u => ρ u * deriv φ (t + u)) :=
    Continuous.integrable_of_hasCompactSupport
      (hρ.continuous.mul (hφ'c.comp (continuous_const.add continuous_id)))
      (hρsupp.mul_right)
  have hsplit : (∫ u, h' u)
      = (∫ u, deriv ρ u * φ (t + u)) + ∫ u, ρ u * deriv φ (t + u) := by
    rw [hh']
    exact integral_add hint1 hint2
  rw [hsplit] at hzero
  linarith

/-- **Uniform approximation.**  Transporting a test function through a unit-mass kernel supported
within `ε` of the origin moves it by at most its modulus at scale `ε`, uniformly in the base
point. -/
theorem abs_kernelTest_sub_le {ρ φ : ℝ → ℝ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hρc : Continuous ρ) (hρsupp : ∀ u : ℝ, ε < |u| → ρ u = 0) (hρnn : ∀ u, 0 ≤ ρ u)
    (hρint : Integrable ρ) (hρmass : (∫ u, ρ u) = 1)
    (hφc : Continuous φ)
    (hmod : ∀ t u : ℝ, |u| ≤ ε → |φ (t + u) - φ t| ≤ M) (t : ℝ) :
    |(∫ u, ρ u * φ (t + u)) - φ t| ≤ M := by
  have hρcompact : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -ε) (b := ε)) fun u hu => ?_
    refine hρsupp u ?_
    rw [mem_Icc, not_and_or] at hu
    rcases hu with hu | hu
    · rw [not_le] at hu
      calc ε < -u := by linarith
        _ ≤ |u| := neg_le_abs u
    · rw [not_le] at hu
      calc ε < u := hu
        _ ≤ |u| := le_abs_self u
  have hint : Integrable (fun u => ρ u * φ (t + u)) :=
    (hρc.mul (hφc.comp (continuous_const.add continuous_id))).integrable_of_hasCompactSupport
      hρcompact.mul_right
  have hconst : Integrable (fun u => ρ u * φ t) := hρint.mul_const (φ t)
  have hdiff : (∫ u, ρ u * φ (t + u)) - φ t = ∫ u, ρ u * (φ (t + u) - φ t) := by
    have hsub : (∫ u, ρ u * (φ (t + u) - φ t))
        = (∫ u, ρ u * φ (t + u)) - ∫ u, ρ u * φ t := by
      rw [← integral_sub hint hconst]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      ring
    rw [hsub, integral_mul_const, hρmass, one_mul]
  rw [hdiff]
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hmod t 0 (by simpa using hε))
  have hbound : ∀ u : ℝ, ‖ρ u * (φ (t + u) - φ t)‖ ≤ ρ u * M := by
    intro u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnn u)]
    rcases le_or_gt |u| ε with hu | hu
    · exact mul_le_mul_of_nonneg_left (hmod t u hu) (hρnn u)
    · rw [hρsupp u hu]
      simp
  calc |∫ u, ρ u * (φ (t + u) - φ t)|
      ≤ ∫ u, ‖ρ u * (φ (t + u) - φ t)‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ u, ρ u * M := by
        refine integral_mono ?_ (hρint.mul_const M) hbound
        refine (hint.sub hconst).norm.congr ?_
        filter_upwards with u
        show ‖ρ u * φ (t + u) - ρ u * φ t‖ = ‖ρ u * (φ (t + u) - φ t)‖
        congr 1
        ring
    _ = M := by rw [integral_mul_const, hρmass, one_mul]

/-- A continuous compactly supported function attains a bound. -/
theorem exists_abs_le_of_hasCompactSupport {f : ℝ → ℝ}
    (hfc : Continuous f) (hfsupp : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨x₀, hx₀⟩ := hfc.norm.exists_forall_ge_of_hasCompactSupport hfsupp.norm
  exact ⟨‖f x₀‖, norm_nonneg _, fun x => by
    have := hx₀ x
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this⟩

/-- A `C¹` function with compactly supported derivative moves by at most `M |u|` under
translation, where `M` bounds the derivative. -/
theorem abs_translate_sub_le_of_deriv_bound {φ : ℝ → ℝ} {M : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hM : ∀ x, |deriv φ x| ≤ M) (t u : ℝ) :
    |φ (t + u) - φ t| ≤ M * |u| := by
  have hderiv : ∀ z ∈ (univ : Set ℝ),
      HasDerivWithinAt φ (deriv φ z) univ z := fun z _ =>
    ((hφ.differentiable one_ne_zero) z).hasDerivAt.hasDerivWithinAt
  have hbound : ∀ z ∈ (univ : Set ℝ), ‖deriv φ z‖ ≤ M := fun z _ => by
    rw [Real.norm_eq_abs]
    exact hM z
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound convex_univ
    (mem_univ t) (mem_univ (t + u))
  calc |φ (t + u) - φ t| = ‖φ (t + u) - φ t‖ := (Real.norm_eq_abs _).symm
    _ ≤ M * ‖t + u - t‖ := this
    _ = M * |u| := by
        rw [show t + u - t = u from by ring, Real.norm_eq_abs]

end GaloisForLFunctions.HTGeometry
