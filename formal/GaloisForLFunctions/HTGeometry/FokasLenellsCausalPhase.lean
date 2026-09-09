import GaloisForLFunctions.HTGeometry.HalfPlaneHardyCauchyTotality
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity
import GaloisForLFunctions.HTGeometry.FokasLenellsSingularPhase

/-!
# Causal Hardy preservation for the singular Fokas–Lenells phase

The nonnegative-time phase exp(-i t/(2z)) is the almost-everywhere boundary
limit of contractive multipliers analytic through the real axis. Their actual
L² multiplication operators converge strongly. Closedness then transfers
upper Hardy preservation to the singular phase, without a boundary-regularity
hypothesis on the input.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The actual nonnegative-time analytic phase, with total field division at zero. -/
def causalAnalyticPhase (t : ℝ≥0) (z : ℂ) : ℂ :=
  Complex.exp (-(((t:ℝ)/2:ℝ):ℂ) * (I / z))

private theorem analytic_phase_norm (t : ℝ≥0) (z : ℂ) :
    ‖causalAnalyticPhase t z‖ = Real.exp (-((t:ℝ)/2) * (z.im / Complex.normSq z)) := by
  rw [causalAnalyticPhase,Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.div_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,
    zero_div,zero_add,neg_zero,sub_zero]

/-- Exact analytic attenuation at every point strictly above the real axis. -/
theorem norm_causalAnalyticPhase (t : ℝ≥0) (z : {z : ℂ // 0 < z.im}) :
    ‖causalAnalyticPhase t z.val‖ =
      Real.exp (-((t:ℝ)/2) * (z.val.im / Complex.normSq z.val)) :=
  analytic_phase_norm t z.val

private theorem analytic_phase_bound (t : ℝ≥0) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖causalAnalyticPhase t z‖ ≤ 1 := by
  rw [analytic_phase_norm,Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg t.property (by norm_num)))
    (div_nonneg hz (Complex.normSq_nonneg z))

/-- The analytic phase has exactly the existing real-line scattering phase as its boundary value. -/
theorem causalAnalyticPhase_real (t : ℝ≥0) (x : ℝ) : causalAnalyticPhase t (x:ℂ) = phase t x := by
  by_cases hx : x = 0
  · simp [hx,causalAnalyticPhase,phase]
  · have hxc : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    unfold causalAnalyticPhase phase
    rw [Complex.ofReal_div,Complex.ofReal_div,Complex.ofReal_mul]
    congr 1
    push_cast
    field_simp

private theorem shifted_ne_zero (a : ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    z + (Real.exp a:ℂ)*I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,Complex.zero_im] at hi
  linarith [Real.exp_pos a]

/-- A contractive analytic regularization whose singularity lies strictly below the real axis. -/
def regularizedCausalPhase (t : ℝ≥0) (a : ℝ) : ClosedUpperHalfPlaneMultiplier where
  fn z := causalAnalyticPhase t (z + (Real.exp a:ℂ)*I)
  bound := 1
  bound_nonneg := by norm_num
  diff z hz := by
    apply Complex.differentiableAt_exp.comp z
    exact (differentiableAt_const _).mul
      ((differentiableAt_const _).div (differentiableAt_id.add_const _) (shifted_ne_zero a hz))
  norm_le z hz := by
    apply analytic_phase_bound t
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero]
    exact add_nonneg hz (Real.exp_pos a).le

private theorem regularized_boundary_tendsto (t : ℝ≥0) {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun a => (regularizedCausalPhase t a).boundary x) atBot (𝓝 (phase t x)) := by
  have hxc : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hd : Tendsto (fun a : ℝ => (x:ℂ)+(Real.exp a:ℂ)*I) atBot (𝓝 (x:ℂ)) := by
    have he := Complex.continuous_ofReal.continuousAt.tendsto.comp Real.tendsto_exp_atBot
    simpa only [Function.comp_apply,Complex.ofReal_zero,zero_mul,add_zero] using tendsto_const_nhds.add (he.mul_const I)
  have hcont : ContinuousAt (causalAnalyticPhase t) (x:ℂ) :=
    Complex.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (continuousAt_const.div continuousAt_id hxc))
  simpa only [Function.comp_def,regularizedCausalPhase,ClosedUpperHalfPlaneMultiplier.boundary,
    causalAnalyticPhase_real] using hcont.tendsto.comp hd

/-- The same regularizations converge to the actual analytic phase at every upper point. -/
theorem regularizedCausalPhase_value_tendsto (t : ℝ≥0) (z : {z : ℂ // 0 < z.im}) :
    Tendsto (fun a => (regularizedCausalPhase t a).fn z.val) atBot (𝓝 (causalAnalyticPhase t z.val)) := by
  have hz : z.val ≠ 0 := by
    intro h
    have hi := z.property
    rw [h,Complex.zero_im] at hi
    exact lt_irrefl 0 hi
  have hd : Tendsto (fun a : ℝ => z.val+(Real.exp a:ℂ)*I) atBot (𝓝 z.val) := by
    have he := Complex.continuous_ofReal.continuousAt.tendsto.comp Real.tendsto_exp_atBot
    simpa only [Function.comp_apply,Complex.ofReal_zero,zero_mul,add_zero] using
      tendsto_const_nhds.add (he.mul_const I)
  have hcont : ContinuousAt (causalAnalyticPhase t) z.val :=
    Complex.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (continuousAt_const.div continuousAt_id hz))
  simpa only [Function.comp_def,regularizedCausalPhase] using hcont.tendsto.comp hd

/-- The actual analytic regularizations converge to the singular phase almost everywhere. -/
theorem regularizedCausalPhase_boundary_tendsto_ae (t : ℝ≥0) :
    ∀ᵐ x ∂(volume : Measure ℝ), Tendsto (fun a => (regularizedCausalPhase t a).boundary x)
      atBot (𝓝 (phase t x)) := by
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  exact regularized_boundary_tendsto t hx

private def patchedBoundary (t : ℝ≥0) (a x : ℝ) : ℂ :=
  if x = 0 then phase t x else (regularizedCausalPhase t a).boundary x

private theorem patched_measurable (t : ℝ≥0) (a : ℝ) : Measurable (patchedBoundary t a) := by
  exact Measurable.ite (measurableSet_singleton 0) (measurable_phase t)
    (regularizedCausalPhase t a).measurable_boundary

private theorem patched_bound (t : ℝ≥0) (a x : ℝ) : ‖patchedBoundary t a x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [patchedBoundary,hx]
  · simpa only [patchedBoundary,if_neg hx,regularizedCausalPhase] using
      (regularizedCausalPhase t a).norm_boundary_le x

/-- Analytic regularization converges strongly on every actual L² input. -/
theorem regularizedCausalPhase_operator_tendsto (t : ℝ≥0) (u : RealLineL2) :
    Tendsto (fun a => (regularizedCausalPhase t a).boundaryMul u) atBot (𝓝 (evolution t u)) := by
  have hpt : ∀ x : ℝ, Tendsto (fun a => patchedBoundary t a x) atBot (𝓝 (phase t x)) := by
    intro x
    by_cases hx : x = 0
    · simpa only [patchedBoundary,if_pos hx] using (tendsto_const_nhds (x := phase t x))
    · simpa only [patchedBoundary,if_neg hx] using regularized_boundary_tendsto t hx
  have hlim := tendsto_lpBoundedMulCLM_apply (μ := (volume : Measure ℝ))
    (patched_measurable t) (measurable_phase t) (by norm_num : (0:ℝ) ≤ 1)
    (patched_bound t) (fun x => (norm_phase t x).le) hpt u
  have he : lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (measurable_phase t) (by norm_num : (0:ℝ) ≤ 1) (fun x => (norm_phase t x).le) u = evolution t u := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (measurable_phase t) (by norm_num : (0:ℝ) ≤ 1) (fun x => (norm_phase t x).le) u,
      evolution_ae t u] with x hx hy
    exact hx.trans hy.symm
  have hi (a : ℝ) : lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (patched_measurable t a) (by norm_num : (0:ℝ) ≤ 1) (patched_bound t a) u =
        (regularizedCausalPhase t a).boundaryMul u := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (patched_measurable t a) (by norm_num : (0:ℝ) ≤ 1) (patched_bound t a) u,
      (regularizedCausalPhase t a).coe_boundaryMul u,(volume : Measure ℝ).ae_ne 0]
      with x hx hy hz
    rw [hx,hy,patchedBoundary,if_neg hz]
  simpa only [he,hi] using hlim

/-- Nonnegative real-time evolution preserves every upper Hardy L² vector. -/
theorem evolution_nonnegative_mem_hardy (t : ℝ≥0) (u : UpperHardyL2) :
    evolution t u.val ∈ RHTower.hardyL2 := by
  apply RHTower.isClosed_hardyL2.mem_of_tendsto (regularizedCausalPhase_operator_tendsto t u.val)
  exact Eventually.of_forall (fun a => (regularizedCausalPhase t a).boundaryMul_mem_hardy u)

/-- The actual singular phase restricts to an isometric causal Hardy evolution. -/
def causalHardyEvolution (t : ℝ≥0) : UpperHardyL2 →ₗᵢ[ℂ] UpperHardyL2 where
  toLinearMap := (((evolution t).toLinearEquiv.toLinearMap).comp UpperHardyL2.subtype).codRestrict
    UpperHardyL2 (evolution_nonnegative_mem_hardy t)
  norm_map' u := norm_evolution t u.val

/-- The restricted causal operators satisfy the actual additive evolution law. -/
theorem causalHardyEvolution_add (s t : ℝ≥0) (u : UpperHardyL2) :
    causalHardyEvolution (s+t) u = causalHardyEvolution s (causalHardyEvolution t u) := by
  apply Subtype.ext
  exact evolution_add s t u.val

/-- Causal Hardy evolution starts at the identity. -/
theorem causalHardyEvolution_zero (u : UpperHardyL2) : causalHardyEvolution 0 u = u := by
  apply Subtype.ext
  exact evolution_zero u.val

end
end GaloisForLFunctions.HTGeometry.FokasLenells
