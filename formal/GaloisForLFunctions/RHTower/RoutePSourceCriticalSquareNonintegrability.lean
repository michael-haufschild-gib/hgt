import GaloisForLFunctions.RHTower.CausalL2LaplaceHolomorphy
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePShiftedAnalyticRigidity
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourcePoleResidue
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewNonintegrability

/-!
# The literal Route-P ray has infinite critical square energy

A finite square budget would make the causal transform holomorphic in the
open right half-plane and force its boundary residues to vanish. Analytic
rigidity identifies that transform with the actual Route-P continuation,
whose residue at a Hardy zero is nonzero. No RH premise is used.

This obstruction concerns zero damping. It does not rule out, or prove,
any of the positive-damping budgets required by Route P.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

private theorem causal_sq_bound {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi 0))) {z : ℂ} (hz : 0 < z.re) :
    ‖causalTransform g z‖ ^ 2 ≤
      (∫ t in Ioi 0, ‖g t‖ ^ 2) / (2 * z.re) := by
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.1).mp hg
  have he := memLp_cexp_kernel hz
  have he2 := (memLp_two_iff_integrable_sq_norm he.1).mp he
  simp_rw [norm_cexp_neg_mul_ofReal] at he2
  have hem : AEStronglyMeasurable (fun t : ℝ => Real.exp (-z.re * t))
      (volume.restrict (Ioi 0)) := (by fun_prop :
        Continuous (fun t : ℝ => Real.exp (-z.re * t))).aestronglyMeasurable
  have hcs := sq_integral_mul_le hg.1.norm hem hg2 he2
  rw [integral_sq_exp_neg_mul_Ioi hz] at hcs
  have hn := norm_integral_le_integral_norm
    (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * g t)
    (μ := volume.restrict (Ioi 0))
  simp_rw [norm_mul, norm_cexp_neg_mul_ofReal,
    mul_comm (Real.exp (-z.re * _))] at hn
  have hi : 0 ≤ ∫ t in Ioi 0, ‖g t‖ * Real.exp (-z.re * t) :=
    integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  change ‖causalTransform g z‖ ≤ _ at hn
  have hs : ‖causalTransform g z‖ ^ 2 ≤
      (∫ t in Ioi 0, ‖g t‖ * Real.exp (-z.re * t)) ^ 2 := by
    nlinarith [norm_nonneg (causalTransform g z)]
  exact hs.trans (by simpa only [div_eq_mul_inv, one_mul] using hcs)

private theorem causal_boundary_residue_zero {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi 0)))
    (z0 : ℂ) (hz0 : z0.re = 0) :
    Tendsto (fun σ : ℝ => (σ : ℂ) * causalTransform g ((σ : ℂ) + z0))
      (𝓝[>] 0) (𝓝 0) := by
  let C : ℝ := ∫ t in Ioi 0, ‖g t‖ ^ 2
  let N : ℝ → ℝ := fun σ => ‖(σ : ℂ) * causalTransform g ((σ : ℂ) + z0)‖
  have hσ : Tendsto (fun σ : ℝ => σ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto (fun σ => C * σ / 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hσ.const_mul C).div_const 2
  have hsq : Tendsto (fun σ => N σ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Eventually.of_forall fun σ => sq_nonneg (N σ)
    · filter_upwards [self_mem_nhdsWithin] with σ hσpos
      have hσpos : 0 < σ := hσpos
      have hz : 0 < ((σ : ℂ) + z0).re := by simpa [hz0] using hσpos
      have hb := causal_sq_bound hg hz
      simp only [Complex.add_re, Complex.ofReal_re, hz0, add_zero] at hb
      dsimp only [N]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσpos, mul_pow]
      calc
        σ ^ 2 * ‖causalTransform g ((σ : ℂ) + z0)‖ ^ 2 ≤
            σ ^ 2 * (C / (2 * σ)) := mul_le_mul_of_nonneg_left hb (sq_nonneg σ)
        _ = C * σ / 2 := by field_simp [hσpos.ne']
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, N]
    using hsqrt

/-- Analytic admission identifies the literal source transform with its
arithmetic continuation throughout the open right half-plane. -/
theorem routePSource_transform_eq_continuation_of_analytic
    (hL : AnalyticOnNhd ℂ (causalTransform (fun t => (routePSourceRay t : ℂ)))
      {w : ℂ | 0 < w.re})
    {z : ℂ} (hz : 0 < z.re) :
    causalTransform (fun t => (routePSourceRay t : ℂ)) z =
      routePSourceLaplaceContinuation z := by
  let L : ℂ → ℂ := causalTransform (fun t => (routePSourceRay t : ℂ))
  let A : ℂ → ℂ := fun s => -(s * ((s + 1 / 2) * L (s - 1 / 2) + 2 / 3)) - 1
  have hA : AnalyticOnNhd ℂ A {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    change 1 / 2 < s.re at hs
    have hshift : AnalyticAt ℂ (fun w : ℂ => w - 1 / 2) s := by fun_prop
    have hs' : 0 < (s - 1 / 2).re := by simp only [Complex.sub_re]; norm_num; linarith
    have hcomp : AnalyticAt ℂ (fun w => L (w - 1 / 2)) s :=
      (hL _ hs').comp (f := fun w : ℂ => w - 1 / 2) hshift
    exact ((analyticAt_id.mul (((analyticAt_id.add analyticAt_const).mul
      hcomp).add analyticAt_const)).neg).sub analyticAt_const
  have hfun : zetaResidueUnit = regularizedRiemannZeta := by funext s; rfl
  have hEq : ∀ s : ℂ, 1 < s.re → A s = logDeriv regularizedRiemannZeta s := by
    intro s hs
    have hs' : 1 / 2 < (s - 1 / 2).re := by
      simp only [Complex.sub_re]; norm_num; linarith
    have hsource : L (s - 1 / 2) = routePSourceLaplaceContinuation (s - 1 / 2) :=
      (routePSourceLaplaceContinuation_eq_laplace hs').symm
    have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
    have hs1 : s + 1 / 2 ≠ 0 := ne_zero_of_re_pos (by
      simp only [Complex.add_re]; norm_num; linarith)
    dsimp only [A]
    rw [hsource, routePSourceLaplaceContinuation,
      criticalNormalizedChebyshevErrorContinuation, hfun,
      show s - 1 / 2 + 1 / 2 = s by ring,
      show s - 1 / 2 + 1 = s + 1 / 2 by ring]
    have hmiddle : (s + 1 / 2) *
        ((-(logDeriv regularizedRiemannZeta s + 1) / s - 2 / 3) / (s + 1 / 2)) +
        2 / 3 = -(logDeriv regularizedRiemannZeta s + 1) / s := by
      rw [mul_comm (s + 1 / 2), div_mul_cancel₀ _ hs1]
      ring
    rw [hmiddle]
    field_simp [hs0]
    ring
  have hz' : 1 / 2 < (z + 1 / 2).re := by
    simp only [Complex.add_re]; norm_num; linarith
  have hLog := logDeriv_regularizedZeta_eq_analytic_extension A hA hEq _ hz'
  dsimp only [A] at hLog
  rw [show z + 1 / 2 - 1 / 2 = z by ring,
    show z + 1 / 2 + 1 / 2 = z + 1 by ring] at hLog
  have hs0 : z + 1 / 2 ≠ 0 := ne_zero_of_re_pos (by
    simp only [Complex.add_re]; norm_num; linarith)
  have hz1 : z + 1 ≠ 0 := ne_zero_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]; linarith)
  change L z = _
  rw [routePSourceLaplaceContinuation, criticalNormalizedChebyshevErrorContinuation, hfun]
  apply (eq_div_iff hz1).2
  have hratio : (z + 1) * L z + 2 / 3 =
      -(logDeriv regularizedRiemannZeta (z + 1 / 2) + 1) / (z + 1 / 2) := by
    apply (eq_div_iff hs0).2
    linear_combination -hLog
  linear_combination hratio

/-- The actual Route-P source cannot have finite undamped square energy. -/
theorem not_memLp_two_routePSourceRay :
    ¬ MemLp (fun t => (routePSourceRay t : ℂ)) 2 (volume.restrict (Ioi 0)) := by
  intro hg
  have hL := (differentiableOn_causalTransform hg).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)
  obtain ⟨T0, hT0, hT⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, hτ, hzero⟩ := hT T0 le_rfl
  have hτ0 : 0 < τ := lt_of_lt_of_le hT0 hτ.1
  have him : 0 < (linePt τ).im := by simpa only [linePt_im] using hτ0
  obtain ⟨m, hm, hres⟩ := routePSourceLaplaceContinuation_residue_of_zero hzero him
  let z0 : ℂ := linePt τ - 1 / 2
  have hz0 : z0.re = 0 := by simp [z0, linePt]
  have hσ : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun σ : ℝ => (σ : ℂ) + z0) (𝓝[>] 0) (𝓝[≠] z0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using hσ.add_const z0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with σ hσpos
    change (σ : ℂ) + z0 ≠ z0
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.ofReal_re, hz0, add_zero] at hre
    exact (ne_of_gt hσpos) hre
  have hpole : Tendsto (fun σ : ℝ => (σ : ℂ) *
      routePSourceLaplaceContinuation ((σ : ℂ) + z0)) (𝓝[>] 0)
      (𝓝 (-(m : ℂ) / (linePt τ * (linePt τ + 1 / 2)))) := by
    simpa only [Function.comp_def, z0, add_sub_cancel_right] using hres.comp hp
  have hvanish : Tendsto (fun σ : ℝ => (σ : ℂ) *
      routePSourceLaplaceContinuation ((σ : ℂ) + z0)) (𝓝[>] 0) (𝓝 0) := by
    apply (causal_boundary_residue_zero hg z0 hz0).congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσpos
    rw [routePSource_transform_eq_continuation_of_analytic hL (by simpa [hz0] using hσpos)]
  have hne : -(m : ℂ) / (linePt τ * (linePt τ + 1 / 2)) ≠ 0 := by
    apply div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
    apply mul_ne_zero
    · intro heq
      have h := congrArg Complex.im heq
      simp only [linePt_im, Complex.zero_im] at h
      linarith
    · intro heq
      have h := congrArg Complex.im heq
      simp [linePt_im] at h
      linarith
  exact hne (tendsto_nhds_unique hpole hvanish)

/-- Unconditional nonintegrability of the literal nonnegative square. -/
theorem not_integrableOn_routePSourceRay_sq :
    ¬ IntegrableOn (fun t => routePSourceRay t ^ 2) (Ioi 0) := by
  intro hi
  apply not_memLp_two_routePSourceRay
  have hm : AEStronglyMeasurable (fun t => (routePSourceRay t : ℂ))
      (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.comp
      GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    (show Integrable (fun t => routePSourceRay t ^ 2) (volume.restrict (Ioi 0)) from hi)

/-- Positive survivor: no finite budget contains all late partial square energies. -/
theorem routePSource_square_energy_cofinally_unbounded (B T : ℝ) :
    ∃ U : ℝ, T ≤ U ∧ B < ∫ t in (0 : ℝ)..U, routePSourceRay t ^ 2 := by
  by_contra hn
  push Not at hn
  apply not_integrableOn_routePSourceRay_sq
  have hc : Continuous (fun t => routePSourceRay t ^ 2) :=
    GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative.pow 2
  have hlocal (U : ℝ) : IntegrableOn (fun t => routePSourceRay t ^ 2) (Ioc 0 U) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded B 0 hlocal tendsto_id
  filter_upwards [eventually_ge_atTop T] with U hU
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hn U hU

end RHTower
