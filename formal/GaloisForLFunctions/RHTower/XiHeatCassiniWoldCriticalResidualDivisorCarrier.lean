import GaloisForLFunctions.RHTower.XiHeatCassiniWoldCriticalGraphNoGo

/-!
# Critical residual divisor carrier for Route T2

Critical mesh energy and open-strip holomorphy cannot regularize the closed critical wall.  Instead,
every critical-line zeta zero is retained there as a quantized radial pole of the canonical Wold
residual Hardy source.  This upgrades the earlier existential survivor to the complete critical
divisor and proves that exponential overregularization beyond half-density is unconditionally
impossible.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- **Complete critical divisor carrier.** Every critical-line zeta zero is carried, with
quantized multiplicity, by a radial boundary residue of the canonical Wold residual Hardy source. -/
theorem xiHeatCassiniWoldResidualLowerHardyKernel_criticalZero_radial_residue
    {rho : ℂ} (hzeta : riemannZeta rho = 0) (hhalf : rho.re = 1 / 2)
    (hsource : AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < 1 / 2})
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun t : ℝ =>
        (t : ℂ) * xiHeatCassiniWoldResidualLowerHardyKernel
          (-Complex.I * ((rho - 1) + (t : ℂ))))
        (𝓝[>] (0 : ℝ)) (𝓝 (-(m : ℂ))) := by
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_residualSource_analytic_criticalEnergy hsource hcritical
  have him : rho.im ≠ 0 := by
    intro him0
    have hrho : rho = (rho.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him0
    rw [hrho, hhalf] at hzeta
    exact riemannZeta_ne_zero_of_ofReal_mem_Ioo (by norm_num) (by norm_num) hzeta
  let s0 : ℂ := rho - 1
  have hs0re : s0.re = -(1 / 2 : ℝ) := by
    dsimp only [s0]
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hs0 : s0 ≠ 0 := by
    intro hs0
    have him0 := congrArg Complex.im hs0
    simp only [s0, Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im] at him0
    exact him him0
  obtain ⟨m, hm, hpole⟩ :=
    xiHeatCassiniWoldCriticalLaplaceContinuation_zero_residue hhalf hzeta
  have hpath : Tendsto (fun t : ℝ => s0 + (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 s0) := by
    have hcont : ContinuousAt (fun t : ℝ => s0 + (t : ℂ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpathPunctured : Tendsto (fun t : ℝ => s0 + (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝[≠] s0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hpath, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    have : (t : ℂ) = 0 := by linear_combination heq
    exact ht.ne' (ofReal_eq_zero.mp this)
  have hpolePath := hpole.comp hpathPunctured
  have hpolePath' : Tendsto (fun t : ℝ =>
      (t : ℂ) * xiHeatCassiniWoldCriticalLaplaceContinuation
        (s0 + (t : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(m : ℂ))) := by
    convert hpolePath using 1
    funext t
    simp only [Function.comp_apply, s0]
    congr 1
    ring
  have hmesh :=
    tendsto_xiHeatCassiniLogMeshLaplaceContinuation_critical_radial
      hs0re hs0 hcritical
  have hholonomy : Tendsto (fun t : ℝ =>
      xiHeatCassiniWoldLaplaceHolonomyCounterterm (s0 + (t : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiHeatCassiniWoldLaplaceHolonomyCounterterm s0)) :=
    (analyticAt_xiHeatCassiniWoldLaplaceHolonomyCounterterm s0).continuousAt.tendsto.comp hpath
  have htzero : Tendsto (fun t : ℝ => (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmeshZero := htzero.mul hmesh
  have hholonomyZero := htzero.mul hholonomy
  have heq : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      xiHeatCassiniWoldCriticalLaplaceContinuation (s0 + (t : ℂ)) =
        xiHeatCassiniWoldResidualLowerHardyKernel
            (-Complex.I * (s0 + (t : ℂ))) +
          xiHeatCassiniLogMeshLaplaceContinuation (s0 + (t : ℂ)) +
          xiHeatCassiniWoldLaplaceHolonomyCounterterm (s0 + (t : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    apply xiHeatCassiniWoldCriticalLaplaceContinuation_eq_decomposition
    · simp only [Complex.add_re, Complex.ofReal_re, hs0re]
      linarith
    · dsimp only [s0]
      simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
        sub_zero, add_zero]
      exact him
    · exact hsource
    · exact hcritical
    · exact hRH
  have hresidue := (hpolePath'.sub hmeshZero).sub hholonomyZero
  refine ⟨m, hm, ?_⟩
  have hcongr : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (t : ℂ) * xiHeatCassiniWoldCriticalLaplaceContinuation (s0 + (t : ℂ)) -
          (t : ℂ) * xiHeatCassiniLogMeshLaplaceContinuation (s0 + (t : ℂ)) -
          (t : ℂ) * xiHeatCassiniWoldLaplaceHolonomyCounterterm (s0 + (t : ℂ)) =
        (t : ℂ) * xiHeatCassiniWoldResidualLowerHardyKernel
          (-Complex.I * (s0 + (t : ℂ))) := by
    exact heq.mono fun t ht => by rw [ht]; ring
  simpa only [zero_mul, sub_zero, s0] using hresidue.congr' hcongr

/-- Every critical zero therefore forces genuine boundary blow-up of the residual Hardy source. -/
theorem xiHeatCassiniWoldResidualLowerHardyKernel_criticalZero_radial_norm_atTop
    {rho : ℂ} (hzeta : riemannZeta rho = 0) (hhalf : rho.re = 1 / 2)
    (hsource : AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < 1 / 2})
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    Tendsto (fun t : ℝ =>
      ‖xiHeatCassiniWoldResidualLowerHardyKernel
        (-Complex.I * ((rho - 1) + (t : ℂ)))‖)
      (𝓝[>] (0 : ℝ)) atTop := by
  obtain ⟨m, hm, hresidue⟩ :=
    xiHeatCassiniWoldResidualLowerHardyKernel_criticalZero_radial_residue
      hzeta hhalf hsource hcritical
  have hmpos : 0 < ‖-(m : ℂ)‖ := by
    rw [norm_neg, Complex.norm_natCast]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hprod := Filter.Tendsto.atTop_mul_pos hmpos hinv hresidue.norm
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  field_simp [ht.ne']

/-- Away from the zeta divisor, the critical Wold continuation is regular at every nonreal point
of the critical wall. -/
theorem differentiableAt_xiHeatCassiniWoldCriticalLaplaceContinuation_of_criticalLine_ne_zero
    {rho : ℂ} (hhalf : rho.re = 1 / 2) (him : rho.im ≠ 0)
    (hzeta : riemannZeta rho ≠ 0) :
    DifferentiableAt ℂ xiHeatCassiniWoldCriticalLaplaceContinuation (rho - 1) := by
  have hrhoOne : rho ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [hhalf] at this
  have hflux : DifferentiableAt ℂ infinitePrimeFlux rho := by
    unfold infinitePrimeFlux
    simpa only [logDeriv_apply, neg_div] using!
      differentiableAt_neg_logDeriv_riemannZeta hrhoOne hzeta
  have htwoOne : 2 * rho ≠ 1 := by
    intro h
    have himEq := congrArg Complex.im h
    have : 2 * rho.im = 0 := by simpa using himEq
    exact him (by linarith)
  have htwoZero : riemannZeta (2 * rho) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp [hhalf]
  have htail : DifferentiableAt ℂ
      xiPrimeLogHigherValuationCriticalContinuation rho :=
    differentiableAt_xiPrimeLogHigherValuationCriticalContinuation
      (by rw [hhalf]; norm_num) htwoOne htwoZero
  have hQ : DifferentiableAt ℂ xiPrimeLogDirichletCriticalContinuation rho := by
    exact hflux.sub htail
  let s0 : ℂ := rho - 1
  have hs01 : s0 + 1 = rho := by dsimp only [s0]; ring
  have h1 : DifferentiableAt ℂ
      (fun s : ℂ => xiPrimeLogDirichletCriticalContinuation (s + (1 : ℂ))) s0 := by
    rw [← hs01] at hQ
    exact hQ.comp s0
      (show DifferentiableAt ℂ (fun s : ℂ => s + (1 : ℂ)) s0 by fun_prop)
  have hs2 : 1 < (s0 + 2).re := by
    dsimp only [s0]
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
    rw [hhalf]
    norm_num
  have hs3 : 1 < (s0 + 3).re := by
    dsimp only [s0]
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
    rw [hhalf]
    norm_num
  have hs4 : 1 < (s0 + 4).re := by
    dsimp only [s0]
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
    rw [hhalf]
    norm_num
  have h2 : DifferentiableAt ℂ
      (fun s : ℂ => xiPrimeLogDirichletContinuation (s + (2 : ℂ))) s0 := by
    change DifferentiableAt ℂ
      (xiPrimeLogDirichletContinuation ∘ fun s : ℂ => s + (2 : ℂ)) s0
    exact (differentiableAt_xiPrimeLogDirichletContinuation_of_one_lt_re hs2).comp s0
      (show DifferentiableAt ℂ (fun s : ℂ => s + (2 : ℂ)) s0 by fun_prop)
  have h3 : DifferentiableAt ℂ
      (fun s : ℂ => xiPrimeLogDirichletContinuation (s + (3 : ℂ))) s0 := by
    change DifferentiableAt ℂ
      (xiPrimeLogDirichletContinuation ∘ fun s : ℂ => s + (3 : ℂ)) s0
    exact (differentiableAt_xiPrimeLogDirichletContinuation_of_one_lt_re hs3).comp s0
      (show DifferentiableAt ℂ (fun s : ℂ => s + (3 : ℂ)) s0 by fun_prop)
  have h4 : DifferentiableAt ℂ
      (fun s : ℂ => xiPrimeLogDirichletContinuation (s + (4 : ℂ))) s0 := by
    change DifferentiableAt ℂ
      (xiPrimeLogDirichletContinuation ∘ fun s : ℂ => s + (4 : ℂ)) s0
    exact (differentiableAt_xiPrimeLogDirichletContinuation_of_one_lt_re hs4).comp s0
      (show DifferentiableAt ℂ (fun s : ℂ => s + (4 : ℂ)) s0 by fun_prop)
  change DifferentiableAt ℂ (fun s : ℂ =>
    xiPrimeLogDirichletCriticalContinuation (s + 1) -
      3 * xiPrimeLogDirichletContinuation (s + 2) +
      3 * xiPrimeLogDirichletContinuation (s + 3) -
      xiPrimeLogDirichletContinuation (s + 4)) s0
  exact ((h1.sub (h2.const_mul 3)).add (h3.const_mul 3)).sub h4

/-- **No spurious critical residues.** A nonzero radial residue of the residual Hardy source at a
nonreal critical-wall point forces that point to be a zeta zero. -/
theorem riemannZeta_eq_zero_of_residualLowerHardyKernel_critical_radial_residue
    {rho L : ℂ} (hhalf : rho.re = 1 / 2) (him : rho.im ≠ 0) (hL : L ≠ 0)
    (hsource : AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < 1 / 2})
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy)
    (hresidue : Tendsto (fun t : ℝ =>
      (t : ℂ) * xiHeatCassiniWoldResidualLowerHardyKernel
        (-Complex.I * ((rho - 1) + (t : ℂ))))
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    riemannZeta rho = 0 := by
  by_contra hzeta
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_residualSource_analytic_criticalEnergy hsource hcritical
  let s0 : ℂ := rho - 1
  have hs0re : s0.re = -(1 / 2 : ℝ) := by
    dsimp only [s0]
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hs0 : s0 ≠ 0 := by
    intro hs0
    have him0 := congrArg Complex.im hs0
    simp only [s0, Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im] at him0
    exact him him0
  have hpath : Tendsto (fun t : ℝ => s0 + (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 s0) := by
    have hcont : ContinuousAt (fun t : ℝ => s0 + (t : ℂ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hWold : Tendsto (fun t : ℝ =>
      xiHeatCassiniWoldCriticalLaplaceContinuation (s0 + (t : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiHeatCassiniWoldCriticalLaplaceContinuation s0)) :=
    (differentiableAt_xiHeatCassiniWoldCriticalLaplaceContinuation_of_criticalLine_ne_zero
      hhalf him hzeta).continuousAt.tendsto.comp hpath
  have hmesh :=
    tendsto_xiHeatCassiniLogMeshLaplaceContinuation_critical_radial
      hs0re hs0 hcritical
  have hholonomy : Tendsto (fun t : ℝ =>
      xiHeatCassiniWoldLaplaceHolonomyCounterterm (s0 + (t : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiHeatCassiniWoldLaplaceHolonomyCounterterm s0)) :=
    (analyticAt_xiHeatCassiniWoldLaplaceHolonomyCounterterm s0).continuousAt.tendsto.comp hpath
  have htzero : Tendsto (fun t : ℝ => (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hWoldZero := htzero.mul hWold
  have hmeshZero := htzero.mul hmesh
  have hholonomyZero := htzero.mul hholonomy
  have heq : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      xiHeatCassiniWoldCriticalLaplaceContinuation (s0 + (t : ℂ)) =
        xiHeatCassiniWoldResidualLowerHardyKernel
            (-Complex.I * (s0 + (t : ℂ))) +
          xiHeatCassiniLogMeshLaplaceContinuation (s0 + (t : ℂ)) +
          xiHeatCassiniWoldLaplaceHolonomyCounterterm (s0 + (t : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    apply xiHeatCassiniWoldCriticalLaplaceContinuation_eq_decomposition
    · simp only [Complex.add_re, Complex.ofReal_re, hs0re]
      linarith
    · dsimp only [s0]
      simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
        sub_zero, add_zero]
      exact him
    · exact hsource
    · exact hcritical
    · exact hRH
  have hzero := (hWoldZero.sub hmeshZero).sub hholonomyZero
  have hcongr : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (t : ℂ) * xiHeatCassiniWoldCriticalLaplaceContinuation (s0 + (t : ℂ)) -
          (t : ℂ) * xiHeatCassiniLogMeshLaplaceContinuation (s0 + (t : ℂ)) -
          (t : ℂ) * xiHeatCassiniWoldLaplaceHolonomyCounterterm (s0 + (t : ℂ)) =
        (t : ℂ) * xiHeatCassiniWoldResidualLowerHardyKernel
          (-Complex.I * (s0 + (t : ℂ))) := by
    exact heq.mono fun t ht => by rw [ht]; ring
  have hresidueZero : Tendsto (fun t : ℝ =>
      (t : ℂ) * xiHeatCassiniWoldResidualLowerHardyKernel
        (-Complex.I * ((rho - 1) + (t : ℂ))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul, sub_zero, s0] using hzero.congr' hcongr
  exact hL (tendsto_nhds_unique hresidue hresidueZero)

/-- **Exact critical boundary-divisor classification.** At every nonreal critical point, zeta
vanishing is equivalent to a nonzero quantized radial residue of the residual Hardy source. -/
theorem riemannZeta_eq_zero_iff_residualLowerHardyKernel_critical_radial_residue
    {rho : ℂ} (hhalf : rho.re = 1 / 2) (him : rho.im ≠ 0)
    (hsource : AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < 1 / 2})
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    riemannZeta rho = 0 ↔
      ∃ m : ℕ, 1 ≤ m ∧
        Tendsto (fun t : ℝ =>
          (t : ℂ) * xiHeatCassiniWoldResidualLowerHardyKernel
            (-Complex.I * ((rho - 1) + (t : ℂ))))
          (𝓝[>] (0 : ℝ)) (𝓝 (-(m : ℂ))) := by
  constructor
  · intro hzeta
    exact xiHeatCassiniWoldResidualLowerHardyKernel_criticalZero_radial_residue
      hzeta hhalf hsource hcritical
  · rintro ⟨m, hm, hresidue⟩
    apply riemannZeta_eq_zero_of_residualLowerHardyKernel_critical_radial_residue
      hhalf him _ hsource hcritical hresidue
    have hm0 : (m : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_zero_of_lt hm
    exact neg_ne_zero.mpr hm0

/-- **Sharp half-density obstruction.** No eventual exponential bound can force the centered Wold
residual through the critical half-density wall. -/
theorem not_eventually_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate_of_half_lt
    {c B : ℝ} (hc : 1 / 2 < c) (hB : 0 ≤ B) :
    ¬(∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N)) := by
  intro hrate
  apply not_half_residualUpperVariation_and_primeGapCriticalEnergy
  constructor
  · exact summable_residualUpperVariationAtom_of_exp_height_rate hc hrate
  · exact summable_primeGapCriticalEnergy_of_residual_exp_height_rate hc hB hrate

end

end RHTower
