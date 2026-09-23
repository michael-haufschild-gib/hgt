import GaloisForLFunctions.RHTower.XiHeatCassiniWoldCriticalBoundaryPole
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualTwoSidedClosure
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite

/-!
# No-go theorem for the absolute critical Route-T graph norm

Critical residual variation gives radial boundary convergence of the residual Hardy series.
Critical prime-gap energy gives radial boundary convergence of the logarithmic mesh.  Their exact
interior identity would therefore make the critical Wold current have zero radial residue.  But an
unconditional nontrivial zeta zero, forced onto the critical line by the same hypotheses, gives the
Wold current a nonzero residue.  Thus the proposed absolute endpoint graph norm is empty.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Inside the translated critical strip, RH lets the cleared residual ODE be divided by zeta.
The resulting identity is exactly Wold = residual + mesh + holonomy. -/
theorem xiHeatCassiniWoldCriticalLaplaceContinuation_eq_decomposition
    {s : ℂ} (hstrip : -(1 / 2 : ℝ) < s.re) (him : s.im ≠ 0)
    (hsource : AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < 1 / 2})
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy)
    (hRH : RiemannHypothesis) :
    xiHeatCassiniWoldCriticalLaplaceContinuation s =
      xiHeatCassiniWoldResidualLowerHardyKernel (-Complex.I * s) +
        xiHeatCassiniLogMeshLaplaceContinuation s +
        xiHeatCassiniWoldLaplaceHolonomyCounterterm s := by
  have hsector : s ∈ xiHeatCassiniWoldResidualODESector s.im := by
    constructor
    · exact hstrip
    · exact mul_self_pos.mpr him
  have hODE :=
    neg_deriv_riemannZeta_shift_eq_residualODECoefficient_mul_on_sector
      him hsource hcritical s hsector
  have hzeta : riemannZeta (s + 1) ≠ 0 :=
    (riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH)
      (s + 1) (by simp; linarith)
  have hflux : infinitePrimeFlux (s + 1) =
      xiHeatCassiniWoldResidualODECoefficient s := by
    rw [infinitePrimeFlux, logDeriv_apply]
    field_simp
    linear_combination hODE
  have hs1 : 1 / 2 < (s + 1).re := by simp; linarith
  have htail := xiPrimeLogHigherValuationCriticalContinuation_eq hs1
  unfold xiHeatCassiniWoldResidualODECoefficient at hflux
  unfold xiHeatCassiniWoldCriticalLaplaceContinuation
  unfold xiPrimeLogDirichletCriticalContinuation
  rw [htail]
  linear_combination hflux

/-- Endpoint residual variation gives radial convergence at every translated critical point. -/
theorem tendsto_xiHeatCassiniWoldResidualLowerHardyKernel_critical_radial
    {s0 : ℂ} (hs0re : s0.re = -(1 / 2 : ℝ))
    (hvariation : Summable
      (xiHeatCassiniWoldResidualUpperVariationAtom (1 / 2))) :
    Tendsto (fun t : ℝ =>
      xiHeatCassiniWoldResidualLowerHardyKernel
        (-Complex.I * (s0 + (t : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiHeatCassiniWoldResidualLowerHardyKernel (-Complex.I * s0))) := by
  let K : ℝ := ‖s0‖ + 1
  let C : ℝ := K * Real.exp K
  let M : ℕ → ℝ := fun N =>
    C * xiHeatCassiniWoldResidualUpperVariationAtom (1 / 2) N
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hM : Summable M := hvariation.mul_left C
  have hpoint : ∀ N : ℕ,
      Tendsto (fun t : ℝ =>
        xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
          (-Complex.I * (s0 + (t : ℂ))) N)
        (𝓝[>] (0 : ℝ))
        (𝓝 (xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
          (-Complex.I * s0) N)) := by
    intro N
    have hcont : ContinuousAt (fun t : ℝ =>
        xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
          (-Complex.I * (s0 + (t : ℂ))) N) 0 := by
      unfold xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
      unfold xiHeatCassiniOrderedPrimeComplexNegativePhase
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
  have hdom : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ N : ℕ,
      ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (-Complex.I * (s0 + (t : ℂ))) N‖ ≤ M N := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht0 ht1 N
    let z : ℂ := -Complex.I * (s0 + (t : ℂ))
    have ht0' : 0 ≤ t := ht0.le
    have hznorm : ‖z‖ ≤ K := by
      dsimp only [z, K]
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      calc
        ‖s0 + (t : ℂ)‖ ≤ ‖s0‖ + ‖(t : ℂ)‖ := norm_add_le _ _
        _ = ‖s0‖ + t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0']
        _ ≤ ‖s0‖ + 1 := by linarith
    have hzim : z.im ≤ 1 / 2 := by
      dsimp only [z]
      simp only [Complex.mul_im, Complex.I_re, zero_mul,
        Complex.neg_im, Complex.I_im, neg_mul, one_mul, Complex.add_re,
        Complex.ofReal_re, zero_add]
      linarith
    have hhexp : Real.exp (xiMassNthPrimeLogHeight N * z.im) ≤
        Real.exp ((1 / 2 : ℝ) * xiMassNthPrimeLogHeight N) := by
      apply Real.exp_le_exp.mpr
      calc
        xiMassNthPrimeLogHeight N * z.im ≤
            xiMassNthPrimeLogHeight N * (1 / 2) :=
          mul_le_mul_of_nonneg_left hzim
            (xiMassNthPrimeLogHeight_pos N).le
        _ = (1 / 2) * xiMassNthPrimeLogHeight N := by ring
    have hshape : ‖z‖ * Real.exp ‖z‖ ≤ K * Real.exp K :=
      mul_le_mul hznorm (Real.exp_le_exp.mpr hznorm)
        (Real.exp_nonneg _) hK
    have hraw :=
      norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_le_global z N
    let A : ℝ := |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      xiHeatCassiniOrderedPrimeLogGap N
    have hA : 0 ≤ A := by
      dsimp only [A]
      exact mul_nonneg (abs_nonneg _)
        (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
    calc
      ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z N‖ ≤
          |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
            xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ * Real.exp ‖z‖ *
              Real.exp (xiMassNthPrimeLogHeight N * z.im) := hraw
      _ = A * (‖z‖ * Real.exp ‖z‖) *
            Real.exp (xiMassNthPrimeLogHeight N * z.im) := by
        dsimp only [A]
        ring
      _ ≤ A * (K * Real.exp K) *
            Real.exp (xiMassNthPrimeLogHeight N * z.im) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hshape hA) (Real.exp_nonneg _)
      _ ≤ A * (K * Real.exp K) *
            Real.exp ((1 / 2 : ℝ) * xiMassNthPrimeLogHeight N) :=
        mul_le_mul_of_nonneg_left hhexp
          (mul_nonneg hA (mul_nonneg hK (Real.exp_nonneg _)))
      _ = M N := by
        dsimp only [M, C, A, xiHeatCassiniWoldResidualUpperVariationAtom]
        ring
  have hmain := tendsto_tsum_of_dominated_convergence hM hpoint hdom
  change Tendsto (fun t : ℝ => ∑' N : ℕ,
      xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (-Complex.I * (s0 + (t : ℂ))) N)
    (𝓝[>] (0 : ℝ))
    (𝓝 (∑' N : ℕ,
      xiHeatCassiniWoldResidualComplexPhaseConnectionAtom (-Complex.I * s0) N))
  exact hmain

/-- Critical prime-gap energy gives radial convergence of the mesh resolvent at its left wall. -/
theorem tendsto_xiHeatCassiniLogMeshLaplaceContinuation_critical_radial
    {s0 : ℂ} (hs0re : s0.re = -(1 / 2 : ℝ)) (hs0 : s0 ≠ 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    Tendsto (fun t : ℝ =>
      xiHeatCassiniLogMeshLaplaceContinuation (s0 + (t : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiHeatCassiniLogMeshLaplaceContinuation s0)) := by
  let K : ℝ := ‖s0‖ + 1
  let C : ℝ := K ^ (2 : ℕ) * Real.exp K
  let M : ℕ → ℝ := fun N =>
    C * xiHeatCassiniPrimeGapAbscissaEnergy (1 / 2) N
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have henergy : Summable (xiHeatCassiniPrimeGapAbscissaEnergy (1 / 2)) :=
    summable_primeGapAbscissaEnergy_of_criticalEnergy
      (by norm_num) (by norm_num) hcritical
  have hM : Summable M := henergy.mul_left C
  have hpoint : ∀ N : ℕ,
      Tendsto (fun t : ℝ =>
        xiHeatCassiniLogMeshLaplaceScaledDefect (s0 + (t : ℂ)) N)
        (𝓝[>] (0 : ℝ))
        (𝓝 (xiHeatCassiniLogMeshLaplaceScaledDefect s0 N)) := by
    intro N
    have hcont : ContinuousAt (fun t : ℝ =>
        xiHeatCassiniLogMeshLaplaceScaledDefect (s0 + (t : ℂ)) N) 0 := by
      unfold xiHeatCassiniLogMeshLaplaceScaledDefect
      unfold xiHeatCassiniLogMeshLaplaceAtom
      unfold xiHeatCassiniOrderedPrimeLaplacePhase
      unfold xiHeatCassiniOrderedPrimeComplexNegativePhase
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
  have hdom : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ N : ℕ,
      ‖xiHeatCassiniLogMeshLaplaceScaledDefect (s0 + (t : ℂ)) N‖ ≤ M N := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht0 ht1 N
    let s : ℂ := s0 + (t : ℂ)
    have ht0' : 0 ≤ t := ht0.le
    have hsnorm : ‖s‖ ≤ K := by
      dsimp only [s, K]
      calc
        ‖s0 + (t : ℂ)‖ ≤ ‖s0‖ + ‖(t : ℂ)‖ := norm_add_le _ _
        _ = ‖s0‖ + t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0']
        _ ≤ ‖s0‖ + 1 := by linarith
    have hfactor : ‖s‖ ^ (2 : ℕ) * Real.exp ‖s‖ ≤ C := by
      dsimp only [C]
      gcongr
    have habscissa : -s.re ≤ 1 / 2 := by
      dsimp only [s]
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    have henergyMono : xiHeatCassiniPrimeGapAbscissaEnergy (-s.re) N ≤
        xiHeatCassiniPrimeGapAbscissaEnergy (1 / 2) N := by
      unfold xiHeatCassiniPrimeGapAbscissaEnergy
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right habscissa
        (xiMassNthPrimeLogHeight_pos (N + 1)).le
    calc
      ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖ ≤
          (‖s‖ ^ (2 : ℕ) * Real.exp ‖s‖) *
            xiHeatCassiniPrimeGapAbscissaEnergy (-s.re) N :=
        norm_xiHeatCassiniLogMeshLaplaceScaledDefect_le_abscissaEnergy s N
      _ ≤ C * xiHeatCassiniPrimeGapAbscissaEnergy (1 / 2) N :=
        mul_le_mul hfactor henergyMono
          (xiHeatCassiniPrimeGapAbscissaEnergy_nonneg (-s.re) N) hC
      _ = M N := rfl
  have hdef := tendsto_tsum_of_dominated_convergence hM hpoint hdom
  have hpath : Tendsto (fun t : ℝ => s0 + (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 s0) := by
    have hcont : ContinuousAt (fun t : ℝ => s0 + (t : ℂ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hphase : Tendsto (fun t : ℝ =>
      xiHeatCassiniOrderedPrimeLaplacePhase 0 (s0 + (t : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiHeatCassiniOrderedPrimeLaplacePhase 0 s0)) := by
    have hcont : ContinuousAt
        (fun s : ℂ => xiHeatCassiniOrderedPrimeLaplacePhase 0 s) s0 := by
      unfold xiHeatCassiniOrderedPrimeLaplacePhase
      unfold xiHeatCassiniOrderedPrimeComplexNegativePhase
      fun_prop
    exact hcont.tendsto.comp hpath
  have hquot := (hphase.sub hdef).div hpath hs0
  change Tendsto (fun t : ℝ =>
      (xiHeatCassiniOrderedPrimeLaplacePhase 0 (s0 + (t : ℂ)) -
        xiHeatCassiniLogMeshLaplaceDefectSum (s0 + (t : ℂ))) /
          (s0 + (t : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((xiHeatCassiniOrderedPrimeLaplacePhase 0 s0 -
        xiHeatCassiniLogMeshLaplaceDefectSum s0) / s0)) at hquot
  simpa only [xiHeatCassiniLogMeshLaplaceContinuation] using hquot

/-- RH plus unconditional nontrivial-zero existence supplies a genuine critical-line zeta zero. -/
theorem exists_criticalLine_riemannZeta_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ rho : ℂ, 0 < rho.re ∧ rho.re < 1 ∧
      riemannZeta rho = 0 ∧ rho.re = 1 / 2 := by
  obtain ⟨rho, hrho0, hrho1, hzeta⟩ := exists_riemannZeta_zero_mem_openStrip
  have hhalf : rho.re = 1 / 2 := by
    apply hRH rho hzeta
    · intro htrivial
      obtain ⟨n, hn⟩ := htrivial
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [hn] at hrho0
      norm_num [Complex.mul_re] at hrho0
      linarith
    · exact riemannZeta_zero_ne_one hzeta
  exact ⟨rho, hrho0, hrho1, hzeta, hhalf⟩

/-- **Positive survivor of the graph no-go.**  If the residual source is holomorphic on the open
critical half-strip and critical mesh energy holds, then some unconditional critical zero appears
as an exact nonzero radial pole of the residual Hardy carrier itself. -/
theorem exists_criticalZero_residualLowerHardyKernel_radial_residue
    (hsource : AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < 1 / 2})
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    ∃ rho : ℂ, ∃ m : ℕ,
      riemannZeta rho = 0 ∧ rho.re = 1 / 2 ∧ 1 ≤ m ∧
      Tendsto (fun t : ℝ =>
        (t : ℂ) * xiHeatCassiniWoldResidualLowerHardyKernel
          (-Complex.I * ((rho - 1) + (t : ℂ))))
        (𝓝[>] (0 : ℝ)) (𝓝 (-(m : ℂ))) := by
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_residualSource_analytic_criticalEnergy hsource hcritical
  obtain ⟨rho, _hrho0, _hrho1, hzeta, hhalf⟩ :=
    exists_criticalLine_riemannZeta_zero_of_riemannHypothesis hRH
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
  refine ⟨rho, m, hzeta, hhalf, hm, ?_⟩
  have hcongr : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (t : ℂ) * xiHeatCassiniWoldCriticalLaplaceContinuation (s0 + (t : ℂ)) -
          (t : ℂ) * xiHeatCassiniLogMeshLaplaceContinuation (s0 + (t : ℂ)) -
          (t : ℂ) * xiHeatCassiniWoldLaplaceHolonomyCounterterm (s0 + (t : ℂ)) =
        (t : ℂ) * xiHeatCassiniWoldResidualLowerHardyKernel
          (-Complex.I * (s0 + (t : ℂ))) := by
    exact heq.mono fun t ht => by rw [ht]; ring
  simpa only [zero_mul, sub_zero, s0] using hresidue.congr' hcongr

/-- The survivor is a genuine boundary blow-up: the residual Hardy norm diverges along the same
radial approach to a critical zero. -/
theorem exists_criticalZero_residualLowerHardyKernel_radial_norm_atTop
    (hsource : AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < 1 / 2})
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    ∃ rho : ℂ, riemannZeta rho = 0 ∧ rho.re = 1 / 2 ∧
      Tendsto (fun t : ℝ =>
        ‖xiHeatCassiniWoldResidualLowerHardyKernel
          (-Complex.I * ((rho - 1) + (t : ℂ)))‖)
        (𝓝[>] (0 : ℝ)) atTop := by
  obtain ⟨rho, m, hzeta, hhalf, hm, hresidue⟩ :=
    exists_criticalZero_residualLowerHardyKernel_radial_residue hsource hcritical
  refine ⟨rho, hzeta, hhalf, ?_⟩
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

/-- Critical residual absolute convergence and critical mesh energy cannot coexist. -/
theorem not_half_residualUpperVariation_and_primeGapCriticalEnergy :
    ¬ (Summable (xiHeatCassiniWoldResidualUpperVariationAtom (1 / 2)) ∧
      Summable xiHeatCassiniPrimeGapCriticalEnergy) := by
  rintro ⟨hleft, hcritical⟩
  have hsource : AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < 1 / 2} :=
    analyticOnNhd_xiHeatCassiniWoldResidualLowerHardyKernel_of_upperVariation
      (by norm_num) hleft
  obtain ⟨rho, m, _hzeta, hhalf, hm, hpole⟩ :=
    exists_criticalZero_residualLowerHardyKernel_radial_residue hsource hcritical
  have hs0re : (rho - 1).re = -(1 / 2 : ℝ) := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hfinite :=
    tendsto_xiHeatCassiniWoldResidualLowerHardyKernel_critical_radial hs0re hleft
  have htzero : Tendsto (fun t : ℝ => (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzero := htzero.mul hfinite
  have hlim : (0 : ℂ) = -(m : ℂ) := by
    have hlim' : -(m : ℂ) = 0 :=
      tendsto_nhds_unique hpole (by simpa only [zero_mul] using hzero)
    exact hlim'.symm
  have hmzero : m = 0 := by
    have : (m : ℂ) = 0 := by linear_combination hlim
    exact_mod_cast this
  omega

/-- The proposed two-sided critical graph norm is therefore unconditionally false. -/
theorem not_half_twoSided_residualUpperVariation :
    ¬ (Summable (xiHeatCassiniWoldResidualUpperVariationAtom (1 / 2)) ∧
      Summable (xiHeatCassiniWoldResidualRightUpperVariationAtom (1 / 2))) := by
  rintro ⟨hleft, hright⟩
  exact not_half_residualUpperVariation_and_primeGapCriticalEnergy
    ⟨hleft,
      summable_primeGapCriticalEnergy_of_half_twoSidedResidualUpperVariation
        hleft hright⟩

end

end RHTower
