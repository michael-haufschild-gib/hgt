import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelContinuationIdentity
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldCriticalBoundaryPole
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualODEClosure
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import GaloisForLFunctions.RHTower.BurnolSoninEvaluationNonvanishing

/-!
# T2 natural square-energy no-go

This module closes the cofinal natural-residual square-energy branch of route T2.
A hypothetical square-energy estimate at any `t > 1 / 2` makes the natural
Abel regular part finite on the critical wall. Zeta-cleared analytic
continuation then identifies it off an unconditional critical-line zero with
the Wold critical current, whose nonzero residue gives a contradiction.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def woldNatRegularContinuation (s : ℂ) : ℂ :=
  woldNatResidualAbelCurrent s +
    (xiHeatCassiniWoldLogHolonomyConstant : ℂ) +
      integerLogMeshContinuation s

theorem analyticOnNhd_woldNatRegularContinuation_of_squareEnergy
    {t : ℝ} (ht : 1 / 2 < t) (hEnergy : WoldNatResidualSquareEnergy t) :
    AnalyticOnNhd ℂ woldNatRegularContinuation
      (xiHeatCassiniWoldResidualODESector 1) := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_xiHeatCassiniWoldResidualODESector 1)
  intro s hs
  change -(1 / 2 : ℝ) < s.re ∧ 0 < (1 : ℝ) * s.im at hs
  simp only [one_mul] at hs
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    simp at hs
  have hA := differentiableAt_woldNatResidualAbelCurrent_of_squareEnergy
    ht hEnergy hs.1
  have hL := differentiableAt_integerLogMeshContinuation
    (by linarith : -1 < s.re) hs0
  unfold woldNatRegularContinuation
  exact ((hA.add_const (xiHeatCassiniWoldLogHolonomyConstant : ℂ)).add hL).differentiableWithinAt

def xiHeatCassiniWoldZetaClearedContinuation (s : ℂ) : ℂ :=
  (-deriv riemannZeta (s + 1) -
      riemannZeta (s + 1) *
        xiPrimeLogHigherValuationCriticalContinuation (s + 1)) -
    3 * (riemannZeta (s + 1) * xiPrimeLogDirichletContinuation (s + 2)) +
    3 * (riemannZeta (s + 1) * xiPrimeLogDirichletContinuation (s + 3)) -
    riemannZeta (s + 1) * xiPrimeLogDirichletContinuation (s + 4)

theorem analyticOnNhd_xiHeatCassiniWoldZetaClearedContinuation :
    AnalyticOnNhd ℂ xiHeatCassiniWoldZetaClearedContinuation
      (xiHeatCassiniWoldResidualODESector 1) := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_xiHeatCassiniWoldResidualODESector 1)
  intro s hs
  change -(1 / 2 : ℝ) < s.re ∧ 0 < (1 : ℝ) * s.im at hs
  simp only [one_mul] at hs
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    simp at hs
  have hs1ne : s + 1 ≠ 1 := by
    intro h
    apply hs0
    linear_combination h
  have hzBase := Sieve.analyticAt_riemannZeta_of_ne_one hs1ne
  have hz : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (z + 1)) s :=
    hzBase.differentiableAt.comp s (by fun_prop)
  have hzDeriv : DifferentiableAt ℂ
      (fun z : ℂ => deriv riemannZeta (z + 1)) s :=
    by
      change DifferentiableAt ℂ ((deriv riemannZeta) ∘ fun z : ℂ => z + 1) s
      exact hzBase.deriv.differentiableAt.comp s
        (show DifferentiableAt ℂ (fun z : ℂ => z + 1) s by fun_prop)
  have htwoOne : 2 * (s + 1) ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    norm_num [Complex.mul_im] at him
    linarith
  have htwoZero : riemannZeta (2 * (s + 1)) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    norm_num [Complex.mul_re]
    linarith
  have hHigherBase := differentiableAt_xiPrimeLogHigherValuationCriticalContinuation
    (s := s + 1) (by simp; linarith) htwoOne htwoZero
  have hHigher : DifferentiableAt ℂ
      (fun z : ℂ => xiPrimeLogHigherValuationCriticalContinuation (z + 1)) s := by
    change DifferentiableAt ℂ
      (xiPrimeLogHigherValuationCriticalContinuation ∘ fun z : ℂ => z + 1) s
    exact hHigherBase.comp s
      (show DifferentiableAt ℂ (fun z : ℂ => z + 1) s by fun_prop)
  have h2Base := analyticOnNhd_xiPrimeLogDirichletContinuation_one_lt
    (s + 2) (by simp; linarith : 1 < (s + 2).re)
  have h2 : DifferentiableAt ℂ
      (fun z : ℂ => xiPrimeLogDirichletContinuation (z + 2)) s := by
    change DifferentiableAt ℂ
      (xiPrimeLogDirichletContinuation ∘ fun z : ℂ => z + 2) s
    exact h2Base.differentiableAt.comp s
      (show DifferentiableAt ℂ (fun z : ℂ => z + 2) s by fun_prop)
  have h3Base := analyticOnNhd_xiPrimeLogDirichletContinuation_one_lt
    (s + 3) (by simp; linarith : 1 < (s + 3).re)
  have h3 : DifferentiableAt ℂ
      (fun z : ℂ => xiPrimeLogDirichletContinuation (z + 3)) s := by
    change DifferentiableAt ℂ
      (xiPrimeLogDirichletContinuation ∘ fun z : ℂ => z + 3) s
    exact h3Base.differentiableAt.comp s
      (show DifferentiableAt ℂ (fun z : ℂ => z + 3) s by fun_prop)
  have h4Base := analyticOnNhd_xiPrimeLogDirichletContinuation_one_lt
    (s + 4) (by simp; linarith : 1 < (s + 4).re)
  have h4 : DifferentiableAt ℂ
      (fun z : ℂ => xiPrimeLogDirichletContinuation (z + 4)) s := by
    change DifferentiableAt ℂ
      (xiPrimeLogDirichletContinuation ∘ fun z : ℂ => z + 4) s
    exact h4Base.differentiableAt.comp s
      (show DifferentiableAt ℂ (fun z : ℂ => z + 4) s by fun_prop)
  unfold xiHeatCassiniWoldZetaClearedContinuation
  exact ((((hzDeriv.neg.sub (hz.mul hHigher)).sub
    ((hz.mul h2).const_mul 3)).add ((hz.mul h3).const_mul 3)).sub
      (hz.mul h4)).differentiableWithinAt

theorem xiHeatCassiniWoldZetaClearedContinuation_eq_mul_critical
    {s : ℂ} (hz : riemannZeta (s + 1) ≠ 0) :
    xiHeatCassiniWoldZetaClearedContinuation s =
      riemannZeta (s + 1) * xiHeatCassiniWoldCriticalLaplaceContinuation s := by
  rw [xiHeatCassiniWoldZetaClearedContinuation,
    xiHeatCassiniWoldCriticalLaplaceContinuation,
    xiPrimeLogDirichletCriticalContinuation, infinitePrimeFlux]
  simp only [logDeriv_apply]
  field_simp [hz]

theorem woldNatRegularContinuation_eq_woldLaplaceCurrent
    {t : ℝ} (ht : 1 / 2 < t) (hEnergy : WoldNatResidualSquareEnergy t)
    {s : ℂ} (hs : 0 < s.re) :
    woldNatRegularContinuation s = xiHeatCassiniWoldLaplaceCurrent s := by
  rw [woldNatRegularContinuation, integerLogMeshContinuation_eq_current hs]
  exact (woldLaplaceCurrent_eq_naturalAbel_add_logMesh ht hEnergy hs).symm

theorem xiHeatCassiniWoldZetaClearedContinuation_eq_mul_regular_safe
    {t : ℝ} (ht : 1 / 2 < t) (hEnergy : WoldNatResidualSquareEnergy t)
    {s : ℂ} (hs : 0 < s.re) :
    xiHeatCassiniWoldZetaClearedContinuation s =
      riemannZeta (s + 1) * woldNatRegularContinuation s := by
  have hz : riemannZeta (s + 1) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp
    linarith
  rw [xiHeatCassiniWoldZetaClearedContinuation_eq_mul_critical hz,
    xiHeatCassiniWoldCriticalLaplaceContinuation_eq (by linarith),
    xiHeatCassiniWoldLaplaceContinuation_eq hs,
    woldNatRegularContinuation_eq_woldLaplaceCurrent ht hEnergy hs]

theorem xiHeatCassiniWoldZetaClearedContinuation_eq_mul_regular_on_sector
    {t : ℝ} (ht : 1 / 2 < t) (hEnergy : WoldNatResidualSquareEnergy t) :
    Set.EqOn xiHeatCassiniWoldZetaClearedContinuation
      (fun s : ℂ => riemannZeta (s + 1) * woldNatRegularContinuation s)
      (xiHeatCassiniWoldResidualODESector 1) := by
  have hL := analyticOnNhd_xiHeatCassiniWoldZetaClearedContinuation
  have hR : AnalyticOnNhd ℂ
      (fun s : ℂ => riemannZeta (s + 1) * woldNatRegularContinuation s)
      (xiHeatCassiniWoldResidualODESector 1) :=
    (analyticOnNhd_riemannZeta_add_one_residualODESector 1).mul
      (analyticOnNhd_woldNatRegularContinuation_of_squareEnergy ht hEnergy)
  let q : ℂ := 1 + Complex.I
  have hq : q ∈ xiHeatCassiniWoldResidualODESector 1 := by
    change -(1 / 2 : ℝ) < q.re ∧ 0 < (1 : ℝ) * q.im
    constructor <;> norm_num [q]
  have hevent : xiHeatCassiniWoldZetaClearedContinuation =ᶠ[𝓝 q]
      (fun s : ℂ => riemannZeta (s + 1) * woldNatRegularContinuation s) := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hqpos : 0 < q.re := by simp [q]
    filter_upwards [hopen.mem_nhds hqpos] with s hs
    exact xiHeatCassiniWoldZetaClearedContinuation_eq_mul_regular_safe
      ht hEnergy hs
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR
    (isPreconnected_xiHeatCassiniWoldResidualODESector 1) hq hevent

theorem tendsto_woldNatRegularContinuation_critical_radial_of_squareEnergy
    {t : ℝ} (ht : 1 / 2 < t) (hEnergy : WoldNatResidualSquareEnergy t)
    {s0 : ℂ} (hs0re : s0.re = -(1 / 2 : ℝ)) (hs0im : s0.im ≠ 0) :
    Tendsto (fun x : ℝ => woldNatRegularContinuation (s0 + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (woldNatRegularContinuation s0)) := by
  have hA := tendsto_woldNatResidualAbelCurrent_critical_radial_of_squareEnergy
    ht hEnergy hs0re hs0im
  have hs00 : s0 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    exact hs0im (by simpa using him)
  have hLAt := differentiableAt_integerLogMeshContinuation
    (s := s0) (by rw [hs0re]; norm_num) hs00
  have hpath : Tendsto (fun x : ℝ => s0 + (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 s0) := by
    have hcont : ContinuousAt (fun x : ℝ => s0 + (x : ℂ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hL : Tendsto
      (fun x : ℝ => integerLogMeshContinuation (s0 + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (integerLogMeshContinuation s0)) :=
    hLAt.continuousAt.tendsto.comp hpath
  simpa only [woldNatRegularContinuation] using
    (hA.add_const (xiHeatCassiniWoldLogHolonomyConstant : ℂ)).add hL

/-- **T2 natural square-energy no-go at the exact half-density wall.**  Any one
square energy strictly above `1/2` analytically regularizes the natural Wold
current across the translated critical wall.  An unconditional Hardy zero
forces a nonzero quantized Wold residue on that same wall, contradiction. -/
theorem not_woldNatResidualSquareEnergy_of_half_lt
    {t : ℝ} (ht : 1 / 2 < t) :
    ¬ WoldNatResidualSquareEnergy t := by
  intro hEnergy
  obtain ⟨T0, hT0, hHardy⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨tau, htauIcc, hzeta⟩ := hHardy T0 le_rfl
  have htau : 0 < tau := lt_of_lt_of_le hT0 htauIcc.1
  let rho : ℂ := linePt tau
  have hrhoRe : rho.re = 1 / 2 := by
    simp [rho, linePt]
  have hrhoIm : rho.im = tau := by
    simp [rho, linePt]
  have hrhoIm0 : rho.im ≠ 0 := by
    rw [hrhoIm]
    exact ne_of_gt htau
  let s0 : ℂ := rho - 1
  have hs0re : s0.re = -(1 / 2 : ℝ) := by
    dsimp only [s0]
    simp only [Complex.sub_re, Complex.one_re, hrhoRe]
    norm_num
  have hs0im : s0.im = tau := by
    dsimp only [s0]
    simp only [Complex.sub_im, Complex.one_im, sub_zero, hrhoIm]
  have hs0im0 : s0.im ≠ 0 := by
    rw [hs0im]
    exact ne_of_gt htau
  obtain ⟨m, hm, hpole⟩ :=
    xiHeatCassiniWoldCriticalLaplaceContinuation_zero_residue hrhoRe hzeta
  have hpathS0 : Tendsto (fun x : ℝ => s0 + (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 s0) := by
    have hcont : ContinuousAt (fun x : ℝ => s0 + (x : ℂ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpathS0Punct : Tendsto (fun x : ℝ => s0 + (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝[≠] s0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hpathS0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    have hx0 : (x : ℂ) = 0 := by linear_combination heq
    exact hx.ne' (ofReal_eq_zero.mp hx0)
  have hpolePath0 := hpole.comp hpathS0Punct
  have hpolePath : Tendsto (fun x : ℝ =>
      (x : ℂ) * xiHeatCassiniWoldCriticalLaplaceContinuation
        (s0 + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(m : ℂ))) := by
    convert hpolePath0 using 1
    funext x
    simp only [Function.comp_apply, s0]
    congr 1
    ring
  have hregular :=
    tendsto_woldNatRegularContinuation_critical_radial_of_squareEnergy
      ht hEnergy hs0re hs0im0
  have hxzero : Tendsto (fun x : ℝ => (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hregularZero : Tendsto (fun x : ℝ =>
      (x : ℂ) * woldNatRegularContinuation (s0 + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using hxzero.mul hregular
  have hsectorEq :=
    xiHeatCassiniWoldZetaClearedContinuation_eq_mul_regular_on_sector
      ht hEnergy
  have hpathRho : Tendsto (fun x : ℝ => rho + (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 rho) := by
    have hcont : ContinuousAt (fun x : ℝ => rho + (x : ℂ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpathRhoPunct : Tendsto (fun x : ℝ => rho + (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝[≠] rho) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hpathRho, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    have hx0 : (x : ℂ) = 0 := by linear_combination heq
    exact hx.ne' (ofReal_eq_zero.mp hx0)
  have hzetaOff : ∀ᶠ z in 𝓝[≠] rho, riemannZeta z ≠ 0 :=
    eventually_riemannZeta_ne_zero_nhdsNE (by rw [hrhoRe]; norm_num)
      (by rw [hrhoRe]; norm_num)
  have hzetaPath : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      riemannZeta (rho + (x : ℂ)) ≠ 0 :=
    hpathRhoPunct.eventually hzetaOff
  have heq : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      xiHeatCassiniWoldCriticalLaplaceContinuation (s0 + (x : ℂ)) =
        woldNatRegularContinuation (s0 + (x : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin, hzetaPath] with x hx hzetaX
    change 0 < x at hx
    let z : ℂ := s0 + (x : ℂ)
    have hzarg : riemannZeta (z + 1) ≠ 0 := by
      rw [show z + 1 = rho + (x : ℂ) by
        dsimp only [z, s0]
        ring]
      exact hzetaX
    have hzmem : z ∈ xiHeatCassiniWoldResidualODESector 1 := by
      change -(1 / 2 : ℝ) < z.re ∧ 0 < (1 : ℝ) * z.im
      dsimp only [z]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im,
        Complex.ofReal_im, add_zero, one_mul, hs0re, hs0im]
      exact ⟨by linarith, htau⟩
    have hclearedRegular := hsectorEq hzmem
    have hclearedCritical :=
      xiHeatCassiniWoldZetaClearedContinuation_eq_mul_critical hzarg
    apply mul_left_cancel₀ hzarg
    exact hclearedCritical.symm.trans hclearedRegular
  have hcriticalZero : Tendsto (fun x : ℝ =>
      (x : ℂ) * xiHeatCassiniWoldCriticalLaplaceContinuation
        (s0 + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hregularZero.congr'
    exact heq.mono fun x hx => by
      change (x : ℂ) * woldNatRegularContinuation (s0 + (x : ℂ)) =
        (x : ℂ) * xiHeatCassiniWoldCriticalLaplaceContinuation (s0 + (x : ℂ))
      rw [hx]
  have hmzero : -(m : ℂ) = 0 :=
    tendsto_nhds_unique hpolePath hcriticalZero
  have hmzero' : (m : ℂ) = 0 := neg_eq_zero.mp hmzero
  have : m = 0 := by exact_mod_cast hmzero'
  omega

/-- The exact cofinal square-energy producer demanded by the T2 endpoint cannot
exist: its value at `t = 5 / 8` contradicts the critical-line obstruction. -/
theorem not_woldNatResidualSquareEnergy_cofinal_threeQuarter :
    ¬ (∀ t : ℝ, 1 / 4 < t → t < 3 / 4 →
      WoldNatResidualSquareEnergy t) := by
  intro hEnergy
  exact not_woldNatResidualSquareEnergy_of_half_lt (t := 5 / 8) (by norm_num)
    (hEnergy (5 / 8) (by norm_num) (by norm_num))

end

end RHTower
