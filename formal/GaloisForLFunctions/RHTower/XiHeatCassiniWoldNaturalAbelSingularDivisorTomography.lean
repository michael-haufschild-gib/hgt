import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelFullCriticalDivisor
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldCriticalResidualDivisorCarrier
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Exact singular-divisor tomography for the natural Wold Abel germ

The literal natural Abel germ has a canonical singular continuation: subtract the holomorphic
integer-log mesh from the critical Wold continuation.  This file proves that the construction
agrees with the literal Abel series on its safe half-plane and classifies its complete nonreal
singular support throughout the closed translated right half-sector.

At `s = rho - 1`, the carrier is complex differentiable exactly when `zeta(rho)` is nonzero.  At
every zero its punctured residue is the negative analytic multiplicity.  Thus T2's singular
carrier and its right-half divisor are no longer open constructions: the remaining source theorem
must exclude strict-interior poles of this fixed carrier.  Regularity throughout that interior is
proved equivalent to RH.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Canonical principal-relative singular continuation of the literal natural Wold Abel germ. -/
def woldNatSingularAbelContinuation (s : ℂ) : ℂ :=
  xiHeatCassiniWoldCriticalLaplaceContinuation s -
    integerLogMeshContinuation s

/-- The singular carrier is a genuine continuation of the literal natural Abel germ. -/
theorem woldNatSingularAbelContinuation_eq_naturalAbel
    {s : ℂ} (hs : 0 < s.re) :
    woldNatSingularAbelContinuation s =
      abelDirichlet woldNatDifferenceCoeff s := by
  rw [woldNatSingularAbelContinuation,
    xiHeatCassiniWoldCriticalLaplaceContinuation_eq (by linarith),
    xiHeatCassiniWoldLaplaceContinuation_eq hs,
    integerLogMeshContinuation_eq_current hs,
    abelDirichlet_woldNatDifferenceCoeff_eq_wold_sub_mesh hs]

/-- The continued integer mesh has zero residue at every nonreal point in the closed translated
right critical half-sector. -/
theorem integerLogMeshContinuation_zero_residue_closedRight
    {rho : ℂ} (hhalf : 1 / 2 ≤ rho.re) (him : rho.im ≠ 0) :
    Tendsto (fun s : ℂ =>
      (s - (rho - 1)) * integerLogMeshContinuation s)
      (𝓝[≠] (rho - 1)) (𝓝 0) := by
  have hs0re : -1 < (rho - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hs0 : rho - 1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact him hi
  have hmesh : Tendsto integerLogMeshContinuation
      (𝓝[≠] (rho - 1))
      (𝓝 (integerLogMeshContinuation (rho - 1))) :=
    (differentiableAt_integerLogMeshContinuation hs0re hs0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact (tendsto_sub_self_punctured_zero (rho - 1)).mul hmesh |>.trans (by simp)

/-- Every nonreal zeta zero in the closed right critical half-plane is an exact nonzero pole of
the canonical natural Abel continuation, with residue minus its analytic multiplicity. -/
theorem woldNatSingularAbelContinuation_zero_residue
    {rho : ℂ} (hhalf : 1 / 2 ≤ rho.re) (him : rho.im ≠ 0)
    (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ =>
        (s - (rho - 1)) * woldNatSingularAbelContinuation s)
        (𝓝[≠] (rho - 1)) (𝓝 (-(m : ℂ))) := by
  have hmesh := integerLogMeshContinuation_zero_residue_closedRight hhalf him
  rcases eq_or_lt_of_le hhalf with hEq | hlt
  · obtain ⟨m, hm, hWold⟩ :=
      xiHeatCassiniWoldCriticalLaplaceContinuation_zero_residue hEq.symm hzeta
    refine ⟨m, hm, ?_⟩
    have hsub := hWold.sub hmesh
    simpa only [woldNatSingularAbelContinuation, mul_sub, sub_zero] using hsub
  · obtain ⟨m, hm, hWold⟩ :=
      xiHeatCassiniWoldLaplaceContinuation_zero_residue hlt hzeta
    refine ⟨m, hm, ?_⟩
    have hopen : IsOpen {s : ℂ | -1 / 2 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hs0 : rho - 1 ∈ {s : ℂ | -1 / 2 < s.re} := by
      change -1 / 2 < (rho - 1).re
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hnear : ∀ᶠ s : ℂ in 𝓝[≠] (rho - 1), -1 / 2 < s.re :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (hopen.mem_nhds hs0)
    have heq : xiHeatCassiniWoldCriticalLaplaceContinuation =ᶠ[𝓝[≠] (rho - 1)]
        xiHeatCassiniWoldLaplaceContinuation := by
      filter_upwards [hnear] with s hs
      exact xiHeatCassiniWoldCriticalLaplaceContinuation_eq hs
    have hWold' : Tendsto (fun s : ℂ =>
        (s - (rho - 1)) * xiHeatCassiniWoldCriticalLaplaceContinuation s)
        (𝓝[≠] (rho - 1)) (𝓝 (-(m : ℂ))) := by
      apply hWold.congr'
      filter_upwards [heq] with s hs
      rw [hs]
    have hsub := hWold'.sub hmesh
    simpa only [woldNatSingularAbelContinuation, mul_sub, sub_zero] using hsub

/-- Strictly inside the translated sector, the critical Wold model is regular wherever zeta is
nonzero. -/
theorem differentiableAt_xiHeatCassiniWoldCriticalLaplaceContinuation_of_half_lt_re_ne_zero
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (him : rho.im ≠ 0)
    (hzeta : riemannZeta rho ≠ 0) :
    DifferentiableAt ℂ xiHeatCassiniWoldCriticalLaplaceContinuation (rho - 1) := by
  have hrhoOne : rho ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact him hi
  have hflux : DifferentiableAt ℂ infinitePrimeFlux rho := by
    unfold infinitePrimeFlux
    simpa only [logDeriv_apply, neg_div] using!
      differentiableAt_neg_logDeriv_riemannZeta hrhoOne hzeta
  have htwoOne : 2 * rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have htwoRe : 1 < (2 * rho).re := by
    norm_num
    linarith
  have htwoZero : riemannZeta (2 * rho) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re htwoRe
  have htail : DifferentiableAt ℂ
      xiPrimeLogHigherValuationCriticalContinuation rho :=
    differentiableAt_xiPrimeLogHigherValuationCriticalContinuation
      (by linarith) htwoOne htwoZero
  have hQ : DifferentiableAt ℂ xiPrimeLogDirichletCriticalContinuation rho :=
    hflux.sub htail
  let s0 : ℂ := rho - 1
  have hs01 : s0 + 1 = rho := by dsimp only [s0]; ring
  have h1 : DifferentiableAt ℂ
      (fun s : ℂ => xiPrimeLogDirichletCriticalContinuation (s + (1 : ℂ))) s0 := by
    rw [← hs01] at hQ
    exact hQ.comp s0
      (show DifferentiableAt ℂ (fun s : ℂ => s + (1 : ℂ)) s0 by fun_prop)
  have hs2 : 1 < (s0 + 2).re := by
    dsimp only [s0]
    simp
    linarith
  have hs3 : 1 < (s0 + 3).re := by
    dsimp only [s0]
    simp
    linarith
  have hs4 : 1 < (s0 + 4).re := by
    dsimp only [s0]
    simp
    linarith
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
  change DifferentiableAt ℂ
    (fun s : ℂ =>
      xiPrimeLogDirichletCriticalContinuation (s + 1) -
        3 * xiPrimeLogDirichletContinuation (s + 2) +
        3 * xiPrimeLogDirichletContinuation (s + 3) -
        xiPrimeLogDirichletContinuation (s + 4)) s0
  exact ((h1.sub (h2.const_mul 3)).add (h3.const_mul 3)).sub h4

/-- Exact singular-support tomography on the closed translated right half-sector: the canonical
natural Abel carrier is regular precisely away from the zeta divisor. -/
theorem differentiableAt_woldNatSingularAbelContinuation_iff
    {rho : ℂ} (hhalf : 1 / 2 ≤ rho.re) (him : rho.im ≠ 0) :
    DifferentiableAt ℂ woldNatSingularAbelContinuation (rho - 1) ↔
      riemannZeta rho ≠ 0 := by
  constructor
  · intro hdiff hzeta
    obtain ⟨m, hm, hres⟩ :=
      woldNatSingularAbelContinuation_zero_residue hhalf him hzeta
    have hcarrier : Tendsto woldNatSingularAbelContinuation
        (𝓝[≠] (rho - 1))
        (𝓝 (woldNatSingularAbelContinuation (rho - 1))) :=
      hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hzero : Tendsto (fun s : ℂ =>
        (s - (rho - 1)) * woldNatSingularAbelContinuation s)
        (𝓝[≠] (rho - 1)) (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_sub_self_punctured_zero (rho - 1)).mul hcarrier
    have hmzero : -(m : ℂ) = 0 := tendsto_nhds_unique hres hzero
    have hmzero' : (m : ℂ) = 0 := neg_eq_zero.mp hmzero
    have : m = 0 := by exact_mod_cast hmzero'
    omega
  · intro hzeta
    have hmeshRe : -1 < (rho - 1).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hs0 : rho - 1 ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      simp at hi
      exact him hi
    have hmesh := differentiableAt_integerLogMeshContinuation hmeshRe hs0
    rcases eq_or_lt_of_le hhalf with hEq | hlt
    · exact (differentiableAt_xiHeatCassiniWoldCriticalLaplaceContinuation_of_criticalLine_ne_zero
        hEq.symm him hzeta).sub hmesh
    · exact (differentiableAt_xiHeatCassiniWoldCriticalLaplaceContinuation_of_half_lt_re_ne_zero
        hlt him hzeta).sub hmesh

/-- T2 terminal connector after divisor tomography: RH is exactly regularity of the canonical
natural Abel singular carrier throughout the strict translated right half-sector. -/
theorem riemannHypothesis_iff_woldNatSingularAbelContinuation_strictRight_regular :
    RiemannHypothesis ↔
      ∀ rho : ℂ, 1 / 2 < rho.re → rho.im ≠ 0 →
        DifferentiableAt ℂ woldNatSingularAbelContinuation (rho - 1) := by
  constructor
  · intro hRH rho hhalf him
    rw [differentiableAt_woldNatSingularAbelContinuation_iff hhalf.le him]
    exact (riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH)
      rho hhalf
  · intro hregular
    by_contra hRH
    obtain ⟨rho, hzeta, hhalf, hone⟩ :=
      exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    have him : rho.im ≠ 0 := by
      intro him0
      have hrho : rho = (rho.re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa using him0
      rw [hrho] at hzeta
      exact riemannZeta_ne_zero_of_ofReal_mem_Ioo (by linarith) hone hzeta
    exact (differentiableAt_woldNatSingularAbelContinuation_iff hhalf.le him).mp
      (hregular rho hhalf him) hzeta

end

end RHTower
