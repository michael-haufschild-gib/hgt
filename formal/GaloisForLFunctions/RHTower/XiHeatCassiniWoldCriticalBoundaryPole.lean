import GaloisForLFunctions.RHTower.XiHeatCassiniWoldZetaPoleCarrier
import GaloisForLFunctions.RHTower.XiPrimeLogHigherValuationCriticalBoundary

/-!
# Critical-boundary pole of the Route-T Wold current

The valuation-two Euler row is reassembled through the doubled zeta logarithmic derivative.  This
continues the higher-valuation tail across `Re s = 1/2` away from the real prime-square pole.  At a
nontrivial critical-line zeta zero the tail is holomorphic, so the valuation-one current and its
Wold finite difference retain the exact nonzero zeta-zero residue.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Prime-log continuation whose higher-valuation subtraction reaches nonreal critical points. -/
def xiPrimeLogDirichletCriticalContinuation (s : ℂ) : ℂ :=
  infinitePrimeFlux s - xiPrimeLogHigherValuationCriticalContinuation s

theorem xiPrimeLogDirichletCriticalContinuation_eq
    {s : ℂ} (hs : 1 / 2 < s.re) :
    xiPrimeLogDirichletCriticalContinuation s =
      xiPrimeLogDirichletContinuation s := by
  rw [xiPrimeLogDirichletCriticalContinuation, xiPrimeLogDirichletContinuation,
    xiPrimeLogHigherValuationCriticalContinuation_eq hs]

/-- Boundary continuation of the Wold current.  Only the first shift needs the critical model. -/
def xiHeatCassiniWoldCriticalLaplaceContinuation (s : ℂ) : ℂ :=
  xiPrimeLogDirichletCriticalContinuation (s + 1) -
    3 * xiPrimeLogDirichletContinuation (s + 2) +
    3 * xiPrimeLogDirichletContinuation (s + 3) -
    xiPrimeLogDirichletContinuation (s + 4)

/-- The boundary and strict-half-plane Wold continuations agree on their overlap. -/
theorem xiHeatCassiniWoldCriticalLaplaceContinuation_eq
    {s : ℂ} (hs : -1 / 2 < s.re) :
    xiHeatCassiniWoldCriticalLaplaceContinuation s =
      xiHeatCassiniWoldLaplaceContinuation s := by
  have hs1 : 1 / 2 < (s + 1).re := by simp; linarith
  rw [xiHeatCassiniWoldCriticalLaplaceContinuation,
    xiHeatCassiniWoldLaplaceContinuation,
    xiPrimeLogDirichletCriticalContinuation_eq hs1]

/-- At every critical-line zeta zero, removing all higher prime powers preserves residue `-m`. -/
theorem xiPrimeLogDirichletCriticalContinuation_zero_residue
    {rho : ℂ} (hhalf : rho.re = 1 / 2) (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ =>
        (s - rho) * xiPrimeLogDirichletCriticalContinuation s)
        (𝓝[≠] rho) (𝓝 (-(m : ℂ))) := by
  obtain ⟨m, hm, hflux⟩ := neg_logDeriv_zeta_zero_residue hzeta
  refine ⟨m, hm, ?_⟩
  have hlin := tendsto_sub_self_punctured_zero rho
  have htail : Tendsto xiPrimeLogHigherValuationCriticalContinuation
      (𝓝[≠] rho) (𝓝 (xiPrimeLogHigherValuationCriticalContinuation rho)) :=
    (xiPrimeLogHigherValuationCriticalContinuation_differentiableAt_zeta_zero
      hhalf hzeta).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have htail0 := hlin.mul htail
  have hflux' : Tendsto (fun s : ℂ => (s - rho) * infinitePrimeFlux s)
      (𝓝[≠] rho) (𝓝 (-(m : ℂ))) := by
    simpa only [infinitePrimeFlux, logDeriv_apply, neg_div] using hflux
  have hsub := hflux'.sub htail0
  simpa only [xiPrimeLogDirichletCriticalContinuation, mul_sub, zero_mul, sub_zero]
    using hsub

/-- **Critical Wold pole survives.**  At `s = rho - 1`, the first shift has residue `-m(rho)`;
the later shifts remain holomorphic in the Euler half-plane. -/
theorem xiHeatCassiniWoldCriticalLaplaceContinuation_zero_residue
    {rho : ℂ} (hhalf : rho.re = 1 / 2) (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ =>
        (s - (rho - 1)) * xiHeatCassiniWoldCriticalLaplaceContinuation s)
        (𝓝[≠] (rho - 1)) (𝓝 (-(m : ℂ))) := by
  obtain ⟨m, hm, hQ⟩ :=
    xiPrimeLogDirichletCriticalContinuation_zero_residue hhalf hzeta
  refine ⟨m, hm, ?_⟩
  let s0 : ℂ := rho - 1
  let R : ℂ → ℂ := fun s =>
    -3 * xiPrimeLogDirichletContinuation (s + 2) +
      3 * xiPrimeLogDirichletContinuation (s + 3) -
      xiPrimeLogDirichletContinuation (s + 4)
  have hs2 : 1 < (s0 + 2).re := by dsimp only [s0]; simp; linarith
  have hs3 : 1 < (s0 + 3).re := by dsimp only [s0]; simp; linarith
  have hs4 : 1 < (s0 + 4).re := by dsimp only [s0]; simp; linarith
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
  have hR : DifferentiableAt ℂ R s0 := by
    dsimp only [R]
    exact ((h2.const_mul (-3)).add (h3.const_mul 3)).sub h4
  have hRt : Tendsto R (𝓝[≠] s0) (𝓝 (R s0)) :=
    hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hR0 := (tendsto_sub_self_punctured_zero s0).mul hRt
  have hshift : Tendsto (fun s : ℂ => s + 1) (𝓝[≠] s0) (𝓝[≠] rho) := by
    have h := sub_const_punctured_tendsto s0 (-1)
    simpa only [sub_neg_eq_add, s0, sub_add_cancel] using h
  have hQshift := hQ.comp hshift
  have hQshift' : Tendsto (fun s : ℂ =>
      (s - s0) * xiPrimeLogDirichletCriticalContinuation (s + 1))
      (𝓝[≠] s0) (𝓝 (-(m : ℂ))) := by
    exact hQshift.congr' (Filter.Eventually.of_forall fun s => by
      simp only [Function.comp_apply, s0]
      congr 1
      ring)
  have hsum := hQshift'.add hR0
  have hfun : (fun s : ℂ =>
      (s - s0) * xiHeatCassiniWoldCriticalLaplaceContinuation s) =
      fun s : ℂ =>
        (s - s0) * xiPrimeLogDirichletCriticalContinuation (s + 1) +
          (s - s0) * R s := by
    funext s
    rw [xiHeatCassiniWoldCriticalLaplaceContinuation]
    dsimp only [R]
    ring
  rw [hfun]
  simpa only [zero_mul, add_zero, s0] using hsum

end

end RHTower
