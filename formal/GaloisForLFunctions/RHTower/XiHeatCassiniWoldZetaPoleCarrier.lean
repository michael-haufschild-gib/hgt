import GaloisForLFunctions.RHTower.XiHeatCassiniWoldPrimeZetaLaplaceSymbol
import GaloisForLFunctions.RHTower.XiPrimeLogHigherValuationHalfPlane
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.PrimePolarResidueCancellation

/-!
# Zeta-pole carrier of the Route-T Wold current

The valuation-one prime-log current is continued as the full von Mangoldt logarithmic derivative
minus the holomorphic valuation-`>= 2` tail.  Its four-shift Wold finite difference agrees with the
safe Laplace current on `Re s > 0`.

At a zeta zero `rho` with `Re rho > 1/2`, the first shift has residue `-m(rho)` at `s = rho - 1`.
The other three shifts lie in `Re z > 1` and are holomorphic.  Hence the Wold finite difference
retains the nonzero residue: neither higher prime powers nor the cubic Euler depletion cancels an
off-critical divisor pole.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Prime-zeta derivative and the valuation-one von Mangoldt current agree on their common
half-plane. -/
theorem neg_deriv_coronaPrimeZeta_eq_xiPrimeLogDirichlet
    {s : ℂ} (hs : 1 < s.re) :
    -deriv coronaPrimeZeta s = xiPrimeLogDirichlet s := by
  rw [tsum_neg_deriv_coronaPrimeZeta hs,
    xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow hs]
  apply tsum_congr
  intro p
  rw [coronaPrimeEigenvalue, Complex.cpow_neg, div_eq_mul_inv]

/-- Meromorphic prime-log model: full von Mangoldt flux with all higher valuations removed. -/
def xiPrimeLogDirichletContinuation (s : ℂ) : ℂ :=
  infinitePrimeFlux s - xiPrimeLogHigherValuation s

theorem xiPrimeLogDirichletContinuation_eq
    {s : ℂ} (hs : 1 < s.re) :
    xiPrimeLogDirichletContinuation s = xiPrimeLogDirichlet s := by
  have h := infinitePrimeFlux_eq_primeLog_add_higherValuation hs
  rw [xiPrimeLogDirichletContinuation]
  linear_combination h

/-- Four-shift meromorphic continuation of the Route-T Wold Laplace current. -/
def xiHeatCassiniWoldLaplaceContinuation (s : ℂ) : ℂ :=
  xiPrimeLogDirichletContinuation (s + 1) -
    3 * xiPrimeLogDirichletContinuation (s + 2) +
    3 * xiPrimeLogDirichletContinuation (s + 3) -
    xiPrimeLogDirichletContinuation (s + 4)

/-- The meromorphic Wold model agrees with the exact prime-zeta current on `Re s > 0`. -/
theorem xiHeatCassiniWoldLaplaceContinuation_eq
    {s : ℂ} (hs : 0 < s.re) :
    xiHeatCassiniWoldLaplaceContinuation s =
      xiHeatCassiniWoldLaplaceCurrent s := by
  have hs1 : 1 < (s + 1).re := by simp; linarith
  have hs2 : 1 < (s + 2).re := by simp; linarith
  have hs3 : 1 < (s + 3).re := by simp; linarith
  have hs4 : 1 < (s + 4).re := by simp; linarith
  have h1 := neg_deriv_coronaPrimeZeta_eq_xiPrimeLogDirichlet hs1
  have h2 := neg_deriv_coronaPrimeZeta_eq_xiPrimeLogDirichlet hs2
  have h3 := neg_deriv_coronaPrimeZeta_eq_xiPrimeLogDirichlet hs3
  have h4 := neg_deriv_coronaPrimeZeta_eq_xiPrimeLogDirichlet hs4
  have h1' : deriv coronaPrimeZeta (s + 1) =
      -xiPrimeLogDirichlet (s + 1) := by linear_combination -h1
  have h2' : deriv coronaPrimeZeta (s + 2) =
      -xiPrimeLogDirichlet (s + 2) := by linear_combination -h2
  have h3' : deriv coronaPrimeZeta (s + 3) =
      -xiPrimeLogDirichlet (s + 3) := by linear_combination -h3
  have h4' : deriv coronaPrimeZeta (s + 4) =
      -xiPrimeLogDirichlet (s + 4) := by linear_combination -h4
  have hc1 := xiPrimeLogDirichletContinuation_eq hs1
  have hc2 := xiPrimeLogDirichletContinuation_eq hs2
  have hc3 := xiPrimeLogDirichletContinuation_eq hs3
  have hc4 := xiPrimeLogDirichletContinuation_eq hs4
  rw [xiHeatCassiniWoldLaplaceCurrent_eq_primeZetaDerivFourShift hs,
    xiHeatCassiniWoldLaplaceContinuation, hc1, hc2, hc3, hc4]
  rw [h1', h2', h3', h4']
  ring

theorem differentiableAt_xiPrimeLogDirichletContinuation_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ xiPrimeLogDirichletContinuation s := by
  have hflux : DifferentiableAt ℂ infinitePrimeFlux s := by
    simpa only [infinitePrimeFlux, logDeriv_apply, neg_div] using!
      differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re hs
  exact hflux.sub
    (differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re (by linarith))

/-- The local coordinate centered at a point tends to zero on its punctured neighbourhood. -/
theorem tendsto_sub_self_punctured_zero (a : ℂ) :
    Tendsto (fun s : ℂ => s - a) (𝓝[≠] a) (𝓝 0) := by
  have h := (continuous_id.sub
    (continuous_const : Continuous fun _ : ℂ => a)).tendsto a
  have hm := h.mono_left (nhdsWithin_le_nhds : 𝓝[≠] a ≤ 𝓝 a)
  change Tendsto ((id : ℂ → ℂ) - fun _ : ℂ => a) (𝓝[≠] a) (𝓝 0)
  have heval : ((id : ℂ → ℂ) - fun _ : ℂ => a) a = 0 := by
    change a - a = 0
    ring
  rw [heval] at hm
  exact hm

/-- Removing the holomorphic higher-valuation tail preserves the exact zeta-zero residue. -/
theorem xiPrimeLogDirichletContinuation_zero_residue
    {rho : ℂ} (hrho : 1 / 2 < rho.re) (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ => (s - rho) * xiPrimeLogDirichletContinuation s)
        (𝓝[≠] rho) (𝓝 (-(m : ℂ))) := by
  obtain ⟨m, hm, hflux⟩ := neg_logDeriv_zeta_zero_residue hzeta
  refine ⟨m, hm, ?_⟩
  have hlin := tendsto_sub_self_punctured_zero rho
  have htail : Tendsto (fun s : ℂ => xiPrimeLogHigherValuation s)
      (𝓝[≠] rho) (𝓝 (xiPrimeLogHigherValuation rho)) :=
    (differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re hrho).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have htail0 := hlin.mul htail
  have hflux' : Tendsto (fun s : ℂ => (s - rho) * infinitePrimeFlux s)
      (𝓝[≠] rho) (𝓝 (-(m : ℂ))) := by
    simpa only [infinitePrimeFlux, logDeriv_apply, neg_div] using hflux
  have hsub := hflux'.sub htail0
  simpa only [xiPrimeLogDirichletContinuation, mul_sub, zero_mul, sub_zero] using hsub

/-- **Off-critical Wold pole survives.**  At `s = rho - 1`, only the first prime-log shift is
singular; all later shifts are in the zero-free Euler half-plane.  Residue remains `-m(rho)`. -/
theorem xiHeatCassiniWoldLaplaceContinuation_zero_residue
    {rho : ℂ} (hrho : 1 / 2 < rho.re) (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ =>
        (s - (rho - 1)) * xiHeatCassiniWoldLaplaceContinuation s)
        (𝓝[≠] (rho - 1)) (𝓝 (-(m : ℂ))) := by
  obtain ⟨m, hm, hQ⟩ :=
    xiPrimeLogDirichletContinuation_zero_residue hrho hzeta
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
    exact (differentiableAt_xiPrimeLogDirichletContinuation_of_one_lt_re
      (s := s0 + (2 : ℂ)) hs2).comp s0
      (show DifferentiableAt ℂ (fun s : ℂ => s + (2 : ℂ)) s0 by fun_prop)
  have h3 : DifferentiableAt ℂ
      (fun s : ℂ => xiPrimeLogDirichletContinuation (s + (3 : ℂ))) s0 := by
    change DifferentiableAt ℂ
      (xiPrimeLogDirichletContinuation ∘ fun s : ℂ => s + (3 : ℂ)) s0
    exact (differentiableAt_xiPrimeLogDirichletContinuation_of_one_lt_re
      (s := s0 + (3 : ℂ)) hs3).comp s0
      (show DifferentiableAt ℂ (fun s : ℂ => s + (3 : ℂ)) s0 by fun_prop)
  have h4 : DifferentiableAt ℂ
      (fun s : ℂ => xiPrimeLogDirichletContinuation (s + (4 : ℂ))) s0 := by
    change DifferentiableAt ℂ
      (xiPrimeLogDirichletContinuation ∘ fun s : ℂ => s + (4 : ℂ)) s0
    exact (differentiableAt_xiPrimeLogDirichletContinuation_of_one_lt_re
      (s := s0 + (4 : ℂ)) hs4).comp s0
      (show DifferentiableAt ℂ (fun s : ℂ => s + (4 : ℂ)) s0 by fun_prop)
  have hR : DifferentiableAt ℂ R s0 := by
    dsimp only [R]
    exact ((h2.const_mul (-3)).add (h3.const_mul 3)).sub h4
  have hRt : Tendsto R (𝓝[≠] s0) (𝓝 (R s0)) :=
    hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlin := tendsto_sub_self_punctured_zero s0
  have hR0 := hlin.mul hRt
  have hshift : Tendsto (fun s : ℂ => s + 1) (𝓝[≠] s0) (𝓝[≠] rho) := by
    have h := sub_const_punctured_tendsto s0 (-1)
    simpa only [sub_neg_eq_add, s0, sub_add_cancel] using h
  have hQshift := hQ.comp hshift
  have hQshift' : Tendsto (fun s : ℂ =>
      (s - s0) * xiPrimeLogDirichletContinuation (s + 1))
      (𝓝[≠] s0) (𝓝 (-(m : ℂ))) := by
    exact hQshift.congr' (Filter.Eventually.of_forall fun s => by
      simp only [Function.comp_apply, s0]
      congr 1
      ring)
  have hsum := hQshift'.add hR0
  have hfun : (fun s : ℂ =>
      (s - s0) * xiHeatCassiniWoldLaplaceContinuation s) =
      fun s : ℂ =>
        (s - s0) * xiPrimeLogDirichletContinuation (s + 1) +
          (s - s0) * R s := by
    funext s
    rw [xiHeatCassiniWoldLaplaceContinuation]
    dsimp only [R]
    ring
  rw [hfun]
  simpa only [zero_mul, add_zero, s0] using hsum

end

end RHTower
