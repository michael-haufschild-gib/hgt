import GaloisForLFunctions.RHTower.ConnesTateFiniteStage
import GaloisForLFunctions.RHTower.ConnesTateLocalZeta

/-!
# The infinite Tate factorization as a limit of finite stages

Appendix I Lemma 1 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  *"one has to control an infinite product of local terms, given locally by `(25)`... Thus the
  convergence for `σ > 1` is the same as for the zeta function."*

The idele group is the increasing union of the open subgroups `J_S = ∏_{v ∈ S} k_v^* ×
∏_{v ∉ S} R_v^*`, and on `J_S` the Haar measure is the product of the local ones (the omitted
factors having mass one).  So the global Tate integral of a tensor test function is, by monotone
convergence along the directed system of finite `S`, the limit of the finite-stage integrals of
`ConnesTateFiniteStage`.  That limit is what this file identifies: it is the Euler product, hence
`ζ(s)` for `Χ_0 = 1`.  No restricted-product measure has to be constructed — the finite stages are
the honest approximants and their limit is the global value.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The finite-stage Tate integral, indexed by a finite set of primes. -/
def connesTateStageIntegral (S : Finset Nat.Primes) (w : Nat.Primes → ℂ) : ℂ :=
  ∫ x : (i : ↥S) → ℚ_[((i : ↥S) : Nat.Primes)]ˣ,
    ∏ i : ↥S, connesPadicRadial (((i : ↥S) : Nat.Primes) : ℕ)
      (connesPadicUnitBallProfile (w ((i : ↥S) : Nat.Primes))) (x i)
    ∂(Measure.pi fun i : ↥S =>
        fieldOnePadicMultiplicativeHaar (((i : ↥S) : Nat.Primes) : ℕ))

theorem connesTateStageIntegral_eq (S : Finset Nat.Primes) {w : Nat.Primes → ℂ}
    (hw : ∀ p : Nat.Primes, ‖w p‖ < 1) :
    connesTateStageIntegral S w = ∏ p ∈ S, (1 - w p)⁻¹ := by
  rw [connesTateStageIntegral,
    connes_tate_finiteStage_prod (ι := ↥S) (fun i => (i : Nat.Primes))
      (fun i => w ((i : ↥S) : Nat.Primes)) (fun i => hw _)]
  exact Finset.prod_coe_sort S (fun p => (1 - w p)⁻¹)

/-- **Appendix I Lemma 1, infinite factorization.**  Whenever the local Euler factors have a
convergent infinite product, the finite-stage Tate integrals converge to it. -/
theorem connes_tate_stage_tendsto {w : Nat.Primes → ℂ} (hw : ∀ p : Nat.Primes, ‖w p‖ < 1)
    {L : ℂ} (hL : HasProd (fun p : Nat.Primes => (1 - w p)⁻¹) L) :
    Tendsto (fun S : Finset Nat.Primes => connesTateStageIntegral S w) atTop (𝓝 L) := by
  refine hL.congr fun S => ?_
  exact (connesTateStageIntegral_eq S hw).symm

/-- **Appendix I Lemma 1 for `k = ℚ`, `Χ_0 = 1`.**  The finite-stage Tate zeta integrals converge
to `ζ(s)` on the half-plane of absolute convergence: Connes' *"the convergence for `σ > 1` is the
same as for the zeta function"*. -/
theorem connes_tate_stage_tendsto_zeta {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun S : Finset Nat.Primes =>
        connesTateStageIntegral S (fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s)))
      atTop (𝓝 (riemannZeta s)) := by
  refine connes_tate_stage_tendsto ?_ (riemannZeta_eulerProduct_hasProd hs)
  intro p
  exact connes_padic_norm_cpow_neg_lt_one (p : ℕ) (lt_trans zero_lt_one hs)

end

end GaloisForLFunctions.RHTower
