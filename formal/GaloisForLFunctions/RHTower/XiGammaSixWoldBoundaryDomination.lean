import GaloisForLFunctions.RHTower.XiGammaSixFilteredBoundaryControl
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldHolonomyLogSmooth

/-!
# Gamma-six boundary / Wold log-smooth domination

The Heat--Cassini route supplies a genuine source-selected residual whose activation--Fisher
energy lies in every prime-log graph domain. The Gamma-six route supplies the literal nonnegative
second boundary Hessian of the coefficient-faithful filtered prime trace. This module tests the
strongest honest coefficientwise bridge between them.

At neutral grade the Gamma Hessian vanishes prime by prime, so every Wold graph energy dominates
it. Off neutral grade the Gamma Hessian contains a fixed positive harmonic-prime tail, while the
Wold graph energy is summable. Hence domination is impossible. The result is a new cross-corpus
RH endpoint and an exact obstruction: sharing activation--Fisher density is insufficient; a
source theorem proving the domination must itself annihilate the retained horizontal grade.
-/

namespace RHTower

noncomputable section

/-- Genuine all-log-smooth Wold/Fisher source energy at one ordinary prime. -/
def xiHeatCassiniWoldGammaSixBoundaryMajorant
    (k : ℕ) (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) ^ (2 * k) * primeActivationOccupancyFisherDensity p *
    xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2

theorem xiHeatCassiniWoldGammaSixBoundaryMajorant_nonneg
    (k : ℕ) (p : Nat.Primes) :
    0 ≤ xiHeatCassiniWoldGammaSixBoundaryMajorant k p := by
  rw [xiHeatCassiniWoldGammaSixBoundaryMajorant]
  exact mul_nonneg
    (mul_nonneg (by positivity) (primeActivationOccupancyFisherDensity_pos' p).le)
    (sq_nonneg _)

/-- Every Wold/Fisher candidate majorant is absolutely summable. -/
theorem summable_xiHeatCassiniWoldGammaSixBoundaryMajorant (k : ℕ) :
    Summable (xiHeatCassiniWoldGammaSixBoundaryMajorant k) := by
  change Summable (fun p : Nat.Primes =>
    Real.log (p : ℝ) ^ (2 * k) * primeActivationOccupancyFisherDensity p *
      xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2)
  exact summable_xiHeatCassiniPrimeWoldResidual_activationFisherLogPowEnergy k

/-- Coefficient-faithful cross-route producer target: the Wold source energy controls the literal
Gamma-six boundary Hessian without relabelling primes or averaging fibres. -/
def XiGammaSixBoundaryWoldDominated
    (m : ℕ) (q : XiZeroCopy) (k : ℕ) : Prop :=
  ∀ p : Nat.Primes,
    gammaSixFilteredBoundarySecondJet m q p ≤
      xiHeatCassiniWoldGammaSixBoundaryMajorant k p

/-- **Cross-corpus classification.** Wold/Fisher domination of the exact Gamma boundary Hessian
holds precisely at neutral horizontal grade. -/
theorem xiGammaSixBoundaryWoldDominated_iff_centeredRate_eq_zero
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (k : ℕ) :
    XiGammaSixBoundaryWoldDominated m q k ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  constructor
  · intro hdom
    apply (exists_summable_majorant_gammaSixFilteredBoundarySecondJet_iff hm q).1
    exact ⟨xiHeatCassiniWoldGammaSixBoundaryMajorant k,
      summable_xiHeatCassiniWoldGammaSixBoundaryMajorant k, hdom⟩
  · intro hrate p
    calc
      gammaSixFilteredBoundarySecondJet m q p = 0 := by
        rw [gammaSixFilteredBoundarySecondJet_eq_factorized hm q p, hrate]
        norm_num
      _ ≤ xiHeatCassiniWoldGammaSixBoundaryMajorant k p :=
        xiHeatCassiniWoldGammaSixBoundaryMajorant_nonneg k p

/-- Quantitative failed-bridge theorem: off neutral grade, some finite prime subset has more Gamma
boundary mass than the same Wold graph energy plus any prescribed reserve. -/
theorem exists_finset_gammaSixBoundary_sum_gt_wold_sum_add
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy)
    (hq : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) (k : ℕ) (C : ℝ) :
    ∃ F : Finset Nat.Primes,
      (∑ p ∈ F, xiHeatCassiniWoldGammaSixBoundaryMajorant k p) + C <
        ∑ p ∈ F, gammaSixFilteredBoundarySecondJet m q p := by
  let W : ℝ := ∑' p, xiHeatCassiniWoldGammaSixBoundaryMajorant k p
  obtain ⟨F, hF⟩ :=
    exists_finset_gammaSixFilteredBoundarySecondJet_sum_gt hm q hq (W + C)
  refine ⟨F, ?_⟩
  have hW : ∑ p ∈ F, xiHeatCassiniWoldGammaSixBoundaryMajorant k p ≤ W :=
    (summable_xiHeatCassiniWoldGammaSixBoundaryMajorant k).sum_le_tsum F
      (fun p _ => xiHeatCassiniWoldGammaSixBoundaryMajorant_nonneg k p)
  linarith

/-- Universal coefficient-faithful Wold domination is exactly RH. -/
theorem forall_xiGammaSixBoundaryWoldDominated_iff_riemannHypothesis
    {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    (∀ q : XiZeroCopy, XiGammaSixBoundaryWoldDominated m q k) ↔
      RiemannHypothesis := by
  constructor
  · intro hdom
    apply (forall_sourceNaturalBoundaryControl_iff_riemannHypothesis hm).1
    intro q
    apply (sourceNaturalBoundaryControl_iff_summable hm q).2
    apply (summable_gammaSixFilteredBoundarySecondJet_iff_centeredRate_eq_zero hm q).2
    exact (xiGammaSixBoundaryWoldDominated_iff_centeredRate_eq_zero hm q k).1 (hdom q)
  · intro hRH q
    apply (xiGammaSixBoundaryWoldDominated_iff_centeredRate_eq_zero hm q k).2
    have hcontrol :=
      (forall_sourceNaturalBoundaryControl_iff_riemannHypothesis hm).2 hRH q
    exact (summable_gammaSixFilteredBoundarySecondJet_iff_centeredRate_eq_zero hm q).1
      ((sourceNaturalBoundaryControl_iff_summable hm q).1 hcontrol)

end

end RHTower
