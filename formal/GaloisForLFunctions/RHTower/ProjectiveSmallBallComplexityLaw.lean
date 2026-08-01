import GaloisForLFunctions.RHTower.StaticChoiPhaseTargetEntropy
import GaloisForLFunctions.RHTower.StaticChoiPhaseDensity

/-!
# Projective small-ball complexity law

Worst-target small-ball probability is the exact concentration resource needed
for circuit-complexity lower bounds.  This file packages the unconditional
minimax-to-dictionary implication without assuming Haar randomness or a design.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- Pullback of a closed metric ball under a state-valued random variable. -/
def randomMetricBallTarget
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    (state : Ω → X) (center : X) (ε : ℝ) : Set Ω :=
  {ω | dist (state ω) center ≤ ε}

/-- Uniform worst-target small-ball bound for a state ensemble. -/
def HasProjectiveSmallBallBound
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    (μ : Measure Ω) (state : Ω → X) (ε q : ℝ) : Prop :=
  ∀ center, μ.real (randomMetricBallTarget state center ε) ≤ q

/-- A finite target dictionary pays only its cardinality against a uniform
small-ball bound. -/
theorem measureReal_iUnion_randomMetricBallTarget_le
    {Ω X κ : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X] [Fintype κ]
    (μ : Measure Ω) (state : Ω → X) (target : κ → X) {ε q : ℝ}
    (hsmall : HasProjectiveSmallBallBound μ state ε q) :
    μ.real (⋃ k, randomMetricBallTarget state (target k) ε) ≤
      (Fintype.card κ : ℝ) * q := by
  calc
    μ.real (⋃ k, randomMetricBallTarget state (target k) ε) ≤
        ∑ k, μ.real (randomMetricBallTarget state (target k) ε) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : κ, q := by
      exact Finset.sum_le_sum fun k _hk ↦ hsmall (target k)
    _ = (Fintype.card κ : ℝ) * q := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- For circuits padded by an identity label, the low-complexity probability
is bounded by `|gate|^(s+1)` times worst-target small-ball probability. -/
theorem measureReal_iUnion_paddedCircuitSmallBall_le
    {Ω X gate : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    [Fintype gate]
    (μ : Measure Ω) (state : Ω → X) (s : ℕ)
    (target : PaddedCircuitWord gate s → X) {ε q : ℝ}
    (hsmall : HasProjectiveSmallBallBound μ state ε q) :
    μ.real (⋃ w, randomMetricBallTarget state (target w) ε) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) * q := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    (measureReal_iUnion_randomMetricBallTarget_le
      μ state target hsmall)

/-- Any prescribed failure budget follows once circuit-dictionary entropy
times the worst-target mass fits inside that budget. -/
theorem measureReal_iUnion_paddedCircuitSmallBall_le_of_budget
    {Ω X gate : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    [Fintype gate]
    (μ : Measure Ω) (state : Ω → X) (s : ℕ)
    (target : PaddedCircuitWord gate s → X) {ε q failure : ℝ}
    (hsmall : HasProjectiveSmallBallBound μ state ε q)
    (hbudget : (Fintype.card gate : ℝ) ^ (s + 1) * q ≤ failure) :
    μ.real (⋃ w, randomMetricBallTarget state (target w) ε) ≤ failure :=
  (measureReal_iUnion_paddedCircuitSmallBall_le
    μ state s target hsmall).trans hbudget

end RHTower
