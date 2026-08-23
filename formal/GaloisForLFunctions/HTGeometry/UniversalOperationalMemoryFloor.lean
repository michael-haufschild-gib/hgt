import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Universal operational memory floor

This file treats an operational theory only through its states, effects, and
the probabilities with which effects respond to states.  A channel carries
states forward and effects backward, with exact Schrödinger--Heisenberg
duality.  No Hilbert space, dimension, spectrum, norm, reversibility, or
closed-system assumption is used.

The supremum response gap over all physical effects is contractive under
every such channel.  Along every pair of trajectories it therefore converges
to one exact asymptotic memory floor.  The floor gives an exhaustive
forgetting/persistence dichotomy, while the complementary information loss
is monotone.  This is the operational arrow available without thermodynamic
or gravitational input.
-/

open Filter
open scoped ENNReal Topology

noncomputable section

namespace RHTower

/- `State` and `Effect` carry independent universes: a theory may have small
states and large effects.  The `checkUnivs` heuristic sees only their `max` in
the structure universe and cannot see the fields that separate them. -/
set_option linter.checkUnivs false in
/-- An operational physical theory: states, effects, and effect
probabilities.  Probability bounds are the only numerical structure used. -/
structure OperationalTheory where
  State : Type*
  Effect : Type*
  probability : Effect → State → ℝ
  probability_nonneg : ∀ e ρ, 0 ≤ probability e ρ
  probability_le_one : ∀ e ρ, probability e ρ ≤ 1

/-- A channel in an operational theory.  `pullback` is the Heisenberg
evolution of effects and `probability_after` is exact
Schrödinger--Heisenberg duality. -/
structure OperationalTheory.Channel (Q : OperationalTheory) where
  evolve : Q.State → Q.State
  pullback : Q.Effect → Q.Effect
  probability_after :
    ∀ e ρ, Q.probability e (evolve ρ) =
      Q.probability (pullback e) ρ

/-- Maximum distinguishability of two states by any physical effect. -/
def OperationalTheory.distance (Q : OperationalTheory)
    (ρ σ : Q.State) : ℝ≥0∞ :=
  ⨆ e : Q.Effect,
    ENNReal.ofReal |Q.probability e ρ - Q.probability e σ|

/-- Operational distinguishability is finite and at most one. -/
theorem OperationalTheory.distance_le_one (Q : OperationalTheory)
    (ρ σ : Q.State) :
    Q.distance ρ σ ≤ 1 := by
  apply iSup_le
  intro e
  rw [ENNReal.ofReal_le_one]
  rw [abs_sub_le_iff]
  constructor <;>
    linarith [Q.probability_nonneg e ρ, Q.probability_le_one e ρ,
      Q.probability_nonneg e σ, Q.probability_le_one e σ]

/-- Operational distinguishability is symmetric. -/
theorem OperationalTheory.distance_comm (Q : OperationalTheory)
    (ρ σ : Q.State) :
    Q.distance ρ σ = Q.distance σ ρ := by
  simp only [OperationalTheory.distance, abs_sub_comm]

/-- Data processing in its maximally abstract operational form: every
channel contracts the supremum response gap. -/
theorem OperationalTheory.Channel.distance_evolve_le
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State) :
    Q.distance (Φ.evolve ρ) (Φ.evolve σ) ≤ Q.distance ρ σ := by
  apply iSup_le
  intro e
  rw [Φ.probability_after e ρ, Φ.probability_after e σ]
  exact le_iSup
    (fun f : Q.Effect =>
      ENNReal.ofReal |Q.probability f ρ - Q.probability f σ|)
    (Φ.pullback e)

/-- Operational distinguishability after `n` repetitions of a channel. -/
def OperationalTheory.Channel.distanceAt
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State)
    (n : ℕ) : ℝ≥0∞ :=
  Q.distance (Φ.evolve^[n] ρ) (Φ.evolve^[n] σ)

/-- Repeating any channel makes operational distinguishability antitone. -/
theorem OperationalTheory.Channel.distanceAt_antitone
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State) :
    Antitone (Φ.distanceAt ρ σ) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [Nat.add_one]
  simp only [OperationalTheory.Channel.distanceAt,
    Function.iterate_succ_apply']
  exact Φ.distance_evolve_le _ _

/-- Exact residual memory after arbitrarily many repetitions of a channel. -/
def OperationalTheory.Channel.memoryFloor
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State) : ℝ≥0∞ :=
  ⨅ n : ℕ, Φ.distanceAt ρ σ n

/-- Universal open-system memory law: for every operational theory, every
channel, and every pair of states, distinguishability converges to one exact
asymptotic floor. -/
theorem OperationalTheory.Channel.tendsto_distanceAt_memoryFloor
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State) :
    Tendsto (Φ.distanceAt ρ σ) atTop
      (𝓝 (Φ.memoryFloor ρ σ)) := by
  exact tendsto_atTop_iInf (Φ.distanceAt_antitone ρ σ)

/-- Complete forgetting is exactly the zero-floor phase. -/
theorem OperationalTheory.Channel.memoryFloor_eq_zero_iff
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State) :
    Φ.memoryFloor ρ σ = 0 ↔
      Tendsto (Φ.distanceAt ρ σ) atTop (𝓝 0) := by
  constructor
  · intro h
    simpa [h] using Φ.tendsto_distanceAt_memoryFloor ρ σ
  · intro h
    exact tendsto_nhds_unique
      (Φ.tendsto_distanceAt_memoryFloor ρ σ) h

/-- Persistent memory is exactly a strictly positive uniform lower bound on
all future operational distinguishabilities. -/
theorem OperationalTheory.Channel.memoryFloor_pos_iff
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State) :
    0 < Φ.memoryFloor ρ σ ↔
      ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ n, ε ≤ Φ.distanceAt ρ σ n := by
  constructor
  · intro h
    refine ⟨Φ.memoryFloor ρ σ, h, fun n => ?_⟩
    exact iInf_le (fun k : ℕ => Φ.distanceAt ρ σ k) n
  · rintro ⟨ε, hε, hbound⟩
    exact lt_of_lt_of_le hε (le_iInf hbound)

/-- The memory floor never exceeds distinguishability at any finite time. -/
theorem OperationalTheory.Channel.memoryFloor_le_distanceAt
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State) (n : ℕ) :
    Φ.memoryFloor ρ σ ≤ Φ.distanceAt ρ σ n :=
  iInf_le _ n

/-- Operational information irreversibly lost by time `n`. -/
def OperationalTheory.Channel.informationLossAt
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State)
    (n : ℕ) : ℝ≥0∞ :=
  Φ.distanceAt ρ σ 0 - Φ.distanceAt ρ σ n

/-- The channel-induced operational information loss is monotone: no later
application can restore distinguishability already removed from the entire
physical effect set. -/
theorem OperationalTheory.Channel.informationLossAt_monotone
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State) :
    Monotone (Φ.informationLossAt ρ σ) := by
  intro n m hnm
  exact tsub_le_tsub_left (Φ.distanceAt_antitone ρ σ hnm)
    (Φ.distanceAt ρ σ 0)

/-- A contractive observer whose operational distinguishability returns to
its initial value along a cofinal subsequence loses no distinguishability at
any finite depth.  Recurrence and data processing must use this same
operational clock; recurrence of a separate scalar observable is insufficient. -/
theorem OperationalTheory.Channel.distanceAt_eq_initial_of_subseq_return
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hreturn : Tendsto (fun j => Φ.distanceAt ρ σ (φ j)) atTop
      (𝓝 (Φ.distanceAt ρ σ 0))) (n : ℕ) :
    Φ.distanceAt ρ σ n = Φ.distanceAt ρ σ 0 := by
  refine le_antisymm (Φ.distanceAt_antitone ρ σ (Nat.zero_le n)) ?_
  refine le_of_tendsto hreturn ?_
  filter_upwards [eventually_ge_atTop n] with j hj
  exact Φ.distanceAt_antitone ρ σ (le_trans hj hφ.le_apply)

/-- Clock-locked recurrent dilation rigidity in operational form: once the
same observer trajectory returns cofinally to its initial distinguishability,
its monotone information-loss ledger is identically zero. -/
theorem OperationalTheory.Channel.informationLossAt_eq_zero_of_subseq_return
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hreturn : Tendsto (fun j => Φ.distanceAt ρ σ (φ j)) atTop
      (𝓝 (Φ.distanceAt ρ σ 0))) (n : ℕ) :
    Φ.informationLossAt ρ σ n = 0 := by
  rw [OperationalTheory.Channel.informationLossAt,
    Φ.distanceAt_eq_initial_of_subseq_return ρ σ hφ hreturn n,
    tsub_self]

/-- Exact two-phase law for every pair of trajectories: either the channel
forgets them completely, or a positive amount of operational
distinguishability survives at every future time. -/
theorem OperationalTheory.Channel.forgetting_or_persistent_memory
    {Q : OperationalTheory} (Φ : Q.Channel) (ρ σ : Q.State) :
    Tendsto (Φ.distanceAt ρ σ) atTop (𝓝 0) ∨
      ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ n, ε ≤ Φ.distanceAt ρ σ n := by
  by_cases hzero : Φ.memoryFloor ρ σ = 0
  · exact Or.inl ((Φ.memoryFloor_eq_zero_iff ρ σ).mp hzero)
  · exact Or.inr ((Φ.memoryFloor_pos_iff ρ σ).mp
      (bot_lt_iff_ne_bot.mpr hzero))

end RHTower
