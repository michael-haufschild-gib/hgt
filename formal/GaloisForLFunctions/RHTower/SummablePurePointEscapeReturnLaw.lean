import GaloisForLFunctions.RHTower.SummablePurePointPhaseRecurrence

/-!
# Summable pure-point escape--return law

The finite escape--return principle extends to every countably infinite
phase packet with nonnegative summable weight.  A finite head is synchronized
quantitatively; every remaining mode is paid as an explicit summable tail.

At the resulting budget, either the full infinite packet never exits its
initial neighborhood or an exit is followed strictly later by a return.
No finite ambient spectral dimension is assumed.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Continuous-time phase energy of a countably infinite summable packet. -/
def summablePhaseEnergyAt
    (a omega : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' p, a p *
    ‖Complex.exp
      (Complex.I * (((t * omega p : ℝ) : ℂ))) - 1‖ ^ 2

/-- Head-synchronization plus summable-tail recurrence budget. -/
def summablePhaseRecurrenceBudget
    (a : ℕ → ℝ) (M Q : ℕ) : ℝ :=
  (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
      ∑ p ∈ Finset.range M, a p +
    4 * ∑' p : {p : ℕ // p ∉ Finset.range M}, a p

/-- Continuous-time energy at an integer time is the original discrete
phase energy. -/
theorem summablePhaseEnergyAt_nat_eq
    (a omega : ℕ → ℝ) (n : ℕ) :
    summablePhaseEnergyAt a omega (n : ℝ) =
      summablePhaseEnergy a omega n := by
  rfl

/-- Sampling physical time at multiples of a tick equals rescaling every
frequency by that tick. -/
theorem summablePhaseEnergyAt_nat_mul_tick_eq_scaled
    (a omega : ℕ → ℝ) (n : ℕ) (tick : ℝ) :
    summablePhaseEnergyAt a omega ((n : ℝ) * tick) =
      summablePhaseEnergy a (fun p => tick * omega p) n := by
  unfold summablePhaseEnergyAt summablePhaseEnergy
  apply tsum_congr
  intro p
  congr 3
  push_cast
  ring_nf

/--
Post-exit quantitative recurrence of every nonnegative summable phase
packet.  A finite synchronized head determines the deadline exponent and
the complete infinite tail enters only through the explicit budget.
-/
theorem exists_summablePhaseEnergyAt_postExit_recurrence_quantitative
    (a omega : ℕ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hsum : Summable a) (M Q : ℕ)
    (exitTime guardTime : ℝ)
    (hexitTime : 0 ≤ exitTime) (hguard : 0 < guardTime)
    (hexit :
      summablePhaseRecurrenceBudget a M Q <
        summablePhaseEnergyAt a omega exitTime) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ M ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^ M : ℕ) : ℝ) * (exitTime + guardTime) ∧
      summablePhaseRecurrenceBudget a M Q <
        summablePhaseEnergyAt a omega exitTime ∧
      summablePhaseEnergyAt a omega
          ((n : ℝ) * (exitTime + guardTime)) ≤
        summablePhaseRecurrenceBudget a M Q := by
  let tick : ℝ := exitTime + guardTime
  have htick : 0 < tick := by
    dsimp only [tick]
    linarith
  obtain ⟨n, hn0, hnQ, hreturn⟩ :=
    exists_summablePhaseEnergy_recurrence_quantitative
      a (fun p => tick * omega p) ha hsum M Q
  refine ⟨n, hn0, hnQ, ?_, ?_, hexit, ?_⟩
  · have hn1 : 1 ≤ n :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn0)
    calc
      exitTime < tick := by
        dsimp only [tick]
        linarith
      _ = (1 : ℝ) * tick := by ring
      _ ≤ (n : ℝ) * tick :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn1) htick.le
  · exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hnQ) htick.le
  · rw [summablePhaseRecurrenceBudget,
      summablePhaseEnergyAt_nat_mul_tick_eq_scaled]
    simpa only [tick] using hreturn

/--
**Universal countable pure-point escape--return dichotomy.**

At every finite-head resolution, a nonnegative summable countable phase
packet either stays forever within the guaranteed budget or exits and later
returns within that same budget before the finite-head deadline.
-/
theorem summablePhaseEnergyAt_neverExits_or_postExit_return
    (a omega : ℕ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hsum : Summable a) (M Q : ℕ)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      summablePhaseEnergyAt a omega t ≤
        summablePhaseRecurrenceBudget a M Q) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧ n ≤ (Q + 1) ^ M ∧
      summablePhaseRecurrenceBudget a M Q <
        summablePhaseEnergyAt a omega exitTime ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^ M : ℕ) : ℝ) * (exitTime + guardTime) ∧
      summablePhaseEnergyAt a omega
          ((n : ℝ) * (exitTime + guardTime)) ≤
        summablePhaseRecurrenceBudget a M Q := by
  classical
  by_cases hnever :
      ∀ t : ℝ, 0 ≤ t →
        summablePhaseEnergyAt a omega t ≤
          summablePhaseRecurrenceBudget a M Q
  · exact Or.inl hnever
  · right
    push Not at hnever
    obtain ⟨exitTime, hexitTime, hexit⟩ := hnever
    obtain ⟨n, hn0, hnQ, hpost, hdeadline, _hexit, hreturn⟩ :=
      exists_summablePhaseEnergyAt_postExit_recurrence_quantitative
        a omega ha hsum M Q exitTime guardTime
        hexitTime hguard hexit
    exact
      ⟨exitTime, n, hexitTime, hn0, hnQ, hexit,
        hpost, hdeadline, hreturn⟩

end RHTower
