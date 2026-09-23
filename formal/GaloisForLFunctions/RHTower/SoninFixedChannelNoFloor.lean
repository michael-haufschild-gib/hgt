import GaloisForLFunctions.RHTower.SoninBurnolCompletionNoFloor
import GaloisForLFunctions.RHTower.SoninBurnolLogShellChannel

/-!
# A fixed channel cannot restore the floor either

Pairing the source packets against one fixed bounded operator gives a per-scale contribution
bounded by the operator norm times the packet energy, and the packet energy is bounded uniformly in
the frequency.  So such a completion is bounded above, while the coupling energy diverges, and the
completed channel stays unbounded below.

In particular the concrete Burnol conductor channel, read at fixed aperture and fixed tower height,
is such an operator.  A completion can only survive by letting the channel itself grow with the
scale.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- The diagonal pairing of the source packets against a fixed operator. -/
def soninFixedChannelContribution (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q : ℝ) (p : ℕ → ℝ)
    (T : evenSubspace →L[ℂ] evenSubspace) (i : ℕ) : ℝ :=
  (⟪soninPacketEven b c hb hbc (2 * Real.pi * (p i * q)),
    T (soninPacketEven b c hb hbc (2 * Real.pi * (p i * q)))⟫_ℂ).re

/-- The pairing is bounded above, uniformly in the scale. -/
theorem soninFixedChannelContribution_le (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q : ℝ)
    (p : ℕ → ℝ) (T : evenSubspace →L[ℂ] evenSubspace) (i : ℕ) :
    soninFixedChannelContribution b c hb hbc q p T i ≤
      ‖T‖ * (2 * ‖soninBumpL2 b c hb hbc‖) ^ (2 : ℕ) := by
  set w : evenSubspace := soninPacketEven b c hb hbc (2 * Real.pi * (p i * q)) with hw
  have hbound : ‖w‖ ≤ 2 * ‖soninBumpL2 b c hb hbc‖ :=
    norm_soninPacketL2_le b c hb hbc (2 * Real.pi * (p i * q))
  have hnn : (0 : ℝ) ≤ 2 * ‖soninBumpL2 b c hb hbc‖ := le_trans (norm_nonneg _) hbound
  have hre : (⟪w, T w⟫_ℂ).re ≤ ‖(⟪w, T w⟫_ℂ)‖ := Complex.re_le_norm _
  have hinner : ‖(⟪w, T w⟫_ℂ)‖ ≤ ‖w‖ * ‖T w‖ := norm_inner_le_norm _ _
  have hop : ‖T w‖ ≤ ‖T‖ * ‖w‖ := T.le_opNorm w
  have hstep : ‖w‖ * ‖T w‖ ≤ ‖T‖ * ‖w‖ ^ (2 : ℕ) := by nlinarith [norm_nonneg w, norm_nonneg (T w)]
  have hsq : ‖w‖ ^ (2 : ℕ) ≤ (2 * ‖soninBumpL2 b c hb hbc‖) ^ (2 : ℕ) := by
    have := norm_nonneg w
    nlinarith
  have hfinal : ‖T‖ * ‖w‖ ^ (2 : ℕ) ≤ ‖T‖ * (2 * ‖soninBumpL2 b c hb hbc‖) ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hsq (norm_nonneg T)
  calc soninFixedChannelContribution b c hb hbc q p T i = (⟪w, T w⟫_ℂ).re := rfl
    _ ≤ ‖(⟪w, T w⟫_ℂ)‖ := hre
    _ ≤ ‖w‖ * ‖T w‖ := hinner
    _ ≤ ‖T‖ * ‖w‖ ^ (2 : ℕ) := hstep
    _ ≤ ‖T‖ * (2 * ‖soninBumpL2 b c hb hbc‖) ^ (2 : ℕ) := hfinal

/-- **No fixed channel restores the floor.**  A completion given by pairing the source packets
against one fixed bounded operator is bounded above, so it leaves the completed channel unbounded
below. -/
theorem not_bddBelow_soninCompletedPacketValueVar_fixedChannel
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) (T : evenSubspace →L[ℂ] evenSubspace) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c (soninCrossingClock a c)
          (one_lt_soninCrossingClock a c)
          (soninFixedChannelContribution b c hb hbc q (soninCrossingClock a c) T) :=
  not_bddBelow_soninCompletedPacketValueVar_of_bddAbove a b c ha hb hab hbc q haq hqb
    (soninFixedChannelContribution b c hb hbc q (soninCrossingClock a c) T)
    (‖T‖ * (2 * ‖soninBumpL2 b c hb hbc‖) ^ (2 : ℕ))
    (fun i => soninFixedChannelContribution_le b c hb hbc q (soninCrossingClock a c) T i)

/-- **The concrete Burnol conductor channel is such a fixed operator.**  Read at one aperture and
one tower height it cannot restore the floor. -/
theorem not_bddBelow_soninCompletedPacketValueVar_logShellConductor
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) (a₀ r₀ : ℝ) (n₀ : ℕ) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c (soninCrossingClock a c)
          (one_lt_soninCrossingClock a c)
          (soninFixedChannelContribution b c hb hbc q (soninCrossingClock a c)
            (soninBurnolLogShellConductor a₀ r₀ n₀)) :=
  not_bddBelow_soninCompletedPacketValueVar_fixedChannel a b c ha hb hab hbc q haq hqb
    (soninBurnolLogShellConductor a₀ r₀ n₀)

end RHTower
