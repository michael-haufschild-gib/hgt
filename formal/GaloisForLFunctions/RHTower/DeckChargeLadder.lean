/-
The additive deck charge on the ξ ladder.

The abstract charge `wCharge (2^k)` of `DeckChargeCalculus`, applied to the vanishing order of a
right-half ξ-zero, is the ladder invariant: the `RH_{2^k}` rung holds exactly when every such zero
carries trivial rung-`k` charge (`rhLadder_iff_ladderCharge_zero`).  Reflection symmetry makes the
charge blind up to the symmetry depth (`wCharge_invisible_below_reflection_depth`) — the additive
statement of why globally symmetric charge counts are too coarse and a quadrant-local detector is
needed.
-/
import GaloisForLFunctions.RHTower.DeckChargeCalculus
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.FoldonFrustration

open Complex

namespace RHTower

/-- The additive deck charge of a right-half ξ-zero: the rung-`k` charge of its vanishing order. -/
noncomputable def ladderCharge (k : ℕ) (ρ : ℂ) : ZMod (2 ^ k) :=
  wCharge (2 ^ k) ((analyticOrderAt xi ρ).toNat : ℤ)

/-- **The RH ladder is vanishing of the additive charge.**  Rung `k` (`RH_{2^k}`: every right-half
ξ-zero has order divisible by `2^k`) holds exactly when every right-half ξ-zero carries trivial
rung-`k` deck charge.  This reads the whole multiplicity-parity ladder through the additive
deck-charge calculus. -/
theorem rhLadder_iff_ladderCharge_zero (k : ℕ) :
    RHLadder k ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 → ladderCharge k ρ = 0 := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rw [rhLadder_iff_toNat_dvd]
  refine forall₃_congr fun ρ _ _ => ?_
  rw [ladderCharge, wCharge_eq_zero_iff, Int.natCast_dvd_natCast]

/-- **Reflection-symmetry blindness, additive form.**  A configuration of off-line zeros invariant
under a free action of a reflection group of order `2^k` (matching multiplicities) carries trivial
rung-`j` charge for every `j ≤ k`: the additive deck charge is blind to a reflection-symmetric
frustration up to its symmetry depth.  Globally symmetric charge counts are therefore too coarse to
detect off-line buckling — the exact obstruction that forces genuinely quadrant-local detectors. -/
theorem wCharge_invisible_below_reflection_depth {G α : Type*} [Group G] [Fintype G]
    [Fintype α] [MulAction G α] [DecidableEq α] {k : ℕ} (hcard : Fintype.card G = 2 ^ k)
    (hfree : ∀ (g : G) (a : α), g • a = a → g = 1)
    (m : α → ℕ) (hm : ∀ (g : G) (a : α), m (g • a) = m a) {j : ℕ} (hj : j ≤ k) :
    wCharge (2 ^ j) (foldonFrustration Finset.univ m) = 0 := by
  haveI : NeZero (2 ^ j) := ⟨pow_ne_zero j (by norm_num)⟩
  rw [wCharge_eq_zero_iff_deckRed_eq_one]
  exact frustration_invisible_below_reflection_depth hcard hfree m hm hj

/-- **A single `2^k`-orbit is first seen at rung `k+1`, additively.**  A reflection orbit of size
`2^k` has charge `0` at every rung `≤ k` and nonzero charge at rung `k+1` (there the multiplicative
class is `-1`): the exact resolution the additive ladder needs to detect a symmetry-depth-`k`
frustration. -/
theorem wCharge_orbit_first_visible (k : ℕ) :
    (∀ j ≤ k, wCharge (2 ^ j) ((2 : ℤ) ^ k) = 0) ∧ deckRed (2 ^ (k + 1)) ((2 : ℤ) ^ k) = -1 := by
  refine ⟨fun j hj => ?_, deckRed_two_pow_next_visible k⟩
  haveI : NeZero (2 ^ j) := ⟨pow_ne_zero j (by norm_num)⟩
  rw [wCharge_eq_zero_iff_deckRed_eq_one]
  exact deckRed_eq_one_below_depth k dvd_rfl hj

end RHTower
