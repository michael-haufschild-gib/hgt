import GaloisForLFunctions.RHTower.SoninBoundedSequenceCompletionFails

/-!
# A completion built from a bounded operator family

The pairing of a vector with a bounded operator's image is at most the operator norm times the
squared vector norm, so a completion assembled from a uniformly bounded family of operators against
vectors of bounded norm contributes a bounded sequence.

Bounded sequences are already known to leave the packet channel without a floor, so no such
completion restores it.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- The pairings of a bounded family against vectors of bounded norm form a bounded sequence. -/
theorem re_inner_family_le (C : ℕ → (evenSubspace →L[ℂ] evenSubspace)) {B : ℝ}
    (hC : ∀ i, ‖C i‖ ≤ B) (hBnn : 0 ≤ B) (w : ℕ → evenSubspace) {W : ℝ}
    (hw : ∀ i, ‖w i‖ ≤ W) (i : ℕ) : (⟪w i, C i (w i)⟫_ℂ).re ≤ B * W ^ 2 :=
  re_inner_self_le_opNorm_mul_sq (hC i) (hw i) hBnn

/-- **No completion from a bounded operator family restores the floor.** -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_bounded_family (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (C : ℕ → (evenSubspace →L[ℂ] evenSubspace)) {B : ℝ}
    (hC : ∀ i, ‖C i‖ ≤ B) (hBnn : 0 ≤ B) (w : ℕ → evenSubspace) {W : ℝ}
    (hw : ∀ i, ‖w i‖ ≤ W) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c
          (fun i => soninShellCutScale b c (Nstart + i) κ) hp
          (fun i => (⟪w i, C i (w i)⟫_ℂ).re) :=
  not_bddBelow_soninCompletedPacketValueVar_of_bddAbove_seq N₀ hN₀ a b c q hbc ha hab hb haq hqb
    (fun i => (⟪w i, C i (w i)⟫_ℂ).re) (B * W ^ 2)
    (re_inner_family_le C hC hBnn w hw)

end RHTower
