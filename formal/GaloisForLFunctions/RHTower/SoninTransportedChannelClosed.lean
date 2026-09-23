import GaloisForLFunctions.RHTower.SoninHilbertSchmidtCompletionFloor
import GaloisForLFunctions.RHTower.SoninCouplingBranchEstimate

/-!
# Transporting a fixed channel along the tower buys nothing

The natural way to make a completion depend on the scale is to carry one fixed channel along the
tower — conjugating it by the dilation that takes one layer to the next.  Dilation is an isometry, so
the transported channel's image is no larger than the original's, and the contribution stays bounded.

The same holds for transport by any contractions on either side.  Since a bounded contribution
sequence already loses the floor, no completion of this shape restores it: the size requirement
cannot be met by moving a fixed operator around.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- A channel conjugated by contractions has image no larger than the channel's own. -/
theorem norm_transported_apply_le {U C V : evenSubspace →L[ℂ] evenSubspace}
    (hU : ∀ x : evenSubspace, ‖U x‖ ≤ ‖x‖) (hV : ∀ x : evenSubspace, ‖V x‖ ≤ ‖x‖)
    (x : evenSubspace) : ‖U (C (V x))‖ ≤ ‖C‖ * ‖x‖ :=
  le_trans (hU _) (le_trans (C.le_opNorm _) (mul_le_mul_of_nonneg_left (hV x) (norm_nonneg C)))

/-- **A fixed channel transported by contractions fails.**  Whatever contractions carry it, the
contribution stays below the channel's norm times the squared vector bound. -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_transported_channel (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (C : evenSubspace →L[ℂ] evenSubspace)
    (U V : ℕ → (evenSubspace →L[ℂ] evenSubspace))
    (hU : ∀ (i : ℕ) (x : evenSubspace), ‖U i x‖ ≤ ‖x‖)
    (hV : ∀ (i : ℕ) (x : evenSubspace), ‖V i x‖ ≤ ‖x‖)
    (v : ℕ → evenSubspace) {W : ℝ} (hv : ∀ i, ‖v i‖ ≤ W) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c
          (fun i => soninShellCutScale b c (Nstart + i) κ) hp
          (fun i => (⟪v i, U i (C (V i (v i)))⟫_ℂ).re) := by
  refine not_bddBelow_soninCompletedPacketValueVar_of_bddAbove_seq N₀ hN₀ a b c q hbc ha hab hb
    haq hqb _ (‖C‖ * W ^ (2 : ℕ)) fun i => ?_
  have h1 : (⟪v i, U i (C (V i (v i)))⟫_ℂ).re ≤ ‖(⟪v i, U i (C (V i (v i)))⟫_ℂ)‖ :=
    Complex.re_le_norm _
  have h2 : ‖(⟪v i, U i (C (V i (v i)))⟫_ℂ)‖ ≤ ‖v i‖ * ‖U i (C (V i (v i)))‖ :=
    norm_inner_le_norm _ _
  have h3 : ‖v i‖ * ‖U i (C (V i (v i)))‖ ≤ ‖v i‖ * (‖C‖ * ‖v i‖) :=
    mul_le_mul_of_nonneg_left (norm_transported_apply_le (hU i) (hV i) (v i)) (norm_nonneg _)
  have h4 : ‖v i‖ * (‖C‖ * ‖v i‖) ≤ ‖C‖ * W ^ (2 : ℕ) := by
    have hsq : ‖v i‖ ^ (2 : ℕ) ≤ W ^ (2 : ℕ) := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg _) (hv i)
    calc ‖v i‖ * (‖C‖ * ‖v i‖) = ‖C‖ * ‖v i‖ ^ (2 : ℕ) := by ring
      _ ≤ ‖C‖ * W ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hsq (norm_nonneg C)
  exact le_trans (le_trans (le_trans h1 h2) h3) h4

/-- **A fixed channel transported by the tower's dilations fails.**  This is the shape a
scale-dependent completion built from one conductor takes, and dilation being an isometry it stays
bounded. -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_dilation_transported (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (C : evenSubspace →L[ℂ] evenSubspace) (p : ℕ → ℝ) (hp : ∀ i, 0 < p i)
    (v : ℕ → evenSubspace) {W : ℝ} (hv : ∀ i, ‖v i‖ ≤ W) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hpc : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c
          (fun i => soninShellCutScale b c (Nstart + i) κ) hpc
          (fun i => (⟪v i, evenDilationCLM (p i) (hp i)
            (C (evenDilationCLM (p i)⁻¹ (inv_pos.mpr (hp i)) (v i)))⟫_ℂ).re) :=
  not_bddBelow_soninCompletedPacketValueVar_of_transported_channel N₀ hN₀ a b c q hbc ha hab hb
    haq hqb C (fun i => evenDilationCLM (p i) (hp i))
    (fun i => evenDilationCLM (p i)⁻¹ (inv_pos.mpr (hp i)))
    (fun i x => le_of_eq (norm_evenDilationCLM_apply (p i) (hp i) x))
    (fun i x => le_of_eq (norm_evenDilationCLM_apply (p i)⁻¹ (inv_pos.mpr (hp i)) x))
    v hv

end RHTower

