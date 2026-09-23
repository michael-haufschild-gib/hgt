import GaloisForLFunctions.HTGeometry.InverseSquareTailSum
import GaloisForLFunctions.HTGeometry.L2PairingLimit

/-!
# Summing the radial channels

Each radial channel contributes a primitive bounded by `B/(c k²)`, uniformly in the endpoint of
integration and in the channel index.  The inverse-square series converges, so the channel bounds
sum to a single bound `2B/c` on the whole radial object.

The order of the two passages is the one used here: sum the channels against a fixed endpoint,
then take the limit of the truncations, then take the supremum over endpoints.  No interchange of
an infinite channel sum with an improper primitive occurs.
-/

noncomputable section

open Filter Topology GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The channel majorant: the `k`-th channel contributes at most `B/(c (k+1)²)`. -/
def channelMajorant (B c : ℝ) (k : ℕ) : ℝ := B / (c * (1 + (k : ℝ)) ^ (2 : ℕ))

theorem channelMajorant_eq (B c : ℝ) (k : ℕ) :
    channelMajorant B c k = B / c * (1 / (1 + (k : ℝ)) ^ (2 : ℕ)) := by
  unfold channelMajorant
  rw [div_mul_eq_div_div_swap]
  ring

theorem channelMajorant_nonneg {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (k : ℕ) :
    0 ≤ channelMajorant B c k := by
  unfold channelMajorant
  positivity

theorem summable_channelMajorant (B : ℝ) {c : ℝ} : Summable (channelMajorant B c) := by
  refine Summable.congr ((summable_inv_sq_shift (σ := 1) one_pos).mul_left (B / c)) ?_
  intro k
  exact (channelMajorant_eq B c k).symm

/-- **The channel majorant sums to `2B/c`.** -/
theorem tsum_channelMajorant_le {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    ∑' k, channelMajorant B c k ≤ 2 * B / c := by
  have hbc : (0 : ℝ) ≤ B / c := by positivity
  have hrw : ∑' k : ℕ, channelMajorant B c k
      = B / c * ∑' k : ℕ, 1 / (1 + (k : ℝ)) ^ (2 : ℕ) := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun k => channelMajorant_eq B c k)
  rw [hrw]
  calc B / c * ∑' k : ℕ, 1 / (1 + (k : ℝ)) ^ (2 : ℕ) ≤ B / c * 2 :=
        mul_le_mul_of_nonneg_left tsum_inv_sq_shift_one_le_two hbc
    _ = 2 * B / c := by ring

/-- **The all-channel primitive bound.**  A channel-by-channel bound `B/(c k²)` on the pairing
against a fixed vector passes to any norm limit of the channel truncations, with the single
constant `2B/c`. -/
theorem norm_inner_le_of_channel_bounds {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c)
    {f : ℕ → E} {x g : E} (hf : Summable f)
    (hC : ∀ k, ‖(inner 𝕜 g (f k) : 𝕜)‖ ≤ channelMajorant B c k)
    (hx : Tendsto (fun n => ∑ k ∈ Finset.range n, f k) atTop (𝓝 x)) :
    ‖(inner 𝕜 g x : 𝕜)‖ ≤ 2 * B / c :=
  le_trans
    (norm_inner_le_tsum_of_tendsto hf (summable_channelMajorant B) hC hx)
    (tsum_channelMajorant_le hB hc)

/-- **The bound is uniform in the endpoint.**  Taking the supremum over endpoints after the two
passages gives the all-radial primitive estimate: a single constant bounds the primitive for every
endpoint at once. -/
theorem iSup_norm_inner_le_of_channel_bounds {B c : ℝ} {ι : Type*} [Nonempty ι]
    (hB : 0 ≤ B) (hc : 0 < c) {f : ι → ℕ → E} {x : ι → E} {g : E}
    (hf : ∀ H, Summable (f H))
    (hC : ∀ H, ∀ k, ‖(inner 𝕜 g (f H k) : 𝕜)‖ ≤ channelMajorant B c k)
    (hx : ∀ H, Tendsto (fun n => ∑ k ∈ Finset.range n, f H k) atTop (𝓝 (x H))) :
    ⨆ H, ‖(inner 𝕜 g (x H) : 𝕜)‖ ≤ 2 * B / c :=
  ciSup_le fun H => norm_inner_le_of_channel_bounds hB hc (hf H) (hC H) (hx H)

end GaloisForLFunctions.RHTower
