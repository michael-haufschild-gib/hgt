import GaloisForLFunctions.RHTower.SoninChannelHeightUniform
import GaloisForLFunctions.RHTower.SoninScaledPacketHighTailBound

/-!
# The frequency-side channel on a rescaled packet does not grow with the tower height

A rescaled packet's spectral mass above twice its carrier is a power tail at every order, so the
height-uniform bound applies to it.  Written with a natural exponent, the tail is a constant over the
radius to the power `2N-1`, which is exactly the decay the outer shells need.

The consequence is that a completion using the frequency-side channel gains nothing by taking the
tower taller: on a rescaled packet the channel's norm is bounded by the largest layer logarithm below
the cut, plus a term geometric in the cut index, and neither mentions the height.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- A physical cutoff's defect after the transform is the frequency cutoff's defect before it. -/
theorem norm_sub_evenIndicatorCutoff_evenFourierTransform (t : ℝ) (w : evenSubspace) :
    ‖evenFourierTransform w - evenIndicatorCutoff t (evenFourierTransform w)‖ =
      ‖w - evenFourierCutoff t w‖ := by
  have hR : evenFourierCutoff t w =
      evenFourierTransform (evenIndicatorCutoff t (evenFourierTransform w)) := by
    rw [evenFourierCutoff_eq_reflectedCutoff t]
    rfl
  have hw : w = evenFourierTransform (evenFourierTransform w) :=
    (evenFourierTransform_involutive w).symm
  calc ‖evenFourierTransform w - evenIndicatorCutoff t (evenFourierTransform w)‖
      = ‖evenFourierTransform (evenFourierTransform w -
          evenIndicatorCutoff t (evenFourierTransform w))‖ :=
        (evenFourierTransform_isometry _).symm
    _ = ‖w - evenFourierCutoff t w‖ := by rw [map_sub, hR, ← hw]

/-- **The packet's spectral tail with a natural exponent.**  Above twice the carrier the mass a
rescaled packet leaves outside a ball is a constant over the radius to the power `2N-1`. -/
theorem exists_norm_sq_sub_evenFourierCutoff_soninScaledPacketEven_le_div (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m δ w t : ℝ) (hδ : 0 < δ), 0 < w → 2 * w ≤ t →
      |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1 →
        ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ -
            evenFourierCutoff t (soninScaledPacketEven m δ (2 * Real.pi * w) hδ)‖ ^ 2 ≤
          (2 * (K * δ ^ 2 / δ ^ (2 * N)) / ((2 * N : ℝ) - 1)) / t ^ (2 * N - 1) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_sq_sub_evenFourierCutoff_soninScaledPacketEven_le N hN
  refine ⟨K, hK0, ?_⟩
  intro m δ w t hδ hw ht hmean
  have htpos : (0 : ℝ) < t := by linarith
  have h1 : 1 ≤ 2 * N := by omega
  have hq : ((2 * N - 1 : ℕ) : ℝ) = 2 * (N : ℝ) - 1 := by
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hrpow : t ^ (1 - (2 * N : ℝ)) = (t ^ (2 * N - 1 : ℕ))⁻¹ := by
    have hneg : (1 : ℝ) - (2 * N : ℝ) = -((2 * N - 1 : ℕ) : ℝ) := by rw [hq]; ring
    rw [hneg, Real.rpow_neg htpos.le, Real.rpow_natCast]
  refine le_trans (hK m δ w t hδ hw ht hmean) (le_of_eq ?_)
  rw [hrpow, div_eq_mul_inv]
  ring

/-- **The frequency-side channel on a rescaled packet, uniformly in the tower height.**  With the
cut placed past twice the carrier, the channel's norm is the largest layer logarithm below the cut
against the packet's own mass, plus a term geometric in the cut index — and the tower's height
appears nowhere. -/
theorem exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le (N : ℕ) (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a r : ℝ), 0 < a → 1 < r → ∀ (n Kc : ℕ) (m δ w M : ℝ) (hδ : 0 < δ),
      0 < w → |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1 →
      1 ≤ logShellRadius a r Kc → 2 * w ≤ logShellRadius a r Kc →
      (∀ k, k < Kc → |Real.log (logShellRadius a r k)| ≤ M) →
        ‖evenFourierLogShellChannel a r n
            (soninScaledPacketEven m δ (2 * Real.pi * w) hδ)‖ ≤
          Real.sqrt (M ^ 2 * ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ 2 +
            4 * (2 * (K * δ ^ 2 / δ ^ (2 * N)) / ((2 * N : ℝ) - 1)) / a ^ (2 * N - 2) *
              ((r ^ (2 * N - 2))⁻¹ ^ Kc * (1 - (r ^ (2 * N - 2))⁻¹)⁻¹)) := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_norm_sq_sub_evenFourierCutoff_soninScaledPacketEven_le_div N (by omega)
  refine ⟨K, hK0, ?_⟩
  intro a r ha hr n Kc m δ w M hδ hw hmean hone h2w hM
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (2 * N : ℝ) - 1 := by linarith
  have hCnn : (0 : ℝ) ≤ 2 * (K * δ ^ 2 / δ ^ (2 * N)) / ((2 * N : ℝ) - 1) := by
    have hnum : (0 : ℝ) ≤ K * δ ^ 2 / δ ^ (2 * N) := by positivity
    positivity
  have hpe : 2 * N - 2 + 1 = 2 * N - 1 := by omega
  refine norm_evenFourierLogShellChannel_apply_le_of_highTail ha hr (p := 2 * N - 2)
    (by omega) n Kc _ hM hCnn hone ?_
  intro t ht
  rw [norm_sub_evenIndicatorCutoff_evenFourierTransform, hpe]
  exact hK m δ w t hδ hw (le_trans h2w ht) hmean

end RHTower

