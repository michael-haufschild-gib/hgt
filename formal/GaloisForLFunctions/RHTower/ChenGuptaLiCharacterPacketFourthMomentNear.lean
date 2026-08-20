/-
# Chen--Gupta--Li energy-selected fourth-moment contribution

This module isolates the compact-kernel contribution from the exact CGL energy
configurations.  Its norm is bounded by `φ(q) E(W)` times interval length.
The complementary far configurations remain explicit for the separate
Fourier-decay argument in CGL Lemma 9.2.

No RH, GRH, smoothness, large-value, energy, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketFourthMomentKernel

noncomputable section

namespace RHTower

/-- The compact interval contribution of the exact CGL energy configurations. -/
noncomputable def cglCharacterPacketNearEnergyContribution {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (A B : ℝ) : ℂ :=
  ∑ pq ∈ cglCharacterPacketEnergyIndexSet w,
    ((q + 1).totient : ℂ) * cglCharacterPacketIntervalKernel A B
      (cglCharacterPacketPairOrdinate w pq.1) (cglCharacterPacketPairOrdinate w pq.2)

/-- The energy-selected part of the quartic packet contribution is bounded by
the literal CGL energy times the compact interval length. -/
theorem norm_cglCharacterPacketNearEnergyContribution_le {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (A B : ℝ) :
    ‖cglCharacterPacketNearEnergyContribution w A B‖ ≤
      ((q + 1).totient : ℝ) * (cglCharacterPacketEnergy w : ℝ) * |B - A| := by
  unfold cglCharacterPacketNearEnergyContribution cglCharacterPacketEnergy
  calc
    ‖∑ pq ∈ cglCharacterPacketEnergyIndexSet w,
        ((q + 1).totient : ℂ) * cglCharacterPacketIntervalKernel A B
          (cglCharacterPacketPairOrdinate w pq.1) (cglCharacterPacketPairOrdinate w pq.2)‖
      ≤ ∑ pq ∈ cglCharacterPacketEnergyIndexSet w,
        ‖((q + 1).totient : ℂ) * cglCharacterPacketIntervalKernel A B
          (cglCharacterPacketPairOrdinate w pq.1) (cglCharacterPacketPairOrdinate w pq.2)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _pq ∈ cglCharacterPacketEnergyIndexSet w,
        ((q + 1).totient : ℝ) * |B - A| := by
      apply Finset.sum_le_sum
      intro pq hpq
      rw [norm_mul, norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (norm_cglCharacterPacketIntervalKernel_le_abs_length A B _ _) (by positivity)
    _ = ((q + 1).totient : ℝ) *
        ((cglCharacterPacketEnergyIndexSet w).card : ℝ) * |B - A| := by
      simp
      ring

end RHTower
