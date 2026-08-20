/-
# Chen--Gupta--Li quartic packet compact kernel

Every pair-pair term in the CGL fourth moment has the same elementary compact
interval kernel as the second moment, with frequencies equal to pair ordinate
sums.  This module proves the uniform length bound used on the energy-selected
near terms before the source's Fourier-decay analysis controls the far terms.

No RH, GRH, smoothness, large-value, energy, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketEnergy

open Complex MeasureTheory

noncomputable section

namespace RHTower

/-- Any compact CGL interval kernel has norm at most the absolute interval
length. -/
theorem norm_cglCharacterPacketIntervalKernel_le_abs_length (A B t u : ℝ) :
    ‖cglCharacterPacketIntervalKernel A B t u‖ ≤ |B - A| := by
  unfold cglCharacterPacketIntervalKernel
  calc
    ‖∫ τ in A..B, cglCharacterPacketWave t τ * star (cglCharacterPacketWave u τ)‖ ≤
        (1 : ℝ) * |B - A| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro τ hτ
      rw [norm_mul]
      have ht : ‖cglCharacterPacketWave t τ‖ = 1 := by
        unfold cglCharacterPacketWave
        exact Complex.norm_exp_ofReal_mul_I _
      have hu : ‖star (cglCharacterPacketWave u τ)‖ = 1 := by
        rw [norm_star]
        unfold cglCharacterPacketWave
        exact Complex.norm_exp_ofReal_mul_I _
      rw [ht, hu]
      norm_num
    _ = _ := by ring

end RHTower
