import GaloisForLFunctions.OrderSixMetaplecticTheory.BoundedRemaindersHaveAtMostASimplePoleAtFourThirds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubicThetaCorrectionHasAHolomorphicRepresentative
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicEisensteinCorrectionIsBoundedOnVerticalStrips

/-!
# The regularized remainder pairing is bounded on vertical strips

For a bounded remainder `G` the pairing `Λ_G(s) = S_G(s) + ⟨G, C(s)⟩` uses the Eisenstein correction `C`,
holomorphic off the real axis. Filling the removable real values of `C` gives `Λ̃_G` (`regPairing`):
holomorphic on `1 < Re s < 13/3` away from `4/3`, equal to `Λ_G` off the real axis and on a punctured
neighbourhood of `4/3`, with `(s − 4/3)²Λ̃_G(s) → 0`. On every closed strip inside `1 < Re s < 13/3` it is
bounded for `|Im s| ≥ 1`: the seed is the Mellin transform of a kernel vanishing below height `2` and
`O(v^{−13/3})` above, and the correction is bounded there.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- A Mellin transform of a kernel vanishing below `2` and `O(v^{−q})` above is bounded on `Re s ≤ B < q`. -/
private theorem mellin_bounded_of_tail (f : ℝ → ℂ) (q B : ℝ) (hB : B < q)
    (hz : ∀ v : ℝ, v ≤ 2 → f v = 0)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 2 ≤ v → ‖f v‖ ≤ C * v ^ (-q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ≤ B → ‖mellin f s‖ ≤ C := by
  obtain ⟨D, hD, hd⟩ := hb
  let g : ℝ → ℝ := (Ioi 2).indicator (fun v => D * v ^ (B - 1 - q))
  have hg : Integrable g :=
    (integrable_indicator_iff measurableSet_Ioi).2
      ((integrableOn_Ioi_rpow_of_lt (by linarith : B - 1 - q < -1)
      (by norm_num : (0 : ℝ) < 2)).const_mul D)
  refine ⟨∫ v in Ioi (0 : ℝ), g v, ?_, ?_⟩
  · apply integral_nonneg
    intro v
    exact indicator_nonneg (fun v hv => mul_nonneg hD
      (Real.rpow_nonneg (by have hv' : 2 < v := hv; linarith) _)) v
  · intro s hs
    unfold mellin
    apply norm_integral_le_of_norm_le hg.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := hv
    by_cases hv2 : 2 < v
    · dsimp only [g]
      rw [indicator_of_mem (s := Ioi (2 : ℝ)) hv2, norm_smul,
        Complex.norm_cpow_eq_rpow_re_of_pos hv0]
      simp only [Complex.sub_re, Complex.one_re]
      calc
        _ ≤ v ^ (B - 1) * (D * v ^ (-q)) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
            (hd v hv2.le) (norm_nonneg _) (Real.rpow_nonneg hv0.le _)
        _ = D * v ^ (B - 1 - q) := by
          rw [mul_left_comm, ← Real.rpow_add hv0]
          congr 2
    · dsimp only [g]
      rw [hz v (not_lt.mp hv2), smul_zero, norm_zero, indicator_of_notMem (s := Ioi (2 : ℝ)) hv2]

namespace RemainderData

variable {G : HyperbolicSpace → ℂ} (hG : RemainderData G)
include hG

/-- `Λ̃_G(s) = S_G(s) + ⟨G, C̃(s)⟩`, the correction with its removable real values filled in. -/
def regPairing (s : ℂ) : ℂ :=
  remainderSeed G s + levelPairing G hG.memLp (regularizedEisensteinCorrection s)

theorem regPairing_eq_of_im_ne (s : ℂ) (hs : 1 < s.re) (hi : s.im ≠ 0) :
    hG.regPairing s = hG.pairing s := by
  rw [regPairing, pairing, regularizedEisensteinCorrection_eq_nonreal s hs hi]

theorem regPairing_eventually_eq : hG.regPairing =ᶠ[𝓝[≠] (4 / 3 : ℂ)] hG.pairing := by
  filter_upwards [regularizedEisensteinCorrection_eventually_eq_center] with s hs
  rw [regPairing, pairing, hs]

theorem regPairing_differentiableAt (s : ℂ) (hs1 : 1 < s.re) (hs : s.re < 13 / 3) (hp : s ≠ 4 / 3) :
    DifferentiableAt ℂ hG.regPairing s :=
  (hG.remainderSeed_differentiableAt s (by linarith) hs).add
    (((levelPairing G hG.memLp).analyticAt _).comp
      (regularizedEisensteinCorrection_analyticAt s hs1 hp)).differentiableAt

/-- **At most a simple pole.** `(s − 4/3)²Λ̃_G(s) → 0`. -/
theorem regPairing_near_four_thirds :
    Tendsto (fun s => (s - 4 / 3) ^ 2 * hG.regPairing s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 0) := by
  refine hG.pairing_near_four_thirds.2.congr' ?_
  filter_upwards [hG.regPairing_eventually_eq] with s hs
  rw [hs]

/-- **Bounded on vertical strips.** -/
theorem regPairing_vertical_bound (a B : ℝ) (ha : 1 < a) (hB : B < 13 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ B → 1 ≤ |s.im| → ‖hG.regPairing s‖ ≤ C := by
  obtain ⟨S, hS, hs⟩ := mellin_bounded_of_tail (remainderSeedKernel G) (13 / 3) B hB
    remainderSeedKernel_eq_zero (by simpa only [neg_div] using hG.norm_remainderSeedKernel_le)
  obtain ⟨D, hD, hd⟩ := kernelEisensteinL2Correction_vertical_bound 2 3
    (by norm_num) (by norm_num) (max B 0) (a - 1) (le_max_right _ _) (by linarith)
  let F := levelPairing G hG.memLp
  refine ⟨S + ‖F‖ * D, add_nonneg hS (mul_nonneg (norm_nonneg _) hD), fun s hsa hsb hsi => ?_⟩
  have hi : s.im ≠ 0 := by intro h; rw [h, abs_zero] at hsi; linarith
  have hc : ‖eisensteinCorrection s‖ ≤ D := hd s
    (abs_le.mpr ⟨by linarith [le_max_right B 0], hsb.trans (le_max_left _ _)⟩)
    ((by linarith : a - 1 ≤ s.re - 1).trans (le_abs_self _)) hsi
  rw [regPairing, regularizedEisensteinCorrection_eq_nonreal s (by linarith) hi]
  calc
    _ ≤ ‖remainderSeed G s‖ + ‖F (eisensteinCorrection s)‖ := norm_add_le _ _
    _ ≤ S + ‖F‖ * D := by
      gcongr
      · rw [remainderSeed_eq_mellin]
        exact hs s hsb
      · exact (F.le_opNorm _).trans (mul_le_mul_of_nonneg_left hc (norm_nonneg _))

end RemainderData

end GaloisForLFunctions.OrderSixMetaplecticTheory
