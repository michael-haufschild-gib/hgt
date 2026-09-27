import GaloisForLFunctions.RHTower.ThetaCompactRealGroundProfiles
import GaloisForLFunctions.RHTower.ThetaPrimeLogCellPositivePairs

/-!
# Equal-mass translated bump packets in actual theta ground coordinates

One physical bump produces a smooth source at every center. All masses agree,
matching shifts have cross correlation equal to that mass, and the complete
continuous cross pairing depends only on the difference of the centers.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

def thetaTranslatedBumpPhysical (r : ℝ) (hr : 0 < r) (c : ℝ) (x : ℝ) : ℝ :=
  polarBumpFn 0 r hr (x - c)

theorem smooth_thetaTranslatedBumpPhysical (r : ℝ) (hr : 0 < r) (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (thetaTranslatedBumpPhysical r hr c) :=
  (polarBumpFn 0 r hr).contDiff.comp (contDiff_id.sub contDiff_const)

theorem compact_thetaTranslatedBumpPhysical (r : ℝ) (hr : 0 < r) (c : ℝ) :
    HasCompactSupport (thetaTranslatedBumpPhysical r hr c) := by
  convert (polarBumpFn 0 r hr).hasCompactSupport.comp_homeomorph (Homeomorph.addRight (-c)) using 1
  funext x
  rfl

def thetaTranslatedBumpGround (r : ℝ) (hr : 0 < r) (c : ℝ) : 𝓢(ℝ, ℝ) :=
  thetaCompactRealGroundProfile (thetaTranslatedBumpPhysical r hr c)
    (smooth_thetaTranslatedBumpPhysical r hr c) (compact_thetaTranslatedBumpPhysical r hr c)

theorem compact_thetaTranslatedBumpGround (r : ℝ) (hr : 0 < r) (c : ℝ) :
    HasCompactSupport (thetaTranslatedBumpGround r hr c) :=
  hasCompactSupport_thetaCompactRealGroundProfile _ _ _

theorem support_thetaTranslatedBumpGround (r : ℝ) (hr : 0 < r) (c : ℝ) :
    Function.support (thetaTranslatedBumpGround r hr c) = Metric.ball c r := by
  rw [thetaTranslatedBumpGround, support_thetaCompactRealGroundProfile]
  ext x
  change x - c ∈ Function.support (polarBumpFn 0 r hr) ↔ x ∈ Metric.ball c r
  rw [(polarBumpFn 0 r hr).support_eq, polarBumpFn_rOut,
    Metric.mem_ball, Metric.mem_ball, Real.dist_eq, Real.dist_eq, sub_zero]

theorem thetaTranslatedBumpGround_nonneg (r : ℝ) (hr : 0 < r) (c x : ℝ) :
    0 ≤ thetaTranslatedBumpGround r hr c x :=
  div_nonneg (polarBumpFn 0 r hr).nonneg (thetaCuspTiltSource.pos x).le

theorem thetaTranslatedBumpGround_center_pos (r : ℝ) (hr : 0 < r) (c : ℝ) :
    0 < thetaTranslatedBumpGround r hr c c := by
  change 0 < polarBumpFn 0 r hr (c - c) / thetaCuspFullSource c
  rw [sub_self]
  apply div_pos _ (thetaCuspTiltSource.pos c)
  apply (polarBumpFn 0 r hr).pos_of_mem_ball
  simpa only [Metric.mem_ball, dist_self, polarBumpFn_rOut] using hr

theorem thetaTranslatedBumpGround_mass (r : ℝ) (hr : 0 < r) (c : ℝ) :
    thetaGroundNormSq (thetaComplexify (thetaTranslatedBumpGround r hr c)) =
      thetaGroundNormSq (thetaComplexify (thetaTranslatedBumpGround r hr 0)) := by
  apply thetaGroundNormSq_matched_physical_translate _ _ _ _ _ _ c
  intro x
  simp only [thetaTranslatedBumpPhysical, add_sub_cancel_right, sub_zero]

theorem thetaTranslatedBumpGround_mass_pos (r : ℝ) (hr : 0 < r) (c : ℝ) :
    0 < thetaGroundNormSq (thetaComplexify (thetaTranslatedBumpGround r hr c)) :=
  thetaGroundNormSq_pos_of_ne_zero _ (by
    rw [thetaComplexify_apply]
    exact Complex.ofReal_ne_zero.mpr (thetaTranslatedBumpGround_center_pos r hr c).ne')

theorem thetaTranslatedBumpGround_matched_cross (r : ℝ) (hr : 0 < r) (c d : ℝ) :
    thetaGroundShiftCross (thetaTranslatedBumpGround r hr c) (thetaTranslatedBumpGround r hr d)
        (d - c) = thetaGroundNormSq (thetaComplexify (thetaTranslatedBumpGround r hr 0)) := by
  rw [← thetaTranslatedBumpGround_mass r hr c]
  apply thetaGroundShiftCross_matched_physical_translate _ _ _ _ _ _ (d - c)
  intro x
  unfold thetaTranslatedBumpPhysical
  congr 1
  ring

theorem thetaGammaPolarGroundCrossPairing_compact_physical
    (f g : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    thetaGammaPolarGroundCrossPairing (thetaCompactRealGroundProfile f hf hfc)
        (thetaCompactRealGroundProfile g hg hgc) =
      ∫ z : ℝ × ℝ, thetaGammaPolarScalingKernel (z.1 - z.2) * f z.2 * g z.1 := by
  unfold thetaGammaPolarGroundCrossPairing
  apply integral_congr_ae
  filter_upwards with z
  calc
    _ = thetaGammaPolarScalingKernel (z.1 - z.2) *
        (thetaCuspFullSource z.2 * thetaCompactRealGroundProfile f hf hfc z.2) *
        (thetaCuspFullSource z.1 * thetaCompactRealGroundProfile g hg hgc z.1) := by ring
    _ = _ := by rw [thetaCompactRealGroundProfile_reconstruct, thetaCompactRealGroundProfile_reconstruct]

theorem thetaTranslatedBumpGround_continuous_cross (r : ℝ) (hr : 0 < r) (c d : ℝ) :
    thetaGammaPolarGroundCrossPairing (thetaTranslatedBumpGround r hr c) (thetaTranslatedBumpGround r hr d) =
      thetaGammaPolarGroundCrossPairing (thetaTranslatedBumpGround r hr 0)
        (thetaTranslatedBumpGround r hr (d - c)) := by
  unfold thetaTranslatedBumpGround
  rw [thetaGammaPolarGroundCrossPairing_compact_physical,
    thetaGammaPolarGroundCrossPairing_compact_physical,
    ← integral_add_right_eq_self (fun z : ℝ × ℝ => thetaGammaPolarScalingKernel (z.1 - z.2) *
      thetaTranslatedBumpPhysical r hr c z.2 * thetaTranslatedBumpPhysical r hr d z.1) (c, c)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Prod.fst_add, Prod.snd_add, thetaTranslatedBumpPhysical, add_sub_cancel_right,
    add_sub_add_right_eq_sub, sub_zero]
  congr 2
  ring

end RHTower
