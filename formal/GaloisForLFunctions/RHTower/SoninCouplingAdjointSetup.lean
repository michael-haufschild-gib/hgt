import GaloisForLFunctions.RHTower.SoninCouplingNonannihilation
import GaloisForLFunctions.RHTower.SoninInnerBandAnnihilation

/-!
# The adjoint coupling, and the outer layer on the wavepacket

The coupling is a product of two self-adjoint layers with the self-adjoint dilation sum between
them, so its adjoint is the same product read backwards.  Feeding it the dilated packet needs two
further facts: the dilation sum applied to an inverse dilate splits as the original plus a doubly
contracted copy, and the outer aperture layer fixes the packet in the limit.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology

/-- **`(19a)`.**  The adjoint of the successive-layer coupling is the reversed product. -/
theorem adjoint_evenSoninApertureSuccessiveLayerTransition (a b c r : ℝ) (hr : 1 < r) :
    ContinuousLinearMap.adjoint (evenSoninApertureSuccessiveLayerTransition a b c r hr) =
      evenSoninApertureLayer b c * evenDilationSum r hr * evenSoninApertureLayer a b := by
  unfold evenSoninApertureSuccessiveLayerTransition
  change ContinuousLinearMap.adjoint
      ((evenSoninApertureLayer a b ∘L evenDilationSum r hr) ∘L
        evenSoninApertureLayer b c) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_evenSoninApertureLayer, adjoint_evenDilationSum,
    adjoint_evenSoninApertureLayer]
  exact (mul_assoc _ _ _).symm

/-- **`(19b)`.**  The dilation sum on an inverse dilate returns the original plus a doubly
contracted copy. -/
theorem evenDilationSum_evenDilationCLM_inv_apply
    (r : ℝ) (hr : 1 < r) (hsq : 0 < (r ^ (2 : ℕ))⁻¹) (w : evenSubspace) :
    evenDilationSum r hr (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w) =
      w + evenDilationCLM ((r ^ (2 : ℕ))⁻¹) hsq w := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  have hsplit := DFunLike.congr_fun (evenDilationSum_eq r hr)
    (evenDilationCLM r⁻¹ hrinv w)
  rw [add_apply] at hsplit
  rw [hsplit]
  have h1 : evenDilationCLM r hr0 (evenDilationCLM r⁻¹ hrinv w) = w := by
    have h := DFunLike.congr_fun (evenDilationCLM_mul r r⁻¹ hr0 hrinv) w
    rw [mul_apply_eq_comp] at h
    rw [h, DFunLike.congr_fun (evenDilationCLM_congr (mul_pos hr0 hrinv)
      (mul_inv_cancel₀ hr0.ne')) w]
    have hone : evenDilationCLM (1 : ℝ) (mul_inv_cancel₀ hr0.ne' ▸ mul_pos hr0 hrinv) =
        (1 : evenSubspace →L[ℂ] evenSubspace) := evenDilationCLM_one
    rw [hone]
    rfl
  have hpow : r⁻¹ * r⁻¹ = (r ^ (2 : ℕ))⁻¹ := by rw [← mul_inv, ← sq]
  have h2 : evenDilationCLM r⁻¹ hrinv (evenDilationCLM r⁻¹ hrinv w) =
      evenDilationCLM ((r ^ (2 : ℕ))⁻¹) hsq w := by
    have h := DFunLike.congr_fun (evenDilationCLM_mul r⁻¹ r⁻¹ hrinv hrinv) w
    rw [mul_apply_eq_comp] at h
    rw [h]
    exact DFunLike.congr_fun (evenDilationCLM_congr (mul_pos hrinv hrinv) hpow) w
  rw [h1, h2]

/-- The Sonin projection differs from the identity by the two cutoffs and the correction. -/
theorem evenCentralSoninProjection_apply_sub (t : ℝ) (w : evenSubspace) :
    evenCentralSoninProjection t w - w =
      -evenIndicatorCutoff t w - evenFourierCutoff t w + evenSoninProjectionCorrection t w := by
  have hdecomp : evenCentralSoninProjection t =
      (1 - evenIndicatorCutoff t - evenFourierCutoff t) + evenSoninProjectionCorrection t := by
    unfold evenSoninProjectionCorrection
    abel
  rw [hdecomp]
  simp only [add_apply, sub_apply]
  rw [show (1 : evenSubspace →L[ℂ] evenSubspace) w = w from rfl]
  abel

/-- **`(19c)`.**  The outer aperture layer fixes the wavepacket in the limit. -/
theorem tendsto_norm_evenSoninApertureLayer_soninPacketEven_sub
    (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureLayer b c (soninPacketEven b c hb hbc (κ n)) -
          soninPacketEven b c hb hbc (κ n)‖) atTop (𝓝 0) := by
  have hBand := tendsto_norm_evenFourierCutoff_soninPacketEven b c hb hbc b κ hκ
  have hCorr := tendsto_norm_evenSoninProjectionCorrection_apply_soninPacketEven b c b
    hb hbc hb κ hκ
  have hmaj : Tendsto (fun n : ℕ =>
      ‖evenFourierCutoff b (soninPacketEven b c hb hbc (κ n))‖ +
        ‖evenSoninProjectionCorrection b (soninPacketEven b c hb hbc (κ n))‖)
      atTop (𝓝 0) := by
    simpa using hBand.add hCorr
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmaj
  set w : evenSubspace := soninPacketEven b c hb hbc (κ n) with hw
  have hhigh : evenIndicatorCutoff c w = w :=
    evenIndicatorCutoff_soninPacketEven_eq_self b c hb hbc (κ n)
  have hlow : evenIndicatorCutoff b w = 0 :=
    evenIndicatorCutoff_soninPacketEven_eq_zero b c hb hbc (κ n)
  rw [evenSoninApertureLayer_eq_of_indicatorCutoff_eq_self b c hhigh,
    evenCentralSoninProjection_apply_sub b w, hlow]
  calc ‖-(0 : evenSubspace) - evenFourierCutoff b w + evenSoninProjectionCorrection b w‖
      = ‖-evenFourierCutoff b w + evenSoninProjectionCorrection b w‖ := by
        rw [neg_zero, zero_sub]
    _ ≤ ‖-evenFourierCutoff b w‖ + ‖evenSoninProjectionCorrection b w‖ := norm_add_le _ _
    _ = ‖evenFourierCutoff b w‖ + ‖evenSoninProjectionCorrection b w‖ := by rw [norm_neg]

end RHTower
