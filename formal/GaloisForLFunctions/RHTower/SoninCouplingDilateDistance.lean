import GaloisForLFunctions.RHTower.SoninShellCut
import GaloisForLFunctions.RHTower.SoninCouplingBranchEstimate

/-!
# How far the coupling moves a shell vector from its dilate

For any vector vanishing inside the inner aperture and fixed by the outer one, the coupling's image
differs from the vector's inverse dilate by three terms: twice the projection correction, the
aperture layer's defect on the dilate, and the vector's own band content.  Only the two support
facts are used, so the estimate holds for a vector supported anywhere in the shell.

Applied to the packets of a shell cut, this turns the coupling into a near-isometry on each packet,
with the error split into pieces that mode counting and the band estimates control separately.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **Distance to the dilate.**  Twice the projection correction, the layer defect on the dilate,
and the band content. -/
theorem norm_soninApertureCoupling_sub_dilate_le
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (hcr : c ≤ r * a)
    {w : evenSubspace}
    (hlow : evenIndicatorCutoff b w = 0) (hhigh : evenIndicatorCutoff c w = w) :
    ‖evenSoninApertureSuccessiveLayerTransition a b c r hr w -
        evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w‖ ≤
      2 * ‖evenSoninProjectionCorrection b w‖ +
        (‖evenSoninApertureLayer a b
              (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w) -
            evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w‖ +
          ‖evenFourierCutoff b w‖) := by
  set v : evenSubspace := evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w with hv
  have hbranch := norm_evenSoninApertureSuccessiveLayerTransition_sub_branches_le
    hab hbc hr hcr hlow hhigh
  have hexp : ‖evenSoninApertureLayer a b
      (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w))‖ ≤
      ‖evenFourierCutoff b w‖ := by
    calc ‖evenSoninApertureLayer a b
          (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w))‖
        ≤ ‖evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w)‖ :=
          norm_evenSoninApertureLayer_apply_le hab _
      _ = ‖evenFourierCutoff b w‖ :=
          norm_evenDilationCLM_apply r (zero_lt_one.trans hr) _
  calc ‖evenSoninApertureSuccessiveLayerTransition a b c r hr w - v‖
      ≤ ‖evenSoninApertureSuccessiveLayerTransition a b c r hr w -
            (evenSoninApertureLayer a b v -
              evenSoninApertureLayer a b
                (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w)))‖ +
          ‖(evenSoninApertureLayer a b v -
              evenSoninApertureLayer a b
                (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w))) - v‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub
          (evenSoninApertureSuccessiveLayerTransition a b c r hr w)
          (evenSoninApertureLayer a b v -
            evenSoninApertureLayer a b
              (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w))) v
    _ ≤ 2 * ‖evenSoninProjectionCorrection b w‖ +
          (‖evenSoninApertureLayer a b v - v‖ + ‖evenFourierCutoff b w‖) := by
        refine add_le_add hbranch ?_
        calc ‖(evenSoninApertureLayer a b v -
                  evenSoninApertureLayer a b
                    (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w))) - v‖
              = ‖(evenSoninApertureLayer a b v - v) -
                  evenSoninApertureLayer a b
                    (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w))‖ := by
                congr 1
                abel
          _ ≤ ‖evenSoninApertureLayer a b v - v‖ +
                ‖evenSoninApertureLayer a b
                    (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w))‖ :=
              norm_sub_le _ _
          _ ≤ ‖evenSoninApertureLayer a b v - v‖ + ‖evenFourierCutoff b w‖ := by
              gcongr

/-- **The estimate for a shell-cut packet.**  Every packet of the cut satisfies the two support
facts, so the coupling carries it to within the three errors of its dilate. -/
theorem norm_soninApertureCoupling_soninShellCutPacket_sub_dilate_le
    (a b c : ℝ) (hb : 0 < b) (hab : a ≤ b) (hbc : b < c) {N : ℕ} (hN : 0 < N)
    {r : ℝ} (hr : 1 < r) (hcr : c ≤ r * a) (κ : ℝ) (i : Fin N) :
    ‖evenSoninApertureSuccessiveLayerTransition a b c r hr
          (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N) κ
            (soninShellCutWidth_pos b c hbc hN)) -
        evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
          (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N) κ
            (soninShellCutWidth_pos b c hbc hN))‖ ≤
      2 * ‖evenSoninProjectionCorrection b
            (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N) κ
              (soninShellCutWidth_pos b c hbc hN))‖ +
        (‖evenSoninApertureLayer a b
              (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
                (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N) κ
                  (soninShellCutWidth_pos b c hbc hN))) -
            evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
              (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N) κ
                (soninShellCutWidth_pos b c hbc hN))‖ +
          ‖evenFourierCutoff b
            (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N) κ
              (soninShellCutWidth_pos b c hbc hN))‖) := by
  obtain ⟨hlow, hhigh⟩ := soninShellCut_le b c hbc hN i
  refine norm_soninApertureCoupling_sub_dilate_le hab hbc.le hr hcr ?_ ?_
  · exact evenIndicatorCutoff_soninScaledPacketEven_eq_zero _ _ κ
      (soninShellCutWidth_pos b c hbc hN) b hlow
  · exact evenIndicatorCutoff_soninScaledPacketEven_eq_self _ _ κ
      (soninShellCutWidth_pos b c hbc hN)
      (soninShellCutCentre_nonneg b c hb hbc hN i) c hhigh

end RHTower
