import GaloisForLFunctions.RHTower.SoninCouplingBranchNormalForm

/-!
# The two-branch difference approximates the coupling

The branch normal form has a trace-class remainder built from the exact projection correction.
Bounding the aperture layer by one and the dilation sum by two turns that remainder into an
estimate: on every annulus vector the coupling differs from the difference of its two opposite
dilation branches by at most twice the norm of the correction.

Unlike the correction-free specialisation, this needs no hypothesis on the vector beyond living in
the annulus, so it applies to the whole test family rather than to a possibly empty subfamily.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- Normalized dilation is isometric on the even carrier. -/
theorem norm_evenDilationCLM_apply (r : ℝ) (hr : 0 < r) (x : evenSubspace) :
    ‖evenDilationCLM r hr x‖ = ‖x‖ := by
  change ‖evenDilationUnitary r hr x‖ = ‖x‖
  exact (evenDilationUnitary r hr).norm_map x

/-- The dilation sum has norm at most two. -/
theorem norm_evenDilationSum_apply_le (r : ℝ) (hr : 1 < r) (x : evenSubspace) :
    ‖evenDilationSum r hr x‖ ≤ 2 * ‖x‖ := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  rw [evenDilationSum_eq]
  have hsplit : (evenDilationCLM r hr0 + evenDilationCLM r⁻¹ hrinv) x =
      evenDilationCLM r hr0 x + evenDilationCLM r⁻¹ hrinv x := rfl
  rw [hsplit]
  calc
    ‖evenDilationCLM r hr0 x + evenDilationCLM r⁻¹ hrinv x‖
        ≤ ‖evenDilationCLM r hr0 x‖ + ‖evenDilationCLM r⁻¹ hrinv x‖ :=
      norm_add_le _ _
    _ = ‖x‖ + ‖x‖ := by
        rw [norm_evenDilationCLM_apply r hr0 x, norm_evenDilationCLM_apply r⁻¹ hrinv x]
    _ = 2 * ‖x‖ := by ring

/-- The aperture layer is a self-adjoint idempotent, hence a contraction. -/
theorem norm_evenSoninApertureLayer_apply_le {a b : ℝ} (hab : a ≤ b)
    (x : evenSubspace) :
    ‖evenSoninApertureLayer a b x‖ ≤ ‖x‖ := by
  have hidem : evenSoninApertureLayer a b * evenSoninApertureLayer a b =
      evenSoninApertureLayer a b := evenSoninApertureLayer_mul_self hab
  have hidemx : evenSoninApertureLayer a b (evenSoninApertureLayer a b x) =
      evenSoninApertureLayer a b x := by
    simpa using DFunLike.congr_fun hidem x
  have hadj : ContinuousLinearMap.adjoint (evenSoninApertureLayer a b) =
      evenSoninApertureLayer a b := adjoint_evenSoninApertureLayer a b
  have hself : inner ℂ (evenSoninApertureLayer a b x)
      (evenSoninApertureLayer a b x) =
      inner ℂ (evenSoninApertureLayer a b x) x := by
    calc
      inner ℂ (evenSoninApertureLayer a b x) (evenSoninApertureLayer a b x)
          = inner ℂ (evenSoninApertureLayer a b x)
              (ContinuousLinearMap.adjoint (evenSoninApertureLayer a b) x) := by
            rw [hadj]
      _ = inner ℂ (evenSoninApertureLayer a b
            (evenSoninApertureLayer a b x)) x :=
          ContinuousLinearMap.adjoint_inner_right (evenSoninApertureLayer a b)
            (evenSoninApertureLayer a b x) x
      _ = inner ℂ (evenSoninApertureLayer a b x) x := by rw [hidemx]
  have hsq : ‖evenSoninApertureLayer a b x‖ ^ 2 =
      ‖(inner ℂ (evenSoninApertureLayer a b x) x : ℂ)‖ := by
    rw [← hself, inner_self_eq_norm_sq_to_K]
    simp
  have hcs : ‖(inner ℂ (evenSoninApertureLayer a b x) x : ℂ)‖ ≤
      ‖evenSoninApertureLayer a b x‖ * ‖x‖ := norm_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (evenSoninApertureLayer a b x)) with h | h
  · rw [← h]
    exact norm_nonneg x
  · have hle : ‖evenSoninApertureLayer a b x‖ ^ 2 ≤
        ‖evenSoninApertureLayer a b x‖ * ‖x‖ := by
      rw [hsq]; exact hcs
    nlinarith [hle, h]

/-- **Two-branch estimate.**  On an annulus vector the coupling is the difference of its two
opposite dilation branches, up to twice the norm of the exact projection correction. -/
theorem norm_evenSoninApertureSuccessiveLayerTransition_sub_branches_le
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (hcr : c ≤ r * a)
    {w : evenSubspace}
    (hlow : evenIndicatorCutoff b w = 0) (hhigh : evenIndicatorCutoff c w = w) :
    ‖evenSoninApertureSuccessiveLayerTransition a b c r hr w -
        (evenSoninApertureLayer a b
            (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w) -
          evenSoninApertureLayer a b
            (evenDilationCLM r (zero_lt_one.trans hr)
              (evenFourierCutoff b w)))‖ ≤
      2 * ‖evenSoninProjectionCorrection b w‖ := by
  have hnf := evenSoninApertureSuccessiveLayerTransition_apply_annulus_branches
    hab hbc hr hcr hlow hhigh
  have hdiff : evenSoninApertureSuccessiveLayerTransition a b c r hr w -
      (evenSoninApertureLayer a b
          (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) w) -
        evenSoninApertureLayer a b
          (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w))) =
      evenSoninApertureLayer a b
        (evenDilationSum r hr (evenSoninProjectionCorrection b w)) := by
    rw [hnf]
    abel
  rw [hdiff]
  calc
    ‖evenSoninApertureLayer a b
        (evenDilationSum r hr (evenSoninProjectionCorrection b w))‖
        ≤ ‖evenDilationSum r hr (evenSoninProjectionCorrection b w)‖ :=
      norm_evenSoninApertureLayer_apply_le hab _
    _ ≤ 2 * ‖evenSoninProjectionCorrection b w‖ :=
      norm_evenDilationSum_apply_le r hr _

end RHTower
