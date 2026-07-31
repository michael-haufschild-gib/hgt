import GaloisForLFunctions.RHTower.SoninShellProductIdeal

/-!
# The shell product is exactly its four mixed-polarization terms

The like-polarization terms of the shell–dilation–shell product vanish identically in the crossing
chamber, so the product is not merely congruent to the mixed terms — it *equals* their sum.

This isolates what actually carries the coupling: four finite time-band blocks, each a physical
band composed with a Fourier band across a dilation.  Whether the coupling vanishes is exactly the
question of whether those four blocks cancel.
-/

noncomputable section

set_option maxHeartbeats 2000000

namespace RHTower

open ContinuousLinearMap

/-- **Exact mixed-term form of the shell product.**  In the crossing chamber the shell product is
the sum of its four mixed-polarization terms; the like-polarization terms are identically zero. -/
theorem evenTwoPolarizationShell_mul_evenDilationSum_mul_shell_eq_mixed
    {a b c r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hr : 1 < r) (hcr : c ≤ r * a) :
    evenTwoPolarizationShell a b * evenDilationSum r hr *
        evenTwoPolarizationShell b c =
      (evenIndicatorCutoff b - evenIndicatorCutoff a) *
            evenDilationCLM r (zero_lt_one.trans hr) *
            (evenFourierCutoff c - evenFourierCutoff b) +
          (evenIndicatorCutoff b - evenIndicatorCutoff a) *
            evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
            (evenFourierCutoff c - evenFourierCutoff b) +
          (evenFourierCutoff b - evenFourierCutoff a) *
            evenDilationCLM r (zero_lt_one.trans hr) *
            (evenIndicatorCutoff c - evenIndicatorCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) *
          evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  have v1 := indicatorShell_forward_vanishing hab hbc hr hcr
  have v2 := indicatorShell_inverse_vanishing ha hab hbc hr
  have v3 := fourierShell_forward_vanishing ha hab hbc hr
  have v4 := fourierShell_inverse_vanishing hab hbc hr hcr
  rw [evenDilationSum_eq]
  unfold evenTwoPolarizationShell
  have hexpand :
      ((evenIndicatorCutoff b - evenIndicatorCutoff a) +
          (evenFourierCutoff b - evenFourierCutoff a)) *
        (evenDilationCLM r hr0 + evenDilationCLM r⁻¹ hrinv) *
        ((evenIndicatorCutoff c - evenIndicatorCutoff b) +
          (evenFourierCutoff c - evenFourierCutoff b)) =
      ((evenIndicatorCutoff b - evenIndicatorCutoff a) * evenDilationCLM r hr0 *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) +
        (evenIndicatorCutoff b - evenIndicatorCutoff a) *
          evenDilationCLM r⁻¹ hrinv *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) * evenDilationCLM r hr0 *
          (evenFourierCutoff c - evenFourierCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) *
          evenDilationCLM r⁻¹ hrinv *
          (evenFourierCutoff c - evenFourierCutoff b)) +
      ((evenIndicatorCutoff b - evenIndicatorCutoff a) * evenDilationCLM r hr0 *
          (evenFourierCutoff c - evenFourierCutoff b) +
        (evenIndicatorCutoff b - evenIndicatorCutoff a) *
          evenDilationCLM r⁻¹ hrinv *
          (evenFourierCutoff c - evenFourierCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) * evenDilationCLM r hr0 *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) *
          evenDilationCLM r⁻¹ hrinv *
          (evenIndicatorCutoff c - evenIndicatorCutoff b)) := by
    noncomm_ring
  rw [hexpand, v1, v2, v3, v4]
  abel

/-- Hence the coupling equals the four mixed blocks up to an element of the relative ideal, and the
vanishing question is exactly whether those blocks cancel. -/
theorem evenSoninApertureSuccessiveLayerTransition_principalRelativeEq_mixed
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (hcr : c ≤ r * a) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr =ᵣ
      (evenIndicatorCutoff b - evenIndicatorCutoff a) *
            evenDilationCLM r (zero_lt_one.trans hr) *
            (evenFourierCutoff c - evenFourierCutoff b) +
          (evenIndicatorCutoff b - evenIndicatorCutoff a) *
            evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
            (evenFourierCutoff c - evenFourierCutoff b) +
          (evenFourierCutoff b - evenFourierCutoff a) *
            evenDilationCLM r (zero_lt_one.trans hr) *
            (evenIndicatorCutoff c - evenIndicatorCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) *
          evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) := by
  have hshell :=
    evenSoninApertureSuccessiveLayerTransition_principalRelativeEq_shellProduct
      ha hb hc hab hbc hr
  rw [← evenTwoPolarizationShell_mul_evenDilationSum_mul_shell_eq_mixed
    ha hab hbc hr hcr]
  exact hshell

end RHTower
