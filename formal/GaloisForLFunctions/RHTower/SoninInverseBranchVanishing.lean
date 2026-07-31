import GaloisForLFunctions.RHTower.SoninForwardBranchVanishing

/-!
# The inverse dilation branch of the aperture layer vanishes on band-limited vectors

Dilation acts inversely on frequency, so the inverse branch contracts a Fourier band rather than
expanding it: a vector band-limited to `[-b,b]` is carried by `U_{r⁻¹}` into band `[-b/r, b/r]`, and
`b <= r a` makes that a subset of `[-a,a]`.  Both Sonin projections annihilate vectors band-limited
to their own window, so the aperture layer kills the inverse branch there.

This is the exact dual of the forward-branch vanishing on the inner band.  The two together mean
that on the two pieces the projection splits into, the aperture layer sees opposite dilation
branches — the expanding one on the vector itself, the contracting one on its Fourier band.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The inverse dilation contracts a Fourier band. -/
theorem fourierCutoff_evenDilationCLM_inv_apply_of_fourierCutoff_eq_self
    {a b r : ℝ} (hr : 1 < r) (hbr : b ≤ r * a)
    {v : evenSubspace} (hv : evenFourierCutoff b v = v) :
    evenFourierCutoff a
        (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) v) =
      evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) v := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  have hmove := evenDilationCLM_mul_evenFourierCutoff b r⁻¹ hrinv
  have hband : evenFourierCutoff (r⁻¹ * b)
      (evenDilationCLM r⁻¹ hrinv v) = evenDilationCLM r⁻¹ hrinv v := by
    have := congrArg (fun T : evenSubspace →L[ℂ] evenSubspace => T v) hmove
    simp only [mul_apply_eq_comp] at this
    rw [hv] at this
    exact this.symm
  have hle : r⁻¹ * b ≤ a := by
    rw [inv_mul_le_iff₀ hr0]
    linarith [hbr]
  calc
    evenFourierCutoff a (evenDilationCLM r⁻¹ hrinv v)
        = evenFourierCutoff a (evenFourierCutoff (r⁻¹ * b)
            (evenDilationCLM r⁻¹ hrinv v)) := by rw [hband]
    _ = (evenFourierCutoff a * evenFourierCutoff (r⁻¹ * b))
          (evenDilationCLM r⁻¹ hrinv v) := rfl
    _ = evenFourierCutoff (r⁻¹ * b) (evenDilationCLM r⁻¹ hrinv v) := by
        rw [evenFourierCutoff_mul_min, min_eq_right hle]
    _ = evenDilationCLM r⁻¹ hrinv v := hband

/-- **Inverse-branch vanishing.**  The aperture layer annihilates the inverse dilation of every
vector band-limited to the inner window. -/
theorem evenSoninApertureLayer_evenDilationCLM_inv_apply_eq_zero
    {a b r : ℝ} (hab : a ≤ b) (hr : 1 < r) (hbr : b ≤ r * a)
    {v : evenSubspace} (hv : evenFourierCutoff b v = v) :
    evenSoninApertureLayer a b
      (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) v) = 0 := by
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr (zero_lt_one.trans hr)
  have hA : evenFourierCutoff a (evenDilationCLM r⁻¹ hrinv v) =
      evenDilationCLM r⁻¹ hrinv v :=
    fourierCutoff_evenDilationCLM_inv_apply_of_fourierCutoff_eq_self hr hbr hv
  have hB : evenFourierCutoff b (evenDilationCLM r⁻¹ hrinv v) =
      evenDilationCLM r⁻¹ hrinv v := by
    calc
      evenFourierCutoff b (evenDilationCLM r⁻¹ hrinv v)
          = evenFourierCutoff b (evenFourierCutoff a
              (evenDilationCLM r⁻¹ hrinv v)) := by rw [hA]
      _ = (evenFourierCutoff b * evenFourierCutoff a)
            (evenDilationCLM r⁻¹ hrinv v) := rfl
      _ = evenFourierCutoff a (evenDilationCLM r⁻¹ hrinv v) := by
          rw [evenFourierCutoff_mul_min, min_eq_right hab]
      _ = evenDilationCLM r⁻¹ hrinv v := hA
  have hQa : evenCentralSoninProjection a (evenDilationCLM r⁻¹ hrinv v) = 0 :=
    evenCentralSoninProjection_eq_zero_of_fourierCutoff_eq_self a hA
  have hQb : evenCentralSoninProjection b (evenDilationCLM r⁻¹ hrinv v) = 0 :=
    evenCentralSoninProjection_eq_zero_of_fourierCutoff_eq_self b hB
  unfold evenSoninApertureLayer
  rw [sub_apply, hQa, hQb, sub_zero]

/-- **Only the forward branch survives on a band-limited vector.**  Dual to the inner-band
statement, where only the inverse branch survives. -/
theorem evenSoninApertureLayer_evenDilationSum_apply_eq_forward
    {a b r : ℝ} (hab : a ≤ b) (hr : 1 < r) (hbr : b ≤ r * a)
    {v : evenSubspace} (hv : evenFourierCutoff b v = v) :
    evenSoninApertureLayer a b (evenDilationSum r hr v) =
      evenSoninApertureLayer a b
        (evenDilationCLM r (zero_lt_one.trans hr) v) := by
  rw [evenDilationSum_eq]
  have hsplit : (evenDilationCLM r (zero_lt_one.trans hr) +
      evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))) v =
      evenDilationCLM r (zero_lt_one.trans hr) v +
        evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) v := rfl
  rw [hsplit, map_add,
    evenSoninApertureLayer_evenDilationCLM_inv_apply_eq_zero hab hr hbr hv,
    add_zero]

end RHTower
