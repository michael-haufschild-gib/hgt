import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinFiniteApertureCenterPairing

/-!
# Normalized-budget transfer for the CCM center pairing

This module isolates the exact asymptotic bookkeeping needed after the finite-aperture center-pairing
estimate.  A center error dominated by a positive defect times a vanishing normalized budget is
negligible relative to that defect.  Two specializations record the correct resource scales for the
CCM center term: normalization by the defect itself and normalization by its logarithmic leading
scale.

No prolate variation estimate is asserted here.  The final theorem makes that remaining input
explicit as the sublinear ratios `V lam / lam -> 0` and `d lam / lam -> 0`.
-/

open Filter Topology Real

namespace RHTower

/-- A norm bound by a positive defect times a vanishing budget forces the error divided by the
defect to tend to zero. -/
theorem tendsto_div_defect_of_norm_le_defect_mul_vanishingBudget
    {α : Type*} {l : Filter α} {d b : α → ℝ} {E : α → ℂ} {C : ℝ}
    (hd : ∀ᶠ x in l, 0 < d x)
    (hbound : ∀ᶠ x in l, ‖E x‖ ≤ C * d x * b x)
    (hb : Tendsto b l (𝓝 0)) :
    Tendsto (fun x => E x / (d x : ℂ)) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hle : ∀ᶠ x in l, ‖E x / (d x : ℂ)‖ ≤ C * b x := by
    filter_upwards [hd, hbound] with x hdx hEx
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdx,
      div_le_iff₀ hdx]
    calc
      ‖E x‖ ≤ C * d x * b x := hEx
      _ = C * b x * d x := by ring
  have hlim : Tendsto (fun x => C * b x) l (𝓝 0) := by
    simpa only [mul_zero] using hb.const_mul C
  exact squeeze_zero' (Filter.Eventually.of_forall fun x => norm_nonneg _) hle hlim

/-- The finite-aperture CCM center error is negligible relative to the defect whenever the variation
and defect parts of its normalized center budget both vanish. -/
theorem tendsto_ccmCenterError_div_defect_of_normalizedBudget
    {d V : ℝ → ℝ} {E : ℝ → ℂ} {C : ℝ}
    (hd : ∀ᶠ lam in atTop, 0 < d lam)
    (hbound : ∀ᶠ lam in atTop,
      ‖E lam‖ ≤ C * d lam *
        ((V lam + d lam) * (Real.log lam + 1) / lam))
    (hV : Tendsto (fun lam : ℝ => V lam * (Real.log lam + 1) / lam)
      atTop (𝓝 0))
    (hdBudget : Tendsto (fun lam : ℝ => d lam * (Real.log lam + 1) / lam)
      atTop (𝓝 0)) :
    Tendsto (fun lam => E lam / (d lam : ℂ)) atTop (𝓝 0) := by
  have hbudget : Tendsto
      (fun lam : ℝ => (V lam + d lam) * (Real.log lam + 1) / lam)
      atTop (𝓝 0) := by
    convert hV.add hdBudget using 1
    · funext lam
      ring_nf
    · ring_nf
  exact tendsto_div_defect_of_norm_le_defect_mul_vanishingBudget hd hbound hbudget

/-- The same CCM center estimate is negligible relative to the logarithmic leading scale whenever
the corresponding leading-scale budget vanishes. -/
theorem tendsto_ccmCenterError_div_defect_mul_log_of_normalizedBudget
    {d V : ℝ → ℝ} {E : ℝ → ℂ} {C : ℝ}
    (hd : ∀ᶠ lam in atTop, 0 < d lam)
    (hbound : ∀ᶠ lam in atTop,
      ‖E lam‖ ≤ C * d lam *
        ((V lam + d lam) * (Real.log lam + 1) / lam))
    (hbudget : Tendsto
      (fun lam : ℝ => (V lam + d lam) * (Real.log lam + 1) /
        (lam * Real.log lam)) atTop (𝓝 0)) :
    Tendsto (fun lam => E lam / ((d lam * Real.log lam : ℝ) : ℂ))
      atTop (𝓝 0) := by
  have hlarge : ∀ᶠ lam : ℝ in atTop, 1 < lam := eventually_gt_atTop 1
  have hdefect : ∀ᶠ lam in atTop, 0 < d lam * Real.log lam := by
    filter_upwards [hd, hlarge] with lam hdlam hlam
    exact mul_pos hdlam (Real.log_pos hlam)
  have hbound' : ∀ᶠ lam in atTop,
      ‖E lam‖ ≤ C * (d lam * Real.log lam) *
        ((V lam + d lam) * (Real.log lam + 1) /
          (lam * Real.log lam)) := by
    filter_upwards [hbound, hlarge] with lam hE hlam
    calc
      ‖E lam‖ ≤ C * d lam *
          ((V lam + d lam) * (Real.log lam + 1) / lam) := hE
      _ = C * (d lam * Real.log lam) *
          ((V lam + d lam) * (Real.log lam + 1) /
            (lam * Real.log lam)) := by
        field_simp [(Real.log_pos hlam).ne', hlam.ne']
  exact tendsto_div_defect_of_norm_le_defect_mul_vanishingBudget hdefect hbound' hbudget

/-- Sublinear variation and defect growth are sufficient to make the CCM center error negligible
relative to the logarithmic leading scale.  This is the exact positive resource ledger exposed by
the center-pairing estimate. -/
theorem tendsto_ccmCenterError_div_defect_mul_log_of_sublinearVariation
    {d V : ℝ → ℝ} {E : ℝ → ℂ} {C : ℝ}
    (hd : ∀ᶠ lam in atTop, 0 < d lam)
    (hbound : ∀ᶠ lam in atTop,
      ‖E lam‖ ≤ C * d lam *
        ((V lam + d lam) * (Real.log lam + 1) / lam))
    (hV : Tendsto (fun lam : ℝ => V lam / lam) atTop (𝓝 0))
    (hdRatio : Tendsto (fun lam : ℝ => d lam / lam) atTop (𝓝 0)) :
    Tendsto (fun lam => E lam / ((d lam * Real.log lam : ℝ) : ℂ))
      atTop (𝓝 0) := by
  have hlarge : ∀ᶠ lam : ℝ in atTop, 1 < lam := eventually_gt_atTop 1
  have hinvLog : Tendsto (fun lam : ℝ => (Real.log lam)⁻¹)
      atTop (𝓝 0) := Real.tendsto_log_atTop.inv_tendsto_atTop
  have hlogRatio : Tendsto
      (fun lam : ℝ => (Real.log lam + 1) / Real.log lam)
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hinvLog
    have heq : (fun lam : ℝ => 1 + (Real.log lam)⁻¹) =ᶠ[atTop]
        fun lam : ℝ => (Real.log lam + 1) / Real.log lam := by
      filter_upwards [hlarge] with lam hlam
      field_simp [(Real.log_pos hlam).ne']
    simpa only [add_zero] using h.congr' heq
  have hbase : Tendsto
      (fun lam : ℝ => V lam / lam + d lam / lam)
      atTop (𝓝 0) := by
    simpa only [zero_add] using hV.add hdRatio
  have hprod : Tendsto
      (fun lam : ℝ => (V lam / lam + d lam / lam) *
        ((Real.log lam + 1) / Real.log lam))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using hbase.mul hlogRatio
  have hbudget : Tendsto
      (fun lam : ℝ =>
        (V lam + d lam) * (Real.log lam + 1) /
          (lam * Real.log lam))
      atTop (𝓝 0) := by
    apply hprod.congr'
    filter_upwards [hlarge] with lam hlam
    field_simp [(Real.log_pos hlam).ne', hlam.ne']
  exact tendsto_ccmCenterError_div_defect_mul_log_of_normalizedBudget hd hbound hbudget

end RHTower
