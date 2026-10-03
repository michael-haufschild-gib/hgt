import GaloisForLFunctions.RHTower.SuzukiRaisedMetricShiftSource
import GaloisForLFunctions.RHTower.SuzukiTaV2MixedSourceLimit

open Complex Filter
open scoped Topology InnerProduct NNReal
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Both aperture and arbitrary nonnegative metric increment are retained. -/
abbrev SuzukiRaisedMetricParameters := SuzukiPositiveAperture × ℝ≥0

def suzukiRaisedMetricPhysical (a : SuzukiPositiveAperture) (t : ℝ≥0) :
    suzukiApertureHilbert a :=
  ccmArchimedeanFormToAperture a
    (suzukiTaToFormCLM a (suzukiRaisedMetricRawDeficiency a t))

private theorem physical_eq (a : SuzukiPositiveAperture) (t : ℝ≥0) :
    suzukiRaisedMetricPhysical a t = (suzukiApertureL2Equiv a)
      (suzukiRaisedMetricCovariance a t (suzukiTaExponentialL2 a 1)) := by
  rw [← suzukiRaisedMetricRawDeficiency_physical]
  change _ = (suzukiApertureL2Equiv a) ((suzukiApertureL2Equiv a).symm _)
  rw [(suzukiApertureL2Equiv a).apply_symm_apply]
  rfl

/-- Actual physical source defect, controlled independently of the increment. -/
theorem norm_suzukiRaisedMetric_physical_defect_le
    (a : SuzukiPositiveAperture) (t : ℝ≥0) :
    ‖(suzukiRaisedMetricShift a t : ℂ) • suzukiRaisedMetricPhysical a t -
        ccmPolarApertureVector a 1‖ ≤
      boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) *
        ‖ccmArchimedeanFormToAperture a
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)) -
            ccmSourceShiftProfile a (ccmPolarApertureVector a 1)‖ := by
  let e := suzukiApertureL2Equiv a
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
  let p := suzukiTaExponentialL2 a 1
  let f := ccmArchimedeanFormToAperture a
    (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1))
  have hp : e p = ccmPolarApertureVector a 1 := by
    apply Subtype.ext
    exact suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector a 1
  have hf : e (suzukiWeilIntervalCovariance a p) = f := by
    rw [← suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance]
    change e (e.symm _) = _
    rw [e.apply_symm_apply]
    rfl
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have hnorm (d : ℝ) (v : SuzukiApertureIntervalL2 a.1) :
      ‖(d : ℂ) • e v - e p‖ = ‖(d : ℂ) • v - p‖ := by
    rw [← e.map_smul, ← e.map_sub, e.norm_map]
  rw [physical_eq, ← hp, hnorm]
  apply (norm_suzukiRaisedMetric_source_defect_le a t p).trans_eq
  rw [← hnorm c, hf, hp]
  have hid : (c : ℂ) • f - ccmPolarApertureVector a 1 =
      (c : ℂ) • (f - ccmSourceShiftProfile a (ccmPolarApertureVector a 1)) := by
    change _ = (c : ℂ) • (f - (((c⁻¹ : ℝ) : ℂ) • ccmPolarApertureVector a 1))
    rw [smul_sub, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne',
      Complex.ofReal_one, one_smul]
  rw [hid, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]

def suzukiRaisedMetricMixedPairing (b : SuzukiRaisedMetricParameters) (s : ℝ) : ℂ :=
  inner ℂ (ccmPolarApertureVector b.1 s) (suzukiRaisedMetricPhysical b.1 b.2)

def suzukiRaisedMetricMixedScale (b : SuzukiRaisedMetricParameters) (s : ℝ) : ℝ :=
  suzukiRaisedMetricShift b.1 b.2 * Real.exp (-(1+s)*b.1.1)

/-- Joint-filter convergence is uniform over every nonnegative shift increment. -/
theorem tendsto_suzukiRaisedMetric_mixed_errors (s : ℝ) (hs : 1/2 ≤ s) :
    Tendsto (fun b : SuzukiRaisedMetricParameters =>
      (suzukiRaisedMetricMixedScale b s : ℂ) * suzukiRaisedMetricMixedPairing b s -
        (Real.exp (-(1+s)*b.1.1) : ℂ) *
          inner ℂ (ccmPolarApertureVector b.1 s) (ccmPolarApertureVector b.1 1))
      (comap (fun b : SuzukiRaisedMetricParameters => b.1.1) atTop) (𝓝 0) ∧
    Tendsto (fun b : SuzukiRaisedMetricParameters =>
      (suzukiRaisedMetricMixedScale b s : ℂ) * suzukiRaisedMetricMixedPairing b (-s) -
        (Real.exp (-(1+s)*b.1.1) : ℂ) *
          inner ℂ (ccmPolarApertureVector b.1 (-s)) (ccmPolarApertureVector b.1 1))
      (comap (fun b : SuzukiRaisedMetricParameters => b.1.1) atTop) (𝓝 0) := by
  let l := comap (fun b : SuzukiRaisedMetricParameters => b.1.1) atTop
  let C := ‖ccmArchimedeanRemainderScalar‖ + 47
  let error := fun a : SuzukiPositiveAperture =>
    ‖ccmArchimedeanFormToAperture a
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)) -
        ccmSourceShiftProfile a (ccmPolarApertureVector a 1)‖
  have hf : Tendsto (fun b : SuzukiRaisedMetricParameters => b.1) l
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) :=
    tendsto_comap_iff.2 tendsto_comap
  have hb : Tendsto (fun b : SuzukiRaisedMetricParameters => C * error b.1) l (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (tendsto_suzukiTaV2_rawSource_profile_norm.const_mul C).comp hf
  have herr (v : (a : SuzukiPositiveAperture) → suzukiApertureHilbert a)
      (hv : ∀ a, ‖v a‖ ≤ Real.exp (s*a.1)) :
      Tendsto (fun b : SuzukiRaisedMetricParameters =>
        (suzukiRaisedMetricMixedScale b s : ℂ) *
            inner ℂ (v b.1) (suzukiRaisedMetricPhysical b.1 b.2) -
          (Real.exp (-(1+s)*b.1.1) : ℂ) * inner ℂ (v b.1) (ccmPolarApertureVector b.1 1))
        l (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp only [sub_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
    apply Eventually.of_forall
    intro b
    let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b.1)
    let r := Real.exp (-(1+s)*b.1.1)
    let d := suzukiRaisedMetricShift b.1 b.2
    let f := suzukiRaisedMetricPhysical b.1 b.2
    let p := ccmPolarApertureVector b.1 1
    have hr : 0 ≤ r := (Real.exp_pos _).le
    have heq : (suzukiRaisedMetricMixedScale b s : ℂ) * inner ℂ (v b.1) f -
        (r : ℂ) * inner ℂ (v b.1) p =
          (r : ℂ) * inner ℂ (v b.1) ((d : ℂ) • f - p) := by
      rw [inner_sub_right, inner_smul_right (v b.1) f (d : ℂ)]
      change (((d*r : ℝ) : ℂ) * _) - _ = _
      push_cast
      ring
    have hfactor : r * Real.exp (s*b.1.1) * c ≤ C := by
      calc
        _ ≤ r * Real.exp (s*b.1.1) * (C * Real.exp b.1.1) :=
          mul_le_mul_of_nonneg_left (suzukiWeilIntervalShift_le_exp b.1)
            (mul_nonneg hr (Real.exp_pos _).le)
        _ = C := by
          change Real.exp (-(1+s)*b.1.1) * Real.exp (s*b.1.1) *
            (C * Real.exp b.1.1) = C
          rw [show Real.exp (-(1+s)*b.1.1) * Real.exp (s*b.1.1) *
            (C * Real.exp b.1.1) = C *
              (Real.exp (-(1+s)*b.1.1) * Real.exp (s*b.1.1) * Real.exp b.1.1) by ring,
            ← Real.exp_add, ← Real.exp_add,
            show -(1+s)*b.1.1+s*b.1.1+b.1.1 = 0 by ring, Real.exp_zero, mul_one]
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    calc
      _ ≤ r * (‖v b.1‖ * ‖(d : ℂ) • f - p‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) hr
      _ ≤ r * (Real.exp (s*b.1.1) * (c * error b.1)) := by
        apply mul_le_mul_of_nonneg_left _ hr
        exact mul_le_mul (hv b.1) (norm_suzukiRaisedMetric_physical_defect_le b.1 b.2)
          (norm_nonneg _) (Real.exp_pos _).le
      _ = (r * Real.exp (s*b.1.1) * c) * error b.1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
  exact ⟨herr (fun a => ccmPolarApertureVector a s)
    (fun a => norm_ccmPolarApertureVector_le_exp_of_half_le a s hs),
    herr (fun a => ccmPolarApertureVector a (-s))
      (fun a => norm_ccmPolarApertureVector_neg_le_exp_of_half_le a s hs)⟩

/-- All raised shifts have the same normalized mixed-source limit. -/
theorem tendsto_suzukiRaisedMetric_mixed_pairings (s : Set.Ioo (1/2 : ℝ) 1) :
    Tendsto (fun b : SuzukiRaisedMetricParameters =>
      (suzukiRaisedMetricMixedScale b s.1 : ℂ) * suzukiRaisedMetricMixedPairing b s.1)
      (comap (fun b : SuzukiRaisedMetricParameters => b.1.1) atTop)
      (𝓝 ((1/(1+s.1) : ℝ) : ℂ)) ∧
    Tendsto (fun b : SuzukiRaisedMetricParameters =>
      (suzukiRaisedMetricMixedScale b s.1 : ℂ) * suzukiRaisedMetricMixedPairing b (-s.1))
      (comap (fun b : SuzukiRaisedMetricParameters => b.1.1) atTop) (𝓝 0) := by
  have hf : Tendsto (fun b : SuzukiRaisedMetricParameters => b.1)
      (comap (fun b : SuzukiRaisedMetricParameters => b.1.1) atTop)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) :=
    tendsto_comap_iff.2 tendsto_comap
  obtain ⟨hp, hm⟩ := tendsto_suzukiTaV2_scaled_mixed_source_pairings s
  obtain ⟨hep, hem⟩ := tendsto_suzukiTaV2_scaled_mixed_source_errors s.1 s.2.1.le
  obtain ⟨htp, htm⟩ := tendsto_suzukiRaisedMetric_mixed_errors s.1 s.2.1.le
  constructor
  · simpa only [Function.comp_def, sub_sub_cancel, sub_add_cancel, sub_zero, zero_add] using
      htp.add ((hp.sub hep).comp hf)
  · simpa only [Function.comp_def, sub_sub_cancel, sub_add_cancel, sub_self, zero_add] using
      htm.add ((hm.sub hem).comp hf)

end RHTower
end
