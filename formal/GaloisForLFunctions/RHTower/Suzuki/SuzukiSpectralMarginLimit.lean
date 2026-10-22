import GaloisForLFunctions.RHTower.Suzuki.SuzukiSpectralMarginSource
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2MixedSourceLimit

open Complex Filter
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

abbrev SuzukiSpectralMarginParameters := SuzukiPositiveAperture × SuzukiSpectralMargin

def suzukiSpectralMarginPhysical (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) :
    suzukiApertureHilbert a :=
  ccmArchimedeanFormToAperture a
    (suzukiTaToFormCLM a (suzukiSpectralMarginRawDeficiency a m))

private theorem physical_eq (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) :
    suzukiSpectralMarginPhysical a m = (suzukiApertureL2Equiv a)
      (suzukiSpectralMarginCovariance a m (suzukiTaExponentialL2 a 1)) := by
  rw [← suzukiSpectralMarginRawDeficiency_physical]
  change _ = (suzukiApertureL2Equiv a) ((suzukiApertureL2Equiv a).symm _)
  rw [(suzukiApertureL2Equiv a).apply_symm_apply]
  rfl

/-- Actual weighted physical defect; no positivity of the metric shift is needed. -/
theorem suzukiSpectralMargin_weighted_physical_defect_le
    (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) :
    suzukiSpectralMarginWeight m *
      ‖(suzukiSpectralMarginShift a m : ℂ) • suzukiSpectralMarginPhysical a m -
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
  apply (suzukiSpectralMargin_weighted_source_defect_le a m p).trans_eq
  rw [← hnorm c, hf, hp]
  have hid : (c : ℂ) • f - ccmPolarApertureVector a 1 =
      (c : ℂ) • (f - ccmSourceShiftProfile a (ccmPolarApertureVector a 1)) := by
    change _ = (c : ℂ) • (f - (((c⁻¹ : ℝ) : ℂ) • ccmPolarApertureVector a 1))
    rw [smul_sub, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne',
      Complex.ofReal_one, one_smul]
  rw [hid, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]

def suzukiSpectralMarginMixedPairing (b : SuzukiSpectralMarginParameters) (s : ℝ) : ℂ :=
  inner ℂ (ccmPolarApertureVector b.1 s) (suzukiSpectralMarginPhysical b.1 b.2)

def suzukiSpectralMarginMixedScale (b : SuzukiSpectralMarginParameters) (s : ℝ) : ℝ :=
  suzukiSpectralMarginShift b.1 b.2 * Real.exp (-(1+s)*b.1.1)

/-- Both full complex mixed-source errors vanish after weighting by the
relative floor margin, uniformly over every strictly admissible shift. -/
theorem tendsto_suzukiSpectralMargin_weighted_mixed_errors (s : ℝ) (hs : 1/2 ≤ s) :
    Tendsto (fun b : SuzukiSpectralMarginParameters =>
      (suzukiSpectralMarginWeight b.2 : ℂ) *
        ((suzukiSpectralMarginMixedScale b s : ℂ) * suzukiSpectralMarginMixedPairing b s -
          (Real.exp (-(1+s)*b.1.1) : ℂ) *
            inner ℂ (ccmPolarApertureVector b.1 s) (ccmPolarApertureVector b.1 1)))
      (comap (fun b : SuzukiSpectralMarginParameters => b.1.1) atTop) (𝓝 0) ∧
    Tendsto (fun b : SuzukiSpectralMarginParameters =>
      (suzukiSpectralMarginWeight b.2 : ℂ) *
        ((suzukiSpectralMarginMixedScale b s : ℂ) * suzukiSpectralMarginMixedPairing b (-s) -
          (Real.exp (-(1+s)*b.1.1) : ℂ) *
            inner ℂ (ccmPolarApertureVector b.1 (-s)) (ccmPolarApertureVector b.1 1)))
      (comap (fun b : SuzukiSpectralMarginParameters => b.1.1) atTop) (𝓝 0) := by
  let l := comap (fun b : SuzukiSpectralMarginParameters => b.1.1) atTop
  let C := ‖ccmArchimedeanRemainderScalar‖ + 47
  let error := fun a : SuzukiPositiveAperture =>
    ‖ccmArchimedeanFormToAperture a
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)) -
        ccmSourceShiftProfile a (ccmPolarApertureVector a 1)‖
  have hf : Tendsto (fun b : SuzukiSpectralMarginParameters => b.1) l
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) :=
    tendsto_comap_iff.2 tendsto_comap
  have hb : Tendsto (fun b : SuzukiSpectralMarginParameters => C * error b.1) l (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (tendsto_suzukiTaV2_rawSource_profile_norm.const_mul C).comp hf
  have herr (v : (a : SuzukiPositiveAperture) → suzukiApertureHilbert a)
      (hv : ∀ a, ‖v a‖ ≤ Real.exp (s*a.1)) :
      Tendsto (fun b : SuzukiSpectralMarginParameters =>
        (suzukiSpectralMarginWeight b.2 : ℂ) *
          ((suzukiSpectralMarginMixedScale b s : ℂ) *
              inner ℂ (v b.1) (suzukiSpectralMarginPhysical b.1 b.2) -
            (Real.exp (-(1+s)*b.1.1) : ℂ) * inner ℂ (v b.1) (ccmPolarApertureVector b.1 1)))
        l (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp only [sub_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
    apply Eventually.of_forall
    intro b
    let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b.1)
    let r := Real.exp (-(1+s)*b.1.1)
    let d := suzukiSpectralMarginShift b.1 b.2
    let f := suzukiSpectralMarginPhysical b.1 b.2
    let p := ccmPolarApertureVector b.1 1
    let q := suzukiSpectralMarginWeight b.2
    have hr : 0 ≤ r := (Real.exp_pos _).le
    have hq : 0 ≤ q := (suzukiSpectralMarginWeight_pos b.2).le
    have heq : (suzukiSpectralMarginMixedScale b s : ℂ) * inner ℂ (v b.1) f -
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
    change ‖(q : ℂ) * (_ - _)‖ ≤ _
    rw [heq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    calc
      _ ≤ q * (r * (‖v b.1‖ * ‖(d : ℂ) • f - p‖)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (norm_inner_le_norm (v b.1) ((d : ℂ) • f - p)) hr) hq
      _ = r * ‖v b.1‖ * (q * ‖(d : ℂ) • f - p‖) := by ring
      _ ≤ r * Real.exp (s*b.1.1) * (c * error b.1) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hv b.1) hr
        · exact suzukiSpectralMargin_weighted_physical_defect_le b.1 b.2
        · exact mul_nonneg hq (norm_nonneg _)
        · exact mul_nonneg hr (Real.exp_pos _).le
      _ = (r * Real.exp (s*b.1.1) * c) * error b.1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
  exact ⟨herr (fun a => ccmPolarApertureVector a s)
    (fun a => norm_ccmPolarApertureVector_le_exp_of_half_le a s hs),
    herr (fun a => ccmPolarApertureVector a (-s))
      (fun a => norm_ccmPolarApertureVector_neg_le_exp_of_half_le a s hs)⟩

private theorem weighted_vanishing {f : SuzukiSpectralMarginParameters → ℂ}
    (h : Tendsto f (comap (fun b : SuzukiSpectralMarginParameters => b.1.1) atTop) (𝓝 0)) :
    Tendsto (fun b => (suzukiSpectralMarginWeight b.2 : ℂ) * f b)
      (comap (fun b : SuzukiSpectralMarginParameters => b.1.1) atTop) (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simp only [sub_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [norm_zero] using h.norm)
  apply Eventually.of_forall
  intro b
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (suzukiSpectralMarginWeight_pos b.2)]
  exact mul_le_of_le_one_left (norm_nonneg _) (min_le_left _ _)

/-- The weighted denominator differs from the free positive limit only by
a vanishing error; the weighted opposite-source numerator itself vanishes. -/
theorem tendsto_suzukiSpectralMargin_weighted_mixed_pairings (s : Set.Ioo (1/2 : ℝ) 1) :
    Tendsto (fun b : SuzukiSpectralMarginParameters =>
      (suzukiSpectralMarginWeight b.2 : ℂ) *
        ((suzukiSpectralMarginMixedScale b s.1 : ℂ) * suzukiSpectralMarginMixedPairing b s.1 -
          ((1/(1+s.1) : ℝ) : ℂ)))
      (comap (fun b : SuzukiSpectralMarginParameters => b.1.1) atTop) (𝓝 0) ∧
    Tendsto (fun b : SuzukiSpectralMarginParameters =>
      (suzukiSpectralMarginWeight b.2 : ℂ) *
        ((suzukiSpectralMarginMixedScale b s.1 : ℂ) * suzukiSpectralMarginMixedPairing b (-s.1)))
      (comap (fun b : SuzukiSpectralMarginParameters => b.1.1) atTop) (𝓝 0) := by
  have hf : Tendsto (fun b : SuzukiSpectralMarginParameters => b.1)
      (comap (fun b : SuzukiSpectralMarginParameters => b.1.1) atTop)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) :=
    tendsto_comap_iff.2 tendsto_comap
  obtain ⟨hp, hm⟩ := tendsto_suzukiTaV2_scaled_mixed_source_pairings s
  obtain ⟨hep, hem⟩ := tendsto_suzukiTaV2_scaled_mixed_source_errors s.1 s.2.1.le
  have hgp := ((hp.sub hep).sub_const ((1/(1+s.1) : ℝ) : ℂ)).comp hf
  have hgm := (hm.sub hem).comp hf
  simp only [sub_zero, sub_sub_cancel, sub_self, Function.comp_def] at hgp hgm
  obtain ⟨htp, htm⟩ := tendsto_suzukiSpectralMargin_weighted_mixed_errors s.1 s.2.1.le
  constructor
  · have h := htp.add (weighted_vanishing hgp)
    simpa only [← mul_add, sub_add_sub_cancel, zero_add] using h
  · have h := htm.add (weighted_vanishing hgm)
    simpa only [← mul_add, sub_add_cancel, zero_add] using h

end RHTower
end
