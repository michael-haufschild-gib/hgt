import GaloisForLFunctions.RHTower.SoninDecayTailIdentity
import GaloisForLFunctions.RHTower.SoninFunctionalEquation
import GaloisForLFunctions.HTGeometry.LineScalingL2

/-!
# The full Mellin transform of the sinc kernel

`fourierBandIndicator a (t) = sin(2πat)/(πt)` is bounded by `2a` near the origin and by `1/(π|t|)`
at infinity, so `∫_0^∞ (fourierBandIndicator a)(t) t^{-s} dt` converges on the strip `0 < Re s < 1`.
This module identifies it: it is `χ(s)·a^s/s`.

The proof never computes the sine Mellin transform.  For `0 < a ≤ b` the difference
`fourierBandIndicator b - fourierBandIndicator a` has Fourier transform vanishing on the band of
aperture `a`, so the corpus's functional equation applies to it and evaluates the difference of the
two full Mellin transforms as `χ(s)(b^s - a^s)/s`.  Since the sinc kernels are dilates of one
another, the full Mellin transform is `a^s` times its value at `a = 1`, and comparing the two
statements at `a = 1, b = 2` forces that value to be `χ(s)/s`.

## Main results

* `norm_soninSincKernel_le` — the `2a` bound near the origin
* `sincFullMellin`, `sincFullMellin_split`, `sincFullMellin_scale`
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Near the origin the sinc kernel is bounded by twice the aperture. -/
theorem norm_soninSincKernel_le {a : ℝ} (ha : 0 < a) :
    ∀ᵐ t ∂(volume : Measure ℝ), ‖soninSincKernel a t‖ ≤ 2 * a := by
  filter_upwards [coeFn_fourierBandIndicator_ae ha, ae_ne_zero] with t h1 h2
  have hval : soninSincKernel a t
      = ((Real.sin (2 * Real.pi * a * t) / (Real.pi * t) : ℝ) : ℂ) := h1
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos Real.pi_pos]
  have habs : (0 : ℝ) < |t| := abs_pos.2 h2
  have hnum : |Real.sin (2 * Real.pi * a * t)| ≤ 2 * Real.pi * a * |t| := by
    refine Real.abs_sin_le_abs.trans (le_of_eq ?_)
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi * a)]
  rw [div_le_iff₀ (by positivity)]
  calc |Real.sin (2 * Real.pi * a * t)| ≤ 2 * Real.pi * a * |t| := hnum
    _ = 2 * a * (Real.pi * |t|) := by ring

theorem integrableOn_sincHead {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : s.re < 1) :
    IntegrableOn (fun t : ℝ => soninSincKernel a t * ((t : ℝ) : ℂ) ^ (-s))
      (Ioc (0 : ℝ) a) volume := by
  have hr : -1 < -s.re := by linarith
  have hmaj : IntegrableOn (fun t : ℝ => 2 * a * t ^ (-s.re)) (Ioc (0 : ℝ) a) volume := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := a) hr).1
    exact h.const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · refine ((aestronglyMeasurable_soninSincKernel a).restrict).mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
    exact (Complex.continuousAt_ofReal_cpow_const t (-s)
      (Or.inr (ne_of_gt ht.1))).continuousWithinAt
  · filter_upwards [ae_restrict_of_ae (norm_soninSincKernel_le ha),
      ae_restrict_mem measurableSet_Ioc] with t ht hmem
    have htpos : 0 < t := hmem.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right ht (Real.rpow_pos_of_pos htpos _).le

/-- The full Mellin transform of the sinc kernel. -/
def sincFullMellin (a : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), soninSincKernel a t * ((t : ℝ) : ℂ) ^ (-s)

theorem sincFullMellin_split {a : ℝ} (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    sincFullMellin a s
      = (∫ t in Ioc (0 : ℝ) a, soninSincKernel a t * ((t : ℝ) : ℂ) ^ (-s)) + sincMellin a s := by
  have h1 := integrableOn_sincHead ha hs1
  have h2 := integrableOn_sincMellin ha hs0 (le_refl a)
  have hunion : Set.Ioc (0 : ℝ) a ∪ Set.Ioi a = Set.Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi ha.le
  rw [sincFullMellin, ← hunion,
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2]
  rfl

theorem integrableOn_sincFull {a : ℝ} (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    IntegrableOn (fun t : ℝ => soninSincKernel a t * ((t : ℝ) : ℂ) ^ (-s))
      (Ioi (0 : ℝ)) volume := by
  have h1 := integrableOn_sincHead ha hs1
  have h2 := integrableOn_sincMellin ha hs0 (le_refl a)
  have hunion : Set.Ioc (0 : ℝ) a ∪ Set.Ioi a = Set.Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi ha.le
  rw [← hunion]
  exact h1.union h2

/-! ## The dilation law -/

theorem soninSincKernel_scale {c : ℝ} (hc : 0 < c) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      soninSincKernel c t = ((c : ℝ) : ℂ) * soninSincKernel 1 (c * t) := by
  have hqmp := GaloisForLFunctions.HTGeometry.quasiMeasurePreserving_const_mul (ne_of_gt hc)
  filter_upwards [coeFn_fourierBandIndicator_ae hc,
    hqmp.ae (coeFn_fourierBandIndicator_ae one_pos), ae_ne_zero] with t h1 h2 h3
  have hv1 : soninSincKernel c t = ((Real.sin (2 * Real.pi * c * t) / (Real.pi * t) : ℝ) : ℂ) := h1
  have hv2 : soninSincKernel 1 (c * t)
      = ((Real.sin (2 * Real.pi * 1 * (c * t)) / (Real.pi * (c * t)) : ℝ) : ℂ) := h2
  have harg : 2 * Real.pi * 1 * (c * t) = 2 * Real.pi * c * t := by ring
  rw [hv1, hv2, harg, ← Complex.ofReal_mul]
  congr 1
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp

theorem sincFullMellin_scale {c : ℝ} (hc : 0 < c) (s : ℂ) :
    sincFullMellin c s = ((c : ℝ) : ℂ) ^ s * sincFullMellin 1 s := by
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  set G : ℝ → ℂ := fun x => ((c : ℝ) : ℂ) * soninSincKernel 1 x * ((x / c : ℝ) : ℂ) ^ (-s) with hG
  have hstep1 : sincFullMellin c s = ∫ t in Ioi (0 : ℝ), G (c * t) := by
    rw [sincFullMellin]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (soninSincKernel_scale hc)] with t ht
    rw [ht, hG]
    simp only
    have hdiv : (c * t / c : ℝ) = t := by field_simp
    rw [hdiv]
  have hstep2 : (∫ t in Ioi (0 : ℝ), G (c * t)) = c⁻¹ • ∫ x in Ioi (0 : ℝ), G x := by
    have h := integral_comp_mul_left_Ioi G 0 hc
    rw [mul_zero] at h
    exact h
  have harg0 : (((c : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hc.le]
    exact ne_of_lt Real.pi_pos
  have hpow : ∀ x : ℝ, 0 < x →
      ((x / c : ℝ) : ℂ) ^ (-s) = ((x : ℝ) : ℂ) ^ (-s) * ((c : ℝ) : ℂ) ^ s := by
    intro x hx
    have hdiv : (x / c : ℝ) = x * c⁻¹ := by ring
    rw [hdiv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hx.le (by positivity), Complex.ofReal_inv,
      Complex.inv_cpow _ _ harg0]
    congr 1
    rw [Complex.cpow_neg, inv_inv]
  have hstep3 : (∫ x in Ioi (0 : ℝ), G x)
      = ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ s * sincFullMellin 1 s := by
    rw [sincFullMellin, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [hG]
    simp only
    rw [hpow x hx]
    ring
  rw [hstep1, hstep2, hstep3, Complex.real_smul, Complex.ofReal_inv]
  field_simp

/-! ## The difference of two sinc kernels -/

theorem bandIndicator_mem_evenSubspace (a : ℝ) : bandIndicator a ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hrefl := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  filter_upwards [l2Reflection_ae (bandIndicator a), hrefl.ae (bandIndicator_coeFn a),
    bandIndicator_coeFn a] with x h1 h2 h3
  rw [h1, h2, h3]
  by_cases hx : x ∈ centralInterval a
  · rw [Set.indicator_of_mem ((neg_mem_centralInterval_iff a x).2 hx),
      Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun hc => hx ((neg_mem_centralInterval_iff a x).1 hc)),
      Set.indicator_of_notMem hx]

theorem fourierBandIndicator_mem_evenSubspace (a : ℝ) :
    fourierBandIndicator a ∈ evenSubspace :=
  fourierUnitary_symm_mem_evenSubspace (bandIndicator_mem_evenSubspace a)

theorem fourierBandIndicator_sub_mem_fourierOrthogonal {a b : ℝ} (hab : a ≤ b) :
    fourierBandIndicator b - fourierBandIndicator a ∈ (centralFourierForbidden a)ᗮ := by
  refine mem_fourierOrthogonal_of_ae ?_
  have hval : fourierUnitary (fourierBandIndicator b - fourierBandIndicator a)
      = bandIndicator b - bandIndicator a := by
    rw [map_sub, fourierBandIndicator, fourierBandIndicator,
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [hval]
  filter_upwards [Lp.coeFn_sub (bandIndicator b) (bandIndicator a),
    bandIndicator_coeFn b, bandIndicator_coeFn a] with u h1 h2 h3 hmem
  have hmemb : u ∈ centralInterval b := by
    rw [centralInterval, Set.mem_Icc]
    rw [centralInterval, Set.mem_Icc] at hmem
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  rw [h1, Pi.sub_apply, h2, h3, Set.indicator_of_mem hmemb, Set.indicator_of_mem hmem]
  ring

/-- **The difference of two sinc Mellin transforms.** -/
theorem sincFullMellin_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ}
    (hs0 : 0 < s.re) (hs : s.re < 1 / 2) :
    sincFullMellin b s - sincFullMellin a s
      = burnolChiFactor s * ((((b : ℝ) : ℂ) ^ s - ((a : ℝ) : ℂ) ^ s) / s) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set w : SoninL2 := fourierBandIndicator b - fourierBandIndicator a with hw
  have hwmem : w ∈ (centralFourierForbidden a)ᗮ :=
    fourierBandIndicator_sub_mem_fourierOrthogonal hab
  have hwev : w ∈ evenSubspace :=
    Submodule.sub_mem _ (fourierBandIndicator_mem_evenSubspace b)
      (fourierBandIndicator_mem_evenSubspace a)
  have hdec : HasInverseDecay w (1 / Real.pi + 1 / Real.pi) :=
    (hasInverseDecay_fourierBandIndicator hb).sub (hasInverseDecay_fourierBandIndicator ha)
  have hFE := soninMellinExtension_add_head_functional_equation ha hwev hwmem hs0 hs
  rw [soninMellinExtension_eq_decayTailMellin ha hdec hwmem hs0] at hFE
  -- identify the right-hand side
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs0
    simp at hs0
  have hRHS : soninMellinIntegral (fourierUnitary w) (1 - s)
      = (((b : ℝ) : ℂ) ^ s - ((a : ℝ) : ℂ) ^ s) / s := by
    have hval : fourierUnitary w = bandIndicator b - bandIndicator a := by
      rw [hw, map_sub, fourierBandIndicator, fourierBandIndicator,
        LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
    have hcongr : soninMellinIntegral (fourierUnitary w) (1 - s)
        = ∫ t in Ioi (0 : ℝ), Set.indicator (Set.Ioc a b)
            (fun t : ℝ => ((t : ℝ) : ℂ) ^ (s - 1)) t := by
      rw [soninMellinIntegral]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (hval ▸ Lp.coeFn_sub (bandIndicator b) (bandIndicator a)),
        ae_restrict_of_ae (bandIndicator_coeFn b), ae_restrict_of_ae (bandIndicator_coeFn a),
        ae_restrict_mem measurableSet_Ioi] with t h1 h2 h3 htpos
      have ht : (0 : ℝ) < t := htpos
      rw [h1, Pi.sub_apply, h2, h3]
      have hneg : -(1 - s) = s - 1 := by ring
      by_cases hle : t ≤ b
      · have hmemb : t ∈ centralInterval b := by
          rw [centralInterval, Set.mem_Icc]
          exact ⟨by linarith, hle⟩
        by_cases hle2 : t ≤ a
        · have hmema : t ∈ centralInterval a := by
            rw [centralInterval, Set.mem_Icc]
            exact ⟨by linarith, hle2⟩
          have hnot : t ∉ Set.Ioc a b := fun hc => absurd hc.1 (not_lt.2 hle2)
          rw [Set.indicator_of_mem hmemb, Set.indicator_of_mem hmema,
            Set.indicator_of_notMem hnot]
          ring
        · have hmema : t ∉ centralInterval a := by
            rw [centralInterval, Set.mem_Icc]
            exact fun hc => hle2 hc.2
          have hmem : t ∈ Set.Ioc a b := ⟨not_le.1 hle2, hle⟩
          rw [Set.indicator_of_mem hmemb, Set.indicator_of_notMem hmema,
            Set.indicator_of_mem hmem, hneg]
          ring
      · have hmemb : t ∉ centralInterval b := by
          rw [centralInterval, Set.mem_Icc]
          exact fun hc => hle hc.2
        have hmema : t ∉ centralInterval a := by
          rw [centralInterval, Set.mem_Icc]
          exact fun hc => hle (le_trans hc.2 hab)
        have hnot : t ∉ Set.Ioc a b := fun hc => hle hc.2
        rw [Set.indicator_of_notMem hmemb, Set.indicator_of_notMem hmema,
          Set.indicator_of_notMem hnot]
        ring
    rw [hcongr, MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    have hinter : Set.Ioi (0 : ℝ) ∩ Set.Ioc a b = Set.Ioc a b := by
      rw [Set.inter_eq_right]
      exact fun x hx => lt_of_lt_of_le ha (le_of_lt hx.1)
    rw [hinter, ← intervalIntegral.integral_of_le hab]
    have hr : -1 < (s - 1).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    rw [integral_cpow (Or.inl hr)]
    have hsum : s - 1 + 1 = s := by ring
    rw [hsum]
  rw [hRHS] at hFE
  -- identify the left-hand side
  have hleft : decayTailMellin w a s
        + ∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (w : ℝ → ℂ) t
      = sincFullMellin b s - sincFullMellin a s := by
    have hs1' : s.re < 1 := by linarith
    have hb1 := integrableOn_sincFull hb hs0 hs1'
    have ha1 := integrableOn_sincFull ha hs0 hs1'
    have hwae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        (w : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s)
          = soninSincKernel b t * ((t : ℝ) : ℂ) ^ (-s)
            - soninSincKernel a t * ((t : ℝ) : ℂ) ^ (-s) := by
      filter_upwards [ae_restrict_of_ae
        (Lp.coeFn_sub (fourierBandIndicator b) (fourierBandIndicator a))] with t ht
      have hwt : (w : ℝ → ℂ) t = soninSincKernel b t - soninSincKernel a t := by
        rw [hw, ht, Pi.sub_apply]
        rfl
      rw [hwt]
      ring
    have hwint : IntegrableOn (fun t : ℝ => (w : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s))
        (Set.Ioi (0 : ℝ)) volume := by
      refine (hb1.sub ha1).congr ?_
      filter_upwards [hwae] with t ht
      rw [Pi.sub_apply]
      exact ht.symm
    have hsub : (∫ t in Set.Ioi (0 : ℝ), (w : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s))
        = sincFullMellin b s - sincFullMellin a s := by
      rw [sincFullMellin, sincFullMellin, ← MeasureTheory.integral_sub hb1 ha1]
      exact integral_congr_ae hwae
    have hunion : Set.Ioc (0 : ℝ) a ∪ Set.Ioi a = Set.Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi ha.le
    have hsplit : (∫ t in Set.Ioi (0 : ℝ), (w : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s))
        = (∫ t in Set.Ioc (0 : ℝ) a, (w : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s))
          + decayTailMellin w a s := by
      rw [← hunion, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hwint.mono_set Set.Ioc_subset_Ioi_self)
        (hwint.mono_set (Set.Ioi_subset_Ioi ha.le))]
      rfl
    have hhead : (∫ t in Set.Ioc (0 : ℝ) a, (w : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s))
        = ∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (w : ℝ → ℂ) t := by
      rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
    rw [← hsub, hsplit, hhead]
    ring
  rw [hleft] at hFE
  exact hFE

/-! ## The value -/

theorem one_lt_norm_two_cpow {s : ℂ} (hs0 : 0 < s.re) : 1 < ‖((2 : ℝ) : ℂ) ^ s‖ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.2 (Or.inl ⟨by norm_num, hs0⟩)

/-- **The sinc Mellin transform at aperture one.** -/
theorem sincFullMellin_one {s : ℂ} (hs0 : 0 < s.re) (hs : s.re < 1 / 2) :
    sincFullMellin 1 s = burnolChiFactor s / s := by
  have h := sincFullMellin_sub (a := 1) (b := 2) one_pos (by norm_num) hs0 hs
  rw [sincFullMellin_scale (by norm_num : (0 : ℝ) < 2) s] at h
  have hone : ((1 : ℝ) : ℂ) ^ s = 1 := by
    rw [Complex.ofReal_one, Complex.one_cpow]
  rw [hone] at h
  have htwo : ((2 : ℝ) : ℂ) ^ s - 1 ≠ 0 := by
    intro hc
    have : ((2 : ℝ) : ℂ) ^ s = 1 := by linear_combination hc
    have hnorm := one_lt_norm_two_cpow hs0
    rw [this] at hnorm
    simp at hnorm
  have hkey : (((2 : ℝ) : ℂ) ^ s - 1) * sincFullMellin 1 s
      = (((2 : ℝ) : ℂ) ^ s - 1) * (burnolChiFactor s / s) := by
    field_simp at h ⊢
    linear_combination h
  exact mul_left_cancel₀ htwo hkey

/-- **The full Mellin transform of the sinc kernel.**  This is the explicit half of Burnol's
Proposition 2.2 for the extended Sonine space. -/
theorem sincFullMellin_eq {a : ℝ} (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) (hs : s.re < 1 / 2) :
    sincFullMellin a s = burnolChiFactor s * (((a : ℝ) : ℂ) ^ s / s) := by
  rw [sincFullMellin_scale ha s, sincFullMellin_one hs0 hs]
  ring

end RHTower

end
