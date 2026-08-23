import GaloisForLFunctions.RHTower.SoninSincFullMellin
import GaloisForLFunctions.RHTower.SoninExtendedMellinPole

/-!
# The functional equation on the extended Sonine space

Burnol's functional equation `M(F₊f)(s) = M(f)(1-s)` is proved in the corpus for the Sonine space
`K_a`.  Splitting a vector of the extended space as `f = h + c·fourierBandIndicator a` — with `h`
in the perpendicular of the frequency band and `c` the Fourier head — reduces the extended case to
two ingredients that are now available: the head-carrying functional equation for `h`
(`soninMellinExtension_add_head_functional_equation`) and the explicit sinc transform
`sincFullMellin_eq`.

## Main results

* `extendedTailMellin`, `extendedFullMellin`
* `soninMellinIntegral_bandIndicator`
* `extendedFullMellin_functional_equation` — **the functional equation on `L_a`**
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The continued full Mellin transform of a vector of `L_a` with Fourier head `c`. -/
def extendedFullMellin (a : ℝ) (c : ℂ) (f : SoninL2) (s : ℂ) : ℂ :=
  extendedTailMellin a c f s + ∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t

/-- The Mellin integral of the band indicator. -/
theorem soninMellinIntegral_bandIndicator {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.re < 1) :
    soninMellinIntegral (bandIndicator a) z
      = ((a : ℝ) : ℂ) ^ ((1 : ℂ) - z) / (1 - z) := by
  have hcongr : soninMellinIntegral (bandIndicator a) z
      = ∫ t in Ioi (0 : ℝ), Set.indicator (Set.Ioc (0 : ℝ) a)
          (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-z)) t := by
    rw [soninMellinIntegral]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (bandIndicator_coeFn a),
      ae_restrict_mem measurableSet_Ioi] with t ht htpos
    have ht0 : (0 : ℝ) < t := htpos
    rw [ht]
    by_cases hle : t ≤ a
    · have hmem : t ∈ centralInterval a := by
        rw [centralInterval, Set.mem_Icc]
        exact ⟨by linarith, hle⟩
      have hmem2 : t ∈ Set.Ioc (0 : ℝ) a := ⟨ht0, hle⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem2, mul_one]
    · have hmem : t ∉ centralInterval a := by
        rw [centralInterval, Set.mem_Icc]
        exact fun hc => hle hc.2
      have hmem2 : t ∉ Set.Ioc (0 : ℝ) a := fun hc => hle hc.2
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem2, mul_zero]
  rw [hcongr, MeasureTheory.setIntegral_indicator measurableSet_Ioc]
  have hinter : Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) a = Set.Ioc (0 : ℝ) a := by
    rw [Set.inter_eq_right]
    exact fun x hx => hx.1
  rw [hinter, ← intervalIntegral.integral_of_le ha.le]
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) - z).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hr : -1 < (-z).re := by
    rw [Complex.neg_re]
    linarith
  rw [integral_cpow (Or.inl hr)]
  have hsum : -z + 1 = (1 : ℂ) - z := by ring
  rw [hsum, Complex.ofReal_zero, Complex.zero_cpow hne, sub_zero]

theorem integrableOn_cpow_mul_fourier_Ioi {a : ℝ} (ha : 0 < a) {g : SoninL2}
    (hg : g ∈ (centralFourierForbidden a)ᗮ) {z : ℂ} (hz : 1 / 2 < z.re) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-z)
      * ((fourierUnitary g : SoninL2) : ℝ → ℂ) t) (Ioi (0 : ℝ)) volume := by
  have hband := fourier_indicator_ae_zero_of_mem_fourierOrthogonal hg
  have hzero : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a →
      ((fourierUnitary g : SoninL2) : ℝ → ℂ) t = 0 := by
    filter_upwards [hband] with t ht hmem
    simpa [Set.indicator_of_mem hmem] using ht
  have htail := integrableOn_cpow_mul_Ioi ha (fourierUnitary g) hz
  have hhead : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-z)
      * ((fourierUnitary g : SoninL2) : ℝ → ℂ) t) (Ioc (0 : ℝ) a) volume := by
    refine (integrable_zero ℝ ℂ (volume.restrict (Ioc (0 : ℝ) a))).congr ?_
    filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem measurableSet_Ioc] with t ht hmem
    have hband2 : t ∈ centralInterval a := by
      rw [centralInterval, Set.mem_Icc]
      exact ⟨by linarith [hmem.1, ha], hmem.2⟩
    rw [ht hband2, mul_zero]
    rfl
  have hunion : Set.Ioc (0 : ℝ) a ∪ Set.Ioi a = Set.Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi ha.le
  rw [← hunion]
  exact hhead.union htail

theorem soninMellinIntegral_fourier_split {a : ℝ} (ha : 0 < a) {f : SoninL2} {c : ℂ}
    (hg : f - c • fourierBandIndicator a ∈ (centralFourierForbidden a)ᗮ) {z : ℂ}
    (hz : 1 / 2 < z.re) (hz1 : z.re < 1) :
    soninMellinIntegral (fourierUnitary f) z
      = soninMellinIntegral (fourierUnitary (f - c • fourierBandIndicator a)) z
        + c * (((a : ℝ) : ℂ) ^ ((1 : ℂ) - z) / (1 - z)) := by
  have hsplit : fourierUnitary f
      = fourierUnitary (f - c • fourierBandIndicator a) + c • bandIndicator a := by
    rw [map_sub, map_smul, fourierBandIndicator, LinearIsometryEquiv.apply_symm_apply]
    abel
  have h1 := integrableOn_cpow_mul_fourier_Ioi ha hg hz
  have h2 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-z)
      * ((c • bandIndicator a : SoninL2) : ℝ → ℂ) t) (Ioi (0 : ℝ)) volume := by
    have hb : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-z)
        * ((bandIndicator a : SoninL2) : ℝ → ℂ) t) (Ioi (0 : ℝ)) volume := by
      have := integrableOn_cpow_mul_Ioi ha (bandIndicator a) hz
      have hhead : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-z)
          * ((bandIndicator a : SoninL2) : ℝ → ℂ) t) (Ioc (0 : ℝ) a) volume := by
        have hmaj : IntegrableOn (fun t : ℝ => t ^ (-z.re)) (Ioc (0 : ℝ) a) volume := by
          have hr : -1 < -z.re := by linarith
          exact (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := a) hr).1
        refine Integrable.mono' hmaj ?_ ?_
        · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
            |>.mul ((Lp.aestronglyMeasurable (bandIndicator a)).restrict)
          exact (Complex.continuousAt_ofReal_cpow_const t (-z)
            (Or.inr (ne_of_gt ht.1))).continuousWithinAt
        · filter_upwards [ae_restrict_of_ae (bandIndicator_coeFn a),
            ae_restrict_mem measurableSet_Ioc] with t ht hmem
          have htpos : 0 < t := hmem.1
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re, ht]
          have hle : ‖(centralInterval a).indicator (fun _ => (1 : ℂ)) t‖ ≤ 1 := by
            by_cases hb2 : t ∈ centralInterval a
            · rw [Set.indicator_of_mem hb2]
              simp
            · rw [Set.indicator_of_notMem hb2]
              simp
          calc t ^ (-z.re) * ‖(centralInterval a).indicator (fun _ => (1 : ℂ)) t‖
              ≤ t ^ (-z.re) * 1 := by
                exact mul_le_mul_of_nonneg_left hle (Real.rpow_pos_of_pos htpos _).le
            _ = t ^ (-z.re) := by ring
      have hunion : Set.Ioc (0 : ℝ) a ∪ Set.Ioi a = Set.Ioi (0 : ℝ) :=
        Set.Ioc_union_Ioi_eq_Ioi ha.le
      rw [← hunion]
      exact hhead.union this
    refine (hb.const_mul c).congr ?_
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c (bandIndicator a))] with t ht
    rw [ht, Pi.smul_apply, smul_eq_mul]
    ring
  rw [soninMellinIntegral, soninMellinIntegral]
  have hstep : (∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-z)
        * ((fourierUnitary f : SoninL2) : ℝ → ℂ) t)
      = (∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-z)
          * ((fourierUnitary (f - c • fourierBandIndicator a) : SoninL2) : ℝ → ℂ) t)
        + ∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-z)
          * ((c • bandIndicator a : SoninL2) : ℝ → ℂ) t := by
    rw [← MeasureTheory.integral_add h1 h2]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (hsplit ▸ Lp.coeFn_add
      (fourierUnitary (f - c • fourierBandIndicator a)) (c • bandIndicator a))] with t ht
    rw [ht, Pi.add_apply]
    ring
  rw [hstep]
  congr 1
  have hval : (∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-z)
      * ((c • bandIndicator a : SoninL2) : ℝ → ℂ) t)
      = c * soninMellinIntegral (bandIndicator a) z := by
    rw [soninMellinIntegral, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c (bandIndicator a))] with t ht
    rw [ht, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hval, soninMellinIntegral_bandIndicator ha hz1]

/-! ## The near-zero head is integrable below the critical line -/

theorem memLp_two_cpow_Ioo {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : s.re < 1 / 2) :
    MemLp (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s)) 2 (volume.restrict (Ioo (0 : ℝ) a)) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s))
      (volume.restrict (Ioo (0 : ℝ) a)) := by
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioo
    exact (Complex.continuousAt_ofReal_cpow_const t (-s)
      (Or.inr (ne_of_gt ht.1))).continuousWithinAt
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hr : -1 < -(2 * s.re) := by linarith
  have hint : IntegrableOn (fun t : ℝ => t ^ (-(2 * s.re))) (Ioo (0 : ℝ) a) volume := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := a) hr).1
    exact h.mono_set Set.Ioo_subset_Ioc_self
  refine hint.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have htpos : 0 < t := ht.1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re,
    ← Real.rpow_natCast (t ^ (-s.re)) 2, ← Real.rpow_mul htpos.le]
  norm_num
  congr 1
  ring

theorem integrableOn_cpow_mul_Ioo {a : ℝ} (ha : 0 < a) (g : SoninL2) {s : ℂ}
    (hs : s.re < 1 / 2) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t)
      (Ioo (0 : ℝ) a) volume := by
  have hg2 : MemLp ((g : ℝ → ℂ)) 2 (volume.restrict (Ioo (0 : ℝ) a)) :=
    (Lp.memLp g).restrict (Ioo (0 : ℝ) a)
  exact (memLp_two_cpow_Ioo ha hs).integrable_mul hg2

/-! ## The functional equation on `L_a` -/

/-- **The functional equation on the extended Sonine space.** -/
theorem extendedFullMellin_functional_equation {a : ℝ} (ha : 0 < a) {f : SoninL2} {c : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    {s : ℂ} (hs0 : 0 < s.re) (hs : s.re < 1 / 2) :
    extendedFullMellin a c f s
      = burnolChiFactor s * soninMellinIntegral (fourierUnitary f) (1 - s) := by
  set h : SoninL2 := f - c • fourierBandIndicator a with hh
  have hg : h ∈ (centralFourierForbidden a)ᗮ := sub_smul_fourierBandIndicator_mem hc
  have hhev : h ∈ evenSubspace :=
    Submodule.sub_mem _ hev (Submodule.smul_mem _ _ (fourierBandIndicator_mem_evenSubspace a))
  have hFE := soninMellinExtension_add_head_functional_equation ha hhev hg hs0 hs
  -- the explicit sinc contribution
  have hsinc := sincFullMellin_eq ha hs0 hs
  have hsincsplit := sincFullMellin_split ha hs0 (by linarith)
  -- the head splits
  have hheadf : (∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
      = (∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (h : ℝ → ℂ) t)
        + c * ∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * soninSincKernel a t := by
    have h1 := integrableOn_cpow_mul_Ioo ha h hs
    have h2 : IntegrableOn (fun t : ℝ => c * (((t : ℝ) : ℂ) ^ (-s) * soninSincKernel a t))
        (Ioo (0 : ℝ) a) volume :=
      (integrableOn_cpow_mul_Ioo ha (fourierBandIndicator a) hs).const_mul c
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add h1 h2]
    · refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (hh ▸ Lp.coeFn_sub f (c • fourierBandIndicator a)),
        ae_restrict_of_ae (Lp.coeFn_smul c (fourierBandIndicator a))] with t k1 k2
      have hft : (f : ℝ → ℂ) t = (h : ℝ → ℂ) t + c * soninSincKernel a t := by
        rw [hh, k1, Pi.sub_apply, k2, Pi.smul_apply, smul_eq_mul, soninSincKernel]
        ring
      rw [hft]
      ring
  -- the sinc head in the two orders
  have hcomm : (∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * soninSincKernel a t)
      = ∫ t in Set.Ioc (0 : ℝ) a, soninSincKernel a t * ((t : ℝ) : ℂ) ^ (-s) := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  have hsplitFourier := soninMellinIntegral_fourier_split ha (c := c) hg
    (z := 1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have hone : (1 : ℂ) - (1 - s) = s := by ring
  rw [hone] at hsplitFourier
  rw [extendedFullMellin, extendedTailMellin, ← hh, hheadf, hcomm, hsplitFourier]
  have hsincval : sincMellin a s
      = burnolChiFactor s * (((a : ℝ) : ℂ) ^ s / s)
        - ∫ t in Set.Ioc (0 : ℝ) a, soninSincKernel a t * ((t : ℝ) : ℂ) ^ (-s) := by
    rw [← hsinc, hsincsplit]
    ring
  rw [hsincval]
  linear_combination hFE

end RHTower

end
