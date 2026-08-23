import GaloisForLFunctions.RHTower.SoninSincTailMellin
import GaloisForLFunctions.RHTower.SoninMellinHalfPlaneExtension
import GaloisForLFunctions.RHTower.SoninExtendedApertureChain

/-!
# The Mellin tail of a vector of the extended Sonine space

Burnol's `L_a` asks the *cosine transform* of a vector to be constant on the band, not zero there.
Subtracting the corresponding multiple of `fourierBandIndicator a` — whose Fourier transform is the
band indicator itself — removes that constant, so the difference lies in the perpendicular of the
frequency band and the corpus's uniform Cauchy estimate continues its Mellin tail to `Re s > 0`.
The subtracted piece is the sinc kernel, whose Mellin tail converges absolutely on the same
half-plane (`SoninSincTailMellin`).

## Main results

* `mem_fourierOrthogonal_of_ae`, `ae_fourier_eq_of_mem_extended`
* `sub_smul_fourierBandIndicator_mem` — the correction lands in `(centralFourierForbidden a)ᗮ`
* `exists_differentiableOn_extendedTailMellin` — the Mellin tail of a vector of `L_a` continues
  holomorphically to `Re s > 0`
-/

noncomputable section

open MeasureTheory Set Filter Topology

open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Vanishing of the Fourier transform on the band -/

theorem mem_fourierOrthogonal_of_ae {a : ℝ} {f : SoninL2}
    (h : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0) :
    f ∈ (centralFourierForbidden a)ᗮ := by
  have hcut : indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (fourierUnitary f) = 0 := by
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a)
      (fourierUnitary f), h,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with u h1 h2 h3
    rw [h1, h3]
    by_cases hmem : u ∈ centralInterval a
    · rw [Set.indicator_of_mem hmem, h2 hmem]
      rfl
    · rw [Set.indicator_of_notMem hmem]
      rfl
  have h0 : fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f = 0 := by
    rw [fourierCutoff_apply, hcut, map_zero]
  have hproj : (fourierForbidden (centralInterval a) (measurableSet_centralInterval a)
      : Submodule ℂ SoninL2).starProjection f = 0 := by
    rw [← fourierCutoff_eq_fourierForbidden_starProjection]
    exact h0
  exact (Submodule.starProjection_apply_eq_zero_iff
    (K := fourierForbidden (centralInterval a) (measurableSet_centralInterval a))).mp hproj

/-! ## The constant Fourier head of a vector of `L_a` -/

theorem mem_centralMeanZeroFourier_iff {a : ℝ} {g : SoninL2} :
    g ∈ centralMeanZeroFourier a ↔ fourierUnitary g ∈ meanZeroBand a := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_fourierForbidden_iff (centralInterval a)
      (measurableSet_centralInterval a) g).1 h1, ?_⟩
    intro q hq
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hq
    have hq' : q = d • bandIndicator a := hd.symm
    have h4 := h2 (d • fourierBandIndicator a) (Submodule.mem_span_singleton.2 ⟨d, rfl⟩)
    have hiso := fourierUnitary.inner_map_map (d • fourierBandIndicator a) g
    rw [map_smul, fourierBandIndicator, LinearIsometryEquiv.apply_symm_apply] at hiso
    rw [hq', hiso]
    exact h4
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_fourierForbidden_iff (centralInterval a)
      (measurableSet_centralInterval a) g).2 h1, ?_⟩
    intro q hq
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hq
    have hq' : q = d • fourierBandIndicator a := hd.symm
    have h4 := h2 (d • bandIndicator a) (Submodule.mem_span_singleton.2 ⟨d, rfl⟩)
    have hiso := fourierUnitary.inner_map_map (d • fourierBandIndicator a) g
    rw [map_smul, fourierBandIndicator, LinearIsometryEquiv.apply_symm_apply] at hiso
    rw [hq']
    have hswap : ⟪d • fourierBandIndicator a, g⟫_ℂ
        = ⟪d • bandIndicator a, fourierUnitary g⟫_ℂ := hiso.symm
    rw [hswap]
    exact h4

theorem ae_fourier_eq_of_mem_extended {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) :
    ∃ c : ℂ, ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c := by
  have hmem : f ∈ (centralMeanZeroFourier a)ᗮ := by
    rw [centralSoninExtendedCarrier] at hf
    exact Submodule.orthogonal_le le_sup_right hf
  have hfour : fourierUnitary f ∈ (meanZeroBand a)ᗮ := by
    intro p hp
    have hpre : fourierUnitary.symm p ∈ centralMeanZeroFourier a := by
      rw [mem_centralMeanZeroFourier_iff, LinearIsometryEquiv.apply_symm_apply]
      exact hp
    have h0 := hmem _ hpre
    have hiso := fourierUnitary.inner_map_map (fourierUnitary.symm p) f
    rw [LinearIsometryEquiv.apply_symm_apply] at hiso
    rw [hiso]
    exact h0
  exact (mem_orthogonal_meanZeroBand_iff a (fourierUnitary f)).1 hfour

theorem sub_smul_fourierBandIndicator_mem {a : ℝ} {f : SoninL2} {c : ℂ}
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c) :
    f - c • fourierBandIndicator a ∈ (centralFourierForbidden a)ᗮ := by
  refine mem_fourierOrthogonal_of_ae ?_
  have hval : fourierUnitary (f - c • fourierBandIndicator a)
      = fourierUnitary f - c • bandIndicator a := by
    rw [map_sub, map_smul, fourierBandIndicator, LinearIsometryEquiv.apply_symm_apply]
  rw [hval]
  filter_upwards [hc, Lp.coeFn_sub (fourierUnitary f) (c • bandIndicator a),
    Lp.coeFn_smul c (bandIndicator a), bandIndicator_coeFn a] with u h1 h2 h3 h4 hmem
  rw [h2, Pi.sub_apply, h3, Pi.smul_apply, h4, h1 hmem, Set.indicator_of_mem hmem]
  simp

/-! ## The Mellin tail on the half-plane of absolute convergence -/

theorem memLp_two_cpow_Ioi {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 / 2 < s.re) :
    MemLp (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s)) 2 (volume.restrict (Ioi a)) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s))
      (volume.restrict (Ioi a)) := by
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact (Complex.continuousAt_ofReal_cpow_const t (-s)
      (Or.inr (ne_of_gt (lt_trans ha ht)))).continuousWithinAt
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hint : IntegrableOn (fun t : ℝ => t ^ (-(2 * s.re))) (Ioi a) volume :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha
  refine hint.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := lt_trans ha ht
  rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re,
    ← Real.rpow_natCast (t ^ (-s.re)) 2, ← Real.rpow_mul htpos.le]
  norm_num
  congr 1
  ring

theorem integrableOn_cpow_mul_Ioi {a : ℝ} (ha : 0 < a) (g : SoninL2) {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t) (Ioi a) volume := by
  have hg2 : MemLp ((g : ℝ → ℂ)) 2 (volume.restrict (Ioi a)) := (Lp.memLp g).restrict (Ioi a)
  exact (memLp_two_cpow_Ioi ha hs).integrable_mul hg2

/-- On the half-plane of absolute convergence the continued Mellin transform is the tail
integral. -/
theorem soninMellinExtension_eq_tail {a : ℝ} (ha : 0 < a) {g : SoninL2}
    (hg : g ∈ (centralFourierForbidden a)ᗮ) {s : ℂ} (hs : 1 / 2 < s.re) :
    soninMellinExtension g a s = ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t := by
  have hs0 : 0 < s.re := by linarith
  have hintA := integrableOn_cpow_mul_Ioi ha g hs
  have hmono : Monotone fun n : ℕ => Set.Ioo a (a + (n : ℝ)) := by
    intro m n hmn
    refine Set.Ioo_subset_Ioo le_rfl ?_
    have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
    linarith
  have htend := MeasureTheory.tendsto_setIntegral_of_monotone
    (μ := (volume : Measure ℝ)) (f := fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t)
    (s := fun n : ℕ => Set.Ioo a (a + (n : ℝ))) (fun _ => measurableSet_Ioo) hmono
    (by rw [iUnion_Ioo_add_nat]; exact hintA)
  rw [iUnion_Ioo_add_nat] at htend
  have hseq : (fun n : ℕ => ∫ t in Set.Ioo a (a + (n : ℝ)),
      ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t) = fun n : ℕ => soninMellinSeq g a n s := rfl
  rw [hseq] at htend
  exact tendsto_nhds_unique (tendsto_soninMellinSeq ha hg hs0) htend

/-- The holomorphic continuation of the Mellin tail of a vector of `L_a` with Fourier head `c`. -/
def extendedTailMellin (a : ℝ) (c : ℂ) (f : SoninL2) (s : ℂ) : ℂ :=
  soninMellinExtension (f - c • fourierBandIndicator a) a s + c * sincMellin a s

theorem differentiableOn_extendedTailMellin {a : ℝ} (ha : 0 < a) {f : SoninL2} {c : ℂ}
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c) :
    DifferentiableOn ℂ (extendedTailMellin a c f) {s : ℂ | 0 < s.re} :=
  (differentiableOn_soninMellinExtension ha (sub_smul_fourierBandIndicator_mem hc)).add
    ((differentiableOn_sincMellin ha).const_mul c)

/-- On the half-plane of absolute convergence the continuation is the tail integral. -/
theorem extendedTailMellin_eq {a : ℝ} (ha : 0 < a) {f : SoninL2} {c : ℂ}
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    extendedTailMellin a c f s = ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  have hg := sub_smul_fourierBandIndicator_mem hc
  have h1 := integrableOn_cpow_mul_Ioi ha (f - c • fourierBandIndicator a) hs
  have h2 : IntegrableOn
      (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (c * soninSincKernel a t)) (Ioi a) volume := by
    have hv2 : MemLp (fun t : ℝ => c * soninSincKernel a t) 2 (volume.restrict (Ioi a)) :=
      (((Lp.memLp (fourierBandIndicator a)).restrict (Ioi a)).const_mul c)
    exact (memLp_two_cpow_Ioi ha hs).integrable_mul hv2
  have hc2 : c * sincMellin a s
      = ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (c * soninSincKernel a t) := by
    rw [sincMellin_eq, ← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  rw [extendedTailMellin, soninMellinExtension_eq_tail ha hg hs, hc2,
    ← MeasureTheory.integral_add h1 h2]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub f (c • fourierBandIndicator a)),
    ae_restrict_of_ae (Lp.coeFn_smul c (fourierBandIndicator a))] with t k1 k2
  rw [k1, Pi.sub_apply, k2, Pi.smul_apply, smul_eq_mul, soninSincKernel]
  ring

/-- **The Mellin tail of a vector of the extended Sonine space continues to `Re s > 0`.** -/
theorem exists_differentiableOn_extendedTailMellin {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s : ℂ | 0 < s.re} ∧
      ∀ s : ℂ, 1 / 2 < s.re → F s = ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  obtain ⟨c, hc⟩ := ae_fourier_eq_of_mem_extended hf
  exact ⟨extendedTailMellin a c f, differentiableOn_extendedTailMellin ha hc,
    fun s hs => extendedTailMellin_eq ha hc hs⟩

end RHTower

end
