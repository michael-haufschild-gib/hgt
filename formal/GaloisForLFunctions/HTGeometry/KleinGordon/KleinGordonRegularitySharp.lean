import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFreqInvNotSurjective

/-!
# The regularity hypothesis is exactly the domain

Statement 65 differentiates `t ↦ sin(t⟨D⟩)x` for `x` in the range of `⟨D⟩⁻¹`. That hypothesis is not
an artifact of the proof: it is the whole domain of differentiability. If the curve has a derivative
at the origin at all, then the datum *is* regular, and the derivative exhibits the regularising
vector.

The mechanism is the sinc function. The difference quotient of `sin(t⟨ξ⟩)` at the origin is
`sin(t⟨ξ⟩)/t`, unbounded in `ξ`; but one power of `⟨D⟩⁻¹` turns it into `sin(t⟨ξ⟩)/(t⟨ξ⟩)`, which is
bounded by one and converges pointwise to one. So `⟨D⟩⁻¹` applied to the difference quotient
converges to the datum, while by hypothesis it converges to `⟨D⟩⁻¹` of the derivative — and the two
limits agree.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

/-! ## The sinc symbol -/

section Symbol

variable {E : Type*} [NormedAddCommGroup E]

/-- The normalised difference quotient of the sine symbol: `sin(t⟨ξ⟩)/(t⟨ξ⟩)`. -/
def kgSinc (t : ℝ) (ξ : E) : ℂ := ((Real.sin (t * kgFreq ξ) / (t * kgFreq ξ) : ℝ) : ℂ)

theorem norm_kgSinc_le (t : ℝ) (ξ : E) : ‖kgSinc t ξ‖ ≤ 1 := by
  rw [kgSinc, Complex.norm_real, Real.norm_eq_abs, abs_div]
  rcases eq_or_ne (t * kgFreq ξ) 0 with h | h
  · rw [h, abs_zero, div_zero]
    exact zero_le_one
  · rw [div_le_one (abs_pos.mpr h)]
    exact Real.abs_sin_le_abs

/-- The sinc symbol tends to one as the time tends to zero. -/
theorem tendsto_kgSinc (ξ : E) :
    Tendsto (fun t : ℝ => kgSinc t ξ) (nhdsWithin 0 {0}ᶜ) (nhds (1 : ℂ)) := by
  have hslope : Tendsto (slope Real.sin 0) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    have h := Real.hasDerivAt_sin 0
    rw [Real.cos_zero] at h
    exact h.tendsto_slope
  have hcongr : ∀ y : ℝ, slope Real.sin 0 y = Real.sin y / y := by
    intro y
    rw [slope_def_field, Real.sin_zero, sub_zero, sub_zero]
  have hreal : Tendsto (fun y : ℝ => Real.sin y / y) (nhdsWithin 0 {0}ᶜ) (nhds 1) :=
    hslope.congr hcongr
  have hmap : Tendsto (fun t : ℝ => t * kgFreq ξ) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ => t * kgFreq ξ) (nhds 0) (nhds (0 * kgFreq ξ)) :=
        (continuous_id.mul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, mul_eq_zero, not_or]
      exact ⟨ht, (kgFreq_pos ξ).ne'⟩
  have hcomp := hreal.comp hmap
  have hfin : Tendsto (fun t : ℝ => Real.sin (t * kgFreq ξ) / (t * kgFreq ξ))
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := hcomp
  have hC := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hfin
  refine hC.congr fun t => rfl

end Symbol

section Sharp

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem continuous_kgSinc (t : ℝ) : Continuous (kgSinc (E := E) t) := by
  show Continuous fun ξ : E => ((Real.sin (t * kgFreq ξ) / (t * kgFreq ξ) : ℝ) : ℂ)
  rcases eq_or_ne t 0 with rfl | ht
  · simpa using continuous_const
  · refine Complex.continuous_ofReal.comp ?_
    refine Continuous.div
      (Real.continuous_sin.comp (continuous_const.mul continuous_kgFreq))
      (continuous_const.mul continuous_kgFreq) fun ξ => ?_
    exact mul_ne_zero ht (kgFreq_pos ξ).ne'

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgSinc (t : ℝ) : Measurable (kgSinc (E := E) t) :=
  (continuous_kgSinc t).measurable

/-- **The regularised difference quotient is the sinc multiplier.** -/
theorem kgFreqInvOp_slope_kgSinOp (k : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : t ≠ 0) :
    kgFreqInvOp (slope (fun s : ℝ => kgSinOp s k) 0 t)
      = fourierMulCLM (measurable_kgSinc (E := E) t) zero_le_one (norm_kgSinc_le t) k := by
  have hsmul : fourierMulCLM (measurable_kgSinc (E := E) t) zero_le_one (norm_kgSinc_le t)
      = (((t⁻¹ : ℝ) : ℂ)) • fourierMulCLM (measurable_kgSinOverFreq (E := E) t) zero_le_one
        (norm_kgSinOverFreq_le t) := by
    refine fourierMulCLM_smul _ _ _ _ _ (norm_kgSinc_le t) _
      (Filter.Eventually.of_forall fun ξ => ?_)
    show ((Real.sin (t * kgFreq ξ) / (t * kgFreq ξ) : ℝ) : ℂ)
      = (((t⁻¹ : ℝ) : ℂ)) * ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  have hrc : ∀ (r : ℝ) (y : Lp ℂ 2 (volume : Measure E)), r • y = ((r : ℂ)) • y := by
    intro r y
    rw [← Complex.coe_algebraMap, algebraMap_smul]
  rw [hsmul, slope_def_module, kgSinOp_zero]
  simp only [zero_apply, sub_zero, smul_apply]
  rw [hrc, map_smul]
  congr 1
  rw [← kgSinFreqOp_eq, kgSinFreqOp_apply_freqInv]

/-- **The regularity hypothesis is exactly the domain.** If `t ↦ sin(t⟨D⟩)k` has a derivative at the
origin then `k` lies in the range of `⟨D⟩⁻¹`, with the derivative as regularising vector. -/
theorem mem_range_kgFreqInvOp_of_hasDerivAt {k L : Lp ℂ 2 (volume : Measure E)}
    (h : HasDerivAt (fun s : ℝ => kgSinOp s k) L 0) : kgFreqInvOp L = k := by
  have hone : Measurable fun _ : E => (1 : ℂ) := measurable_const
  have honeb : ∀ _ξ : E, ‖(1 : ℂ)‖ ≤ 1 := fun _ => le_of_eq norm_one
  have hlim1 : Tendsto
      (fun t : ℝ => fourierMulCLM (measurable_kgSinc (E := E) t) zero_le_one (norm_kgSinc_le t) k)
      (nhdsWithin 0 {0}ᶜ) (nhds (fourierMulCLM hone zero_le_one honeb k)) :=
    tendsto_fourierMulCLM_apply (l := nhdsWithin 0 {0}ᶜ)
      (fun t => measurable_kgSinc (E := E) t) hone zero_le_one
      (fun t => norm_kgSinc_le t) honeb (fun ξ => tendsto_kgSinc ξ) k
  have hid : fourierMulCLM hone zero_le_one honeb
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) :=
    fourierMulCLM_eq_id _ _ _ (Filter.Eventually.of_forall fun _ => rfl)
  rw [hid] at hlim1
  have hslope := (hasDerivAt_iff_tendsto_slope.mp h)
  have hlim2 : Tendsto (fun t : ℝ => kgFreqInvOp (slope (fun s : ℝ => kgSinOp s k) 0 t))
      (nhdsWithin 0 {0}ᶜ) (nhds (kgFreqInvOp L)) :=
    ((kgFreqInvOp (E := E)).continuous.tendsto L).comp hslope
  have hcongr : Tendsto
      (fun t : ℝ => fourierMulCLM (measurable_kgSinc (E := E) t) zero_le_one (norm_kgSinc_le t) k)
      (nhdsWithin 0 {0}ᶜ) (nhds (kgFreqInvOp L)) := by
    refine hlim2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact kgFreqInvOp_slope_kgSinOp k ht
  exact tendsto_nhds_unique hcongr (by simpa using hlim1)

/-- **Differentiability at the origin characterises the regular data.** -/
theorem hasDerivAt_kgSinOp_iff (k : Lp ℂ 2 (volume : Measure E)) :
    (∃ L, HasDerivAt (fun s : ℝ => kgSinOp s k) L 0) ↔ ∃ g, k = kgFreqInvOp g := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, (mem_range_kgFreqInvOp_of_hasDerivAt hL).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨kgCosOp 0 g, hasDerivAt_kgSinOp_freqInv 0 g⟩

end Sharp

end GaloisForLFunctions.HTGeometry
