import GaloisForLFunctions.HTGeometry.RegularizedHerglotzTransform
import GaloisForLFunctions.HTGeometry.LeafCauchyTransform

/-!
# Translation collapse of the Cauchy transform of a finite measure

Translating the spectral parameter of the Cauchy transform of a finite positive measure drives it
to zero, uniformly on every compact subset of the open upper half plane.

The mechanism is a two-regime split of the defining integral.  On the part of the spectrum bounded
by `R` the kernel is small because its real part is of size `|t|`; on the rest the kernel is bounded
by the reciprocal of the imaginary part, and the mass there is small because the measure is finite.
Both estimates are uniform in the spectral parameter on a strip of bounded real part and imaginary
part bounded below, which is exactly the geometry of a compact subset of the upper half plane.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Set

open scoped Topology ENNReal

noncomputable section

/-- The strip of the upper half plane with imaginary part at least `delta` and real part at most
`A` in absolute value. -/
def upperStrip (delta A : ℝ) : Set ℂ := {z : ℂ | delta ≤ z.im ∧ |z.re| ≤ A}

/-- Tail masses of a finite measure are eventually small. -/
theorem exists_tail_measureReal_lt (ν : Measure ℝ) [IsFiniteMeasure ν] {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ν.real {t : ℝ | R < |t|} < ε := by
  have hmeas : ∀ n : ℕ, NullMeasurableSet {t : ℝ | (n : ℝ) < |t|} ν := fun n =>
    (measurableSet_lt measurable_const continuous_abs.measurable).nullMeasurableSet
  have hanti : Antitone fun n : ℕ => {t : ℝ | (n : ℝ) < |t|} := by
    intro m n hmn t ht
    simp only [mem_setOf_eq] at ht ⊢
    exact lt_of_le_of_lt (by exact_mod_cast hmn) ht
  have hfin : ∃ n : ℕ, ν {t : ℝ | (n : ℝ) < |t|} ≠ ⊤ := ⟨0, measure_ne_top ν _⟩
  have hinter : (⋂ n : ℕ, {t : ℝ | (n : ℝ) < |t|}) = (∅ : Set ℝ) := by
    ext t
    simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_gt |t|
    exact ⟨n, hn.le⟩
  have htend := tendsto_measure_iInter_atTop hmeas hanti hfin
  rw [hinter, measure_empty] at htend
  have htendReal : Tendsto (fun n : ℕ => ν.real {t : ℝ | (n : ℝ) < |t|}) atTop (𝓝 0) := by
    have hcomp := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp htend
    simpa [Measure.real, Function.comp_def] using hcomp
  obtain ⟨n, hn⟩ := (htendReal.eventually_lt_const hε).exists
  exact ⟨n, Nat.cast_nonneg n, hn⟩

/-- Off a strip of the upper half plane the translated Cauchy kernel is bounded by the reciprocal
of the height. -/
theorem norm_translatedKernel_le_inv_im {delta lam t : ℝ} {z : ℂ} (hdelta : 0 < delta)
    (hz : delta ≤ z.im) : ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ≤ delta⁻¹ := by
  have him : delta ≤ ‖(lam : ℂ) - (z + (t : ℂ))‖ := by
    refine le_trans hz ?_
    have h1 : |((lam : ℂ) - (z + (t : ℂ))).im| ≤ ‖(lam : ℂ) - (z + (t : ℂ))‖ :=
      Complex.abs_im_le_norm _
    have h2 : ((lam : ℂ) - (z + (t : ℂ))).im = -z.im := by simp
    rw [h2, abs_neg, abs_of_nonneg (le_trans hdelta.le hz)] at h1
    exact h1
  rw [norm_inv, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le hdelta him

/-- On the bounded part of the spectrum the translated Cauchy kernel is small because its real part
is of size `|t|`. -/
theorem norm_translatedKernel_le_inv_re {A R lam t : ℝ} {z : ℂ} (hre : |z.re| ≤ A)
    (hlam : |lam| ≤ R) (ht : R + A < |t|) :
    ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ≤ (|t| - R - A)⁻¹ := by
  have hpos : 0 < |t| - R - A := by linarith
  have hre' : |t| - R - A ≤ ‖(lam : ℂ) - (z + (t : ℂ))‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    have hval : ((lam : ℂ) - (z + (t : ℂ))).re = lam - z.re - t := by
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
      ring
    rw [hval]
    have h1 : |t| - |lam| - |z.re| ≤ |lam - z.re - t| := by
      have := abs_sub_abs_le_abs_sub (lam - z.re) t
      have h2 : |lam - z.re| ≤ |lam| + |z.re| := abs_sub _ _
      have h3 : |lam - z.re - t| = |(lam - z.re) - t| := rfl
      have h4 : |t| - |lam - z.re| ≤ |(lam - z.re) - t| := by
        have := abs_sub_abs_le_abs_sub t (lam - z.re)
        rw [abs_sub_comm t (lam - z.re)] at this
        linarith
      linarith
    linarith
  rw [norm_inv, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le hpos hre'

/-- **Two-regime bound for a translated Cauchy transform.** -/
theorem norm_cauchyTransform_translate_le (ν : Measure ℝ) [IsFiniteMeasure ν]
    {delta A R t : ℝ} (hdelta : 0 < delta) (ht : R + A < |t|) {z : ℂ}
    (hz : z ∈ upperStrip delta A) :
    ‖cauchyTransform ν (z + (t : ℂ))‖
      ≤ ν.real Set.univ * (|t| - R - A)⁻¹ + ν.real {lam : ℝ | R < |lam|} * delta⁻¹ := by
  obtain ⟨hzim, hzre⟩ := hz
  have hpos : 0 < |t| - R - A := by linarith
  have hzt : (z + (t : ℂ)).im ≠ 0 := by
    have : (z + (t : ℂ)).im = z.im := by simp
    rw [this]
    exact ne_of_gt (lt_of_lt_of_le hdelta hzim)
  have hint : Integrable (fun lam : ℝ => ((lam : ℂ) - (z + (t : ℂ)))⁻¹) ν :=
    HTGeometry.integrable_cauchy_kernel ν hzt
  set S : Set ℝ := {lam : ℝ | |lam| ≤ R} with hS
  have hSmeas : MeasurableSet S := measurableSet_le continuous_abs.measurable measurable_const
  have hScompl : Sᶜ = {lam : ℝ | R < |lam|} := by
    ext lam
    simp [hS, not_le]
  have hsplit : ∫ lam in S, ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ∂ν
      + ∫ lam in Sᶜ, ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ∂ν
      = ∫ lam, ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ∂ν :=
    integral_add_compl hSmeas hint.norm
  have hnear : ∫ lam in S, ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ∂ν
      ≤ ν.real Set.univ * (|t| - R - A)⁻¹ := by
    have hmono : ∫ lam in S, ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ∂ν
        ≤ ∫ _lam in S, (|t| - R - A)⁻¹ ∂ν := by
      refine setIntegral_mono_on hint.norm.integrableOn
        ((integrable_const _).integrableOn) hSmeas ?_
      intro lam hlam
      exact norm_translatedKernel_le_inv_re hzre hlam ht
    refine le_trans hmono ?_
    rw [setIntegral_const, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (measureReal_mono (Set.subset_univ S)) (by positivity)
  have hfar : ∫ lam in Sᶜ, ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ∂ν
      ≤ ν.real {lam : ℝ | R < |lam|} * delta⁻¹ := by
    have hmono : ∫ lam in Sᶜ, ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ∂ν
        ≤ ∫ _lam in Sᶜ, delta⁻¹ ∂ν := by
      refine setIntegral_mono_on hint.norm.integrableOn
        ((integrable_const _).integrableOn) hSmeas.compl ?_
      intro lam _
      exact norm_translatedKernel_le_inv_im hdelta hzim
    refine le_trans hmono ?_
    rw [setIntegral_const, smul_eq_mul, hScompl]
  calc ‖cauchyTransform ν (z + (t : ℂ))‖
      ≤ ∫ lam, ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ∂ν := norm_integral_le_integral_norm _
    _ = ∫ lam in S, ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ∂ν
        + ∫ lam in Sᶜ, ‖((lam : ℂ) - (z + (t : ℂ)))⁻¹‖ ∂ν := hsplit.symm
    _ ≤ ν.real Set.univ * (|t| - R - A)⁻¹ + ν.real {lam : ℝ | R < |lam|} * delta⁻¹ :=
        add_le_add hnear hfar

/-- **Strip form of the collapse.**  The translated Cauchy transform of a finite measure tends to
zero uniformly on every strip of bounded real part and height bounded below. -/
theorem tendstoUniformlyOn_cauchyTransform_translate (ν : Measure ℝ) [IsFiniteMeasure ν]
    {delta A : ℝ} (hdelta : 0 < delta) :
    TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => cauchyTransform ν (z + (t : ℂ)))
      (fun _ => (0 : ℂ)) (cocompact ℝ) (upperStrip delta A) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR0, hR⟩ := exists_tail_measureReal_lt ν (show 0 < ε * delta / 2 by positivity)
  set M : ℝ := ν.real Set.univ with hM
  have hM0 : 0 ≤ M := measureReal_nonneg
  set C : ℝ := R + A + 2 * (M + 1) / ε with hC
  have habs : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop := by
    have h := tendsto_norm_cocompact_atTop (E := ℝ)
    exact Filter.Tendsto.congr (fun t => Real.norm_eq_abs t) h
  filter_upwards [habs.eventually_ge_atTop C] with t ht
  intro z hz
  have hgap : 2 * (M + 1) / ε ≤ |t| - R - A := by
    rw [hC] at ht
    linarith
  have hgappos : 0 < |t| - R - A := by
    have : 0 < 2 * (M + 1) / ε := by positivity
    linarith
  have hlt : R + A < |t| := by linarith
  have hbound := norm_cauchyTransform_translate_le ν hdelta hlt hz
  have hnear : M * (|t| - R - A)⁻¹ < ε / 2 := by
    have h1 : 2 * (M + 1) ≤ (|t| - R - A) * ε := by
      have hdiv := (div_le_iff₀ hε).mp hgap
      linarith
    have h2 : M * (|t| - R - A)⁻¹ = M / (|t| - R - A) := by rw [div_eq_mul_inv]
    rw [h2, div_lt_iff₀ hgappos]
    nlinarith [h1]
  have hfar : ν.real {lam : ℝ | R < |lam|} * delta⁻¹ < ε / 2 := by
    have hstep : ν.real {lam : ℝ | R < |lam|} * delta⁻¹ < (ε * delta / 2) * delta⁻¹ :=
      mul_lt_mul_of_pos_right hR (by positivity)
    refine lt_of_lt_of_le hstep (le_of_eq ?_)
    field_simp
  have hdist : dist ((fun _ : ℂ => (0 : ℂ)) z) (cauchyTransform ν (z + (t : ℂ)))
      = ‖cauchyTransform ν (z + (t : ℂ))‖ := by
    simp [dist_zero_left]
  rw [hdist]
  calc ‖cauchyTransform ν (z + (t : ℂ))‖
      ≤ M * (|t| - R - A)⁻¹ + ν.real {lam : ℝ | R < |lam|} * delta⁻¹ := hbound
    _ < ε / 2 + ε / 2 := add_lt_add hnear hfar
    _ = ε := by ring

/-- **Compact form of the collapse.**  The translated Cauchy transform of a finite measure tends to
zero uniformly on every compact subset of the open upper half plane. -/
theorem tendstoUniformlyOn_cauchyTransform_translate_isCompact (ν : Measure ℝ) [IsFiniteMeasure ν]
    {K : Set ℂ} (hK : IsCompact K) (hKH : ∀ z ∈ K, 0 < z.im) :
    TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => cauchyTransform ν (z + (t : ℂ)))
      (fun _ => (0 : ℂ)) (cocompact ℝ) K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp [TendstoUniformlyOn]
  obtain ⟨z₀, hz₀K, hz₀⟩ := hK.exists_isMinOn hne (Complex.continuous_im.continuousOn)
  obtain ⟨A, hA⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  refine TendstoUniformlyOn.mono
    (tendstoUniformlyOn_cauchyTransform_translate ν (delta := z₀.im) (A := A) (hKH z₀ hz₀K)) ?_
  intro z hzK
  refine ⟨hz₀ hzK, ?_⟩
  have hnorm : ‖z‖ ≤ A := by
    have := hA hzK
    simpa [Metric.mem_closedBall] using this
  exact le_trans (Complex.abs_re_le_norm z) hnorm

end

end GaloisForLFunctions.HTGeometry
