import GaloisForLFunctions.HTGeometry.KleinGordonBandLimit

/-!
# The band is invariant under the evolution

A frequency band is preserved by the free evolution for the trivial reason that everything in sight
is a Fourier multiplier and multipliers commute. It is preserved by the *perturbed* evolution exactly
when the perturbation neither reads nor writes outside the band — which is what the band compression
of the previous files arranges.

The consequence is that the whole theory restricts to a band: band-limited data evolve into
band-limited states, so on the band the operator `⟨D⟩` is bounded and the obstruction that forced the
smoothing hypothesis of statements 103–109 is simply absent.

The proof of the invariance is uniqueness. The projected curve satisfies the same Duhamel equation
with the projected data, because the projection passes through the propagators and is absorbed by the
perturbation on both sides.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The projection commutes with the propagators -/

set_option maxHeartbeats 1000000 in
theorem kgCosOp_kgLowPassOp (t R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgCosOp t (kgLowPassOp R x) = kgLowPassOp R (kgCosOp t x) := by
  have hmeas : Measurable fun ξ : E => kgCosSymbol t ξ * kgLowPass R ξ :=
    (measurable_kgCosSymbol t).mul (measurable_kgLowPass R)
  have hbd : ∀ ξ : E, ‖kgCosSymbol t ξ * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgCosSymbol_le t ξ
    have h2 := norm_kgLowPass_le R ξ
    nlinarith [norm_nonneg (kgCosSymbol t ξ), norm_nonneg (kgLowPass R ξ)]
  have h1 : (kgCosOp (E := E) t).comp (kgLowPassOp R) = fourierMulCLM hmeas zero_le_one hbd := by
    rw [kgCosOp_eq, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hmeas _ _ _ _ zero_le_one hbd
      (Filter.Eventually.of_forall fun _ => rfl)
  have h2 : (kgLowPassOp (E := E) R).comp (kgCosOp t) = fourierMulCLM hmeas zero_le_one hbd := by
    rw [kgCosOp_eq, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hmeas _ _ _ _ zero_le_one hbd
      (Filter.Eventually.of_forall fun ξ => mul_comm _ _)
  have hcomp : (kgCosOp (E := E) t).comp (kgLowPassOp R)
      = (kgLowPassOp (E := E) R).comp (kgCosOp t) := by rw [h1, h2]
  exact congrArg (fun T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) => T x)
    hcomp

set_option maxHeartbeats 1000000 in
theorem kgSinFreqOp_kgLowPassOp (t R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgSinFreqOp t (kgLowPassOp R x) = kgLowPassOp R (kgSinFreqOp t x) := by
  have hmeas : Measurable fun ξ : E => kgSinOverFreq t ξ * kgLowPass R ξ :=
    (measurable_kgSinOverFreq t).mul (measurable_kgLowPass R)
  have hbd : ∀ ξ : E, ‖kgSinOverFreq t ξ * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgSinOverFreq_le t ξ
    have h2 := norm_kgLowPass_le R ξ
    nlinarith [norm_nonneg (kgSinOverFreq t ξ), norm_nonneg (kgLowPass R ξ)]
  have h1 : (kgSinFreqOp (E := E) t).comp (kgLowPassOp R)
      = fourierMulCLM hmeas zero_le_one hbd := by
    rw [kgSinFreqOp_eq, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hmeas _ _ _ _ zero_le_one hbd
      (Filter.Eventually.of_forall fun _ => rfl)
  have h2 : (kgLowPassOp (E := E) R).comp (kgSinFreqOp t)
      = fourierMulCLM hmeas zero_le_one hbd := by
    rw [kgSinFreqOp_eq, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hmeas _ _ _ _ zero_le_one hbd
      (Filter.Eventually.of_forall fun ξ => mul_comm _ _)
  have hcomp : (kgSinFreqOp (E := E) t).comp (kgLowPassOp R)
      = (kgLowPassOp (E := E) R).comp (kgSinFreqOp t) := by rw [h1, h2]
  exact congrArg (fun T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) => T x)
    hcomp

/-- **The projection passes through the free field.** -/
theorem kgLowPassOp_kgFieldFree (R : ℝ) (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgLowPassOp R (kgFieldFree f h t)
      = kgFieldFree (kgLowPassOp R f) (kgLowPassOp R h) t := by
  rw [kgFieldFree, kgFieldFree, map_add, kgCosOp_kgLowPassOp, kgSinFreqOp_kgLowPassOp]

/-! ## The band is invariant -/

section Invariance

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The projection passes through the perturbed evolution**, when the perturbation lives on the
band. -/
theorem kgLowPassOp_kgFieldMild (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) {R : ℝ}
    (hdom : ∀ v : Lp ℂ 2 (volume : Measure E), W (kgLowPassOp R v) = W v)
    (hran : ∀ v : Lp ℂ 2 (volume : Measure E), kgLowPassOp R (W v) = W v)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgLowPassOp R (kgFieldMild W f h t)
      = kgFieldMild W (kgLowPassOp R f) (kgLowPassOp R h) t := by
  have hcu : Continuous (kgFieldMild W f h) := continuous_kgFieldMild hb0 hW f h
  have hproj : Continuous fun τ : ℝ => kgLowPassOp R (kgFieldMild W f h τ) :=
    (kgLowPassOp (E := E) R).continuous.comp hcu
  have hduh : ∀ τ : ℝ, kgLowPassOp R (kgFieldMild W f h τ)
      = kgFieldFree (kgLowPassOp R f) (kgLowPassOp R h) τ
        + ∫ s in (0 : ℝ)..τ, kgFieldKernel W τ s (kgLowPassOp R (kgFieldMild W f h s)) := by
    intro τ
    have hI := intervalIntegrable_kgFieldKernel hcu W τ
    have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) τ,
        kgLowPassOp R (kgFieldKernel W τ s (kgFieldMild W f h s))
          = kgFieldKernel W τ s (kgLowPassOp R (kgFieldMild W f h s)) := by
      intro s _
      rw [kgFieldKernel_apply, kgFieldKernel_apply, hdom, ← kgSinFreqOp_kgLowPassOp, hran]
    rw [kgFieldMild_eq hb0 hW f h τ, map_add, kgLowPassOp_kgFieldFree,
      ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI,
      intervalIntegral.integral_congr hpt]
  have hfin := eq_kgFieldMild_of_duhamel hb0 hW (kgLowPassOp R f) (kgLowPassOp R h) hproj hduh
  exact congrFun hfin t

/-- **The band is invariant under the evolution.** Band-limited data evolve into band-limited
states. -/
theorem kgFieldMild_lowPass_invariant (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) {R : ℝ}
    (hdom : ∀ v : Lp ℂ 2 (volume : Measure E), W (kgLowPassOp R v) = W v)
    (hran : ∀ v : Lp ℂ 2 (volume : Measure E), kgLowPassOp R (W v) = W v)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgLowPassOp R (kgFieldMild W (kgLowPassOp R f) (kgLowPassOp R h) t)
      = kgFieldMild W (kgLowPassOp R f) (kgLowPassOp R h) t := by
  rw [kgLowPassOp_kgFieldMild hb0 hW hdom hran, kgLowPassOp_idem, kgLowPassOp_idem]

end Invariance

/-! ## The band compression lives on the band -/

theorem kgBandOp_dom (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (R : ℝ) (v : Lp ℂ 2 (volume : Measure E)) :
    kgBandOp W₀ R (kgLowPassOp R v) = kgBandOp W₀ R v := by
  rw [kgBandOp_apply, kgBandOp_apply, kgLowPassOp_idem]

theorem kgBandOp_ran (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (R : ℝ) (v : Lp ℂ 2 (volume : Measure E)) :
    kgLowPassOp R (kgBandOp W₀ R v) = kgBandOp W₀ R v := by
  rw [kgBandOp_apply, kgLowPassOp_idem]

/-- **The band is invariant under a band-compressed perturbation.** -/
theorem kgBandOp_lowPass_invariant
    {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}
    (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b) (R : ℝ) (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgLowPassOp R (kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R f) (kgLowPassOp R h) t)
      = kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R f) (kgLowPassOp R h) t :=
  kgFieldMild_lowPass_invariant hb0 (norm_kgBandOp_le hb0 hW R) (kgBandOp_dom W₀ R)
    (kgBandOp_ran W₀ R) f h t

/-! ## On a band the frequency is bounded -/

/-- The symbol of `⟨D⟩²` cut to the frequencies below `R`. -/
def kgFreqSqLow (R : ℝ) (ξ : E) : ℂ := ((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ) * kgLowPass R ξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgFreqSqLow (R : ℝ) : Measurable (kgFreqSqLow (E := E) R) :=
  ((Complex.continuous_ofReal.comp ((continuous_kgFreq (E := E)).pow 2)).measurable).mul
    (measurable_kgLowPass R)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgFreqSqLow_le (R : ℝ) (ξ : E) : ‖kgFreqSqLow R ξ‖ ≤ 1 + R ^ (2 : ℕ) := by
  have hB0 : (0 : ℝ) ≤ 1 + R ^ (2 : ℕ) := by positivity
  rw [kgFreqSqLow, kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), kgFreq,
      Real.sq_sqrt (by positivity)]
    have h : ‖ξ‖ ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
      have := norm_nonneg ξ
      nlinarith
    linarith
  · simpa using hB0

/-- **`⟨D⟩²` restricted to a band**, as a bounded operator of norm at most `1 + R²`. -/
def kgFreqSqLowOp (R : ℝ) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  fourierMulCLM (measurable_kgFreqSqLow (E := E) R) (by positivity) (norm_kgFreqSqLow_le R)

theorem norm_kgFreqSqLowOp_le (R : ℝ) : ‖kgFreqSqLowOp (E := E) R‖ ≤ 1 + R ^ (2 : ℕ) :=
  norm_fourierMulCLM_le _ _ _

set_option maxHeartbeats 1000000 in
/-- **On a band the frequency obstruction disappears**: dividing the band-restricted `⟨D⟩²` twice by
the frequency returns the projection, so `⟨D⟩²` really is realised there by a bounded operator. -/
theorem kgFreqInvOp_sq_kgFreqSqLowOp (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgFreqInvOp (kgFreqInvOp (kgFreqSqLowOp R x)) = kgLowPassOp R x := by
  have hmeas : Measurable fun ξ : E => kgFreqInv ξ * kgFreqSqLow R ξ :=
    (measurable_kgFreqInv (E := E)).mul (measurable_kgFreqSqLow R)
  have hbd : ∀ ξ : E, ‖kgFreqInv ξ * kgFreqSqLow R ξ‖ ≤ Real.sqrt (1 + R ^ (2 : ℕ)) := by
    intro ξ
    have hpos := kgFreq_pos ξ
    have hne : kgFreq ξ ≠ 0 := hpos.ne'
    rw [kgFreqSqLow, kgLowPass]
    split
    · rename_i hξ
      rw [mul_one, kgFreqInv, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
      have hval : (kgFreq ξ)⁻¹ * kgFreq ξ ^ (2 : ℕ) = kgFreq ξ := by
        field_simp
      rw [hval, abs_of_pos hpos, kgFreq]
      refine Real.sqrt_le_sqrt ?_
      have hn := norm_nonneg ξ
      nlinarith
    · simp only [mul_zero, norm_zero]
      positivity
  have hB0 : (0 : ℝ) ≤ Real.sqrt (1 + R ^ (2 : ℕ)) := Real.sqrt_nonneg _
  have hstep1 : (kgFreqInvOp (E := E)).comp (kgFreqSqLowOp R)
      = fourierMulCLM hmeas hB0 hbd := by
    rw [kgFreqInvOp_eq, kgFreqSqLowOp]
    exact fourierMulCLM_comp _ _ hmeas _ _ _ _ hB0 hbd
      (Filter.Eventually.of_forall fun _ => rfl)
  have hstep2 : (kgFreqInvOp (E := E)).comp (fourierMulCLM hmeas hB0 hbd)
      = kgLowPassOp R := by
    rw [kgFreqInvOp_eq, kgLowPassOp_eq]
    refine fourierMulCLM_comp _ _ (measurable_kgLowPass (E := E) R) _ _ _ _ zero_le_one
      (norm_kgLowPass_le R) (Filter.Eventually.of_forall fun ξ => ?_)
    have hpos := kgFreq_pos ξ
    have hne : ((kgFreq ξ : ℝ) : ℂ) ≠ 0 := by
      simpa using hpos.ne'
    by_cases hξ : ‖ξ‖ ≤ R
    · rw [kgFreqSqLow, kgLowPass, if_pos hξ, kgFreqInv, mul_one]
      push_cast
      field_simp
    · rw [kgFreqSqLow, kgLowPass, if_neg hξ]
      simp
  have hchain : kgFreqInvOp (E := E) (kgFreqInvOp (kgFreqSqLowOp R x)) = kgLowPassOp R x := by
    have h1 : kgFreqInvOp (E := E) (kgFreqSqLowOp R x) = fourierMulCLM hmeas hB0 hbd x :=
      congrArg (fun T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) => T x)
        hstep1
    rw [h1]
    exact congrArg (fun T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) => T x)
      hstep2
  exact hchain

end GaloisForLFunctions.HTGeometry
