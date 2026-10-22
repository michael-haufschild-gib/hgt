import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFieldRegularity

/-!
# Separating the observation time from the source time in the Duhamel term

The Duhamel integrand `(sin((t-s)⟨D⟩)/⟨D⟩) g(s)` depends on the observation time `t` both through
the upper limit of the integral and through the propagator inside it, which is what blocks a naive
differentiation. The addition formula unentangles the two:

`sin((t-s)⟨ξ⟩)/⟨ξ⟩ = (sin(t⟨ξ⟩)/⟨ξ⟩)·cos(s⟨ξ⟩) - cos(t⟨ξ⟩)·(sin(s⟨ξ⟩)/⟨ξ⟩)`,

so the Duhamel term is a pair of **fixed** operators applied to integrals whose only `t`-dependence
is the upper limit:

`∫₀ᵗ (sin((t-s)⟨D⟩)/⟨D⟩) g(s) ds
   = (sin(t⟨D⟩)/⟨D⟩)(∫₀ᵗ cos(s⟨D⟩)g(s) ds) - cos(t⟨D⟩)(∫₀ᵗ (sin(s⟨D⟩)/⟨D⟩)g(s) ds)`.

Pulling the operators out of the Bochner integral is legitimate because they are bounded, and
that is the whole content of the separation.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The subtraction laws for the propagators -/

section SymbolBounds

variable {E : Type*} [NormedAddCommGroup E] (t s : ℝ)

private theorem norm_sinFreqMulCos_le (ξ : E) :
    ‖kgSinOverFreq t ξ * kgCosSymbol s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgSinOverFreq_le t ξ) (norm_nonneg _) (norm_kgCosSymbol_le s ξ)

private theorem norm_cosMulSinFreq_le (ξ : E) :
    ‖kgCosSymbol t ξ * kgSinOverFreq s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgCosSymbol_le t ξ) (norm_nonneg _) (norm_kgSinOverFreq_le s ξ)

end SymbolBounds

section Symbols

variable (t s : ℝ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem measurable_sinFreqMulCos :
    Measurable fun ξ : E => kgSinOverFreq t ξ * kgCosSymbol s ξ :=
  (measurable_kgSinOverFreq t).mul (measurable_kgCosSymbol s)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem measurable_cosMulSinFreq :
    Measurable fun ξ : E => kgCosSymbol t ξ * kgSinOverFreq s ξ :=
  (measurable_kgCosSymbol t).mul (measurable_kgSinOverFreq s)

/-- **The subtraction law for the half-order propagator.** -/
theorem kgSinFreqOp_sub :
    kgSinFreqOp (E := E) (t - s)
      = (kgSinFreqOp t).comp (kgCosOp s) - (kgCosOp t).comp (kgSinFreqOp s) := by
  have hA := measurable_sinFreqMulCos (E := E) t s
  have hB := measurable_cosMulSinFreq (E := E) t s
  have h1 : (kgSinFreqOp (E := E) t).comp (kgCosOp s)
      = fourierMulCLM hA zero_le_one (norm_sinFreqMulCos_le t s) := by
    rw [kgSinFreqOp_eq, kgCosOp_eq]
    exact fourierMulCLM_comp _ _ hA _ _ _ _ _ (norm_sinFreqMulCos_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have h2 : (kgCosOp (E := E) t).comp (kgSinFreqOp s)
      = fourierMulCLM hB zero_le_one (norm_cosMulSinFreq_le t s) := by
    rw [kgCosOp_eq, kgSinFreqOp_eq]
    exact fourierMulCLM_comp _ _ hB _ _ _ _ _ (norm_cosMulSinFreq_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hsub : kgSinFreqOp (E := E) (t - s)
      = fourierMulCLM hA zero_le_one (norm_sinFreqMulCos_le t s)
        - fourierMulCLM hB zero_le_one (norm_cosMulSinFreq_le t s) := by
    rw [kgSinFreqOp_eq]
    refine fourierMulCLM_sub hA hB (measurable_kgSinOverFreq (E := E) (t - s)) zero_le_one
      (norm_sinFreqMulCos_le t s) zero_le_one (norm_cosMulSinFreq_le t s) zero_le_one
      (norm_kgSinOverFreq_le (t - s)) (Filter.Eventually.of_forall fun ξ => ?_)
    show ((Real.sin ((t - s) * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
      = ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ) * ((Real.cos (s * kgFreq ξ) : ℝ) : ℂ)
        - ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.sin (s * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, sub_mul, Real.sin_sub]
    congr 1
    ring
  rw [hsub, h1, h2]

end Symbols

/-! ## Continuity of the cosine propagator along families -/

theorem continuous_kgCosOp_comp {ι : Type*} [TopologicalSpace ι] {r : ι → ℝ}
    {x : ι → Lp ℂ 2 (volume : Measure E)} (hr : Continuous r) (hx : Continuous x) :
    Continuous fun i => kgCosOp (r i) (x i) :=
  continuous_of_strong_comp norm_kgCosOp_le continuous_kgCosOp_apply hr hx

/-! ## The separated Duhamel term -/

/-- **The Duhamel term in separated form.** The observation time appears only in two fixed operators
and in the upper limit; the source time only inside the integrals. -/
theorem intervalIntegral_kgFieldKernel_separated
    (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    {u : ℝ → Lp ℂ 2 (volume : Measure E)} (hu : Continuous u) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, kgFieldKernel W t s (u s))
      = kgSinFreqOp t (∫ s in (0 : ℝ)..t, kgCosOp s (W (u s)))
        - kgCosOp t (∫ s in (0 : ℝ)..t, kgSinFreqOp s (W (u s))) := by
  have hg : Continuous fun s : ℝ => W (u s) := W.continuous.comp hu
  have hc : Continuous fun s : ℝ => kgCosOp s (W (u s)) :=
    continuous_kgCosOp_comp continuous_id hg
  have hs : Continuous fun s : ℝ => kgSinFreqOp s (W (u s)) :=
    continuous_kgSinFreqOp_comp continuous_id hg
  have hIc := hc.intervalIntegrable (μ := volume) 0 t
  have hIs := hs.intervalIntegrable (μ := volume) 0 t
  have hc' : Continuous fun s : ℝ => kgSinFreqOp t (kgCosOp s (W (u s))) :=
    continuous_kgSinFreqOp_comp continuous_const hc
  have hs' : Continuous fun s : ℝ => kgCosOp t (kgSinFreqOp s (W (u s))) :=
    continuous_kgCosOp_comp continuous_const hs
  have hpoint : ∀ s ∈ Set.uIcc (0 : ℝ) t, kgFieldKernel W t s (u s)
      = kgSinFreqOp t (kgCosOp s (W (u s))) - kgCosOp t (kgSinFreqOp s (W (u s))) := by
    intro s _
    rw [kgFieldKernel_apply, kgSinFreqOp_sub]
    rfl
  rw [intervalIntegral.integral_congr hpoint,
    intervalIntegral.integral_sub (hc'.intervalIntegrable (μ := volume) 0 t)
      (hs'.intervalIntegrable (μ := volume) 0 t),
    ContinuousLinearMap.intervalIntegral_comp_comm _ hIc,
    ContinuousLinearMap.intervalIntegral_comp_comm _ hIs]

/-- **The Duhamel formula in separated form.** -/
theorem kgFieldMild_eq_separated
    {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}
    (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMild W f h t
      = kgFieldFree f h t
        + (kgSinFreqOp t (∫ s in (0 : ℝ)..t, kgCosOp s (W (kgFieldMild W f h s)))
          - kgCosOp t (∫ s in (0 : ℝ)..t, kgSinFreqOp s (W (kgFieldMild W f h s)))) := by
  rw [kgFieldMild_eq hb0 hW f h t,
    intervalIntegral_kgFieldKernel_separated W (continuous_kgFieldMild hb0 hW f h) t]

end GaloisForLFunctions.HTGeometry
