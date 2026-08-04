import GaloisForLFunctions.HTGeometry.KleinGordonFieldVelocity

/-!
# The second differentiation of the Duhamel term

The velocity of the mild solution carries the integral `∫₀ᵗ cos((t-s)⟨D⟩)k(s) ds`, and
differentiating it once more is where the regularity of the source is finally used. Separating the
two times again turns it into `cos(t⟨D⟩)P(t) + sin(t⟨D⟩)Q(t)`, and the product rule needs `P(t)` and
`Q(t)` to lie in the range of `⟨D⟩⁻¹` — which they do exactly when `k` does.

For `k = ⟨D⟩⁻¹k₀` the computation closes: the two endpoint contributions are
`cos(t⟨D⟩)⟨D⟩⁻¹cos(t⟨D⟩)k₀(t)` and `sin(t⟨D⟩)⟨D⟩⁻¹sin(t⟨D⟩)k₀(t)`, whose sum is `⟨D⟩⁻¹k₀(t) = k(t)` by
the Pythagorean identity, and the two surviving terms recombine by the sine subtraction law into
`-∫₀ᵗ sin((t-s)⟨D⟩)k₀(s) ds`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The sine subtraction law -/

section Symbols

variable (t s : ℝ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem measurable_sinCos' :
    Measurable fun ξ : E => kgSinPhase t ξ * kgCosSymbol s ξ :=
  (measurable_kgSinPhase t).mul (measurable_kgCosSymbol s)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem measurable_cosSin' :
    Measurable fun ξ : E => kgCosSymbol t ξ * kgSinPhase s ξ :=
  (measurable_kgCosSymbol t).mul (measurable_kgSinPhase s)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem norm_sinCos'_le (ξ : E) : ‖kgSinPhase t ξ * kgCosSymbol s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgSinPhase_le t ξ) (norm_nonneg _) (norm_kgCosSymbol_le s ξ)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem norm_cosSin'_le (ξ : E) : ‖kgCosSymbol t ξ * kgSinPhase s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgCosSymbol_le t ξ) (norm_nonneg _) (norm_kgSinPhase_le s ξ)

/-- **The subtraction law for the energy-coordinate sine.** -/
theorem kgSinOp_sub :
    kgSinOp (E := E) (t - s)
      = (kgSinOp t).comp (kgCosOp s) - (kgCosOp t).comp (kgSinOp s) := by
  have hA := measurable_sinCos' (E := E) t s
  have hB := measurable_cosSin' (E := E) t s
  have h1 : (kgSinOp (E := E) t).comp (kgCosOp s)
      = fourierMulCLM hA zero_le_one (norm_sinCos'_le t s) := by
    rw [kgSinOp_eq, kgCosOp_eq]
    exact fourierMulCLM_comp _ _ hA _ _ _ _ _ (norm_sinCos'_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have h2 : (kgCosOp (E := E) t).comp (kgSinOp s)
      = fourierMulCLM hB zero_le_one (norm_cosSin'_le t s) := by
    rw [kgCosOp_eq, kgSinOp_eq]
    exact fourierMulCLM_comp _ _ hB _ _ _ _ _ (norm_cosSin'_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hsub : kgSinOp (E := E) (t - s)
      = fourierMulCLM hA zero_le_one (norm_sinCos'_le t s)
        - fourierMulCLM hB zero_le_one (norm_cosSin'_le t s) := by
    rw [kgSinOp_eq]
    refine fourierMulCLM_sub hA hB (measurable_kgSinPhase (E := E) (t - s)) zero_le_one
      (norm_sinCos'_le t s) zero_le_one (norm_cosSin'_le t s) zero_le_one
      (norm_kgSinPhase_le (t - s)) (Filter.Eventually.of_forall fun ξ => ?_)
    show ((Real.sin ((t - s) * kgFreq ξ) : ℝ) : ℂ)
      = ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.cos (s * kgFreq ξ) : ℝ) : ℂ)
        - ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.sin (s * kgFreq ξ) : ℝ) : ℂ)
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, sub_mul, Real.sin_sub]
  rw [hsub, h1, h2]

end Symbols

/-! ## The two integrals of a regular source -/

section Regular

variable {k : ℝ → Lp ℂ 2 (volume : Measure E)}

theorem intervalIntegral_kgCosOp_freqInv (hk : Continuous k) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, kgCosOp s (kgFreqInvOp (k s)))
      = kgFreqInvOp (∫ s in (0 : ℝ)..t, kgCosOp s (k s)) := by
  have hcos : Continuous fun s : ℝ => kgCosOp s (k s) :=
    continuous_kgCosOp_comp continuous_id hk
  have hI := hcos.intervalIntegrable (μ := volume) 0 t
  have hpoint : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      kgCosOp s (kgFreqInvOp (k s)) = kgFreqInvOp (kgCosOp s (k s)) := fun s _ =>
    (kgFreqInvOp_kgCosOp s (k s)).symm
  rw [intervalIntegral.integral_congr hpoint,
    ContinuousLinearMap.intervalIntegral_comp_comm _ hI]

theorem intervalIntegral_kgSinOp_freqInv (hk : Continuous k) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, kgSinOp s (kgFreqInvOp (k s)))
      = kgFreqInvOp (∫ s in (0 : ℝ)..t, kgSinOp s (k s)) := by
  have hsin : Continuous fun s : ℝ => kgSinOp s (k s) :=
    continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply continuous_id hk
  have hI := hsin.intervalIntegrable (μ := volume) 0 t
  have hpoint : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      kgSinOp s (kgFreqInvOp (k s)) = kgFreqInvOp (kgSinOp s (k s)) := fun s _ =>
    (kgFreqInvOp_kgSinOp s (k s)).symm
  rw [intervalIntegral.integral_congr hpoint,
    ContinuousLinearMap.intervalIntegral_comp_comm _ hI]

/-- The two surviving terms recombine, by the sine subtraction law, into a single integral. -/
theorem kgSinDuhamel_recombine (hk : Continuous k) (t : ℝ) :
    kgSinOp t (∫ s in (0 : ℝ)..t, kgCosOp s (k s))
        - kgCosOp t (∫ s in (0 : ℝ)..t, kgSinOp s (k s))
      = ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (k s) := by
  have hcos : Continuous fun s : ℝ => kgCosOp s (k s) :=
    continuous_kgCosOp_comp continuous_id hk
  have hsin : Continuous fun s : ℝ => kgSinOp s (k s) :=
    continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply continuous_id hk
  have hIc := hcos.intervalIntegrable (μ := volume) 0 t
  have hIs := hsin.intervalIntegrable (μ := volume) 0 t
  have hc' : Continuous fun s : ℝ => kgSinOp t (kgCosOp s (k s)) :=
    continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply continuous_const hcos
  have hs' : Continuous fun s : ℝ => kgCosOp t (kgSinOp s (k s)) :=
    continuous_kgCosOp_comp continuous_const hsin
  have hpoint : ∀ s ∈ Set.uIcc (0 : ℝ) t, kgSinOp (t - s) (k s)
      = kgSinOp t (kgCosOp s (k s)) - kgCosOp t (kgSinOp s (k s)) := by
    intro s _
    rw [kgSinOp_sub]
    rfl
  rw [intervalIntegral.integral_congr hpoint,
    intervalIntegral.integral_sub (hc'.intervalIntegrable (μ := volume) 0 t)
      (hs'.intervalIntegrable (μ := volume) 0 t),
    ContinuousLinearMap.intervalIntegral_comp_comm _ hIc,
    ContinuousLinearMap.intervalIntegral_comp_comm _ hIs]

end Regular

/-! ## The endpoint contributions add up to the source -/

theorem kgCosOp_sq_add_kgSinOp_sq_apply (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgCosOp t (kgCosOp t x) + kgSinOp t (kgSinOp t x) = x := by
  have happ := congrArg
    (fun T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) => T x)
    (kgCosOp_sq_add_kgSinOp_sq (E := E) t)
  simpa using happ

theorem kgEndpoint_sum (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgCosOp t (kgFreqInvOp (kgCosOp t x)) + kgSinOp t (kgFreqInvOp (kgSinOp t x))
      = kgFreqInvOp x := by
  rw [← kgFreqInvOp_kgCosOp, ← kgFreqInvOp_kgSinOp, ← map_add,
    kgCosOp_sq_add_kgSinOp_sq_apply]


/-! ## The second differentiation -/

/-- **The velocity integral is differentiable when the source is regular.** The two endpoint
contributions add to the source by the Pythagorean identity; the two surviving terms recombine by
the sine subtraction law. -/
theorem hasDerivAt_kgCosDuhamel {k : ℝ → Lp ℂ 2 (volume : Measure E)} (hk : Continuous k)
    (t : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, kgCosOp (r - s) (kgFreqInvOp (k s)))
      (kgFreqInvOp (k t) - ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (k s)) t := by
  have hg : Continuous fun s : ℝ => kgFreqInvOp (k s) :=
    (kgFreqInvOp (E := E)).continuous.comp hk
  have hsep : ∀ r : ℝ, (∫ s in (0 : ℝ)..r, kgCosOp (r - s) (kgFreqInvOp (k s)))
      = kgCosOp r (kgFreqInvOp (∫ s in (0 : ℝ)..r, kgCosOp s (k s)))
        + kgSinOp r (kgFreqInvOp (∫ s in (0 : ℝ)..r, kgSinOp s (k s))) := by
    intro r
    rw [← kgDuhamel_deriv_eq hg r, intervalIntegral_kgCosOp_freqInv hk r,
      intervalIntegral_kgSinOp_freqInv hk r]
  have hMc : ∀ r : ℝ, ‖(kgCosOp (E := E) r).restrictScalars ℝ‖ ≤ 1 := by
    intro r
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact norm_kgCosOp_le r
  have hMs : ∀ r : ℝ, ‖(kgSinOp (E := E) r).restrictScalars ℝ‖ ≤ 1 := by
    intro r
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact norm_kgSinOp_le r
  have hyc : HasDerivAt (fun r : ℝ => kgFreqInvOp (∫ s in (0 : ℝ)..r, kgCosOp s (k s)))
      (kgFreqInvOp (kgCosOp t (k t))) t :=
    hasDerivAt_clm _ (hasDerivAt_intervalIntegral_kgCosOp hk t)
  have hys : HasDerivAt (fun r : ℝ => kgFreqInvOp (∫ s in (0 : ℝ)..r, kgSinOp s (k s)))
      (kgFreqInvOp (kgSinOp t (k t))) t :=
    hasDerivAt_clm _ (hasDerivAt_intervalIntegral_kgSinOp hk t)
  have h1 : HasDerivAt
      (fun r : ℝ => kgCosOp r (kgFreqInvOp (∫ s in (0 : ℝ)..r, kgCosOp s (k s))))
      (kgCosOp t (kgFreqInvOp (kgCosOp t (k t)))
        + -(kgSinOp t (∫ s in (0 : ℝ)..t, kgCosOp s (k s)))) t :=
    hasDerivAt_strong_apply hMc (fun x => continuous_kgCosOp_apply x) hyc
      (hasDerivAt_kgCosOp_freqInv t (∫ s in (0 : ℝ)..t, kgCosOp s (k s)))
  have h2 : HasDerivAt
      (fun r : ℝ => kgSinOp r (kgFreqInvOp (∫ s in (0 : ℝ)..r, kgSinOp s (k s))))
      (kgSinOp t (kgFreqInvOp (kgSinOp t (k t)))
        + kgCosOp t (∫ s in (0 : ℝ)..t, kgSinOp s (k s))) t :=
    hasDerivAt_strong_apply hMs (fun x => continuous_kgSinOp_apply x) hys
      (hasDerivAt_kgSinOp_freqInv t (∫ s in (0 : ℝ)..t, kgSinOp s (k s)))
  have hsum := h1.add h2
  have hval : (kgCosOp (E := E) t (kgFreqInvOp (kgCosOp t (k t)))
        + -(kgSinOp t (∫ s in (0 : ℝ)..t, kgCosOp s (k s))))
      + (kgSinOp t (kgFreqInvOp (kgSinOp t (k t)))
        + kgCosOp t (∫ s in (0 : ℝ)..t, kgSinOp s (k s)))
      = kgFreqInvOp (k t) - ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (k s) := by
    rw [← kgSinDuhamel_recombine hk t, ← kgEndpoint_sum (E := E) t (k t)]
    abel
  rw [hval] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun r => ?_
  simp only [Pi.add_apply]
  exact hsep r

end GaloisForLFunctions.HTGeometry
