import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonDuhamelDerivative

/-!
# The first derivative of the Duhamel term

Assembling statements 89–93: the Duhamel term of the field equation is differentiable, and its
derivative is the classical one,

`d/dt ∫₀ᵗ (sin((t-s)⟨D⟩)/⟨D⟩) g(s) ds = ∫₀ᵗ cos((t-s)⟨D⟩) g(s) ds`.

The endpoint contribution vanishes because `sin(0)=0`; the two contributions coming from the
`t`-dependence of the propagators cancel because the multipliers commute; and what survives
recombines, by the cosine subtraction law, into a single integral. No hypothesis on `g` beyond
continuity is needed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Two more symbol identities -/

section Symbols

variable (t s : ℝ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem measurable_cosCos :
    Measurable fun ξ : E => kgCosSymbol t ξ * kgCosSymbol s ξ :=
  (measurable_kgCosSymbol t).mul (measurable_kgCosSymbol s)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem measurable_sinSin :
    Measurable fun ξ : E => kgSinPhase t ξ * kgSinPhase s ξ :=
  (measurable_kgSinPhase t).mul (measurable_kgSinPhase s)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem measurable_sinFreqCos :
    Measurable fun ξ : E => kgSinOverFreq t ξ * kgCosSymbol s ξ :=
  (measurable_kgSinOverFreq t).mul (measurable_kgCosSymbol s)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem norm_cosCos_le (ξ : E) : ‖kgCosSymbol t ξ * kgCosSymbol s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgCosSymbol_le t ξ) (norm_nonneg _) (norm_kgCosSymbol_le s ξ)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem norm_sinSin_le (ξ : E) : ‖kgSinPhase t ξ * kgSinPhase s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgSinPhase_le t ξ) (norm_nonneg _) (norm_kgSinPhase_le s ξ)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem norm_sinFreqCos_le (ξ : E) : ‖kgSinOverFreq t ξ * kgCosSymbol s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgSinOverFreq_le t ξ) (norm_nonneg _) (norm_kgCosSymbol_le s ξ)

/-- **The subtraction law for the cosine propagator.** -/
theorem kgCosOp_sub :
    kgCosOp (E := E) (t - s)
      = (kgCosOp t).comp (kgCosOp s) + (kgSinOp t).comp (kgSinOp s) := by
  have hA := measurable_cosCos (E := E) t s
  have hB := measurable_sinSin (E := E) t s
  have h1 : (kgCosOp (E := E) t).comp (kgCosOp s)
      = fourierMulCLM hA zero_le_one (norm_cosCos_le t s) := by
    rw [kgCosOp_eq, kgCosOp_eq]
    exact fourierMulCLM_comp _ _ hA _ _ _ _ _ (norm_cosCos_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have h2 : (kgSinOp (E := E) t).comp (kgSinOp s)
      = fourierMulCLM hB zero_le_one (norm_sinSin_le t s) := by
    rw [kgSinOp_eq, kgSinOp_eq]
    exact fourierMulCLM_comp _ _ hB _ _ _ _ _ (norm_sinSin_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hadd : kgCosOp (E := E) (t - s)
      = fourierMulCLM hA zero_le_one (norm_cosCos_le t s)
        + fourierMulCLM hB zero_le_one (norm_sinSin_le t s) := by
    rw [kgCosOp_eq]
    refine fourierMulCLM_add hA hB (measurable_kgCosSymbol (E := E) (t - s)) zero_le_one
      (norm_cosCos_le t s) zero_le_one (norm_sinSin_le t s) zero_le_one
      (norm_kgCosSymbol_le (t - s)) (Filter.Eventually.of_forall fun ξ => ?_)
    show ((Real.cos ((t - s) * kgFreq ξ) : ℝ) : ℂ)
      = ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.cos (s * kgFreq ξ) : ℝ) : ℂ)
        + ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.sin (s * kgFreq ξ) : ℝ) : ℂ)
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, sub_mul, Real.cos_sub]
  rw [hadd, h1, h2]

/-- **The half-order propagator commutes with the cosine propagator.** -/
theorem kgSinFreqOp_comm_kgCosOp :
    (kgSinFreqOp (E := E) t).comp (kgCosOp s) = (kgCosOp s).comp (kgSinFreqOp t) := by
  have hA := measurable_sinFreqCos (E := E) t s
  have h1 : (kgSinFreqOp (E := E) t).comp (kgCosOp s)
      = fourierMulCLM hA zero_le_one (norm_sinFreqCos_le t s) := by
    rw [kgSinFreqOp_eq, kgCosOp_eq]
    exact fourierMulCLM_comp _ _ hA _ _ _ _ _ (norm_sinFreqCos_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have h2 : (kgCosOp (E := E) s).comp (kgSinFreqOp t)
      = fourierMulCLM hA zero_le_one (norm_sinFreqCos_le t s) := by
    rw [kgCosOp_eq, kgSinFreqOp_eq]
    exact fourierMulCLM_comp _ _ hA _ _ _ _ _ (norm_sinFreqCos_le t s)
      (Filter.Eventually.of_forall fun _ => mul_comm _ _)
  rw [h1, h2]

end Symbols

/-! ## Differentiating the two halves of the separated term -/

section Derivative

variable {g : ℝ → Lp ℂ 2 (volume : Measure E)}

/-- The first half of the separated Duhamel term. -/
theorem hasDerivAt_kgDuhamelFirst (hg : Continuous g) (t : ℝ) :
    HasDerivAt (fun r : ℝ => kgSinFreqOp r (∫ s in (0 : ℝ)..r, kgCosOp s (g s)))
      (kgSinFreqOp t (kgCosOp t (g t))
        + kgCosOp t (∫ s in (0 : ℝ)..t, kgCosOp s (g s))) t := by
  have hM : ∀ r : ℝ, ‖(kgSinFreqOp (E := E) r).restrictScalars ℝ‖ ≤ 1 := by
    intro r
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact norm_kgSinFreqOp_le r
  exact hasDerivAt_strong_apply hM (fun x => continuous_kgSinFreqOp_apply x)
    (hasDerivAt_intervalIntegral_kgCosOp hg t)
    (hasDerivAt_kgSinFreqOp t (∫ s in (0 : ℝ)..t, kgCosOp s (g s)))

/-- The second half of the separated Duhamel term. Its vector argument is regular, which is what the
cosine propagator's derivative requires. -/
theorem hasDerivAt_kgDuhamelSecond (hg : Continuous g) (t : ℝ) :
    HasDerivAt (fun r : ℝ => kgCosOp r (kgFreqInvOp (∫ s in (0 : ℝ)..r, kgSinOp s (g s))))
      (kgCosOp t (kgFreqInvOp (kgSinOp t (g t)))
        + -(kgSinOp t (∫ s in (0 : ℝ)..t, kgSinOp s (g s)))) t := by
  have hM : ∀ r : ℝ, ‖(kgCosOp (E := E) r).restrictScalars ℝ‖ ≤ 1 := by
    intro r
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact norm_kgCosOp_le r
  have hy : HasDerivAt (fun r : ℝ => kgFreqInvOp (∫ s in (0 : ℝ)..r, kgSinOp s (g s)))
      (kgFreqInvOp (kgSinOp t (g t))) t :=
    hasDerivAt_clm _ (hasDerivAt_intervalIntegral_kgSinOp hg t)
  exact hasDerivAt_strong_apply hM (fun x => continuous_kgCosOp_apply x) hy
    (hasDerivAt_kgCosOp_freqInv t (∫ s in (0 : ℝ)..t, kgSinOp s (g s)))

end Derivative

/-! ## The derivative of the Duhamel term -/

/-- **The Duhamel term is differentiable, with the classical derivative.** The two contributions of
the propagators' own `t`-dependence cancel, because the multipliers commute; what survives is the
cosine subtraction law, recombined into a single integral. -/
theorem hasDerivAt_kgDuhamel {g : ℝ → Lp ℂ 2 (volume : Measure E)} (hg : Continuous g) (t : ℝ) :
    HasDerivAt
      (fun r : ℝ => kgSinFreqOp r (∫ s in (0 : ℝ)..r, kgCosOp s (g s))
        - kgCosOp r (∫ s in (0 : ℝ)..r, kgSinFreqOp s (g s)))
      (kgCosOp t (∫ s in (0 : ℝ)..t, kgCosOp s (g s))
        + kgSinOp t (∫ s in (0 : ℝ)..t, kgSinOp s (g s))) t := by
  have hrw : ∀ r : ℝ, (∫ s in (0 : ℝ)..r, kgSinFreqOp s (g s))
      = kgFreqInvOp (∫ s in (0 : ℝ)..r, kgSinOp s (g s)) := fun r =>
    intervalIntegral_kgSinFreqOp_eq hg r
  have hsub := (hasDerivAt_kgDuhamelFirst hg t).sub (hasDerivAt_kgDuhamelSecond hg t)
  have hcancel : kgSinFreqOp (E := E) t (kgCosOp t (g t))
      = kgCosOp t (kgFreqInvOp (kgSinOp t (g t))) := by
    have h := kgSinFreqOp_comm_kgCosOp (E := E) t t
    have happ := congrArg
      (fun T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) => T (g t)) h
    rw [← kgSinFreqOp_apply_freqInv]
    exact happ
  have hval : kgSinFreqOp (E := E) t (kgCosOp t (g t))
        + kgCosOp t (∫ s in (0 : ℝ)..t, kgCosOp s (g s))
      - (kgCosOp t (kgFreqInvOp (kgSinOp t (g t)))
        + -(kgSinOp t (∫ s in (0 : ℝ)..t, kgSinOp s (g s))))
      = kgCosOp t (∫ s in (0 : ℝ)..t, kgCosOp s (g s))
        + kgSinOp t (∫ s in (0 : ℝ)..t, kgSinOp s (g s)) := by
    rw [hcancel]
    abel
  rw [hval] at hsub
  refine hsub.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun r => ?_
  simp only [Pi.sub_apply]
  rw [hrw r]

/-- **The derivative of the Duhamel term is the classical integral.** -/
theorem kgDuhamel_deriv_eq {g : ℝ → Lp ℂ 2 (volume : Measure E)} (hg : Continuous g) (t : ℝ) :
    kgCosOp t (∫ s in (0 : ℝ)..t, kgCosOp s (g s))
        + kgSinOp t (∫ s in (0 : ℝ)..t, kgSinOp s (g s))
      = ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (g s) := by
  have hcos : Continuous fun s : ℝ => kgCosOp s (g s) :=
    continuous_kgCosOp_comp continuous_id hg
  have hsin : Continuous fun s : ℝ => kgSinOp s (g s) :=
    continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply continuous_id hg
  have hIc := hcos.intervalIntegrable (μ := volume) 0 t
  have hIs := hsin.intervalIntegrable (μ := volume) 0 t
  have hc' : Continuous fun s : ℝ => kgCosOp t (kgCosOp s (g s)) :=
    continuous_kgCosOp_comp continuous_const hcos
  have hs' : Continuous fun s : ℝ => kgSinOp t (kgSinOp s (g s)) :=
    continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply continuous_const hsin
  have hpoint : ∀ s ∈ Set.uIcc (0 : ℝ) t, kgCosOp (t - s) (g s)
      = kgCosOp t (kgCosOp s (g s)) + kgSinOp t (kgSinOp s (g s)) := by
    intro s _
    rw [kgCosOp_sub]
    rfl
  rw [intervalIntegral.integral_congr hpoint,
    intervalIntegral.integral_add (hc'.intervalIntegrable (μ := volume) 0 t)
      (hs'.intervalIntegrable (μ := volume) 0 t),
    ContinuousLinearMap.intervalIntegral_comp_comm _ hIc,
    ContinuousLinearMap.intervalIntegral_comp_comm _ hIs]

end GaloisForLFunctions.HTGeometry
