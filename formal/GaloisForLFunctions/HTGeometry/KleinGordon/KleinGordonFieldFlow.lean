import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonRegularitySharp

/-!
# The free field evolution is a flow

A solution of an autonomous equation restarted from its own state at an intermediate time continues
the same solution. For the free Klein–Gordon field that is an algebraic identity between propagators,
and it is the addition laws that supply it: the cosine addition law moves the position datum, the
sine addition law moves the velocity datum, and the two cross terms are exactly what the commutation
of the multipliers lets one exchange.

The statement needs the position datum to carry one power of `⟨D⟩⁻¹`, because the velocity at the
intermediate time is only defined there (statement 87); the velocity datum is arbitrary.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The addition law for the half-order propagator -/

section Symbols

variable (t s : ℝ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem measurable_cosSinFreq :
    Measurable fun ξ : E => kgCosSymbol t ξ * kgSinOverFreq s ξ :=
  (measurable_kgCosSymbol t).mul (measurable_kgSinOverFreq s)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem measurable_sinFreqCos' :
    Measurable fun ξ : E => kgSinOverFreq t ξ * kgCosSymbol s ξ :=
  (measurable_kgSinOverFreq t).mul (measurable_kgCosSymbol s)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem norm_cosSinFreq_le (ξ : E) : ‖kgCosSymbol t ξ * kgSinOverFreq s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgCosSymbol_le t ξ) (norm_nonneg _) (norm_kgSinOverFreq_le s ξ)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem norm_sinFreqCos'_le (ξ : E) : ‖kgSinOverFreq t ξ * kgCosSymbol s ξ‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_kgSinOverFreq_le t ξ) (norm_nonneg _) (norm_kgCosSymbol_le s ξ)

/-- **The addition law for the half-order propagator.** -/
theorem kgSinFreqOp_add :
    kgSinFreqOp (E := E) (t + s)
      = (kgCosOp t).comp (kgSinFreqOp s) + (kgSinFreqOp t).comp (kgCosOp s) := by
  have hA := measurable_cosSinFreq (E := E) t s
  have hB := measurable_sinFreqCos' (E := E) t s
  have h1 : (kgCosOp (E := E) t).comp (kgSinFreqOp s)
      = fourierMulCLM hA zero_le_one (norm_cosSinFreq_le t s) := by
    rw [kgCosOp_eq, kgSinFreqOp_eq]
    exact fourierMulCLM_comp _ _ hA _ _ _ _ _ (norm_cosSinFreq_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have h2 : (kgSinFreqOp (E := E) t).comp (kgCosOp s)
      = fourierMulCLM hB zero_le_one (norm_sinFreqCos'_le t s) := by
    rw [kgSinFreqOp_eq, kgCosOp_eq]
    exact fourierMulCLM_comp _ _ hB _ _ _ _ _ (norm_sinFreqCos'_le t s)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hadd : kgSinFreqOp (E := E) (t + s)
      = fourierMulCLM hA zero_le_one (norm_cosSinFreq_le t s)
        + fourierMulCLM hB zero_le_one (norm_sinFreqCos'_le t s) := by
    rw [kgSinFreqOp_eq]
    refine fourierMulCLM_add hA hB (measurable_kgSinOverFreq (E := E) (t + s)) zero_le_one
      (norm_cosSinFreq_le t s) zero_le_one (norm_sinFreqCos'_le t s) zero_le_one
      (norm_kgSinOverFreq_le (t + s)) (Filter.Eventually.of_forall fun ξ => ?_)
    show ((Real.sin ((t + s) * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
      = ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ) * ((Real.sin (s * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
        + ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ) * ((Real.cos (s * kgFreq ξ) : ℝ) : ℂ)
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, add_mul, Real.sin_add]
    congr 1
    ring
  rw [hadd, h1, h2]

end Symbols

/-! ## The flow property -/

/-- The velocity of the free field with position datum `⟨D⟩⁻¹g` and velocity datum `h`. -/
def kgFieldFreeVel (g h : Lp ℂ 2 (volume : Measure E)) (s : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  -(kgSinOp s g) + kgCosOp s h

theorem hasDerivAt_kgFieldFree' (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgFieldFree (kgFreqInvOp g) h) (kgFieldFreeVel g h t) t :=
  hasDerivAt_kgFieldFree g h t

/-- **The free field evolution is a flow.** Restarting the solution from its own state at time `s`
reproduces it. -/
theorem kgFieldFree_flow (g h : Lp ℂ 2 (volume : Measure E)) (t s : ℝ) :
    kgFieldFree (kgFreqInvOp g) h (t + s)
      = kgFieldFree (kgFieldFree (kgFreqInvOp g) h s) (kgFieldFreeVel g h s) t := by
  have hcomm : kgSinFreqOp (E := E) t (kgSinOp s g)
      = kgSinOp t (kgSinOp s (kgFreqInvOp g)) := by
    rw [kgSinFreqOp_apply_freqInv, kgFreqInvOp_kgSinOp, kgFreqInvOp_kgSinOp]
  have hcos := kgCosOp_add (E := E) t s
  have hsin := kgSinFreqOp_add (E := E) t s
  simp only [kgFieldFree, kgFieldFreeVel, hcos, hsin, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, map_add, map_neg, hcomm]
  abel

end GaloisForLFunctions.HTGeometry
