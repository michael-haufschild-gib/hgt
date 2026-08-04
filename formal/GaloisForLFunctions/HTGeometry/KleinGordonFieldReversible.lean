import GaloisForLFunctions.HTGeometry.KleinGordonFieldStateStability

/-!
# The field evolution is reversible

The Klein–Gordon equation contains only the second time derivative, so reversing time carries a
solution to a solution with the velocity reversed. At the level of the propagators this is the parity
of the trigonometric functions: the cosine is even, the half-order sine is odd.

For the mild solution the Duhamel integral has to be reversed as well, and the change of variable
`r ↦ -r` does it: the two sign changes — one from the orientation of the interval, one from the
oddness of the propagator — cancel, so the reflected curve satisfies the Duhamel formula with the
reflected data. Uniqueness finishes it.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Parity of the propagators -/

private theorem fourierMulCLM_congr' {φ ψ : E → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    {C D : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D) (hD : ∀ ξ, ‖ψ ξ‖ ≤ D)
    (hae : ∀ᵐ ξ ∂(volume : Measure E), ψ ξ = φ ξ) :
    fourierMulCLM hψ hD0 hD = fourierMulCLM hφ hC0 hC := by
  have h := fourierMulCLM_smul hφ hψ hC0 hC hD0 hD (1 : ℂ)
    (by filter_upwards [hae] with ξ hξ; rw [hξ, one_mul])
  rwa [one_smul] at h

/-- **The cosine propagator is even in the time.** -/
theorem kgCosOp_neg (t : ℝ) : kgCosOp (E := E) (-t) = kgCosOp t := by
  rw [kgCosOp_eq, kgCosOp_eq]
  refine fourierMulCLM_congr' _ _ _ _ _ (norm_kgCosSymbol_le (-t))
    (Filter.Eventually.of_forall fun ξ => ?_)
  show ((Real.cos (-t * kgFreq ξ) : ℝ) : ℂ) = ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ)
  rw [neg_mul, Real.cos_neg]

/-- **The half-order sine propagator is odd in the time.** -/
theorem kgSinFreqOp_neg (t : ℝ) : kgSinFreqOp (E := E) (-t) = -(kgSinFreqOp t) := by
  rw [kgSinFreqOp_eq, kgSinFreqOp_eq]
  refine fourierMulCLM_neg _ _ _ _ _ (norm_kgSinOverFreq_le (-t))
    (Filter.Eventually.of_forall fun ξ => ?_)
  show ((Real.sin (-t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
    = -((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
  rw [neg_mul, Real.sin_neg, ← Complex.ofReal_neg]
  congr 1
  ring

/-- **The free field is reversible.** -/
theorem kgFieldFree_neg (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldFree f h (-t) = kgFieldFree f (-h) t := by
  rw [kgFieldFree, kgFieldFree, kgCosOp_neg, kgSinFreqOp_neg]
  simp

/-! ## Reversibility of the mild solution -/

section Reverse

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The field evolution is reversible.** Running the solution backwards in time is the same as
running the solution with the reversed velocity datum forwards. -/
theorem kgFieldMild_neg (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMild W f h (-t) = kgFieldMild W f (-h) t := by
  set u := kgFieldMild W f h with hu
  have hcu : Continuous u := continuous_kgFieldMild hb0 hW f h
  have hk : Continuous fun r : ℝ => W (u r) := W.continuous.comp hcu
  have hrefl : Continuous fun τ : ℝ => u (-τ) := hcu.comp continuous_neg
  have hduh : ∀ τ : ℝ, u (-τ) = kgFieldFree f (-h) τ
      + ∫ ρ in (0 : ℝ)..τ, kgFieldKernel W τ ρ (u (-ρ)) := by
    intro τ
    have hF : Continuous fun r : ℝ => kgSinFreqOp (-τ - r) (W (u r)) :=
      continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hk
    have hker : (∫ r in (0 : ℝ)..(-τ), kgFieldKernel W (-τ) r (u r))
        = ∫ r in (0 : ℝ)..(-τ), kgSinFreqOp (-τ - r) (W (u r)) :=
      intervalIntegral.integral_congr fun r _ => kgFieldKernel_apply W (-τ) r (u r)
    have hcv : (∫ ρ in (0 : ℝ)..τ, kgSinFreqOp (-τ - -ρ) (W (u (-ρ))))
        = ∫ r in (-τ)..(0 : ℝ), kgSinFreqOp (-τ - r) (W (u r)) := by
      have h := intervalIntegral.integral_comp_neg
        (a := (0 : ℝ)) (b := τ) (f := fun r : ℝ => kgSinFreqOp (-τ - r) (W (u r)))
      rw [neg_zero] at h
      exact h
    have hsign : (∫ ρ in (0 : ℝ)..τ, kgFieldKernel W τ ρ (u (-ρ)))
        = ∫ r in (0 : ℝ)..(-τ), kgSinFreqOp (-τ - r) (W (u r)) := by
      have hpt : ∀ ρ ∈ Set.uIcc (0 : ℝ) τ, kgFieldKernel W τ ρ (u (-ρ))
          = -(kgSinFreqOp (-τ - -ρ) (W (u (-ρ)))) := by
        intro ρ _
        rw [kgFieldKernel_apply]
        have hneg : -τ - -ρ = -(τ - ρ) := by ring
        rw [hneg, kgSinFreqOp_neg, neg_apply, neg_neg]
      rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_neg, hcv,
        ← intervalIntegral.integral_symm]
    rw [hsign, ← hker, ← kgFieldFree_neg f h τ]
    exact kgFieldMild_eq hb0 hW f h (-τ)
  have hfin := eq_kgFieldMild_of_duhamel hb0 hW f (-h) hrefl hduh
  exact congrFun hfin t

end Reverse

end GaloisForLFunctions.HTGeometry
