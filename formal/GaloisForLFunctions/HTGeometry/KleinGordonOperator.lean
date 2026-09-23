import GaloisForLFunctions.HTGeometry.KleinGordonSynthesis

/-!
# The Klein–Gordon frequency squared is the Klein–Gordon operator

The frequency `⟨ξ⟩ = √(1 + ‖ξ‖²)` was chosen so that the symbol calculus stays smooth at the origin.
This file identifies what the multiplier `⟨ξ⟩²` is on the physical side:

`𝓕⁻(⟨ξ⟩² 𝓕f) = f - (2π)⁻² Δ f`,

the Klein–Gordon operator of unit mass in the convention mathlib's Fourier transform imposes. So the
oscillator equation `∂ₜ²û = -⟨ξ⟩²û` of the propagator symbols is the Klein–Gordon equation
`∂ₜ²u = (2π)⁻²Δu - u` of the field.
-/

namespace GaloisForLFunctions.HTGeometry

open SchwartzMap

open scoped SchwartzMap Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace F]

omit [NormedSpace ℂ F] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F] [InnerProductSpace ℝ E] in
theorem kgFreq_sq (ξ : E) : kgFreq ξ ^ (2 : ℕ) = 1 + ‖ξ‖ ^ (2 : ℕ) := by
  rw [kgFreq, Real.sq_sqrt (by positivity)]

/-- **The Klein–Gordon multiplier is the Klein–Gordon operator.** -/
theorem fourierMultiplierCLM_kgFreqSq (f : 𝓢(E, F)) :
    fourierMultiplierCLM (𝕜 := ℝ) F (fun ξ : E => kgFreq ξ ^ (2 : ℕ)) f
      = f - (((2 * Real.pi) ^ (2 : ℕ))⁻¹ : ℝ) • Δ f := by
  classical
  set g : Fin 2 → E → ℝ := ![fun _ : E => (1 : ℝ), fun ξ : E => ‖ξ‖ ^ (2 : ℕ)] with hg
  have hgrow : ∀ i ∈ (Finset.univ : Finset (Fin 2)), (g i).HasTemperateGrowth := by
    intro i _
    fin_cases i
    · exact Function.HasTemperateGrowth.const (1 : ℝ)
    · exact Function.hasTemperateGrowth_norm_sq E
  have hsum : (fun ξ : E => ∑ i : Fin 2, g i ξ) = fun ξ : E => kgFreq ξ ^ (2 : ℕ) := by
    funext ξ
    rw [Fin.sum_univ_two, kgFreq_sq, hg]
    simp
  have hmul := fourierMultiplierCLM_sum (𝕜 := ℝ) F hgrow
  rw [← hsum]
  have happ : (fourierMultiplierCLM (𝕜 := ℝ) F fun ξ : E => ∑ i : Fin 2, g i ξ) f
      = ∑ i : Fin 2, fourierMultiplierCLM (𝕜 := ℝ) F (g i) f := by
    rw [hmul]
    simp
  rw [happ, Fin.sum_univ_two, hg]
  have hone : fourierMultiplierCLM (𝕜 := ℝ) F (fun _ : E => (1 : ℝ)) f = f := by
    have := fourierMultiplierCLM_const (𝕜 := ℝ) (F := F) (E := E) (1 : ℝ)
    rw [this]
    simp
  have hlap : fourierMultiplierCLM (𝕜 := ℝ) F (fun ξ : E => ‖ξ‖ ^ (2 : ℕ)) f
      = -(((2 * Real.pi) ^ (2 : ℕ))⁻¹ : ℝ) • Δ f := by
    have hL := laplacian_eq_fourierMultiplierCLM (F := F) f
    rw [hL, smul_smul]
    have hpi : (0 : ℝ) < (2 * Real.pi) ^ (2 : ℕ) := by positivity
    rw [show -(((2 * Real.pi) ^ (2 : ℕ))⁻¹ : ℝ) * -(2 * Real.pi) ^ (2 : ℕ) = 1 from by
      field_simp]
    simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hone, hlap, neg_smul]
  abel

end GaloisForLFunctions.HTGeometry
