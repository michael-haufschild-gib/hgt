import GaloisForLFunctions.HTGeometry.KleinGordonOperator

/-!
# The free Klein–Gordon evolution of a Schwartz datum

The cosine propagator applied to a Schwartz function is again a Schwartz function, and this file
records what it is: the evolution starts at the datum, and the Klein–Gordon operator applied to it is
the multiplier with symbol `⟨ξ⟩² cos(t⟨ξ⟩)`.

Together with the oscillator equation `∂ₜ²cos(t⟨ξ⟩) = -⟨ξ⟩²cos(t⟨ξ⟩)` proved for the symbols, this
says that the spatial side of the field equation and the second time derivative are the *same*
multiplier, up to sign — which is the free Klein–Gordon equation.
-/

namespace GaloisForLFunctions.HTGeometry

open SchwartzMap Function

open scoped SchwartzMap Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace F]

/-- The free Klein–Gordon evolution of a Schwartz datum, at rest. -/
noncomputable def kgFree (f : 𝓢(E, F)) (t : ℝ) : 𝓢(E, F) :=
  fourierMultiplierCLM F (kgCosSymbol t) f

/-- The free evolution driven by an initial velocity. -/
noncomputable def kgFreeVel (f : 𝓢(E, F)) (t : ℝ) : 𝓢(E, F) :=
  fourierMultiplierCLM F (kgSinSymbol t) f

/-- **The evolution starts at the datum.** -/
theorem kgFree_zero (f : 𝓢(E, F)) : kgFree f 0 = f := by
  have hsymb : (kgCosSymbol (E := E) 0) = fun _ : E => (1 : ℂ) := by
    funext ξ
    exact kgCosSymbol_zero ξ
  rw [kgFree, hsymb, fourierMultiplierCLM_const]
  simp

/-- **The velocity evolution starts at zero.** -/
theorem kgFreeVel_zero (f : 𝓢(E, F)) : kgFreeVel f 0 = 0 := by
  have hsymb : (kgSinSymbol (E := E) 0) = fun _ : E => (0 : ℂ) := by
    funext ξ
    exact kgSinSymbol_zero ξ
  rw [kgFreeVel, hsymb, fourierMultiplierCLM_const]
  simp

/-- **The Klein–Gordon operator applied to the free evolution** is the multiplier with symbol
`⟨ξ⟩² cos(t⟨ξ⟩)`. -/
theorem kgOperator_kgFree (f : 𝓢(E, F)) (t : ℝ) :
    kgFree f t - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • Δ (kgFree f t)
      = fourierMultiplierCLM F
        (fun ξ : E => ((kgFreq ξ ^ 2 : ℝ) : ℂ) * kgCosSymbol t ξ) f := by
  have hfreq : Function.HasTemperateGrowth fun ξ : E => ((kgFreq ξ ^ 2 : ℝ) : ℂ) := by
    have hreal : Function.HasTemperateGrowth fun ξ : E => kgFreq ξ ^ 2 :=
      (hasTemperateGrowth_kgFreq E).pow 2
    exact Complex.hasTemperateGrowth_ofReal.comp hreal
  have hcos : Function.HasTemperateGrowth (kgCosSymbol (E := E) t) :=
    hasTemperateGrowth_kgCosSymbol t
  have hbase := fourierMultiplierCLM_kgFreqSq (F := F) (kgFree f t)
  have hcast : fourierMultiplierCLM (𝕜 := ℝ) F (fun ξ : E => kgFreq ξ ^ 2) (kgFree f t)
      = fourierMultiplierCLM F (fun ξ : E => ((kgFreq ξ ^ 2 : ℝ) : ℂ)) (kgFree f t) := by
    have h := fourierMultiplierCLM_ofReal (𝕜 := ℂ) (F := F)
      (g := fun ξ : E => kgFreq ξ ^ 2) ((hasTemperateGrowth_kgFreq E).pow 2) (kgFree f t)
    exact h.symm
  rw [← hbase, hcast, kgFree,
    fourierMultiplierCLM_fourierMultiplierCLM_apply hfreq hcos]
  rfl

end GaloisForLFunctions.HTGeometry
