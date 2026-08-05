import GaloisForLFunctions.HTGeometry.ImplicitLipschitzGraph

/-!
# Dominating partial coefficients exist

The implicit-graph and carrier laws are conditioned on one partial coefficient of a linear
functional dominating the approximation error.  The coefficient of a coordinate functional is one at
its own index and zero elsewhere, so the coordinate functional dominates every error below one — and
scaling it by a constant dominates every error below that constant's modulus.
-/

open Complex

namespace GaloisForLFunctions

variable {m : ℕ}

/-- The partial coefficients of a coordinate functional. -/
@[simp] theorem partialCoeff_proj (j k : Fin m) :
    partialCoeff (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) j) k =
      if j = k then 1 else 0 := by
  rw [partialCoeff]
  simp [Pi.single_apply]

/-- **The coordinate functional dominates every error below one.** -/
theorem lt_norm_partialCoeff_proj {C : ℝ} (hC : C < 1) (j : Fin m) :
    C < ‖partialCoeff (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) j) j‖ := by
  rw [partialCoeff_proj]
  simpa using hC

/-- A scaled coordinate functional dominates every error below the scale. -/
theorem lt_norm_partialCoeff_smul_proj {C : ℝ} {c : ℂ} (hC : C < ‖c‖) (j : Fin m) :
    C < ‖partialCoeff (c • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) j) j‖ := by
  have hval : partialCoeff (c • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) j) j
      = c := by
    rw [partialCoeff]
    simp
  rw [hval]
  exact hC

/-- So the domination hypothesis is satisfiable at every error level. -/
theorem exists_lt_norm_partialCoeff (C : ℝ) (j : Fin m) :
    ∃ L : ((Fin m) → ℂ) →L[ℂ] ℂ, C < ‖partialCoeff L j‖ := by
  refine ⟨((C + 1 : ℝ) : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) j, ?_⟩
  refine lt_norm_partialCoeff_smul_proj ?_ j
  rw [Complex.norm_real, Real.norm_eq_abs]
  have : C < |C + 1| := by
    rcases abs_cases (C + 1) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  exact this

end GaloisForLFunctions
