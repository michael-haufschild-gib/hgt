import GaloisForLFunctions.HTGeometry.LpInjectionCompression

/-! # Coordinates outside the image of an `ℓ²` injection -/

namespace RHTower
noncomputable section

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-- The canonical isometric coordinate injection is zero outside its image. -/
theorem lpScalarInjection_coordinate_of_not_mem (f : I → J) (hf : Function.Injective f)
    (x : lp (fun _ : I => ℂ) 2) (j : J) (hj : j ∉ Set.range f) :
    lpScalarInjection f hf x j = 0 := by
  have hp : lpCoordinatePullback (E := ℂ) f hf (lp.single 2 j 1) = 0 := by
    ext i
    have hne : f i ≠ j := fun h => hj ⟨i, h⟩
    simp [hne]
  rw [lpCoordinatePullback_eq_adjoint_lpScalarInjection] at hp
  have h := ContinuousLinearMap.adjoint_inner_left
    (lpScalarInjection f hf).toContinuousLinearMap x (lp.single 2 j 1)
  rw [hp] at h
  simpa [lp.inner_single_left] using h.symm

end
end RHTower
