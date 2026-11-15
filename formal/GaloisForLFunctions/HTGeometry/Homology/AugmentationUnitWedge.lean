import GaloisForLFunctions.HTGeometry.Homology.SquareZeroCyclicExterior

/-!
# Exterior moments of inverse units

An augmentation derivation sends the unit to zero. Applying its Leibniz rule to
an inverse pair forces the exterior product of their tangent moments to vanish:
one augmentation coefficient is invertible, so it cancels from the wedge relation.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.SquareZeroCyclic
variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]

/-- An augmentation derivation vanishes on the algebra unit. -/
theorem augmentationDerivation_one (ε : A →ₐ[ℂ] ℂ) (δ : A →ₗ[ℂ] V)
    (hδ : ∀ a b, δ (a*b) = ε a • δ b + ε b • δ a) : δ 1 = 0 := by
  have h := hδ 1 1
  simp only [one_mul, map_one, one_smul] at h
  apply add_left_cancel (a := δ 1)
  simpa only [add_zero] using h.symm

/-- The tangent moments of a unit and its inverse have zero exterior product. -/
theorem augmentationUnit_tangentWedge (ε : A →ₐ[ℂ] ℂ) (δ : A →ₗ[ℂ] V)
    (hδ : ∀ a b, δ (a*b) = ε a • δ b + ε b • δ a) (u : Aˣ) :
    tangentWedge (δ (↑(u⁻¹) : A)) (δ (↑u : A)) = 0 := by
  have hu : (↑(u⁻¹) : A) * (↑u : A) = 1 := Units.inv_mul u
  have h := hδ (↑(u⁻¹) : A) (↑u : A)
  rw [hu, augmentationDerivation_one ε δ hδ] at h
  have hw := congrArg (fun z : V => tangentWedge (δ (↑(u⁻¹) : A)) z) h
  simp only [tangentWedge_zero_right, tangentWedge_add_right, tangentWedge_smul_right,
    tangentWedge_self, smul_zero, add_zero] at hw
  have hε : ε (↑(u⁻¹) : A) ≠ 0 := Units.ne_zero (Units.map ε.toMonoidHom (u⁻¹))
  exact (smul_eq_zero.mp hw.symm).resolve_left hε

#print axioms augmentationDerivation_one
#print axioms augmentationUnit_tangentWedge
end GaloisForLFunctions.RHTower.SquareZeroCyclic
