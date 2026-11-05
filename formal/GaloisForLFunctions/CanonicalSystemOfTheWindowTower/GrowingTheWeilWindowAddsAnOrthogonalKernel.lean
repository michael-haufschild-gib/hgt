import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLocalWeilKernelIsHermiteBiehler

/-!
# Orthogonal increments of the actual Weil kernel

Aperture inclusion preserves every Fourier coordinate. Its adjoint therefore
maps the larger evaluation vector to the smaller one. The new Riesz component
is orthogonal to the whole old space, and its Gram kernel is exactly the
increase of the reproducing kernel.
-/

open Complex
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

/-- Restriction of an evaluation Riesz vector is the adjoint of exact aperture inclusion. -/
theorem inclusion_adjoint_evalVector {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    (inclusion hab).toContinuousLinearMap.adjoint (evalVector b z) = evalVector a z := by
  apply ext_inner_right ℂ (E := WeilHilbertBeforeContact a)
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left, inner_evalVector, inner_evalVector]
  exact fourier_inclusion hab u z

/-- The additional Riesz component when the aperture increases. -/
def evalVectorIncrement {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    WeilHilbertBeforeContact b := evalVector b z - inclusion hab (evalVector a z)

/-- The additional component is orthogonal to every vector from the old Weil space. -/
theorem inner_evalVectorIncrement_inclusion {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (z : ℂ) (u : WeilHilbertBeforeContact a) :
    inner ℂ (evalVectorIncrement hab z) (inclusion hab u) = 0 := by
  rw [evalVectorIncrement, inner_sub_left (E := WeilHilbertBeforeContact b),
    (inclusion hab).inner_map_map, inner_evalVector, inner_evalVector]
  exact sub_eq_zero.mpr (fourier_inclusion hab u z)

/-- Increasing the aperture adds exactly the Gram kernel of the orthogonal Riesz increments. -/
theorem kernel_sub_eq_inner_increment {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (w z : ℂ) :
    kernel b w z - kernel a w z =
      inner ℂ (evalVectorIncrement hab z) (evalVectorIncrement hab w) := by
  have hcross : inner ℂ (evalVectorIncrement hab z) (inclusion hab (evalVector a w)) = 0 :=
    inner_evalVectorIncrement_inclusion hab z _
  have hreverse : inner ℂ (inclusion hab (evalVector a z)) (evalVectorIncrement hab w) = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) (E := WeilHilbertBeforeContact b),
      inner_evalVectorIncrement_inclusion, map_zero]
  have hsplit (t : ℂ) : evalVector b t =
      evalVectorIncrement hab t + inclusion hab (evalVector a t) := by
    unfold evalVectorIncrement
    exact (sub_add_cancel _ _).symm
  have hi : inner ℂ (evalVector b z) (evalVector b w) =
      inner ℂ (evalVectorIncrement hab z) (evalVectorIncrement hab w) +
        inner ℂ (evalVector a z) (evalVector a w) := by
    rw [hsplit z, hsplit w, inner_add_left (E := WeilHilbertBeforeContact b),
      inner_add_right (E := WeilHilbertBeforeContact b),
      inner_add_right (E := WeilHilbertBeforeContact b), hcross, hreverse,
      (inclusion hab).inner_map_map, add_zero, zero_add]
  rw [inner_evalVector, inner_evalVector] at hi
  exact sub_eq_iff_eq_add.mpr hi

/-- Diagonal kernel growth is the exact squared Weil norm of the new component. -/
theorem kernel_diagonal_sub_eq_norm_increment_sq {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    (kernel b z z - kernel a z z).re = ‖evalVectorIncrement hab z‖ ^ 2 := by
  rw [kernel_sub_eq_inner_increment hab]
  exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
    (E := WeilHilbertBeforeContact b) (evalVectorIncrement hab z)).symm

#print axioms inclusion_adjoint_evalVector
#print axioms inner_evalVectorIncrement_inclusion
#print axioms kernel_sub_eq_inner_increment
#print axioms kernel_diagonal_sub_eq_norm_increment_sq
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
