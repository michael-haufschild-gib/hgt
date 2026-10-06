import Mathlib

/-!
# Determinant scaling of top-degree alternating maps and orientation signs

On an `n`-dimensional real vector space `E` a top-degree alternating map `f` transforms under a
linear map `L` by the determinant: `f(L v₁, …, L vₙ) = det L · f(v₁, …, vₙ)`.

Relative to a reference orientation `e`, an orientation `o` has sign `+1` if `o = e` and `−1`
otherwise.  Transporting `o` by a linear automorphism `L` multiplies the sign by the sign of
`det L`, so that `|det L| · sign_e(L_* o) = det L · sign_e(o)`.  Together the two rules are the
change-of-variables law of oriented top-form densities.
-/

open Module

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}

/-- **Determinant scaling**: a top-degree alternating map evaluated on `L ∘ v` is `det L` times its
value on `v`. -/
theorem topForm_apply_comp_eq_det_mul (hn : finrank ℝ E = n)
    (f : E [⋀^Fin n]→L[ℝ] ℝ) (L : E →L[ℝ] E) (v : Fin n → E) :
    f (L ∘ v) = LinearMap.det (L : E →ₗ[ℝ] E) * f v := by
  let b : Basis (Fin n) ℝ E := finBasisOfFinrankEq ℝ E hn
  have hf : f.toAlternatingMap = f b • b.det := f.toAlternatingMap.eq_smul_basis_det b
  have h1 : f (L ∘ v) = f b * b.det (L ∘ v) := by
    have := congrArg (fun g : E [⋀^Fin n]→ₗ[ℝ] ℝ => g (L ∘ v)) hf
    simpa using this
  have h2 : f v = f b * b.det v := by
    have := congrArg (fun g : E [⋀^Fin n]→ₗ[ℝ] ℝ => g v) hf
    simpa using this
  rw [h1, h2, show (L ∘ v) = (L : E →ₗ[ℝ] E) ∘ v from rfl, b.det_comp]
  ring

/-- The sign of an orientation relative to a reference orientation. -/
noncomputable def orientationSign (e o : Orientation ℝ E (Fin n)) : ℝ :=
  open Classical in if o = e then 1 else -1

omit [FiniteDimensional ℝ E] in
theorem orientationSign_self (e : Orientation ℝ E (Fin n)) : orientationSign e e = 1 := by
  simp [orientationSign]

omit [FiniteDimensional ℝ E] in
theorem orientationSign_sq (e o : Orientation ℝ E (Fin n)) : orientationSign e o ^ 2 = 1 := by
  unfold orientationSign
  split_ifs <;> norm_num

omit [FiniteDimensional ℝ E] in
theorem abs_orientationSign (e o : Orientation ℝ E (Fin n)) : |orientationSign e o| = 1 := by
  unfold orientationSign
  split_ifs <;> norm_num

/-- **Orientation transport**: `|det L| · sign_e(L_* o) = det L · sign_e(o)`. -/
theorem abs_det_mul_orientationSign_map (hn : finrank ℝ E = n)
    (e o : Orientation ℝ E (Fin n)) (L : E ≃ₗ[ℝ] E) :
    |LinearMap.det (L : E →ₗ[ℝ] E)| * orientationSign e (Orientation.map (Fin n) L o) =
      LinearMap.det (L : E →ₗ[ℝ] E) * orientationSign e o := by
  have hcard : Fintype.card (Fin n) = finrank ℝ E := by simp [hn]
  have hdet : LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 := by
    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  have hne : e ≠ -e := Module.Ray.ne_neg_self e
  rcases Orientation.eq_or_eq_neg o e hcard with ho | ho
  · subst ho
    rcases lt_or_gt_of_ne hdet with hneg | hpos
    · have hm : Orientation.map (Fin n) L o = -o :=
        (Orientation.map_eq_neg_iff_det_neg o L hcard).mpr hneg
      rw [hm, orientationSign, if_neg (Module.Ray.ne_neg_self o).symm, orientationSign_self,
        abs_of_neg hneg]
      ring
    · have hm : Orientation.map (Fin n) L o = o :=
        (Orientation.map_eq_iff_det_pos o L hcard).mpr hpos
      rw [hm, orientationSign_self, abs_of_pos hpos]
  · subst ho
    have hmap : Orientation.map (Fin n) L (-e) = -Orientation.map (Fin n) L e :=
      Orientation.map_neg _ _
    rcases lt_or_gt_of_ne hdet with hneg | hpos
    · have hm : Orientation.map (Fin n) L e = -e :=
        (Orientation.map_eq_neg_iff_det_neg e L hcard).mpr hneg
      have hnn : -(-e) = e := neg_neg e
      rw [hmap, hm, hnn, orientationSign_self, orientationSign, if_neg hne.symm,
        abs_of_neg hneg]
      ring
    · have hm : Orientation.map (Fin n) L e = e :=
        (Orientation.map_eq_iff_det_pos e L hcard).mpr hpos
      rw [hmap, hm, abs_of_pos hpos]

end GaloisForLFunctions.HTGeometry
