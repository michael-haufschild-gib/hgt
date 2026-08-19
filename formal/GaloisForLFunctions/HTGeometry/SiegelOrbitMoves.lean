import GaloisForLFunctions.HTGeometry.SiegelOrbit

/-!
# The two reduction moves inside the orbit

A Jacobi datum has a positive definite form, so every congruate of it again carries Jacobi data.
Size reduction moves inside the orbit without changing the potential — it leaves the diagonal fixed
— and a swap at a failing index moves inside the orbit while contracting the potential by `3/4`.

* `JacobiData.posDef` : the form of a Jacobi datum is positive definite.
* `exists_sizeReduced_inOrbit` : **size reduction, inside the orbit, at constant potential.**
* `exists_swap_inOrbit` : **a contracting swap, inside the orbit.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **The form of a Jacobi datum is positive definite.** -/
theorem JacobiData.posDef (J : JacobiData n) : J.form.PosDef := by
  haveI : Invertible J.U :=
    Matrix.invertibleOfIsUnitDet _ (by rw [J.det_eq_one]; exact isUnit_one)
  have hDpos : (Matrix.diagonal J.d).PosDef := Matrix.posDef_diagonal_iff.2 J.pos
  have hinj : Function.Injective (J.U).mulVec :=
    Matrix.mulVec_injective_of_isUnit (isUnit_of_invertible _)
  have hcast : (J.U)ᴴ * Matrix.diagonal J.d * J.U = J.form := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    rfl
  rw [← hcast]
  exact hDpos.conjTranspose_mul_mul_same hinj

/-- The potential is unchanged by a shear, which leaves the diagonal fixed. -/
theorem potentialOf_shear_eq (J : JacobiData n) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : IsIntUnipotent γ) : potentialOf (J.shear hγ).form = potentialOf J.form := by
  rw [potentialOf_form, potentialOf_form]
  rfl

/-- **Size reduction inside the orbit, at constant potential.** -/
theorem exists_sizeReduced_inOrbit {A : Matrix (Fin n) (Fin n) ℝ} (J : JacobiData n)
    (hJ : InOrbit A J.form) :
    ∃ J' : JacobiData n, InOrbit A J'.form ∧ potentialOf J'.form = potentialOf J.form ∧
      ∀ a b : Fin n, a < b → |J'.U a b| ≤ 1 / 2 := by
  obtain ⟨γ, hγ, _, hred⟩ := exists_sizeReduced_shear J
  refine ⟨J.shear hγ, ?_, potentialOf_shear_eq J hγ, hred⟩
  rw [J.shear_form hγ]
  exact hJ.congr hγ.isIntUnimodular

/-- **A contracting swap inside the orbit.** -/
theorem exists_swap_inOrbit {A : Matrix (Fin n) (Fin n) ℝ} (J : JacobiData n)
    (hJ : InOrbit A J.form) {i j : Fin n} (hij : i ≠ j) (hji : i ≤ j)
    (hjs : (j : ℕ) = (i : ℕ) + 1)
    (hfail : J.projNorm i (Pi.single j (1 : ℝ)) < 3 / 4 * J.d i) :
    ∃ J' : JacobiData n, InOrbit A J'.form ∧
      potentialOf J'.form < 3 / 4 * potentialOf J.form := by
  classical
  set τ : Matrix (Fin n) (Fin n) ℝ := permMatrix (Equiv.swap i j) with hτ
  have hτu : IsIntUnimodular τ := isIntUnimodular_permMatrix _
  obtain ⟨g, hgu, hg⟩ := id hτu
  have hdet : IsUnit τ.det := by
    have hmap : τ = g.map (fun z : ℤ => (z : ℝ)) := by
      ext a b
      exact hg a b
    have hdc : (g.map (fun z : ℤ => (z : ℝ))).det = ((g.det : ℤ) : ℝ) :=
      (RingHom.map_det (Int.castRingHom ℝ) g).symm
    rw [hmap, hdc]
    refine (isUnit_iff_ne_zero).2 ?_
    intro hcon
    have hgz : g.det = 0 := by exact_mod_cast hcon
    exact ((Matrix.isUnit_iff_isUnit_det g).1 hgu).ne_zero hgz
  have hτinv : Function.Injective τ.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det τ).2 hdet)
  have hpos : (τᵀ * J.form * τ).PosDef := by
    have hcast : τᴴ * J.form * τ = τᵀ * J.form * τ := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [← hcast]
    exact J.posDef.conjTranspose_mul_mul_same hτinv
  obtain ⟨J', hJ'form⟩ := exists_jacobiData hpos
  refine ⟨J', ?_, ?_⟩
  · rw [hJ'form]
    exact hJ.congr hτu
  · exact potentialOf_swap_lt hij hji hjs hJ'form hfail

end GaloisForLFunctions.HTGeometry
