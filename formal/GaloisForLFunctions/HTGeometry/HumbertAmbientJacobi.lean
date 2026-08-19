import GaloisForLFunctions.HTGeometry.HumbertCoordinates

/-!
# The ambient Jacobi data of a Humbert form

A Humbert form factors as `Wᵀ E W` with `W` unipotent upper triangular and `E` block diagonal, its
`m`-th block being the pullback of the `m`-th Gram–Schmidt diagonal along the embedding matrix.  So
its ambient Jacobi data is computed outright: the diagonal is the concatenation of the blocks'
diagonals, and the unipotent factor is the block diagonal of the blocks' unipotent factors times `W`.

This is the bridge on which "reduced over the order ⟹ reduced over `ℤ`" runs.

* `humbertBlock` : the diagonal block attached to one Gram–Schmidt diagonal.
* `humbertAmbient` : **the ambient Jacobi data.**
* `humbertAmbient_form` : **its form is the Humbert form.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {nb d : ℕ} {R : Type*} [CommRing R]

/-- The diagonal block attached to one Gram–Schmidt diagonal. -/
noncomputable def humbertBlock (T : RealOrderData R d) (Δ : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  T.embMatrixᵀ * Matrix.diagonal Δ * T.embMatrix

theorem humbertBlock_posDef (T : RealOrderData R d) {Δ : Fin d → ℝ} (hΔ : ∀ v, 0 < Δ v) :
    (humbertBlock T Δ).PosDef := by
  refine posDef_congr (Matrix.posDef_diagonal_iff.2 hΔ) fun x hx => ?_
  have hinj := Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det T.embMatrix).2 T.invertible)
  refine hinj ?_
  show T.embMatrix *ᵥ x = T.embMatrix *ᵥ 0
  rw [hx, Matrix.mulVec_zero]

theorem humbertDiagonal_eq (T : RealOrderData R d) (Jv : Fin d → JacobiData nb) :
    humbertDiagonal T Jv
      = blockEmbed (Matrix.diagonal fun m => humbertBlock T (fun v => (Jv v).d m)) := rfl

/-- The ambient Jacobi data of a Humbert form. -/
noncomputable def humbertAmbient (T : RealOrderData R d) (Jv : Fin d → JacobiData nb)
    (Jm : Fin nb → JacobiData d) : JacobiData (nb * d) :=
  (blockJacobi Jm).twist (isUnipotentUpper_humbertUnipotent T Jv)

@[simp]
theorem humbertAmbient_d (T : RealOrderData R d) (Jv : Fin d → JacobiData nb)
    (Jm : Fin nb → JacobiData d) (p : Fin (nb * d)) :
    (humbertAmbient T Jv Jm).d p = (Jm (Fin.divNat p)).d (Fin.modNat p) := rfl

@[simp]
theorem humbertAmbient_U (T : RealOrderData R d) (Jv : Fin d → JacobiData nb)
    (Jm : Fin nb → JacobiData d) :
    (humbertAmbient T Jv Jm).U
      = blockEmbed (Matrix.diagonal fun m => (Jm m).U) * humbertUnipotent T Jv := rfl

/-- **The ambient Jacobi data of a Humbert form.** -/
theorem humbertAmbient_form (T : RealOrderData R d) (Jv : Fin d → JacobiData nb)
    (Jm : Fin nb → JacobiData d)
    (hJm : ∀ m, (Jm m).form = humbertBlock T (fun v => (Jv v).d m)) :
    (humbertAmbient T Jv Jm).form
      = humbertForm T (Matrix.of fun i j => fun v => (Jv v).form i j) := by
  classical
  rw [humbertAmbient, blockJacobi_twist_form, humbertForm_factor]
  have hEq : (Matrix.diagonal fun m => (Jm m).form)
      = (Matrix.diagonal fun m => humbertBlock T (fun v => (Jv v).d m)) := by
    refine funext fun m => funext fun m' => ?_
    by_cases hmm : m = m'
    · subst hmm
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hJm m]
    · rw [Matrix.diagonal_apply_ne _ hmm, Matrix.diagonal_apply_ne _ hmm]
  rw [hEq, humbertDiagonal_eq]

/-- The blocks of a Humbert form built from Gram–Schmidt data carry Jacobi data. -/
theorem exists_humbertBlock_jacobi (T : RealOrderData R d) (Jv : Fin d → JacobiData nb) :
    ∃ Jm : Fin nb → JacobiData d, ∀ m, (Jm m).form = humbertBlock T (fun v => (Jv v).d m) := by
  classical
  choose Jm hJm using fun m : Fin nb =>
    exists_jacobiData (humbertBlock_posDef T (fun v => (Jv v).pos m))
  exact ⟨Jm, hJm⟩

/-- **Every Humbert form built from Gram–Schmidt data has explicit ambient Jacobi data.** -/
theorem exists_ambient_jacobi_humbert (T : RealOrderData R d) (Jv : Fin d → JacobiData nb) :
    ∃ Jm : Fin nb → JacobiData d,
      (∀ m, (Jm m).form = humbertBlock T (fun v => (Jv v).d m)) ∧
      (humbertAmbient T Jv Jm).form
        = humbertForm T (Matrix.of fun i j => fun v => (Jv v).form i j) := by
  obtain ⟨Jm, hJm⟩ := exists_humbertBlock_jacobi T Jv
  exact ⟨Jm, hJm, humbertAmbient_form T Jv Jm hJm⟩

end GaloisForLFunctions.HTGeometry
