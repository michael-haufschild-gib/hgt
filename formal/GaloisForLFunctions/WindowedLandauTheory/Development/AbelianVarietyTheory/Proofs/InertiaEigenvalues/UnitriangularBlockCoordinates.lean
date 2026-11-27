import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularParabolicCosets
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraCuspidalRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicBlockMatrices

/-! The unipotent Levi blocks and the rectangle give independent
coordinates on upper unitriangular matrices. -/

noncomputable section
open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

local notation "Rect" => Matrix (Fin a) (Fin b) (ZMod g)

private theorem castAdd_ne_natAdd (i : Fin a) (j : Fin b) :
    Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h
  have he : i.val = a + j.val := congrArg Fin.val h
  have hi := i.isLt
  omega

/-- An upper-block matrix with both diagonal blocks unitriangular is unitriangular. -/
theorem isUniUp_upperBlockMatrix_of_blocks (A : Mt g a) (X : Rect) (D : Mt g b)
    (hA : IsUniUp A) (hD : IsUniUp D) : IsUniUp (upperBlockMatrix A X D) := by
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [upperBlockMatrix, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₁₁]
    exact ⟨fun h => (hA i j).1 (show j.val < i.val from h),
      fun h => (hA i j).2 (Fin.castAdd_inj.mp h)⟩
  · refine ⟨fun h => ?_, fun h => (castAdd_ne_natAdd i j h).elim⟩
    change a + j.val < i.val at h
    omega
  · refine ⟨fun _ => ?_, fun h => (castAdd_ne_natAdd j i h.symm).elim⟩
    simp [upperBlockMatrix]
  · simp only [upperBlockMatrix, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₂₂]
    exact ⟨fun h => (hD i j).1 (Nat.lt_of_add_lt_add_left h),
      fun h => (hD i j).2 ((Fin.natAdd_inj a).mp h)⟩

private def upperParabolicInclusion :
    upperUnitriangular g (a + b) →* twoBlockParabolic g a b :=
  Subgroup.inclusion upperUnitriangular_le_twoBlockParabolic

private def upperLevi :
    upperUnitriangular g (a + b) →* Gn g a × Gn g b :=
  twoBlockLevi.comp upperParabolicInclusion

private theorem left_unitriangular (u : upperUnitriangular g (a + b)) :
    (upperLevi u).1 ∈ upperUnitriangular g a := by
  have hu := mem_upperUnitriangular.mp u.property
  intro i j
  change (j < i → tl a u.val.val i j = 0) ∧ (i = j → tl a u.val.val i j = 1)
  rw [tl_apply_add]
  exact ⟨fun h => (hu _ _).1 (show j.val < i.val from h),
    fun h => (hu _ _).2 (congrArg (Fin.castAdd b) h)⟩

private theorem right_unitriangular (u : upperUnitriangular g (a + b)) :
    (upperLevi u).2 ∈ upperUnitriangular g b := by
  have hu := mem_upperUnitriangular.mp u.property
  intro i j
  change (j < i → br a b u.val.val i j = 0) ∧ (i = j → br a b u.val.val i j = 1)
  rw [br_apply_add]
  exact ⟨fun h => (hu _ _).1 (Nat.add_lt_add_left h _),
    fun h => (hu _ _).2 (congrArg (Fin.natAdd a) h)⟩

/-- The two-block Levi map restricted to upper unitriangular groups. -/
def unitriangularLevi :
    upperUnitriangular g (a + b) →* upperUnitriangular g a × upperUnitriangular g b where
  toFun u := (⟨(upperLevi u).1, left_unitriangular u⟩, ⟨(upperLevi u).2, right_unitriangular u⟩)
  map_one' := Prod.ext
    (Subtype.ext (congrArg Prod.fst (map_one upperLevi)))
    (Subtype.ext (congrArg Prod.snd (map_one upperLevi)))
  map_mul' u v := Prod.ext
    (Subtype.ext (congrArg Prod.fst (map_mul upperLevi u v)))
    (Subtype.ext (congrArg Prod.snd (map_mul upperLevi u v)))

theorem unitriangularLevi_fst_val (u : upperUnitriangular g (a + b)) :
    (unitriangularLevi u).1.val.val = tl a u.val.val := rfl

/-- The unitriangular group in one coordinate is trivial. -/
theorem unitriangular_one_subsingleton : Subsingleton (upperUnitriangular g 1) :=
  ⟨fun A B => Subtype.ext (Units.ext (Matrix.ext fun i j =>
    ((A.property i j).2 (Subsingleton.elim i j)).trans
      ((B.property i j).2 (Subsingleton.elim i j)).symm))⟩

/-- Assemble an upper unitriangular matrix from the two diagonal blocks and a rectangle. -/
def unitriangularBlock (A : upperUnitriangular g a) (X : Rect) (D : upperUnitriangular g b) :
    upperUnitriangular g (a + b) :=
  ⟨upperBlockUnit A.val X D.val, isUniUp_upperBlockMatrix_of_blocks _ _ _ A.property D.property⟩

@[simp] theorem unitriangularLevi_block (A : upperUnitriangular g a) (X : Rect)
    (D : upperUnitriangular g b) : unitriangularLevi (unitriangularBlock A X D) = (A, D) := by
  have h : upperLevi (unitriangularBlock A X D) = (A.val, D.val) :=
    twoBlockLevi_upperBlockUnit A.val X D.val
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-- The independent matrix entries give coordinates on the upper unitriangular group. -/
def unitriangularBlockEquiv :
    upperUnitriangular g (a + b) ≃ (upperUnitriangular g a × upperUnitriangular g b) × Rect where
  toFun u := (unitriangularLevi u, upperRightBlock u.val.val)
  invFun z := unitriangularBlock z.1.1 z.2 z.1.2
  left_inv u := Subtype.ext (upperBlockUnit_eq_of_mem_parabolic (upperParabolicInclusion u))
  right_inv z := Prod.ext (unitriangularLevi_block z.1.1 z.2 z.1.2)
    (upperRightBlock_upperBlockMatrix z.1.1.val.val z.2 z.1.2.val.val)

/-- A Levi fibre consists of all rectangles with the two given diagonal blocks. -/
theorem res_eq_sum_rectangle (χ : Gn g (a + b) → ℂ)
    (A : Gn g a) (D : Gn g b) :
    res a b χ A D = ((g : ℂ) ^ (a * b))⁻¹ * ∑ X : Rect, χ (upperBlockUnit A X D) := by
  let P := twoBlockParabolic g a b
  let S (p : P) : Prop := twoBlockLevi p = (A, D)
  let e : {p : P // S p} ≃ Rect :=
    { toFun := fun p => upperRightBlock p.val.val.val
      invFun := fun X => ⟨⟨upperBlockUnit A X D, inPar_upperBlockMatrix A.val X D.val⟩,
        twoBlockLevi_upperBlockUnit A X D⟩
      left_inv := fun p => by
        apply Subtype.ext
        apply Subtype.ext
        have h := upperBlockUnit_eq_of_mem_parabolic p.val
        rw [show twoBlockLevi p.val = (A, D) from p.property] at h
        exact h
      right_inv := fun X => upperRightBlock_upperBlockMatrix A.val X D.val }
  rw [res_eq_sum_diagonal_fibre]
  apply congrArg (((g : ℂ) ^ (a * b))⁻¹ * ·)
  change (∑ p : P, if S p then χ p.val else 0) = _
  rw [← Finset.sum_filter]
  calc
    (∑ p ∈ Finset.univ.filter S, χ p.val) = ∑ p : {p : P // S p}, χ p.val.val :=
      Finset.sum_subtype (p := S) (Finset.univ.filter S)
        (fun p => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ p)))
        (fun p : P => χ p.val)
    _ = _ := Fintype.sum_equiv e _ _ fun p => by
      change χ p.val.val = χ (upperBlockUnit A (upperRightBlock p.val.val.val) D)
      have h := upperBlockUnit_eq_of_mem_parabolic p.val
      rw [show twoBlockLevi p.val = (A, D) from p.property] at h
      exact congrArg χ h.symm

end GlobalTheory.GLq
