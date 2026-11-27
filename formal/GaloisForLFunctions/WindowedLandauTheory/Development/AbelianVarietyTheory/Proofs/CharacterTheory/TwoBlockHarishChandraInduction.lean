import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import GaloisForLFunctions.RHTower.Artin.ArtinClassFunctionInduction
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Harish–Chandra induction is ordinary induction from the block
parabolic after composing with the map to the two diagonal blocks. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g a b : ℕ}

/-- A block upper triangular matrix in the standard decomposition of the coordinate space. -/
def upperBlockMatrix (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    Mt g (a + b) :=
  (Matrix.fromBlocks A B 0 D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- The upper-right rectangle in the standard two-block decomposition. -/
def upperRightBlock (M : Mt g (a + b)) : Matrix (Fin a) (Fin b) (ZMod g) :=
  fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)

variable [Fact g.Prime]

theorem tl_apply_add (M : Mt g (a + b)) (i j : Fin a) :
    tl a M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [tl, entN, hi, hj, and_self, dif_pos]
  rfl

theorem br_apply_add (M : Mt g (a + b)) (i j : Fin b) :
    br a b M i j = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [br, entN, hi, hj, and_self, dif_pos]
  rfl

theorem inPar_iff_lowerLeft_zero (M : Mt g (a + b)) :
    InPar a M ↔ ∀ (i : Fin b) (j : Fin a), M (Fin.natAdd a i) (Fin.castAdd b j) = 0 := by
  constructor
  · intro h i j
    exact h _ _ j.isLt (Nat.le_add_right _ _)
  · intro h i j hj hi
    have hj' : (Fin.castAdd b (⟨j.val, hj⟩ : Fin a)) = j := Fin.ext rfl
    have hi' : (Fin.natAdd a (⟨i.val - a, by
      have e := i.isLt
      omega⟩ : Fin b)) = i :=
      Fin.ext (Nat.add_sub_of_le hi)
    exact (congrArg₂ M hi' hj').symm.trans (h _ _)

theorem inPar_upperBlockMatrix (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    InPar a (upperBlockMatrix A B D) := by
  rw [inPar_iff_lowerLeft_zero]
  intro i j
  simp [upperBlockMatrix]

theorem upperBlockMatrix_eq {M : Mt g (a + b)} (h : InPar a M) :
    upperBlockMatrix (tl a M) (upperRightBlock M) (br a b M) = M := by
  rw [inPar_iff_lowerLeft_zero] at h
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [upperBlockMatrix, tl_apply_add, br_apply_add, upperRightBlock, h]

theorem det_upperBlockMatrix (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    (upperBlockMatrix A B D).det = A.det * D.det := by
  rw [upperBlockMatrix, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

theorem upperBlockMatrix_mul
    (A A' : Mt g a) (B B' : Matrix (Fin a) (Fin b) (ZMod g)) (D D' : Mt g b) :
    upperBlockMatrix A B D * upperBlockMatrix A' B' D' =
      upperBlockMatrix (A * A') (A * B' + B * D') (D * D') := by
  rw [upperBlockMatrix, upperBlockMatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [upperBlockMatrix]

private theorem blocks_mul (x y : Mt g (a + b)) (hx : InPar a x) (hy : InPar a y) :
    InPar a (x * y) ∧ tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y := by
  have e := upperBlockMatrix_mul (tl a x) (tl a y) (upperRightBlock x) (upperRightBlock y) (br a b x) (br a b y)
  rw [upperBlockMatrix_eq hx, upperBlockMatrix_eq hy] at e
  rw [e]
  refine ⟨inPar_upperBlockMatrix _ _ _, ?_, ?_⟩
  · ext i j
    simp [tl_apply_add, upperBlockMatrix]
  · ext i j
    simp [br_apply_add, upperBlockMatrix]

private def twoBlockSubmonoid (g a b : ℕ) [Fact g.Prime] : Submonoid (Gn g (a + b)) where
  carrier := {x | InPar a (x : Mt g (a + b))}
  one_mem' := fun i j hj hi => Matrix.one_apply_ne (by rintro rfl; omega)
  mul_mem' := fun {x y} hx hy => (blocks_mul (x : Mt g (a + b)) (y : Mt g (a + b)) hx hy).1

/-- The parabolic subgroup preserving the first coordinate block. -/
def twoBlockParabolic (g a b : ℕ) [Fact g.Prime] : Subgroup (Gn g (a + b)) where
  __ := twoBlockSubmonoid g a b
  inv_mem' := by
    intro x hx
    have e : x ^ (orderOf x - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [inv_eq_of_mul_eq_one_left e]
    exact (twoBlockSubmonoid g a b).pow_mem hx _

private def topLeftMonoidHom : twoBlockParabolic g a b →* Mt g a where
  toFun p := tl a (p.val : Mt g (a + b))
  map_one' := by
    ext i j
    simp [tl_apply_add, Matrix.one_apply, Fin.castAdd_inj]
  map_mul' u v := (blocks_mul (u.val : Mt g (a + b)) (v.val : Mt g (a + b)) u.2 v.2).2.1

private def bottomRightMonoidHom : twoBlockParabolic g a b →* Mt g b where
  toFun p := br a b (p.val : Mt g (a + b))
  map_one' := by
    ext i j
    simp [br_apply_add, Matrix.one_apply, Fin.natAdd_inj]
  map_mul' u v := (blocks_mul (u.val : Mt g (a + b)) (v.val : Mt g (a + b)) u.2 v.2).2.2

/-- The diagonal block map to the two general linear groups. -/
def twoBlockLevi : twoBlockParabolic g a b →* Gn g a × Gn g b :=
  (topLeftMonoidHom (g := g) (a := a) (b := b)).toHomUnits.prod
    (bottomRightMonoidHom (g := g) (a := a) (b := b)).toHomUnits

theorem twoBlockLevi_val (p : twoBlockParabolic g a b) :
    twoBlockLevi p = (toG (tl a (p.val : Mt g (a + b))), toG (br a b (p.val : Mt g (a + b)))) := by
  apply Prod.ext
  · have h : IsUnit (tl a (p.val : Mt g (a + b))) := (twoBlockLevi p).1.isUnit
    apply Units.ext
    change tl a (p.val : Mt g (a + b)) = (toG (tl a (p.val : Mt g (a + b)))).val
    rw [toG, dif_pos h, IsUnit.unit_spec]
  · have h : IsUnit (br a b (p.val : Mt g (a + b))) := (twoBlockLevi p).2.isUnit
    apply Units.ext
    change br a b (p.val : Mt g (a + b)) = (toG (br a b (p.val : Mt g (a + b)))).val
    rw [toG, dif_pos h, IsUnit.unit_spec]

/-- The two-block Harish–Chandra sum is induction of the block character. -/
theorem hc_eq_inducedFunction (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) = inducedFunction (twoBlockParabolic g a b)
      (fun p => α (twoBlockLevi p).1 * β (twoBlockLevi p).2) := by
  let P := twoBlockParabolic g a b
  let f (p : P) := α (twoBlockLevi p).1 * β (twoBlockLevi p).2
  have hcard : Nat.card P =
      (Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact congrArg Finset.card (Finset.filter_congr fun _ _ => Iff.rfl)
  funext x
  unfold hc hcT inducedFunction
  rw [hcard]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv (Gn g (a + b))) _ _ fun y => ?_
  simp only [Equiv.inv_apply, inv_inv]
  let z := y⁻¹ * x * y
  by_cases h : z ∈ P
  · rw [if_pos (show InPar a (z : Mt g (a + b)) from h), extendByZero_of_mem _ f h]
    exact (congrArg (fun p : Gn g a × Gn g b => α p.1 * β p.2) (twoBlockLevi_val ⟨z, h⟩)).symm
  · rw [if_neg (show ¬InPar a (z : Mt g (a + b)) from h), extendByZero_of_notMem _ f h]

/-- Harish–Chandra induction of two representation characters is a representation character. -/
theorem isChar_hc {α : Gn g a → ℂ} {β : Gn g b → ℂ} (hα : IsChar α) (hβ : IsChar β) :
    IsChar (hc a b α β (a + b)) := by
  obtain ⟨V, hV⟩ := hα
  obtain ⟨W, hW⟩ := hβ
  let P := twoBlockParabolic g a b
  let π : P →* Gn g a × Gn g b := twoBlockLevi
  let ρV := V.ρ.comp ((MonoidHom.fst (Gn g a) (Gn g b)).comp π)
  let ρW := W.ρ.comp ((MonoidHom.snd (Gn g a) (Gn g b)).comp π)
  let ρ := Representation.tprod ρV ρW
  refine ⟨FDRep.of (Representation.ind P.subtype ρ), fun x => ?_⟩
  change (Representation.ind P.subtype ρ).character x = _
  rw [induced_character_eq_inducedFunction, hc_eq_inducedFunction]
  congr 1
  funext p
  change (Representation.tprod ρV ρW).character p = _
  rw [Representation.char_tensor, Pi.mul_apply]
  exact congrArg₂ (· * ·) (hV (π p).1) (hW (π p).2)

/-- Iterating block induction preserves the property of being a representation character. -/
theorem isChar_hcL (L : List (Pc g)) (h : ∀ p ∈ L, IsChar p.2) : IsChar (hcL L (degL L)) := by
  induction L with
  | nil =>
    refine ⟨FDRep.of (Representation.trivial ℂ (Gn g 0) ℂ), fun x => ?_⟩
    change LinearMap.trace ℂ ℂ ((Representation.trivial ℂ (Gn g 0) ℂ) x) = 1
    simp [Representation.trivial]
  | cons p L ih =>
    change IsChar (hc p.1 (degL L) p.2 (hcL L (degL L)) (p.1 + degL L))
    exact isChar_hc (h p List.mem_cons_self) (ih fun q hq => h q (List.mem_cons_of_mem p hq))

end GlobalTheory.GLq
