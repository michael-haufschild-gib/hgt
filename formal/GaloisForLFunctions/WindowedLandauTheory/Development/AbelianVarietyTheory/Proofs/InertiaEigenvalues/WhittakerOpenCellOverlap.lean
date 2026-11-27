import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularParabolicCosets
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedCharacterDoubleCosets
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicBlockMatrices

/-! The intersection in the open cell is a direct product of the two
unitriangular groups in the Levi quotient. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

abbrev openCellOverlap (g a b : ℕ) [Fact g.Prime] :=
  doubleCosetOverlap (upperUnitriangular g (a + b)) (twoBlockParabolic g a b)
    (permutationUnit (openCellPermutation a b))

variable {g a b : ℕ} [Fact g.Prime]

local notation "U" => upperUnitriangular g (a + b)
local notation "P" => twoBlockParabolic g a b
local notation "O" => openCellOverlap g a b
local notation "σ" => openCellPermutation a b
local notation "w" => (permutationUnit σ : Gn g (a + b))

abbrev openCellConj : O →* P := doubleCosetOverlapConj U P w

private theorem left_lt_left (i j : Fin a) :
    σ (Fin.castAdd b i) < σ (Fin.castAdd b j) ↔ i < j := by
  change (σ (Fin.castAdd b i)).val < (σ (Fin.castAdd b j)).val ↔ i.val < j.val
  rw [openCellPermutation_left, openCellPermutation_left]
  omega

private theorem right_lt_right (i j : Fin b) :
    σ (Fin.natAdd a i) < σ (Fin.natAdd a j) ↔ i < j := by
  change (σ (Fin.natAdd a i)).val < (σ (Fin.natAdd a j)).val ↔ i.val < j.val
  rw [openCellPermutation_right, openCellPermutation_right]

private theorem right_lt_left (i : Fin a) (j : Fin b) :
    σ (Fin.natAdd a j) < σ (Fin.castAdd b i) := by
  change (σ (Fin.natAdd a j)).val < (σ (Fin.castAdd b i)).val
  rw [openCellPermutation_right, openCellPermutation_left]
  exact j.isLt.trans_le (Nat.le_add_right _ _)

theorem openCellConj_apply (u : O) (i j : Fin (a + b)) :
    (openCellConj u).val.val i j = u.val.val.val (σ i) (σ j) := by
  change (w⁻¹ * u.val.val * w : Gn g (a + b)).val i j = u.val.val.val (σ i) (σ j)
  simpa only [Units.val_one, inv_one, one_mul, mul_one] using
    monomialConj_apply σ (fun _ => 1) u.val.val i j

private theorem openCellConj_rectangle_zero (u : O) :
    upperRightBlock (openCellConj u).val.val = 0 := by
  ext i j
  change (openCellConj u).val.val (Fin.castAdd b i) (Fin.natAdd a j) = 0
  rw [openCellConj_apply]
  exact (mem_upperUnitriangular.mp u.val.property _ _).1 (right_lt_left i j)

private theorem leftLevi_mem (u : O) : (twoBlockLevi (openCellConj u)).1 ∈ upperUnitriangular g a := by
  intro i j
  change (j < i → tl a (openCellConj u).val.val i j = 0) ∧
    (i = j → tl a (openCellConj u).val.val i j = 1)
  rw [tl_apply_add, openCellConj_apply]
  have h := mem_upperUnitriangular.mp u.val.property (σ (Fin.castAdd b i)) (σ (Fin.castAdd b j))
  exact ⟨fun e => h.1 ((left_lt_left j i).mpr e), fun e => h.2 (congrArg (σ ∘ Fin.castAdd b) e)⟩

private theorem rightLevi_mem (u : O) : (twoBlockLevi (openCellConj u)).2 ∈ upperUnitriangular g b := by
  intro i j
  change (j < i → br a b (openCellConj u).val.val i j = 0) ∧
    (i = j → br a b (openCellConj u).val.val i j = 1)
  rw [br_apply_add, openCellConj_apply]
  have h := mem_upperUnitriangular.mp u.val.property (σ (Fin.natAdd a i)) (σ (Fin.natAdd a j))
  exact ⟨fun e => h.1 ((right_lt_right j i).mpr e), fun e => h.2 (congrArg (σ ∘ Fin.natAdd a) e)⟩

private abbrev levi := (twoBlockLevi (g := g) (a := a) (b := b)).comp
  (openCellConj (g := g) (a := a) (b := b))

/-- Conjugation into the parabolic followed by projection onto the two diagonal blocks. -/
def openCellProjection : O →* upperUnitriangular g a × upperUnitriangular g b where
  toFun u := (⟨(levi u).1, leftLevi_mem u⟩, ⟨(levi u).2, rightLevi_mem u⟩)
  map_one' := Prod.ext (Subtype.ext (congrArg Prod.fst (map_one levi)))
    (Subtype.ext (congrArg Prod.snd (map_one levi)))
  map_mul' u v := Prod.ext (Subtype.ext (congrArg Prod.fst (map_mul levi u v)))
    (Subtype.ext (congrArg Prod.snd (map_mul levi u v)))

theorem openCellConj_eq_diagonal (u : O) :
    (openCellConj u).val = upperBlockUnit (levi u).1 0 (levi u).2 := by
  have h := (upperBlockUnit_eq_of_mem_parabolic (openCellConj u)).symm
  rw [openCellConj_rectangle_zero] at h
  exact h

private theorem openCellProjection_injective : Function.Injective (openCellProjection (g := g) (a := a) (b := b)) := by
  intro u v h
  have hL : levi u = levi v := congrArg
    (fun t : upperUnitriangular g a × upperUnitriangular g b => (t.1.val, t.2.val)) h
  have he : (openCellConj u).val = (openCellConj v).val :=
    (openCellConj_eq_diagonal u).trans
      ((congrArg (fun t : Gn g a × Gn g b => upperBlockUnit t.1 0 t.2) hL).trans
        (openCellConj_eq_diagonal v).symm)
  apply Subtype.ext
  apply Subtype.ext
  change w⁻¹ * u.val.val * w = w⁻¹ * v.val.val * w at he
  exact mul_left_cancel (mul_right_cancel he)

private theorem openCellProjection_surjective : Function.Surjective (openCellProjection (g := g) (a := a) (b := b)) := by
  rintro ⟨A, B⟩
  let p : P := ⟨upperBlockUnit A.val 0 B.val, inPar_upperBlockMatrix A.val.val 0 B.val.val⟩
  let x : Gn g (a + b) := w * p.val * w⁻¹
  have he : w⁻¹ * x * w = p.val := by dsimp only [x]; group
  have hEnt (i j : Fin (a + b)) :
      x.val (σ i) (σ j) = upperBlockMatrix A.val.val 0 B.val.val i j := by
    have h := monomialConj_apply σ (fun _ => 1) x i j
    rw [he, Units.val_one, inv_one, one_mul, mul_one] at h
    exact h.symm
  have hx : IsUniUp x.val := by
    intro i j
    obtain ⟨r, rfl⟩ := (openCellPermutation a b).surjective i
    obtain ⟨s, rfl⟩ := (openCellPermutation a b).surjective j
    rw [hEnt]
    refine Fin.addCases (fun r => ?_) (fun r => ?_) r <;>
      refine Fin.addCases (fun s => ?_) (fun s => ?_) s
    · simp only [upperBlockMatrix, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
        Matrix.fromBlocks_apply₁₁]
      have h := mem_upperUnitriangular.mp A.property r s
      exact ⟨fun e => h.1 ((left_lt_left s r).mp e), fun e =>
        h.2 (Fin.castAdd_inj.mp ((openCellPermutation a b).injective e))⟩
    · exact ⟨fun _ => by simp [upperBlockMatrix], fun e =>
        (ne_of_lt (right_lt_left r s) e.symm).elim⟩
    · exact ⟨fun _ => by simp [upperBlockMatrix], fun e =>
        (ne_of_lt (right_lt_left s r) e).elim⟩
    · simp only [upperBlockMatrix, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
        Matrix.fromBlocks_apply₂₂]
      have h := mem_upperUnitriangular.mp B.property r s
      exact ⟨fun e => h.1 ((right_lt_right s r).mp e), fun e =>
        h.2 ((Fin.natAdd_inj a).mp ((openCellPermutation a b).injective e))⟩
  let u : U := ⟨x, hx⟩
  let z : O := ⟨u, (mem_doubleCosetOverlap U P w u).mpr (he.symm ▸ p.property)⟩
  have hp : openCellConj z = p := Subtype.ext he
  have hL : levi z = (A.val, B.val) :=
    (congrArg twoBlockLevi hp).trans (twoBlockLevi_upperBlockUnit A.val 0 B.val)
  exact ⟨z, Prod.ext (Subtype.ext (congrArg Prod.fst hL)) (Subtype.ext (congrArg Prod.snd hL))⟩

/-- The open-cell overlap maps isomorphically to the two unitriangular Levi blocks. -/
def openCellOverlapEquiv : O ≃* upperUnitriangular g a × upperUnitriangular g b :=
  MulEquiv.ofBijective openCellProjection ⟨openCellProjection_injective, openCellProjection_surjective⟩

/-- In the original coordinate order, the overlap matrix has the two diagonal blocks in reverse order. -/
theorem openCellReindexedMatrix (u : O) :
    let e := finCongr (Nat.add_comm b a)
    u.val.val.val.submatrix e e =
      upperBlockMatrix (openCellProjection u).2.val.val 0 (openCellProjection u).1.val.val := by
  let e := finCongr (Nat.add_comm b a)
  let τ : Fin (b + a) ≃ Fin (a + b) :=
    finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin b) (Fin a)).trans finSumFinEquiv)
  have hL (i : Fin b) : τ (Fin.castAdd a i) = Fin.natAdd a i := by simp [τ]
  have hR (j : Fin a) : τ (Fin.natAdd b j) = Fin.castAdd b j := by simp [τ]
  have he (i : Fin (b + a)) : e i = σ (τ i) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · apply Fin.ext
      rw [hL, openCellPermutation_right]
      rfl
    · apply Fin.ext
      rw [hR, openCellPermutation_left]
      rfl
  ext i j
  change u.val.val.val (e i) (e j) =
    upperBlockMatrix (levi u).2.val 0 (levi u).1.val i j
  rw [he i, he j, ← openCellConj_apply, openCellConj_eq_diagonal]
  change upperBlockMatrix (levi u).1.val 0 (levi u).2.val (τ i) (τ j) =
    upperBlockMatrix (levi u).2.val 0 (levi u).1.val i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [upperBlockMatrix, hL, hR]

end GlobalTheory.GLq
