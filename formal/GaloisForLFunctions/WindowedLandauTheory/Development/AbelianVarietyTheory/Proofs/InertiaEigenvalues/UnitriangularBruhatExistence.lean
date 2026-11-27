import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularMonomialCosets
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularPivot
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Successive first-column pivots give a monomial representative of every
unitriangular double coset. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions.HTGeometry Matrix
open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

private def pivotIndex (p : Fin (n + 1)) : Unit ⊕ Fin n ≃ Fin (n + 1) :=
  Equiv.ofBijective (Sum.elim (fun _ : Unit => p) p.succAbove) ⟨by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (Subsingleton.elim a b)
    · exact (p.ne_succAbove b h).elim
    · exact (p.succAbove_ne a h).elim
    · exact congrArg Sum.inr (p.succAbove_right_injective h), by
    intro i
    by_cases h : i = p
    · exact ⟨.inl (), h.symm⟩
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h
      exact ⟨.inr j, hj⟩⟩

@[simp] private theorem pivotIndex_inl (p : Fin (n + 1)) (i : Unit) :
    pivotIndex p (.inl i) = p := rfl

@[simp] private theorem pivotIndex_inr (p : Fin (n + 1)) (i : Fin n) :
    pivotIndex p (.inr i) = p.succAbove i := rfl

private def pivotMatrix (c : ZMod g) (M : Mt g n) :
    Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) (ZMod g) :=
  fromBlocks (fun _ _ : Unit => c) 0 0 M

private theorem pivotMatrix_mul (c d : ZMod g) (A B : Mt g n) :
    pivotMatrix c A * pivotMatrix d B = pivotMatrix (c * d) (A * B) := by
  unfold pivotMatrix
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  ext i j
  simp [Matrix.mul_apply]

private theorem pivotMatrix_one : pivotMatrix (1 : ZMod g) (1 : Mt g n) = 1 := by
  have e : (fun _ _ : Unit => (1 : ZMod g)) = (1 : Matrix Unit Unit (ZMod g)) := by
    ext i j
    cases i
    cases j
    exact (Matrix.one_apply_eq ()).symm
  exact (congrArg (fun D => fromBlocks D 0 0 (1 : Mt g n)) e).trans Matrix.fromBlocks_one

private def pivotBlockUnit (a : Gn g n) : (Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) (ZMod g))ˣ where
  val := pivotMatrix 1 (a : Mt g n)
  inv := pivotMatrix 1 ((a⁻¹ : Gn g n) : Mt g n)
  val_inv := by rw [pivotMatrix_mul, one_mul, Units.mul_inv, pivotMatrix_one]
  inv_val := by rw [pivotMatrix_mul, one_mul, Units.inv_mul, pivotMatrix_one]

private def liftTail (p : Fin (n + 1)) (a : Gn g n) : Gn g (n + 1) :=
  Units.map (Matrix.reindexRingEquiv (ZMod g) (pivotIndex p)).toRingHom.toMonoidHom (pivotBlockUnit a)

private theorem liftTail_blocks (p : Fin (n + 1)) (a : Gn g n) :
    ((liftTail p a : Gn g (n + 1)) : Mt g (n + 1)).submatrix (pivotIndex p) (pivotIndex p) =
      pivotMatrix 1 (a : Mt g n) := by
  ext i j
  change pivotMatrix 1 (a : Mt g n)
    ((pivotIndex p).symm (pivotIndex p i)) ((pivotIndex p).symm (pivotIndex p j)) = _
  rw [(pivotIndex p).symm_apply_apply, (pivotIndex p).symm_apply_apply]

private theorem liftTail_mem (p : Fin (n + 1)) (a : upperUnitriangular g n) :
    liftTail p a.val ∈ upperUnitriangular g (n + 1) := by
  let e := pivotIndex p
  have h (i j : Unit ⊕ Fin n) :
      (liftTail p (a : Gn g n) : Mt g (n + 1)) (e i) (e j) = pivotMatrix 1 (a.val : Mt g n) i j :=
    congrArg (fun M : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) (ZMod g) => M i j) (liftTail_blocks p a.val)
  have hu : IsUniUp (a.val : Mt g n) := mem_upperUnitriangular.mp a.2
  intro x y
  obtain ⟨i, rfl⟩ := e.surjective x
  obtain ⟨j, rfl⟩ := e.surjective y
  constructor
  · intro hij
    rw [h]
    cases i with
    | inl i =>
      cases j with
      | inl j => exact (lt_irrefl p hij).elim
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j => exact (hu i j).1 ((Fin.strictMono_succAbove p).lt_iff_lt.mp hij)
  · intro hij
    obtain rfl := e.injective hij
    rw [h]
    cases i with
    | inl i => rfl
    | inr i => exact (hu i i).2 rfl

private def pivotPerm (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (pivotIndex (0 : Fin (n + 1))).symm.trans (((Equiv.refl Unit).sumCongr σ).trans (pivotIndex p))

private def pivotScale (c : (ZMod g)ˣ) (d : Fin n → (ZMod g)ˣ) : Fin (n + 1) → (ZMod g)ˣ :=
  Sum.elim (fun _ : Unit => c) d ∘ (pivotIndex (0 : Fin (n + 1))).symm

private theorem pivot_monomial_blocks (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n))
    (c : (ZMod g)ˣ) (d : Fin n → (ZMod g)ˣ) :
    (monomialUnit (pivotPerm p σ) (pivotScale c d) : Mt g (n + 1)).submatrix
        (pivotIndex p) (pivotIndex (0 : Fin (n + 1))) =
      pivotMatrix (c : ZMod g) (signedMonomialMatrix σ d) := by
  ext i j
  change (if pivotIndex p i = pivotPerm p σ (pivotIndex (0 : Fin (n + 1)) j)
    then (pivotScale c d (pivotIndex (0 : Fin (n + 1)) j) : ZMod g) else 0) = _
  have h (j : Unit ⊕ Fin n) :
      pivotPerm p σ (pivotIndex (0 : Fin (n + 1)) j) = pivotIndex p (((Equiv.refl Unit).sumCongr σ) j) := by
    unfold pivotPerm
    rw [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.trans_apply]
  have he : pivotIndex p i = pivotPerm p σ (pivotIndex (0 : Fin (n + 1)) j) ↔
      i = ((Equiv.refl Unit).sumCongr σ) j :=
    ⟨fun e => (pivotIndex p).injective (e.trans (h j)),
      fun e => (congrArg (pivotIndex p) e).trans (h j).symm⟩
  have hscale : pivotScale c d (pivotIndex (0 : Fin (n + 1)) j) = Sum.elim (fun _ : Unit => c) d j :=
    congrArg (Sum.elim (fun _ : Unit => c) d) ((pivotIndex (0 : Fin (n + 1))).symm_apply_apply j)
  refine (if_congr he rfl rfl).trans ?_
  rw [hscale]
  cases i <;> cases j <;> simp [pivotMatrix, signedMonomialMatrix]

private theorem pivot_blocks {B : Mt g (n + 1)} {p : Fin (n + 1)} {c : (ZMod g)ˣ}
    (hp : B p 0 = c) (hcol : ∀ i, i ≠ p → B i 0 = 0) (hrow : ∀ j, j ≠ 0 → B p j = 0) :
    B.submatrix (pivotIndex p) (pivotIndex (0 : Fin (n + 1))) =
      pivotMatrix (c : ZMod g) (B.submatrix p.succAbove Fin.succ) := by
  ext (i | i) (j | j)
  · exact hp
  · exact hrow j.succ (Fin.succ_ne_zero _)
  · exact hcol (p.succAbove i) (p.succAbove_ne _)
  · rfl

private theorem pivot_tail_det_ne_zero (B : Gn g (n + 1)) (p : Fin (n + 1))
    (h : ∀ i, i ≠ p → (B : Mt g (n + 1)) i 0 = 0) :
    ((B : Mt g (n + 1)).submatrix p.succAbove Fin.succ).det ≠ 0 := by
  intro hz
  apply (Matrix.isUnits_det_units B).ne_zero
  rw [Matrix.det_succ_column_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i = p
  · subst i
    rw [hz, mul_zero]
  · rw [h i hi, mul_zero, zero_mul]

/-- Upper unitriangular operations on both sides reduce any invertible
matrix to a permutation with nonzero column entries. -/
theorem exists_unitriangular_monomial (g : ℕ) [Fact g.Prime] (n : ℕ) (A : Gn g n) :
    ∃ (l r : upperUnitriangular g n) (σ : Equiv.Perm (Fin n)) (c : Fin n → (ZMod g)ˣ),
      A = (l : Gn g n) * monomialUnit σ c * r := by
  induction n with
  | zero =>
    exact ⟨1, 1, Equiv.refl _, fun i => Fin.elim0 i, Subsingleton.elim _ _⟩
  | succ n ih =>
    let U := upperUnitriangular g (n + 1)
    obtain ⟨a, b, p, v, hp, hcol, hrow⟩ := exists_unitriangular_pivot A
    let B := (a : Gn g (n + 1)) * A * b
    let D := (B : Mt g (n + 1)).submatrix p.succAbove Fin.succ
    have hD : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr
      (isUnit_iff_ne_zero.mpr (pivot_tail_det_ne_zero B p hcol))
    obtain ⟨l, r, σ, c, he⟩ := ih hD.unit
    let L : U := ⟨liftTail p l.val, liftTail_mem p l⟩
    let R : U := ⟨liftTail 0 r.val, liftTail_mem 0 r⟩
    let X := monomialUnit (pivotPerm p σ) (pivotScale v c)
    have htail : D = (l.val : Mt g n) * signedMonomialMatrix σ c * (r.val : Mt g n) :=
      hD.unit_spec.symm.trans (congrArg Units.val he)
    have hB : B = (L : Gn g (n + 1)) * X * R := by
      apply Units.ext
      apply Matrix.ext
      intro i j
      obtain ⟨i, rfl⟩ := (pivotIndex p).surjective i
      obtain ⟨j, rfl⟩ := (pivotIndex (0 : Fin (n + 1))).surjective j
      have eq : (B : Mt g (n + 1)).submatrix (pivotIndex p) (pivotIndex (0 : Fin (n + 1))) =
          (((L.val : Mt g (n + 1)) * (X : Mt g (n + 1))) * (R.val : Mt g (n + 1))).submatrix
            (pivotIndex p) (pivotIndex (0 : Fin (n + 1))) := by
        change _ = (((liftTail p l.val : Mt g (n + 1)) *
          (monomialUnit (pivotPerm p σ) (pivotScale v c) : Mt g (n + 1))) *
          (liftTail 0 r.val : Mt g (n + 1))).submatrix (pivotIndex p) (pivotIndex (0 : Fin (n + 1)))
        rw [← submatrix_mul_equiv _ _ _ (pivotIndex (0 : Fin (n + 1))) _,
          ← submatrix_mul_equiv _ _ _ (pivotIndex p) _,
          liftTail_blocks, liftTail_blocks, pivot_monomial_blocks, pivotMatrix_mul, pivotMatrix_mul,
          one_mul, mul_one, pivot_blocks hp hcol hrow]
        exact congrArg (pivotMatrix (v : ZMod g)) htail
      exact congrArg (fun M : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) (ZMod g) => M i j) eq
    refine ⟨a⁻¹ * L, R * b⁻¹, pivotPerm p σ, pivotScale v c, ?_⟩
    have e : A = (a : Gn g (n + 1))⁻¹ * B * (b : Gn g (n + 1))⁻¹ := by
      change A = (a : Gn g (n + 1))⁻¹ * ((a : Gn g (n + 1)) * A * b) * (b : Gn g (n + 1))⁻¹
      group
    exact e.trans ((congrArg (fun y => (a : Gn g (n + 1))⁻¹ * y * (b : Gn g (n + 1))⁻¹) hB).trans
      (by change _ = (a : Gn g (n + 1))⁻¹ * L.val * X * (R.val * (b : Gn g (n + 1))⁻¹)
          group))

end GlobalTheory.GLq
