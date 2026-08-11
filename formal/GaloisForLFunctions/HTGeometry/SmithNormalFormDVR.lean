import Mathlib
import GaloisForLFunctions.HTGeometry.DVRFiniteSpan
import GaloisForLFunctions.HTGeometry.DeterminantalIdeal

/-!
# Smith normal form over a discrete valuation ring

Every square matrix over a discrete valuation ring is equivalent to a diagonal matrix whose
entries form a divisibility chain.  The proof is the classical algorithm: an entry of least
valuation divides every entry, so after a row and a column swap it can be used to clear the rest of
its row and column by elementary operations, and the remaining block is handled by induction.

The bookkeeping is done with the corner extension `blockPivot`, which places a pivot in the
top-left corner and a smaller matrix in the complementary block.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-! ## Corner extensions -/

section Block

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The corner extension: a pivot in the top-left entry, a smaller matrix in the complementary
block, and zeros in the rest of the first row and column. -/
def blockPivot (π : R) (A : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of (Fin.cons (Fin.cons π fun _ => 0) fun i => Fin.cons 0 (A i))

@[simp] theorem blockPivot_zero_zero (π : R) (A : Matrix (Fin m) (Fin m) R) :
    blockPivot π A 0 0 = π := rfl

@[simp] theorem blockPivot_zero_succ (π : R) (A : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    blockPivot π A 0 j.succ = 0 := rfl

@[simp] theorem blockPivot_succ_zero (π : R) (A : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    blockPivot π A i.succ 0 = 0 := rfl

@[simp] theorem blockPivot_succ_succ (π : R) (A : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    blockPivot π A i.succ j.succ = A i j := rfl

/-- The corner extension by the unit pivot. -/
abbrev blockOne (A : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  blockPivot 1 A

theorem submatrix_blockPivot (π : R) (A : Matrix (Fin m) (Fin m) R) :
    (blockPivot π A).submatrix Fin.succ Fin.succ = A := by
  ext i j
  rfl

/-- The determinant of a corner extension. -/
theorem det_blockPivot (π : R) (A : Matrix (Fin m) (Fin m) R) :
    (blockPivot π A).det = π * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hzero : ∀ j : Fin m, (-1 : R) ^ ((j.succ : Fin (m + 1)) : ℕ) * blockPivot π A 0 j.succ
      * ((blockPivot π A).submatrix Fin.succ (Fin.succAbove j.succ)).det = 0 := by
    intro j
    rw [blockPivot_zero_succ, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero, add_zero,
    Fin.succAbove_zero, submatrix_blockPivot]
  simp

theorem det_blockOne (A : Matrix (Fin m) (Fin m) R) : (blockOne A).det = A.det := by
  rw [det_blockPivot, one_mul]

theorem blockOne_mul_blockPivot (U : Matrix (Fin m) (Fin m) R) (π : R)
    (B : Matrix (Fin m) (Fin m) R) :
    blockOne U * blockPivot π B = blockPivot π (U * B) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp
    · intro b
      simp
  · intro a
    refine Fin.cases ?_ ?_ j
    · simp
    · intro b
      simp [Matrix.mul_apply]

theorem blockPivot_mul_blockOne (π : R) (B : Matrix (Fin m) (Fin m) R)
    (V : Matrix (Fin m) (Fin m) R) :
    blockPivot π B * blockOne V = blockPivot π (B * V) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp
    · intro b
      simp
  · intro a
    refine Fin.cases ?_ ?_ j
    · simp
    · intro b
      simp [Matrix.mul_apply]

theorem blockPivot_diagonal (π : R) (d : Fin m → R) :
    blockPivot π (Matrix.diagonal d) = Matrix.diagonal (Fin.cons π d) := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · rw [blockPivot_zero_zero, Matrix.diagonal_apply_eq]
      rfl
    · intro b
      rw [blockPivot_zero_succ, Matrix.diagonal_apply_ne _ (Ne.symm (Fin.succ_ne_zero b))]
  · intro a
    refine Fin.cases ?_ ?_ j
    · rw [blockPivot_succ_zero, Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero a)]
    · intro b
      rw [blockPivot_succ_succ]
      by_cases hab : a = b
      · subst hab
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        rfl
      · rw [Matrix.diagonal_apply_ne _ hab,
          Matrix.diagonal_apply_ne _ fun h => hab (Fin.succ_injective m h)]

end Block


/-! ## Elementary clearing operations -/

section Clearing

variable {R : Type*} [CommRing R] {m : ℕ}

/-- A matrix whose first row vanishes off the corner has the determinant of its lower-right
block, scaled by the corner. -/
theorem det_of_firstRow (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (hj : ∀ j : Fin m, A 0 j.succ = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hzero : ∀ j : Fin m, (-1 : R) ^ ((j.succ : Fin (m + 1)) : ℕ) * A 0 j.succ
      * ((A).submatrix Fin.succ (Fin.succAbove j.succ)).det = 0 := by
    intro j
    rw [hj j, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero, add_zero,
    Fin.succAbove_zero]
  simp

/-- The elementary matrix subtracting multiples of the first row from the remaining rows. -/
def clearCol (c : Fin m → R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of (Fin.cons (Fin.cons 1 fun _ => 0)
    fun i => Fin.cons (-(c i)) fun j => (1 : Matrix (Fin m) (Fin m) R) i j)

@[simp] theorem clearCol_zero_zero (c : Fin m → R) : clearCol c 0 0 = 1 := rfl
@[simp] theorem clearCol_zero_succ (c : Fin m → R) (j : Fin m) : clearCol c 0 j.succ = 0 := rfl
@[simp] theorem clearCol_succ_zero (c : Fin m → R) (i : Fin m) : clearCol c i.succ 0 = -(c i) := rfl
@[simp] theorem clearCol_succ_succ (c : Fin m → R) (i j : Fin m) :
    clearCol c i.succ j.succ = (1 : Matrix (Fin m) (Fin m) R) i j := rfl

theorem det_clearCol (c : Fin m → R) : (clearCol c).det = 1 := by
  have hsub : (clearCol c).submatrix Fin.succ Fin.succ = (1 : Matrix (Fin m) (Fin m) R) := by
    ext i j
    rfl
  rw [det_of_firstRow _ (fun j => clearCol_zero_succ c j), hsub, Matrix.det_one,
    clearCol_zero_zero, mul_one]

theorem clearCol_mul_zero (c : Fin m → R) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (j : Fin (m + 1)) : (clearCol c * M) 0 j = M 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ, clearCol_zero_zero, one_mul]
  have : ∀ b : Fin m, clearCol c 0 b.succ * M b.succ j = 0 := by
    intro b
    rw [clearCol_zero_succ, zero_mul]
  rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_const_zero, add_zero]

theorem clearCol_mul_succ (c : Fin m → R) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (i : Fin m) (j : Fin (m + 1)) :
    (clearCol c * M) i.succ j = M i.succ j - c i * M 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ, clearCol_succ_zero]
  have hsum : ∑ b : Fin m, clearCol c i.succ b.succ * M b.succ j = M i.succ j := by
    have : ∀ b : Fin m, clearCol c i.succ b.succ * M b.succ j
        = if i = b then M b.succ j else 0 := by
      intro b
      rw [clearCol_succ_succ, Matrix.one_apply]
      by_cases h : i = b
      · rw [if_pos h, if_pos h, one_mul]
      · rw [if_neg h, if_neg h, zero_mul]
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_ite_eq]
    simp
  rw [hsum]
  ring

/-- The elementary matrix subtracting multiples of the first column from the remaining columns. -/
def clearRow (c : Fin m → R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R := (clearCol c)ᵀ

theorem det_clearRow (c : Fin m → R) : (clearRow c).det = 1 := by
  rw [clearRow, Matrix.det_transpose, det_clearCol]

theorem mul_clearRow_zero (c : Fin m → R) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (i : Fin (m + 1)) : (M * clearRow c) i 0 = M i 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  have hz : (clearRow c) 0 0 = 1 := rfl
  rw [hz, mul_one]
  have : ∀ b : Fin m, M i b.succ * (clearRow c) b.succ 0 = 0 := by
    intro b
    have : (clearRow c) b.succ 0 = 0 := rfl
    rw [this, mul_zero]
  rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_const_zero, add_zero]

theorem mul_clearRow_succ (c : Fin m → R) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (i : Fin (m + 1)) (j : Fin m) :
    (M * clearRow c) i j.succ = M i j.succ - c j * M i 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  have h0 : (clearRow c) 0 j.succ = -(c j) := rfl
  rw [h0]
  have hsum : ∑ b : Fin m, M i b.succ * (clearRow c) b.succ j.succ = M i j.succ := by
    have : ∀ b : Fin m, M i b.succ * (clearRow c) b.succ j.succ
        = if j = b then M i b.succ else 0 := by
      intro b
      have hb : (clearRow c) b.succ j.succ = (1 : Matrix (Fin m) (Fin m) R) j b := rfl
      rw [hb, Matrix.one_apply]
      by_cases h : j = b
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_ite_eq]
    simp
  rw [hsum]
  ring

/-- A matrix with vanishing first row and column off the corner is a corner extension. -/
theorem eq_blockPivot (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (h1 : ∀ i : Fin m, A i.succ 0 = 0) (h2 : ∀ j : Fin m, A 0 j.succ = 0) :
    A = blockPivot (A 0 0) (A.submatrix Fin.succ Fin.succ) := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · rfl
    · intro b
      rw [h2 b, blockPivot_zero_succ]
  · intro a
    refine Fin.cases ?_ ?_ j
    · rw [h1 a, blockPivot_succ_zero]
    · intro b
      rfl

theorem dvd_entries_mul_left {ι : Type*} [Fintype ι] [DecidableEq ι] {π : R}
    (A M : Matrix ι ι R) (h : ∀ i j, π ∣ M i j) (i j : ι) : π ∣ (A * M) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (h k j) _

theorem dvd_entries_mul_right {ι : Type*} [Fintype ι] [DecidableEq ι] {π : R}
    (M A : Matrix ι ι R) (h : ∀ i j, π ∣ M i j) (i j : ι) : π ∣ (M * A) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_right (h i k) _

end Clearing


/-! ## Smith normal form -/

section Smith

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem isUnit_intCast_units {u : ℤˣ} : IsUnit (((u : ℤ) : R)) := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h]
  · simp
  · simp

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem isUnit_det_rowPerm {n : ℕ} (e : Equiv.Perm (Fin n)) :
    IsUnit ((1 : Matrix (Fin n) (Fin n) R).submatrix e id).det := by
  rw [Matrix.det_permute, Matrix.det_one, mul_one]
  exact isUnit_intCast_units

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem isUnit_det_colPerm {n : ℕ} (f : Equiv.Perm (Fin n)) :
    IsUnit ((1 : Matrix (Fin n) (Fin n) R).submatrix id f).det := by
  rw [Matrix.det_permute', Matrix.det_one, mul_one]
  exact isUnit_intCast_units

/-- **Smith normal form over a discrete valuation ring.**  Every square matrix is equivalent to a
diagonal matrix whose entries form a divisibility chain. -/
theorem exists_smithNormalForm :
    ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) R),
      ∃ (U V : Matrix (Fin n) (Fin n) R) (d : Fin n → R),
        IsUnit U.det ∧ IsUnit V.det ∧ U * M * V = Matrix.diagonal d ∧
          ∀ i j : Fin n, i ≤ j → d i ∣ d j := by
  intro n
  induction n with
  | zero =>
    intro M
    exact ⟨1, 1, Fin.elim0, by simp, by simp, Subsingleton.elim _ _, fun i => Fin.elim0 i⟩
  | succ m ih =>
    intro M
    classical
    obtain ⟨p, -, hp⟩ := Finset.exists_min_image
      (Finset.univ : Finset (Fin (m + 1) × Fin (m + 1)))
      (fun q => addVal R (M q.1 q.2)) ⟨(0, 0), Finset.mem_univ _⟩
    have hdvd : ∀ i j, M p.1 p.2 ∣ M i j := fun i j =>
      addVal_le_iff_dvd.mp (hp (i, j) (Finset.mem_univ _))
    set e : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 p.1 with he
    set f : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 p.2 with hf
    set P : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix e id with hP
    set Q : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix id f with hQ
    set M₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) R := M.submatrix e f with hM₁def
    have hM₁ : P * M * Q = M₁ := by
      have h1 : P * M = M.submatrix e id := by
        ext i j
        simp [hP, Matrix.mul_apply, Matrix.one_apply]
      rw [h1]
      ext i j
      simp [hQ, hM₁def, Matrix.mul_apply, Matrix.one_apply]
    have hpivot : M₁ 0 0 = M p.1 p.2 := by
      show M (e 0) (f 0) = M p.1 p.2
      rw [he, hf, Equiv.swap_apply_left, Equiv.swap_apply_left]
    have hdvd₁ : ∀ i j, M₁ 0 0 ∣ M₁ i j := by
      intro i j
      rw [hpivot]
      exact hdvd _ _
    -- clear the first column
    set c : Fin m → R := fun i => (hdvd₁ i.succ 0).choose with hc
    have hcspec : ∀ i : Fin m, M₁ i.succ 0 = M₁ 0 0 * c i := fun i => (hdvd₁ i.succ 0).choose_spec
    set M₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) R := clearCol c * M₁ with hM₂def
    have hM₂zero : ∀ j, M₂ 0 j = M₁ 0 j := fun j => clearCol_mul_zero c M₁ j
    have hM₂succ : ∀ (i : Fin m) (j), M₂ i.succ j = M₁ i.succ j - c i * M₁ 0 j :=
      fun i j => clearCol_mul_succ c M₁ i j
    have hM₂col : ∀ i : Fin m, M₂ i.succ 0 = 0 := by
      intro i
      rw [hM₂succ, hcspec i]
      ring
    have hdvd₂ : ∀ i j, M₁ 0 0 ∣ M₂ i j := by
      intro i j
      rw [hM₂def]
      exact dvd_entries_mul_left _ _ hdvd₁ i j
    -- clear the first row
    have hdvd₂row : ∀ j : Fin m, M₂ 0 0 ∣ M₂ 0 j.succ := by
      intro j
      rw [hM₂zero, hM₂zero]
      exact hdvd₁ 0 j.succ
    set c' : Fin m → R := fun j => (hdvd₂row j).choose with hc'
    have hc'spec : ∀ j : Fin m, M₂ 0 j.succ = M₂ 0 0 * c' j := fun j => (hdvd₂row j).choose_spec
    set M₃ : Matrix (Fin (m + 1)) (Fin (m + 1)) R := M₂ * clearRow c' with hM₃def
    have hM₃col : ∀ i, M₃ i 0 = M₂ i 0 := fun i => mul_clearRow_zero c' M₂ i
    have hM₃succ : ∀ (i) (j : Fin m), M₃ i j.succ = M₂ i j.succ - c' j * M₂ i 0 :=
      fun i j => mul_clearRow_succ c' M₂ i j
    have hM₃row : ∀ j : Fin m, M₃ 0 j.succ = 0 := by
      intro j
      rw [hM₃succ, hc'spec j]
      ring
    have hM₃colzero : ∀ i : Fin m, M₃ i.succ 0 = 0 := by
      intro i
      rw [hM₃col, hM₂col]
    have hM₃corner : M₃ 0 0 = M₁ 0 0 := by
      rw [hM₃col, hM₂zero]
    have hdvd₃ : ∀ i j, M₁ 0 0 ∣ M₃ i j := by
      intro i j
      rw [hM₃def]
      exact dvd_entries_mul_right _ _ hdvd₂ i j
    -- the corner extension
    set B : Matrix (Fin m) (Fin m) R := M₃.submatrix Fin.succ Fin.succ with hBdef
    have hblock : M₃ = blockPivot (M₁ 0 0) B := by
      rw [← hM₃corner]
      exact eq_blockPivot M₃ hM₃colzero hM₃row
    have hdvdB : ∀ i j, M₁ 0 0 ∣ B i j := fun i j => hdvd₃ i.succ j.succ
    obtain ⟨UB, VB, dB, hUB, hVB, hBeq, hBchain⟩ := ih B
    have hdvddB : ∀ b : Fin m, M₁ 0 0 ∣ dB b := by
      intro b
      have h1 : dB b = (UB * B * VB) b b := by
        rw [hBeq, Matrix.diagonal_apply_eq]
      rw [h1]
      exact dvd_entries_mul_right _ _ (fun i j => dvd_entries_mul_left _ _ hdvdB i j) b b
    refine ⟨blockOne UB * clearCol c * P, Q * clearRow c' * blockOne VB,
      Fin.cons (M₁ 0 0) dB, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne, det_clearCol, mul_one]
      exact hUB.mul (isUnit_det_rowPerm e)
    · rw [Matrix.det_mul, Matrix.det_mul, det_clearRow, det_blockOne, mul_one]
      exact (isUnit_det_colPerm f).mul hVB
    · have hstep : blockOne UB * M₃ * blockOne VB = Matrix.diagonal (Fin.cons (M₁ 0 0) dB) := by
        rw [hblock, blockOne_mul_blockPivot, blockPivot_mul_blockOne, hBeq, blockPivot_diagonal]
      rw [← hstep, hM₃def, hM₂def, ← hM₁]
      simp only [Matrix.mul_assoc]
    · intro i j hij
      rcases i.eq_zero_or_eq_succ with rfl | ⟨a, rfl⟩
      · rcases j.eq_zero_or_eq_succ with rfl | ⟨b, rfl⟩
        · rw [Fin.cons_zero]
        · rw [Fin.cons_zero, Fin.cons_succ]
          exact hdvddB b
      · rcases j.eq_zero_or_eq_succ with rfl | ⟨b, rfl⟩
        · exact absurd (le_antisymm hij (Fin.zero_le _)) (Fin.succ_ne_zero a)
        · rw [Fin.cons_succ, Fin.cons_succ]
          exact hBchain a b (Fin.succ_le_succ_iff.mp hij)

end Smith


/-! ## Determinantal ideals of a divisibility chain -/

section DiagonalIdeal

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The product of the first `k` entries of a divisibility chain divides the product along any
injective selection of `k` entries. -/
theorem prod_castLE_dvd_prod {N : ℕ} (d : Fin N → R)
    (hchain : ∀ i j : Fin N, i ≤ j → d i ∣ d j) {k : ℕ} (hk : k ≤ N) {I : Fin k → Fin N}
    (hI : Function.Injective I) :
    (∏ α : Fin k, d (Fin.castLE hk α)) ∣ ∏ α : Fin k, d (I α) := by
  classical
  have hJ : StrictMono (I ∘ Tuple.sort I) :=
    (Tuple.monotone_sort I).strictMono_of_injective (hI.comp (Equiv.injective _))
  have hprod : ∏ α : Fin k, d (I α) = ∏ α : Fin k, d ((I ∘ Tuple.sort I) α) :=
    (Equiv.prod_comp (Tuple.sort I) fun α => d (I α)).symm
  rw [hprod]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun α _ => hchain _ _ ?_
  rw [Fin.le_def]
  simpa using val_le_val_of_strictMono hJ α

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **The determinantal ideals of a divisibility chain.**  The `k`-th determinantal ideal of a
diagonal matrix whose entries form a divisibility chain is generated by the product of the first
`k` entries. -/
theorem detIdeal_diagonal_chain {N : ℕ} (d : Fin N → R)
    (hchain : ∀ i j : Fin N, i ≤ j → d i ∣ d j) {k : ℕ} (hk : k ≤ N) :
    detIdeal (Matrix.diagonal d) k = Ideal.span {∏ α : Fin k, d (Fin.castLE hk α)} := by
  classical
  refine le_antisymm (detIdeal_le fun I m => ?_) ?_
  · rw [Ideal.mem_span_singleton]
    by_cases hI : Function.Injective I
    · by_cases hm : Function.Injective m
      · rw [Matrix.det_apply']
        refine Finset.dvd_sum fun σ _ => Dvd.dvd.mul_left ?_ _
        by_cases hall : ∀ α, I (σ α) = m α
        · have hent : ∀ α : Fin k,
              (Matrix.diagonal d).submatrix I m (σ α) α = d (I (σ α)) := by
            intro α
            rw [Matrix.submatrix_apply, ← hall α, Matrix.diagonal_apply_eq]
          rw [Finset.prod_congr rfl fun α _ => hent α]
          exact prod_castLE_dvd_prod d hchain hk (hI.comp (Equiv.injective σ))
        · push Not at hall
          obtain ⟨α, hα⟩ := hall
          have hz : ∏ β : Fin k, (Matrix.diagonal d).submatrix I m (σ β) β = 0 := by
            refine Finset.prod_eq_zero (Finset.mem_univ α) ?_
            rw [Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ hα]
          rw [hz]
          exact dvd_zero _
      · obtain ⟨a, b, hab, hne⟩ : ∃ a b, m a = m b ∧ a ≠ b := by
          by_contra hcon
          push Not at hcon
          exact hm fun u v huv => hcon u v huv
        rw [Matrix.det_zero_of_column_eq hne fun γ => by
          rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hab]]
        exact dvd_zero _
    · obtain ⟨a, b, hab, hne⟩ : ∃ a b, I a = I b ∧ a ≠ b := by
        by_contra hcon
        push Not at hcon
        exact hI fun u v huv => hcon u v huv
      rw [Matrix.det_zero_of_row_eq hne (by
        funext γ
        rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hab])]
      exact dvd_zero _
  · rw [Ideal.span_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hsub : (Matrix.diagonal d).submatrix (Fin.castLE hk) (Fin.castLE hk)
        = Matrix.diagonal fun α => d (Fin.castLE hk α) := by
      ext α β
      rw [Matrix.submatrix_apply]
      by_cases h : α = β
      · subst h
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ fun hcon => h (Fin.castLE_injective hk hcon),
          Matrix.diagonal_apply_ne _ h]
    have hmem := minor_mem_detIdeal (Matrix.diagonal d) (Fin.castLE hk) (Fin.castLE hk)
    rwa [hsub, Matrix.det_diagonal] at hmem

/-- **The determinantal divisors of any square matrix over a discrete valuation ring.**  There is a
divisibility chain `d` such that the `k`-th determinantal ideal is generated by the product of its
first `k` entries; `d` is the diagonal of a Smith normal form. -/
theorem exists_smith_detIdeal {N : ℕ} (M : Matrix (Fin N) (Fin N) R) :
    ∃ d : Fin N → R, (∀ i j : Fin N, i ≤ j → d i ∣ d j) ∧
      ∀ (k : ℕ) (hk : k ≤ N),
        detIdeal M k = Ideal.span {∏ α : Fin k, d (Fin.castLE hk α)} := by
  obtain ⟨U, V, d, hU, hV, heq, hchain⟩ := exists_smithNormalForm M
  refine ⟨d, hchain, fun k hk => ?_⟩
  rw [← detIdeal_equiv hU hV M k, heq]
  exact detIdeal_diagonal_chain d hchain hk

end DiagonalIdeal


/-! ## The cokernel barcode -/

section Cokernel

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The range of a diagonal matrix is the product of the principal ideals it generates. -/
theorem range_diagonal_mulVecLin {N : ℕ} (d : Fin N → R) :
    LinearMap.range (Matrix.diagonal d).mulVecLin
      = Submodule.pi Set.univ fun i => (Ideal.span {d i} : Submodule R R) := by
  classical
  ext w
  constructor
  · rintro ⟨v, rfl⟩ i -
    refine Ideal.mem_span_singleton.mpr ⟨v i, ?_⟩
    show (Matrix.diagonal d).mulVec v i = d i * v i
    rw [Matrix.mulVec_diagonal]
  · intro hw
    have hdvd : ∀ i, d i ∣ w i := fun i =>
      Ideal.mem_span_singleton.mp (hw i (Set.mem_univ i))
    refine ⟨fun i => (hdvd i).choose, ?_⟩
    funext i
    show (Matrix.diagonal d).mulVec (fun i => (hdvd i).choose) i = w i
    rw [Matrix.mulVec_diagonal]
    exact ((hdvd i).choose_spec).symm

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem range_mulVecLin_eq_top {N : ℕ} {U : Matrix (Fin N) (Fin N) R} (hU : IsUnit U.det) :
    LinearMap.range U.mulVecLin = ⊤ := by
  classical
  rw [LinearMap.range_eq_top]
  intro w
  refine ⟨U⁻¹.mulVec w, ?_⟩
  show U.mulVec (U⁻¹.mulVec w) = w
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv U hU, Matrix.one_mulVec]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- A matrix equivalent to a diagonal matrix has the corresponding product cokernel. -/
theorem cokernel_equiv_pi_of_diagonal {N : ℕ} {M U V : Matrix (Fin N) (Fin N) R} {d : Fin N → R}
    (hU : IsUnit U.det) (hV : IsUnit V.det) (heq : U * M * V = Matrix.diagonal d) :
    Nonempty (((Fin N → R) ⧸ LinearMap.range M.mulVecLin)
      ≃ₗ[R] ∀ i : Fin N, R ⧸ (Ideal.span {d i} : Submodule R R)) := by
  classical
  haveI : Invertible U := Matrix.invertibleOfIsUnitDet U hU
  have hrangeV : LinearMap.range V.mulVecLin = ⊤ := range_mulVecLin_eq_top hV
  have hmap : Submodule.map (Matrix.toLinearEquiv' U ‹Invertible U› :
        (Fin N → R) →ₗ[R] (Fin N → R)) (LinearMap.range M.mulVecLin)
      = LinearMap.range (Matrix.diagonal d).mulVecLin := by
    rw [← heq, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.range_comp, hrangeV,
      Submodule.map_top, LinearMap.range_comp]
    rfl
  exact ⟨(Submodule.Quotient.equiv _ _ (Matrix.toLinearEquiv' U ‹Invertible U›) hmap).trans
    ((range_diagonal_mulVecLin d) ▸ Submodule.quotientPi fun i => (Ideal.span {d i} :
      Submodule R R))⟩

/-- **The observer barcode.**  The cokernel of a square matrix over a discrete valuation ring is
the product of the cyclic quotients by its invariant factors, and those invariant factors compute
every determinantal ideal. -/
theorem exists_cokernel_equiv_pi {N : ℕ} (M : Matrix (Fin N) (Fin N) R) :
    ∃ d : Fin N → R, (∀ i j : Fin N, i ≤ j → d i ∣ d j) ∧
      (∀ (k : ℕ) (hk : k ≤ N), detIdeal M k = Ideal.span {∏ α : Fin k, d (Fin.castLE hk α)}) ∧
      Nonempty (((Fin N → R) ⧸ LinearMap.range M.mulVecLin)
        ≃ₗ[R] ∀ i : Fin N, R ⧸ (Ideal.span {d i} : Submodule R R)) := by
  classical
  obtain ⟨U, V, d, hU, hV, heq, hchain⟩ := exists_smithNormalForm M
  refine ⟨d, hchain, fun k hk => ?_, ?_⟩
  · rw [← detIdeal_equiv hU hV M k, heq]
    exact detIdeal_diagonal_chain d hchain hk
  · exact cokernel_equiv_pi_of_diagonal hU hV heq

end Cokernel

end GaloisForLFunctions.HTGeometry
