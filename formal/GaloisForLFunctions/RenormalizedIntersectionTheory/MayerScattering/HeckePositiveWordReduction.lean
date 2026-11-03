import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPositiveMatrixCoding
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.TheHeckeConesTileTheQuadrant

/-!
# Positive-word normal forms for Hecke matrices

Euclidean row subtraction reduces every nonnegative matrix of positive determinant
to a unique Hecke basis. Left and right reduction provide the finite word partitions
needed to transport the Lewis equation through actual Hecke cones.
-/

set_option autoImplicit false
open Matrix
open GaloisForLFunctions RenormalizedIntersectionTheory MayerCoding

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering


/-- Positive determinant without truncated subtraction in the natural entries. -/
def HasHeckeDeterminant (n : ℕ) (A : NatMatrix) : Prop :=
  A 0 0 * A 1 1 = A 0 1 * A 1 0 + n

/-- Terminal rows for positive-word reduction are precisely the Hecke cross inequalities. -/
def IsHeckeTerminal (A : NatMatrix) : Prop := A 1 0 < A 0 0 ∧ A 0 1 < A 1 1

/-- The sum of entries decreases strictly under a permitted Euclidean subtraction. -/
def heckeMatrixSize (A : NatMatrix) : ℕ := A 0 0 + A 0 1 + A 1 0 + A 1 1

private theorem positive_generator_true_mul (A : NatMatrix) :
    generator true * A = !![A 0 0 + A 1 0, A 0 1 + A 1 1; A 1 0, A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [generator, Matrix.mul_apply, Fin.sum_univ_two]

private theorem positive_generator_false_mul (A : NatMatrix) :
    generator false * A = !![A 0 0, A 0 1; A 0 0 + A 1 0, A 0 1 + A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [generator, Matrix.mul_apply, Fin.sum_univ_two]

private theorem hecke_diagonal_pos {n : ℕ} (hn : 0 < n) {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) : 0 < A 0 0 ∧ 0 < A 1 1 := by
  dsimp only [HasHeckeDeterminant] at hA
  constructor
  · by_contra h
    have hz : A 0 0 = 0 := by omega
    rw [hz, zero_mul] at hA
    omega
  · by_contra h
    have hz : A 1 1 = 0 := by omega
    rw [hz, mul_zero] at hA
    omega

private theorem hecke_rows_comparable_or_terminal {n : ℕ} (hn : 0 < n) {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) :
    (A 0 0 ≤ A 1 0 ∧ A 0 1 ≤ A 1 1) ∨
      (A 1 0 ≤ A 0 0 ∧ A 1 1 ≤ A 0 1) ∨ IsHeckeTerminal A := by
  dsimp only [HasHeckeDeterminant] at hA
  by_cases hac : A 0 0 ≤ A 1 0
  · left
    refine ⟨hac, ?_⟩
    by_contra hbd
    have hm := Nat.mul_le_mul hac (le_of_lt (lt_of_not_ge hbd))
    nlinarith only [hm, hA, hn]
  · by_cases hdb : A 1 1 ≤ A 0 1
    · exact Or.inr (Or.inl ⟨by omega, hdb⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

/-- A positive generator preserves every determinant, not just determinant one. -/
theorem hasHeckeDeterminant_generator_mul {n : ℕ} {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) (b : Bool) : HasHeckeDeterminant n (generator b * A) := by
  dsimp only [HasHeckeDeterminant] at hA
  cases b
  · rw [positive_generator_false_mul]
    change A 0 0 * (A 0 1 + A 1 1) = A 0 1 * (A 0 0 + A 1 0) + n
    nlinarith only [hA]
  · rw [positive_generator_true_mul]
    change (A 0 0 + A 1 0) * A 1 1 = (A 0 1 + A 1 1) * A 1 0 + n
    nlinarith only [hA]

/-- Positive words preserve the actual determinant of the terminal basis. -/
theorem hasHeckeDeterminant_word_mul {n : ℕ} {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) (u : List Bool) : HasHeckeDeterminant n (matrixWord u * A) := by
  induction u with
  | nil => simpa only [matrixWord, one_mul] using hA
  | cons b u ih =>
      rw [matrixWord, mul_assoc]
      exact hasHeckeDeterminant_generator_mul ih b

/-- Every nonnegative matrix of positive determinant reduces to a Hecke basis by a
finite word of Euclidean row additions. -/
theorem heckeWordNormalForm_exists {n : ℕ} (hn : 0 < n) (A : NatMatrix)
    (hA : HasHeckeDeterminant n A) :
    ∃ u : List Bool, ∃ B : NatMatrix,
      HasHeckeDeterminant n B ∧ IsHeckeTerminal B ∧ matrixWord u * B = A := by
  generalize hm : heckeMatrixSize A = m
  induction m using Nat.strong_induction_on generalizing A with
  | h m ih =>
      have hp := hecke_diagonal_pos hn hA
      rcases hecke_rows_comparable_or_terminal hn hA with hr | hr | hterm
      · let C : NatMatrix := !![A 0 0, A 0 1; A 1 0 - A 0 0, A 1 1 - A 0 1]
        have hc : (A 1 0 - A 0 0) + A 0 0 = A 1 0 := Nat.sub_add_cancel hr.1
        have hd : (A 1 1 - A 0 1) + A 0 1 = A 1 1 := Nat.sub_add_cancel hr.2
        have hC : HasHeckeDeterminant n C := by
          change A 0 0 * (A 1 1 - A 0 1) = A 0 1 * (A 1 0 - A 0 0) + n
          dsimp only [HasHeckeDeterminant] at hA
          nlinarith only [hA, hc, hd]
        have hsize : heckeMatrixSize C < m := by
          dsimp [heckeMatrixSize, C] at hm ⊢
          omega
        obtain ⟨u, B, hB, hBt, hu⟩ := ih _ hsize C hC rfl
        refine ⟨false :: u, B, hB, hBt, ?_⟩
        rw [matrixWord, mul_assoc, hu, positive_generator_false_mul]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [C, hr.1, hr.2]
      · let C : NatMatrix := !![A 0 0 - A 1 0, A 0 1 - A 1 1; A 1 0, A 1 1]
        have ha : (A 0 0 - A 1 0) + A 1 0 = A 0 0 := Nat.sub_add_cancel hr.1
        have hb : (A 0 1 - A 1 1) + A 1 1 = A 0 1 := Nat.sub_add_cancel hr.2
        have hC : HasHeckeDeterminant n C := by
          change (A 0 0 - A 1 0) * A 1 1 = (A 0 1 - A 1 1) * A 1 0 + n
          dsimp only [HasHeckeDeterminant] at hA
          nlinarith only [hA, ha, hb]
        have hsize : heckeMatrixSize C < m := by
          dsimp [heckeMatrixSize, C] at hm ⊢
          omega
        obtain ⟨u, B, hB, hBt, hu⟩ := ih _ hsize C hC rfl
        refine ⟨true :: u, B, hB, hBt, ?_⟩
        rw [matrixWord, mul_assoc, hu, positive_generator_true_mul]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [C, ha, hb]
      · exact ⟨[], A, hA, hterm, by simp only [matrixWord, one_mul]⟩

#print axioms heckeWordNormalForm_exists


private theorem positive_generator_left_cancel (b : Bool) {A B : NatMatrix}
    (h : generator b * A = generator b * B) : A = B := by
  have h00 := congrArg (fun M : NatMatrix => M 0 0) h
  have h01 := congrArg (fun M : NatMatrix => M 0 1) h
  have h10 := congrArg (fun M : NatMatrix => M 1 0) h
  have h11 := congrArg (fun M : NatMatrix => M 1 1) h
  cases b
  · rw [positive_generator_false_mul, positive_generator_false_mul] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp at * <;> omega
  · rw [positive_generator_true_mul, positive_generator_true_mul] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp at * <;> omega

private theorem hecke_terminal_ne_generator {B : NatMatrix} (hB : IsHeckeTerminal B)
    (b : Bool) (A : NatMatrix) : B ≠ generator b * A := by
  intro he
  rcases hB with ⟨hca, hbd⟩
  cases b
  · rw [he, positive_generator_false_mul] at hca
    dsimp at hca
    omega
  · rw [he, positive_generator_true_mul] at hbd
    dsimp at hbd
    omega

private theorem hecke_opposite_generators_ne {n : ℕ} (hn : 0 < n)
    {A : NatMatrix} (hA : HasHeckeDeterminant n A) (B : NatMatrix) :
    generator true * A ≠ generator false * B := by
  intro he
  have h00 := congrArg (fun M : NatMatrix => M 0 0) he
  have h10 := congrArg (fun M : NatMatrix => M 1 0) he
  rw [positive_generator_true_mul, positive_generator_false_mul] at h00 h10
  dsimp at h00 h10
  have hp := (hecke_diagonal_pos hn hA).1
  omega

/-- The terminal basis and the full positive word are both uniquely determined. -/
theorem heckeWordNormalForm_unique {n : ℕ} (hn : 0 < n) {A B : NatMatrix}
    (hA : HasHeckeDeterminant n A) (hB : HasHeckeDeterminant n B)
    (htA : IsHeckeTerminal A) (htB : IsHeckeTerminal B)
    (u v : List Bool) (he : matrixWord u * A = matrixWord v * B) : u = v ∧ A = B := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => simpa only [matrixWord, one_mul, true_and] using he
      | cons b v =>
          simp only [matrixWord, one_mul, mul_assoc] at he
          exact False.elim (hecke_terminal_ne_generator htA b _ he)
  | cons b u ih =>
      cases v with
      | nil =>
          simp only [matrixWord, one_mul, mul_assoc] at he
          exact False.elim (hecke_terminal_ne_generator htB b _ he.symm)
      | cons c v =>
          simp only [matrixWord, mul_assoc] at he
          by_cases hbc : b = c
          · subst c
            obtain ⟨hu, hAB⟩ := ih v (positive_generator_left_cancel b he)
            exact ⟨congrArg (List.cons b) hu, hAB⟩
          · cases b <;> cases c
            · exact False.elim (hbc rfl)
            · exact False.elim (hecke_opposite_generators_ne hn
                (hasHeckeDeterminant_word_mul hB v) _ he.symm)
            · exact False.elim (hecke_opposite_generators_ne hn
                (hasHeckeDeterminant_word_mul hA u) _ he)
            · exact False.elim (hbc rfl)

/-- Each positive letter strictly increases the entry sum. -/
theorem heckeMatrixSize_generator_growth {n : ℕ} (hn : 0 < n) {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) (b : Bool) :
    heckeMatrixSize A + 1 ≤ heckeMatrixSize (generator b * A) := by
  have hp := hecke_diagonal_pos hn hA
  cases b
  · rw [positive_generator_false_mul]
    dsimp [heckeMatrixSize]
    omega
  · rw [positive_generator_true_mul]
    dsimp [heckeMatrixSize]
    omega

/-- Word length is controlled by growth of the actual matrix entries. -/
theorem heckeMatrixSize_word_growth {n : ℕ} (hn : 0 < n) {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) (u : List Bool) :
    u.length + heckeMatrixSize A ≤ heckeMatrixSize (matrixWord u * A) := by
  induction u with
  | nil => simp only [List.length_nil, zero_add, matrixWord, one_mul, le_refl]
  | cons b u ih =>
      have hg := heckeMatrixSize_generator_growth hn (hasHeckeDeterminant_word_mul hA u) b
      simp only [List.length_cons, matrixWord, mul_assoc]
      omega

/-- Natural terminal matrices are literal integral Hecke bases. -/
theorem heckeTerminal_isHeckeBasis {n : ℕ} {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) (ht : IsHeckeTerminal A) :
    IsHeckeBasis n (A 0 0) (A 0 1) (A 1 0) (A 1 1) := by
  refine ⟨by positivity, by exact_mod_cast ht.1, by positivity,
    by exact_mod_cast ht.2, ?_⟩
  have he : (A 0 0 : ℤ) * A 1 1 = (A 0 1 : ℤ) * A 1 0 + n := by
    exact_mod_cast hA
  omega

/-- Terminal matrices have uniformly bounded entries, at every positive determinant. -/
theorem heckeTerminal_size_le {n : ℕ} {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) (ht : IsHeckeTerminal A) :
    heckeMatrixSize A ≤ 4 * n := by
  have hb := heckeBasis_bounds (heckeTerminal_isHeckeBasis hA ht)
  have ha : A 0 0 ≤ n := by exact_mod_cast hb.2.1
  have hb' : A 0 1 ≤ n := by exact_mod_cast hb.2.2.2.1
  have hc : A 1 0 ≤ n := by exact_mod_cast hb.2.2.2.2.2.1
  have hd : A 1 1 ≤ n := by exact_mod_cast hb.2.2.2.2.2.2.2
  dsimp only [heckeMatrixSize]
  omega

#print axioms heckeWordNormalForm_unique
#print axioms heckeMatrixSize_word_growth
#print axioms heckeTerminal_isHeckeBasis
#print axioms heckeTerminal_size_le


/-- Transposition preserves the unsigned positive-determinant equation. -/
theorem hasHeckeDeterminant_transpose {n : ℕ} {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) : HasHeckeDeterminant n A.transpose := by
  change A 0 0 * A 1 1 = A 1 0 * A 0 1 + n
  simpa only [HasHeckeDeterminant, mul_comm] using hA

private theorem heckeMatrixSize_transpose (A : NatMatrix) :
    heckeMatrixSize A.transpose = heckeMatrixSize A := by
  dsimp only [heckeMatrixSize, Matrix.transpose_apply]
  omega

private theorem positive_generator_transpose (b : Bool) :
    (generator b).transpose = generator (!b) := by
  cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [generator, Matrix.transpose_apply]

private theorem hecke_left_division_exists {n : ℕ} (hn : 0 < n) {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) (hs : 4 * n < heckeMatrixSize A) :
    ∃ b : Bool, ∃ B : NatMatrix, HasHeckeDeterminant n B ∧ generator b * B = A := by
  obtain ⟨u, C, hC, htC, hu⟩ := heckeWordNormalForm_exists hn A hA
  cases u with
  | nil =>
      simp only [matrixWord, one_mul] at hu
      subst A
      have hb := heckeTerminal_size_le hC htC
      omega
  | cons b u =>
      exact ⟨b, matrixWord u * C, hasHeckeDeterminant_word_mul hC u,
        by simpa only [matrixWord, mul_assoc] using hu⟩

/-- Outside the finite terminal bound, a positive determinant matrix has a right
Euclidean predecessor. -/
theorem heckeRightDivision_exists {n : ℕ} (hn : 0 < n) {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) (hs : 4 * n < heckeMatrixSize A) :
    ∃ b : Bool, ∃ B : NatMatrix, HasHeckeDeterminant n B ∧ B * generator b = A := by
  have hs' : 4 * n < heckeMatrixSize A.transpose := by
    simpa only [heckeMatrixSize_transpose] using hs
  obtain ⟨b, B, hB, hb⟩ := hecke_left_division_exists hn
    (hasHeckeDeterminant_transpose hA) hs'
  refine ⟨!b, B.transpose, hasHeckeDeterminant_transpose hB, ?_⟩
  have he := congrArg Matrix.transpose hb
  simpa only [Matrix.transpose_mul, positive_generator_transpose,
    Matrix.transpose_transpose] using he

private theorem hecke_left_division_unique {n : ℕ} (hn : 0 < n) {A B : NatMatrix}
    (hA : HasHeckeDeterminant n A) (hB : HasHeckeDeterminant n B) (b c : Bool)
    (he : generator b * A = generator c * B) : b = c ∧ A = B := by
  by_cases hbc : b = c
  · subst c
    exact ⟨rfl, positive_generator_left_cancel b he⟩
  · cases b <;> cases c
    · exact False.elim (hbc rfl)
    · exact False.elim (hecke_opposite_generators_ne hn hB _ he.symm)
    · exact False.elim (hecke_opposite_generators_ne hn hA _ he)
    · exact False.elim (hbc rfl)

/-- The last positive letter and its predecessor are unique. -/
theorem heckeRightDivision_unique {n : ℕ} (hn : 0 < n) {A B : NatMatrix}
    (hA : HasHeckeDeterminant n A) (hB : HasHeckeDeterminant n B) (b c : Bool)
    (he : A * generator b = B * generator c) : b = c ∧ A = B := by
  have ht := congrArg Matrix.transpose he
  simp only [Matrix.transpose_mul, positive_generator_transpose] at ht
  obtain ⟨hbc, hAB⟩ := hecke_left_division_unique hn
    (hasHeckeDeterminant_transpose hA) (hasHeckeDeterminant_transpose hB) (!b) (!c) ht
  constructor
  · cases b <;> cases c <;> simp_all
  · have h := congrArg Matrix.transpose hAB
    simpa only [Matrix.transpose_transpose] using h

/-- Positive right multiplication also preserves the determinant. -/
theorem hasHeckeDeterminant_mul_generator {n : ℕ} {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) (b : Bool) : HasHeckeDeterminant n (A * generator b) := by
  have h := hasHeckeDeterminant_transpose
    (hasHeckeDeterminant_generator_mul (hasHeckeDeterminant_transpose hA) (!b))
  simpa only [Matrix.transpose_mul, positive_generator_transpose,
    Matrix.transpose_transpose, Bool.not_not] using h

#print axioms heckeRightDivision_exists
#print axioms heckeRightDivision_unique
#print axioms hasHeckeDeterminant_mul_generator


/-- The integral finite set contains exactly the cross-ordered determinant bases. -/
theorem mem_heckeSet_iff_basis {n : ℕ} {M : ℤ × ℤ × ℤ × ℤ} :
    M ∈ heckeSet n ↔ IsHeckeBasis n M.1 M.2.1 M.2.2.1 M.2.2.2 := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hb := heckeBasis_bounds h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨hb.1, hb.2.1⟩, ⟨hb.2.2.1, hb.2.2.2.1⟩,
      ⟨hb.2.2.2.2.1, hb.2.2.2.2.2.1⟩, ⟨hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2⟩⟩

/-- The literal four integral entries used by the source Hecke operator. -/
def heckeMatrixTuple (A : NatMatrix) : ℤ × ℤ × ℤ × ℤ :=
  (A 0 0, A 0 1, A 1 0, A 1 1)

/-- Read the nonnegative entries of an actual source Hecke basis as a matrix. -/
def heckeNatMatrix (M : ℤ × ℤ × ℤ × ℤ) : NatMatrix :=
  !![M.1.toNat, M.2.1.toNat; M.2.2.1.toNat, M.2.2.2.toNat]

/-- The tuple map loses no natural matrix entries. -/
theorem heckeNatMatrix_tuple (A : NatMatrix) : heckeNatMatrix (heckeMatrixTuple A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeNatMatrix, heckeMatrixTuple]

/-- On the actual Hecke set, conversion to natural matrices loses no integral entries. -/
theorem heckeMatrixTuple_natMatrix {n : ℕ} {M : ℤ × ℤ × ℤ × ℤ}
    (hM : M ∈ heckeSet n) : heckeMatrixTuple (heckeNatMatrix M) = M := by
  have hb := heckeBasis_bounds (mem_heckeSet_iff_basis.mp hM)
  rcases M with ⟨a, b, c, d⟩
  change ((a.toNat : ℤ), (b.toNat : ℤ), (c.toNat : ℤ), (d.toNat : ℤ)) = (a, b, c, d)
  have ha : (a.toNat : ℤ) = a := Int.toNat_of_nonneg hb.1
  have hb' : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb.2.2.1
  have hc : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hb.2.2.2.2.1
  have hd : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hb.2.2.2.2.2.2.1
  simp only [ha, hb', hc, hd]

/-- Terminal positive-determinant matrices are exactly the bases in the source sum. -/
theorem heckeMatrixTuple_mem_iff {n : ℕ} {A : NatMatrix} :
    heckeMatrixTuple A ∈ heckeSet n ↔ HasHeckeDeterminant n A ∧ IsHeckeTerminal A := by
  rw [mem_heckeSet_iff_basis]
  constructor
  · intro h
    have hd : (A 0 0 : ℤ) * A 1 1 = (A 0 1 : ℤ) * A 1 0 + n := by
      have he := h.det
      dsimp only [heckeMatrixTuple] at he
      omega
    refine ⟨?_, ?_⟩
    · dsimp only [HasHeckeDeterminant]
      exact_mod_cast hd
    · have hc : (A 1 0 : ℤ) < A 0 0 := h.c_lt
      have hb : (A 0 1 : ℤ) < A 1 1 := h.b_lt
      exact ⟨by exact_mod_cast hc, by exact_mod_cast hb⟩
  · rintro ⟨hA, ht⟩
    exact heckeTerminal_isHeckeBasis hA ht

open Classical in
/-- The actual source Hecke bases, represented as nonnegative matrices. -/
noncomputable def naturalHeckeSet (n : ℕ) : Finset NatMatrix :=
  (heckeSet n).image heckeNatMatrix

/-- Membership in the finite matrix set has precisely the determinant and terminal conditions. -/
theorem mem_naturalHeckeSet_iff {n : ℕ} {A : NatMatrix} :
    A ∈ naturalHeckeSet n ↔ HasHeckeDeterminant n A ∧ IsHeckeTerminal A := by
  classical
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    apply heckeMatrixTuple_mem_iff.mp
    simpa only [heckeMatrixTuple_natMatrix hM] using hM
  · intro h
    exact Finset.mem_image.mpr ⟨heckeMatrixTuple A, heckeMatrixTuple_mem_iff.mpr h,
      heckeNatMatrix_tuple A⟩

#print axioms heckeMatrixTuple_natMatrix
#print axioms heckeMatrixTuple_mem_iff
#print axioms mem_naturalHeckeSet_iff


private theorem heckeMatrixSize_generator_upper (A : NatMatrix) (b : Bool) :
    heckeMatrixSize (generator b * A) ≤ 2 * heckeMatrixSize A := by
  cases b
  · rw [positive_generator_false_mul]
    dsimp [heckeMatrixSize]
    omega
  · rw [positive_generator_true_mul]
    dsimp [heckeMatrixSize]
    omega

private theorem heckeMatrixSize_right_generator_upper (A : NatMatrix) (b : Bool) :
    heckeMatrixSize (A * generator b) ≤ 2 * heckeMatrixSize A := by
  have h := heckeMatrixSize_generator_upper A.transpose (!b)
  have he : generator (!b) * A.transpose = (A * generator b).transpose := by
    rw [Matrix.transpose_mul, positive_generator_transpose]
  rw [he, heckeMatrixSize_transpose, heckeMatrixSize_transpose] at h
  exact h

/-- Appending one source branch to a Hecke basis yields a uniformly bounded
transition word and another actual Hecke basis. -/
theorem heckeTransition_exists {n : ℕ} (hn : 0 < n) {B : NatMatrix}
    (hB : B ∈ naturalHeckeSet n) (b : Bool) :
    ∃ u : List Bool, ∃ C ∈ naturalHeckeSet n,
      matrixWord u * C = B * generator b ∧ u.length ≤ 8 * n := by
  have hb := mem_naturalHeckeSet_iff.mp hB
  obtain ⟨u, C, hC, htC, hu⟩ := heckeWordNormalForm_exists hn (B * generator b)
    (hasHeckeDeterminant_mul_generator hb.1 b)
  refine ⟨u, C, mem_naturalHeckeSet_iff.mpr ⟨hC, htC⟩, hu, ?_⟩
  have hg := heckeMatrixSize_word_growth hn hC u
  rw [hu] at hg
  have hs := heckeMatrixSize_right_generator_upper B b
  have ht := heckeTerminal_size_le hb.1 hb.2
  omega

/-- Every sufficiently long word over a fixed target Hecke basis ends in a
transition word. The remaining prefix accounts for the right predecessor. -/
theorem heckeTransition_suffix_exists {n : ℕ} (hn : 0 < n) {C : NatMatrix}
    (hC : C ∈ naturalHeckeSet n) (W : List Bool) (hW : 4 * n < W.length) :
    ∃ B ∈ naturalHeckeSet n, ∃ b : Bool, ∃ u v : List Bool,
      matrixWord u * C = B * generator b ∧ W = v ++ u ∧ u.length ≤ 8 * n := by
  have hc := mem_naturalHeckeSet_iff.mp hC
  have hs : 4 * n < heckeMatrixSize (matrixWord W * C) := by
    have hg := heckeMatrixSize_word_growth hn hc.1 W
    omega
  obtain ⟨b, M, hM, hm⟩ := heckeRightDivision_exists hn
    (hasHeckeDeterminant_word_mul hc.1 W) hs
  obtain ⟨v, B, hB, htB, hv⟩ := heckeWordNormalForm_exists hn M hM
  have hb : B ∈ naturalHeckeSet n := mem_naturalHeckeSet_iff.mpr ⟨hB, htB⟩
  obtain ⟨u, C', hC', hu, hul⟩ := heckeTransition_exists hn hb b
  have he : matrixWord (v ++ u) * C' = matrixWord W * C := by
    calc
      matrixWord (v ++ u) * C' = matrixWord v * (matrixWord u * C') := by
        rw [matrixWord_append, mul_assoc]
      _ = matrixWord v * (B * generator b) := congrArg (matrixWord v * ·) hu
      _ = M * generator b := by rw [← mul_assoc, hv]
      _ = matrixWord W * C := hm
  have hc' := mem_naturalHeckeSet_iff.mp hC'
  obtain ⟨hw, hCC⟩ := heckeWordNormalForm_unique hn hc'.1 hc.1 hc'.2 hc.2
    (v ++ u) W he
  subst C'
  exact ⟨B, hb, b, u, v, hu, hw.symm, hul⟩

/-- Suffix labels cannot overlap: right division and the left normal form recover
both the source branch and the word split. -/
theorem heckeTransition_suffix_unique {n : ℕ} (hn : 0 < n)
    {B B' C : NatMatrix} (hB : B ∈ naturalHeckeSet n) (hB' : B' ∈ naturalHeckeSet n)
    (b b' : Bool) (u u' v v' : List Bool)
    (hu : matrixWord u * C = B * generator b)
    (hu' : matrixWord u' * C = B' * generator b')
    (hw : v ++ u = v' ++ u') : b = b' ∧ B = B' ∧ v = v' ∧ u = u' := by
  have hb := mem_naturalHeckeSet_iff.mp hB
  have hb' := mem_naturalHeckeSet_iff.mp hB'
  have he : (matrixWord v * B) * generator b =
      (matrixWord v' * B') * generator b' := by
    calc
      (matrixWord v * B) * generator b = matrixWord (v ++ u) * C := by
        simp only [matrixWord_append, mul_assoc, hu]
      _ = matrixWord (v' ++ u') * C := congrArg (fun W => matrixWord W * C) hw
      _ = (matrixWord v' * B') * generator b' := by
        simp only [matrixWord_append, mul_assoc, hu']
  obtain ⟨hbb, hm⟩ := heckeRightDivision_unique hn
    (hasHeckeDeterminant_word_mul hb.1 v) (hasHeckeDeterminant_word_mul hb'.1 v') b b' he
  obtain ⟨hvv, hBB⟩ := heckeWordNormalForm_unique hn hb.1 hb'.1 hb.2 hb'.2 v v' hm
  refine ⟨hbb, hBB, hvv, ?_⟩
  subst v'
  exact List.append_cancel_left hw

#print axioms heckeTransition_exists
#print axioms heckeTransition_suffix_exists
#print axioms heckeTransition_suffix_unique

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
