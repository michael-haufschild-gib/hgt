import GaloisForLFunctions.SelbergClass.Primon.KestenTailGeometry
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Innovation factorization and finite precision

Consecutive normalized likelihood tails are whitened by a bidiagonal
backward-difference matrix. Their inverse Gram form is a sum of squared
nearest-neighbor differences and one terminal boundary term.
-/

open _root_.RHTower Matrix
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Backward differences at every depth except the terminal one. -/
def kestenInnovationMatrix (p : Nat.Primes) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Fin.lastCases (Pi.single (Fin.last n) 1)
    (fun i => Pi.single i.castSucc 1 - primeReciprocal p • Pi.single i.succ 1)

private theorem innovation_last (p : Nat.Primes) (n : ℕ) :
    kestenInnovationMatrix p n (Fin.last n) = Pi.single (Fin.last n) 1 := by
  simp only [kestenInnovationMatrix, Fin.lastCases_last]

private theorem innovation_castSucc (p : Nat.Primes) (n : ℕ) (i : Fin n) :
    kestenInnovationMatrix p n i.castSucc =
      Pi.single i.castSucc 1 - primeReciprocal p • Pi.single i.succ 1 := by
  simp only [kestenInnovationMatrix, Fin.lastCases_castSucc]

/-- The innovation matrix acts by ordinary adjacent backward differences. -/
theorem kestenInnovationMatrix_mulVec (p : Nat.Primes) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    kestenInnovationMatrix p n *ᵥ c =
      Fin.lastCases (c (Fin.last n)) (fun i => c i.castSucc - primeReciprocal p * c i.succ) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [Matrix.mulVec, dotProduct, innovation_last, Pi.single_apply]
  | cast i =>
      simp [Matrix.mulVec, dotProduct, innovation_castSucc, Pi.single_apply,
        sub_mul, Finset.sum_sub_distrib]

/-- The bidiagonal innovation change of coordinates has determinant one. -/
theorem det_kestenInnovationMatrix (p : Nat.Primes) (n : ℕ) :
    (kestenInnovationMatrix p n).det = 1 := by
  have ht : (kestenInnovationMatrix p n).BlockTriangular id := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
        have hji : j ≠ Fin.last n := ne_of_lt hij
        simp [innovation_last, hji]
    | cast i =>
        have hji : j ≠ i.castSucc := ne_of_lt hij
        have hjs : j ≠ i.succ := by
          intro h
          subst j
          have := hij
          simp only [id_eq, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at this
          omega
        simp [innovation_castSucc, hji, hjs]
  rw [Matrix.det_of_upperTriangular ht]
  apply Finset.prod_eq_one
  intro i _
  induction i using Fin.lastCases with
  | last => simp [innovation_last]
  | cast i =>
      have hi : i.castSucc ≠ i.succ := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega
      simp [innovation_castSucc, hi]

/-- The terminal coordinate retains the geometric tail variance. -/
def kestenInnovationVariance (p : Nat.Primes) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i = Fin.last n then 1 / (1 - primeReciprocal p ^ 2) else 1

/-- Reciprocal innovation variances, including the terminal boundary correction. -/
def kestenInnovationPrecision (p : Nat.Primes) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i = Fin.last n then 1 - primeReciprocal p ^ 2 else 1

private theorem innovation_synthesis (p : Nat.Primes) (N n : ℕ) (i : Fin (n + 1)) :
    (∑ j, kestenInnovationMatrix p n i j • kestenNormalizedTail p (N + j)) =
      Fin.lastCases (kestenNormalizedTail p (N + n))
        (fun k => spectralCharacterVector (2 * (N + k))) i := by
  induction i using Fin.lastCases with
  | last => simp [innovation_last, Pi.single_apply]
  | cast i =>
      simp only [innovation_castSucc, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
        Fin.lastCases_castSucc]
      simp only [Pi.single_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_castSucc, Fin.val_succ]
      rw [show N + (i.val + 1) = (N + i.val) + 1 by omega,
        kestenNormalizedTail_innovation]

private theorem innovation_gram (p : Nat.Primes) (N n : ℕ) :
    kestenInnovationMatrix p n * kestenDepthGram p N (n + 1) *
        (kestenInnovationMatrix p n).transpose =
      Matrix.diagonal (kestenInnovationVariance p n) := by
  ext i j
  have hg : (kestenInnovationMatrix p n * kestenDepthGram p N (n + 1) *
        (kestenInnovationMatrix p n).transpose) i j =
      inner ℝ (∑ k, kestenInnovationMatrix p n i k • kestenNormalizedTail p (N + k))
        (∑ l, kestenInnovationMatrix p n j l • kestenNormalizedTail p (N + l)) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, kestenDepthGram,
      sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hg, innovation_synthesis, innovation_synthesis]
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last =>
          simp only [Fin.lastCases_last]
          rw [inner_kestenNormalizedTail_sameDepth]
          simp [Matrix.diagonal, kestenInnovationVariance, pow_two]
      | cast j =>
          rw [Fin.lastCases_last, Fin.lastCases_castSucc,
            inner_kestenNormalizedTail_earlier p _ _ (by exact Nat.add_lt_add_left j.isLt N)]
          rw [Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last j).symm]
  | cast i =>
      induction j using Fin.lastCases with
      | last =>
          rw [Fin.lastCases_castSucc, Fin.lastCases_last, real_inner_comm,
            inner_kestenNormalizedTail_earlier p _ _ (by exact Nat.add_lt_add_left i.isLt N)]
          simp [Matrix.diagonal, Fin.castSucc_ne_last]
      | cast j =>
          simp only [Fin.lastCases_castSucc, inner_spectralCharacterVector]
          have he : 2 * (N + i.val) = 2 * (N + j.val) ↔ i = j := by
            constructor
            · intro h; apply Fin.ext; omega
            · rintro rfl; rfl
          simp [he, Matrix.diagonal, kestenInnovationVariance, Fin.castSucc_ne_last]


/-- The exact inverse Gram matrix is the innovation precision pulled back by differences. -/
theorem inv_kestenDepthGram (p : Nat.Primes) (N n : ℕ) :
    (kestenDepthGram p N (n + 1))⁻¹ =
      (kestenInnovationMatrix p n).transpose *
        Matrix.diagonal (kestenInnovationPrecision p n) * kestenInnovationMatrix p n := by
  let L := kestenInnovationMatrix p n
  let G := kestenDepthGram p N (n + 1)
  let D := Matrix.diagonal (kestenInnovationPrecision p n)
  let C := Matrix.diagonal (kestenInnovationVariance p n)
  have hLT : IsUnit L.transpose.det := by
    rw [Matrix.det_transpose, det_kestenInnovationMatrix]
    exact isUnit_one
  have hden : 1 - primeReciprocal p ^ 2 ≠ 0 := by
    have hq := primeReciprocal_lt_one p
    have hs := mul_lt_mul_of_pos_left hq (primeReciprocal_pos p)
    nlinarith only [hq, hs]
  have hDC : D * C = 1 := by
    change Matrix.diagonal (kestenInnovationPrecision p n) *
      Matrix.diagonal (kestenInnovationVariance p n) = 1
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
        kestenInnovationPrecision, kestenInnovationVariance]
      split_ifs <;> simp [hden]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hgram : L * G * L.transpose = C := innovation_gram p N n
  have hprod : (L.transpose * D * L * G) * L.transpose = L.transpose := by
    calc
      _ = L.transpose * (D * (L * G * L.transpose)) := by simp only [Matrix.mul_assoc]
      _ = L.transpose := by rw [hgram, hDC, Matrix.mul_one]
  apply Matrix.inv_eq_left_inv
  change L.transpose * D * L * G = 1
  calc
    _ = ((L.transpose * D * L * G) * L.transpose) * L.transpose⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLT, Matrix.mul_one]
    _ = 1 := by rw [hprod, Matrix.mul_nonsing_inv _ hLT]

/-- The inverse Gram energy consists of nearest-neighbor squares and one boundary term. -/
theorem kestenDepthGram_inverse_energy (p : Nat.Primes) (N n : ℕ) (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ ((kestenDepthGram p N (n + 1))⁻¹ *ᵥ c) =
      (∑ i : Fin n, (c i.castSucc - primeReciprocal p * c i.succ) ^ 2) +
        (1 - primeReciprocal p ^ 2) * c (Fin.last n) ^ 2 := by
  rw [inv_kestenDepthGram]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct, Matrix.mulVec_diagonal, kestenInnovationMatrix_mulVec]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last,
    kestenInnovationPrecision, Fin.castSucc_ne_last, if_false, ite_true, one_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring


private theorem innovation_support (p : Nat.Primes) (n : ℕ) (k i : Fin (n + 1))
    (h : kestenInnovationMatrix p n k i ≠ 0) : i.val = k.val ∨ i.val = k.val + 1 := by
  induction k using Fin.lastCases with
  | last =>
      by_cases hi : i = Fin.last n
      · subst i; exact Or.inl rfl
      · simp [innovation_last, hi] at h
  | cast k =>
      by_cases hi : i = k.castSucc
      · subst i; exact Or.inl rfl
      · by_cases hs : i = k.succ
        · subst i; exact Or.inr rfl
        · simp [innovation_castSucc, hi, hs] at h

/-- Precision couples only equal or adjacent depths. -/
theorem kestenDepthGram_inverse_tridiagonal (p : Nat.Primes) (N n : ℕ)
    (i j : Fin (n + 1)) (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (kestenDepthGram p N (n + 1))⁻¹ i j = 0 := by
  rw [inv_kestenDepthGram, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  by_cases hi : kestenInnovationMatrix p n k i = 0
  · rw [hi, zero_mul, zero_mul]
  · have hj : kestenInnovationMatrix p n k j = 0 := by
      by_contra hj
      have hki := innovation_support p n k i hi
      have hkj := innovation_support p n k j hj
      omega
    rw [hj, mul_zero]

end
end GaloisForLFunctions.SelbergClass.Primon

