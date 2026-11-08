import GaloisForLFunctions.SelbergClass.Primon.KestenGreenKernel
import GaloisForLFunctions.SelbergClass.Primon.KestenGreenInnovations
import GaloisForLFunctions.SelbergClass.Primon.KestenTailPrecision
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite prime Green matrices and exact precision

The first `n+1` character coordinates of the Green operator have a
unitriangular innovation factorization. The initial innovation variance
is `q/(1+q)` and the others are `q`, where `q=1/p`. This gives the exact
determinant and a tridiagonal inverse with a nearest-neighbor energy.
-/

open _root_.RHTower Matrix
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem inner_state_smul_left (a : ℝ) (f g : KestenLikelihoodHilbert) :
    inner ℝ (a • f) g = a * inner ℝ f g := by
  simpa only [conj_trivial] using (_root_.inner_smul_left (𝕜 := ℝ) f g a)

private theorem inner_state_smul_right (a : ℝ) (f g : KestenLikelihoodHilbert) :
    inner ℝ f (a • g) = a * inner ℝ f g :=
  _root_.inner_smul_right (𝕜 := ℝ) f g a

/-- The Green covariance restricted to the first `n+1` even characters. -/
def kestenFiniteGreen (p : Nat.Primes) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => kestenGreenEntry p i j

theorem isSymm_kestenFiniteGreen (p : Nat.Primes) (n : ℕ) :
    (kestenFiniteGreen p n).IsSymm := by
  change (kestenFiniteGreen p n).transpose = kestenFiniteGreen p n
  ext i j
  exact kestenGreenEntry_symm p j i

/-- Causal differences: the initial coordinate and each coordinate minus `q` times its predecessor. -/
def kestenGreenDifference (p : Nat.Primes) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (kestenInnovationMatrix p n).transpose

private theorem difference_zero (p : Nat.Primes) (n : ℕ) :
    kestenGreenDifference p n 0 = Pi.single 0 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [kestenGreenDifference, kestenInnovationMatrix, Pi.single_apply, eq_comm]
  | cast j => simp [kestenGreenDifference, kestenInnovationMatrix, Pi.single_apply, eq_comm]

private theorem difference_succ (p : Nat.Primes) (n : ℕ) (i : Fin n) :
    kestenGreenDifference p n i.succ =
      Pi.single i.succ 1 - primeReciprocal p • Pi.single i.castSucc 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [kestenGreenDifference, kestenInnovationMatrix, Pi.single_apply, eq_comm]
  | cast j => simp [kestenGreenDifference, kestenInnovationMatrix, Pi.single_apply, eq_comm]

/-- The finite difference matrix acts by causal first differences. -/
theorem kestenGreenDifference_mulVec (p : Nat.Primes) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    kestenGreenDifference p n *ᵥ c =
      Fin.cases (c 0) (fun i => c i.succ - primeReciprocal p * c i.castSucc) := by
  ext i
  induction i using Fin.cases with
  | zero => simp [Matrix.mulVec, dotProduct, difference_zero, Pi.single_apply]
  | succ i =>
      simp [Matrix.mulVec, dotProduct, difference_succ, Pi.single_apply,
        sub_mul, Finset.sum_sub_distrib]

theorem det_kestenGreenDifference (p : Nat.Primes) (n : ℕ) :
    (kestenGreenDifference p n).det = 1 := by
  rw [kestenGreenDifference, Matrix.det_transpose, det_kestenInnovationMatrix]

/-- The unique exceptional variance occurs at the initial character. -/
def kestenGreenVariance (p : Nat.Primes) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i = 0 then primeReciprocal p / (1 + primeReciprocal p) else primeReciprocal p

/-- Reciprocal Green innovation variances. -/
def kestenGreenPrecision (p : Nat.Primes) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i = 0 then (1 + primeReciprocal p) / primeReciprocal p else (primeReciprocal p)⁻¹

private theorem difference_synthesis (p : Nat.Primes) (n : ℕ) (i : Fin (n + 1)) :
    (∑ j, kestenGreenDifference p n i j • kestenCharacterState j) =
      kestenGreenInnovation p i := by
  induction i using Fin.cases with
  | zero => simp [difference_zero, Pi.single_apply, kestenGreenInnovation_zero]
  | succ i =>
      simp only [difference_succ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
      simp only [Pi.single_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_succ, Fin.val_castSucc]
      rw [kestenGreenInnovation_succ]

/-- Causal differences diagonalize every finite Green section exactly. -/
theorem kestenFiniteGreen_whitening (p : Nat.Primes) (n : ℕ) :
    kestenGreenDifference p n * kestenFiniteGreen p n * (kestenGreenDifference p n).transpose =
      Matrix.diagonal (kestenGreenVariance p n) := by
  ext i j
  have hg : (kestenGreenDifference p n * kestenFiniteGreen p n *
      (kestenGreenDifference p n).transpose) i j =
      inner ℝ (∑ k, kestenGreenDifference p n i k • kestenCharacterState k)
        (kestenGreenOperator p (∑ l, kestenGreenDifference p n j l • kestenCharacterState l)) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, kestenFiniteGreen, kestenGreenEntry,
      map_sum, map_smul, sum_inner, inner_sum, inner_state_smul_left, inner_state_smul_right,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hg, difference_synthesis, difference_synthesis, inner_kestenGreenInnovations]
  have he : i.val = j.val ↔ i = j := Fin.ext_iff.symm
  have hz : i.val = 0 ↔ i = 0 := by
    constructor
    · exact fun h => Fin.ext h
    · intro h
      simp [h]
  simp only [he, hz, Matrix.diagonal, kestenGreenVariance]
  rfl

/-- Every extra character contributes exactly one factor `q` to the Green determinant. -/
theorem det_kestenFiniteGreen (p : Nat.Primes) (n : ℕ) :
    (kestenFiniteGreen p n).det = primeReciprocal p ^ (n + 1) / (1 + primeReciprocal p) := by
  have h := congrArg Matrix.det (kestenFiniteGreen_whitening p n)
  simp only [Matrix.det_mul, Matrix.det_transpose, det_kestenGreenDifference,
    one_mul, mul_one, Matrix.det_diagonal] at h
  rw [h, Fin.prod_univ_succ]
  simp only [kestenGreenVariance, ite_true, Fin.succ_ne_zero, if_false,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_succ]
  ring

theorem det_kestenFiniteGreen_pos (p : Nat.Primes) (n : ℕ) :
    0 < (kestenFiniteGreen p n).det := by
  rw [det_kestenFiniteGreen]
  exact div_pos (pow_pos (primeReciprocal_pos p) _) (by have := primeReciprocal_pos p; positivity)

/-- The exact finite inverse is the reciprocal innovation variance pulled back by causal differences. -/
theorem inv_kestenFiniteGreen (p : Nat.Primes) (n : ℕ) :
    (kestenFiniteGreen p n)⁻¹ = (kestenGreenDifference p n).transpose *
      Matrix.diagonal (kestenGreenPrecision p n) * kestenGreenDifference p n := by
  let L := kestenGreenDifference p n
  let G := kestenFiniteGreen p n
  let D := Matrix.diagonal (kestenGreenPrecision p n)
  let C := Matrix.diagonal (kestenGreenVariance p n)
  have hLT : IsUnit L.transpose.det := by
    rw [Matrix.det_transpose, det_kestenGreenDifference]
    exact isUnit_one
  have hq : primeReciprocal p ≠ 0 := (primeReciprocal_pos p).ne'
  have hq1 : 1 + primeReciprocal p ≠ 0 := by have := primeReciprocal_pos p; positivity
  have hDC : D * C = 1 := by
    change Matrix.diagonal (kestenGreenPrecision p n) * Matrix.diagonal (kestenGreenVariance p n) = 1
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, kestenGreenPrecision, kestenGreenVariance]
      split_ifs <;> field_simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hgram : L * G * L.transpose = C := kestenFiniteGreen_whitening p n
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

theorem isSymm_kestenFiniteGreen_inverse (p : Nat.Primes) (n : ℕ) :
    ((kestenFiniteGreen p n)⁻¹).IsSymm := by
  rw [inv_kestenFiniteGreen]
  change ((kestenGreenDifference p n).transpose * Matrix.diagonal (kestenGreenPrecision p n) *
    kestenGreenDifference p n).transpose = _
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
    (Matrix.isSymm_diagonal (kestenGreenPrecision p n)).eq, Matrix.mul_assoc]

/-- Every finite precision matrix is positive definite, including the one-coordinate section. -/
theorem posDef_kestenFiniteGreen_inverse (p : Nat.Primes) (n : ℕ) :
    ((kestenFiniteGreen p n)⁻¹).PosDef := by
  have hD : (Matrix.diagonal (kestenGreenPrecision p n)).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    unfold kestenGreenPrecision
    split_ifs
    · exact div_pos (by have := primeReciprocal_pos p; positivity) (primeReciprocal_pos p)
    · exact inv_pos.mpr (primeReciprocal_pos p)
  have hL : IsUnit (kestenGreenDifference p n) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [det_kestenGreenDifference]
    exact isUnit_one
  have ht : (kestenGreenDifference p n).conjTranspose = (kestenGreenDifference p n).transpose := by
    ext i j
    rfl
  rw [inv_kestenFiniteGreen, ← ht]
  exact hD.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hL)

/-- The actual Green covariance is strictly positive definite on every finite character section. -/
theorem posDef_kestenFiniteGreen (p : Nat.Primes) (n : ℕ) :
    (kestenFiniteGreen p n).PosDef :=
  Matrix.posDef_inv_iff.mp (posDef_kestenFiniteGreen_inverse p n)

/-- The finite inverse energy is a sum of squared causal differences and one initial term. -/
theorem kestenFiniteGreen_inverse_energy (p : Nat.Primes) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ ((kestenFiniteGreen p n)⁻¹ *ᵥ c) =
      (1 + primeReciprocal p) / primeReciprocal p * c 0 ^ 2 +
        (primeReciprocal p)⁻¹ * ∑ i : Fin n, (c i.succ - primeReciprocal p * c i.castSucc) ^ 2 := by
  rw [inv_kestenFiniteGreen]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct, Matrix.mulVec_diagonal, kestenGreenDifference_mulVec]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, kestenGreenPrecision,
    Fin.succ_ne_zero, if_false, ite_true]
  rw [Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

private theorem difference_support (p : Nat.Primes) (n : ℕ) (k i : Fin (n + 1))
    (h : kestenGreenDifference p n k i ≠ 0) : i.val = k.val ∨ i.val + 1 = k.val := by
  induction k using Fin.cases with
  | zero =>
      by_cases hi : i = 0
      · subst i; exact Or.inl rfl
      · simp [difference_zero, hi] at h
  | succ k =>
      by_cases hi : i = k.succ
      · subst i; exact Or.inl rfl
      · by_cases hs : i = k.castSucc
        · subst i; exact Or.inr rfl
        · simp [difference_succ, hi, hs] at h

/-- The inverse Green matrix has no coupling beyond adjacent depths. -/
theorem kestenFiniteGreen_inverse_tridiagonal (p : Nat.Primes) (n : ℕ)
    (i j : Fin (n + 1)) :
    i.val + 1 < j.val ∨ j.val + 1 < i.val → (kestenFiniteGreen p n)⁻¹ i j = 0 := by
  intro h
  rw [inv_kestenFiniteGreen, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  by_cases hi : kestenGreenDifference p n k i = 0
  · rw [hi, zero_mul, zero_mul]
  · have hj : kestenGreenDifference p n k j = 0 := by
      by_contra hj
      have hki := difference_support p n k i hi
      have hkj := difference_support p n k j hj
      omega
    rw [hj, mul_zero]

end
end GaloisForLFunctions.SelbergClass.Primon
