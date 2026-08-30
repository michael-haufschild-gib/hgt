import GaloisForLFunctions.HTGeometry.ComplexSiegelWeightedIsometry

/-!
# Inverse and triangular vanishing for complex weighted isometries

The inverse of a complex weighted isometry is its weighted conjugate transpose.  Factoring that
inverse through upper-triangular Jacobi factors forces entries to vanish across a sufficiently
large ordered weight gap.  These are the Hermitian analogues of the central real Siegel-finiteness
lemmas.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- Weighted conjugate transpose relative to two positive Jacobi diagonals. -/
noncomputable def complexIsometryInv
    (J J' : ComplexJacobiData n) (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => (J.d k : ℂ) * star (M k i) / (J'.d i : ℂ)

/-- The weighted conjugate transpose is a left inverse of a complex weighted isometry. -/
theorem complexIsometryInv_mul
    {J J' : ComplexJacobiData n} {M : Matrix (Fin n) (Fin n) ℂ}
    (hiso : Matrix.conjTranspose M * Matrix.diagonal (fun i => (J.d i : ℂ)) * M =
      Matrix.diagonal (fun i => (J'.d i : ℂ))) :
    complexIsometryInv J J' M * M = 1 := by
  classical
  have hmul : ∀ a b : Fin n,
      (Matrix.conjTranspose M * Matrix.diagonal (fun i => (J.d i : ℂ))) a b =
        star (M b a) * (J.d b : ℂ) := by
    intro a b
    rw [Matrix.mul_apply,
      Finset.sum_eq_single b
        (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
        (fun hcon => absurd (Finset.mem_univ b) hcon),
      Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
  have hexp : ∀ i j : Fin n,
      (∑ k, star (M k i) * (J.d k : ℂ) * M k j) =
        Matrix.diagonal (fun a => (J'.d a : ℂ)) i j := by
    intro i j
    have h := congrFun (congrFun hiso i) j
    rw [Matrix.mul_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => by rw [hmul]
  ext i j
  rw [Matrix.mul_apply]
  have hstep :
      (∑ k, complexIsometryInv J J' M i k * M k j) =
        (∑ k, star (M k i) * (J.d k : ℂ) * M k j) / (J'.d i : ℂ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by
      show (J.d k : ℂ) * star (M k i) / (J'.d i : ℂ) * M k j = _
      ring
  rw [hstep, hexp i j]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq,
      div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt (J'.pos i))), Matrix.one_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, zero_div, Matrix.one_apply_ne hij]

/-- The weighted conjugate transpose equals any right inverse of a complex weighted isometry. -/
theorem complexIsometryInv_eq
    {J J' : ComplexJacobiData n} {M P : Matrix (Fin n) (Fin n) ℂ}
    (hiso : Matrix.conjTranspose M * Matrix.diagonal (fun i => (J.d i : ℂ)) * M =
      Matrix.diagonal (fun i => (J'.d i : ℂ)))
    (hMP : M * P = 1) : complexIsometryInv J J' M = P := by
  calc
    complexIsometryInv J J' M = complexIsometryInv J J' M * (M * P) := by
      rw [hMP, Matrix.mul_one]
    _ = (complexIsometryInv J J' M * M) * P := by rw [Matrix.mul_assoc]
    _ = P := by rw [complexIsometryInv_mul hiso, Matrix.one_mul]

/-- An entry of `U' δ U⁻¹` vanishes across a sufficiently large ordered weight gap. -/
theorem complex_triangular_conjugate_entry_zero
    {J J' : ComplexJacobiData n} {t u R : ℝ} (ht : 1 ≤ t)
    (hR : 0 ≤ R) (hS : J.IsSiegel t u) {δ : Matrix (Fin n) (Fin n) ℂ}
    (hδ : ∀ a b : Fin n, δ a b ≠ 0 → J.d a ≤ R * J.d b)
    {i k : Fin n} (hbig : t ^ n * (R * (t ^ n * J.d k)) < J.d i) :
    (J'.U * δ * J.U⁻¹) i k = 0 := by
  classical
  have htn : (0 : ℝ) ≤ t ^ n := pow_nonneg (le_trans zero_le_one ht) n
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hbk : k < b
  · rw [J.inv_upper b k hbk, mul_zero]
  · have hbk' : (b : ℕ) ≤ (k : ℕ) := Fin.le_def.1 (not_lt.1 hbk)
    have hinner : (J'.U * δ) i b = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases hai : a < i
      · rw [J'.upper i a hai, zero_mul]
      · have hia : (i : ℕ) ≤ (a : ℕ) := Fin.le_def.1 (not_lt.1 hai)
        have hzero : δ a b = 0 := by
          by_contra hne
          have h1 : J.d a ≤ R * J.d b := hδ a b hne
          have h2 : J.d i ≤ t ^ n * J.d a := J.d_le_pow_n ht hS hia
          have h3 : J.d b ≤ t ^ n * J.d k := J.d_le_pow_n ht hS hbk'
          have h4 : R * J.d b ≤ R * (t ^ n * J.d k) :=
            mul_le_mul_of_nonneg_left h3 hR
          have h5 : J.d i ≤ t ^ n * (R * (t ^ n * J.d k)) :=
            h2.trans ((mul_le_mul_of_nonneg_left h1 htn).trans
              (mul_le_mul_of_nonneg_left h4 htn))
          linarith
        rw [hzero, mul_zero]
    rw [hinner, zero_mul]

/-- Entrywise norm bound for a product of two complex matrices. -/
theorem complex_entry_norm_mul_le
    {X Y : Matrix (Fin n) (Fin n) ℂ} {a b : ℝ}
    (hX : ∀ p q, ‖X p q‖ ≤ a) (hY : ∀ p q, ‖Y p q‖ ≤ b)
    (k i : Fin n) : ‖(X * Y) k i‖ ≤ (n : ℝ) * (a * b) := by
  classical
  have ha : 0 ≤ a := (norm_nonneg (X k i)).trans (hX k i)
  rw [Matrix.mul_apply]
  calc
    ‖∑ m, X k m * Y m i‖ ≤ ∑ m, ‖X k m * Y m i‖ := norm_sum_le _ _
    _ ≤ ∑ _m : Fin n, a * b := by
      exact Finset.sum_le_sum fun m _ => by
        rw [norm_mul]
        exact mul_le_mul (hX k m) (hY m i) (norm_nonneg _) ha
    _ = (n : ℝ) * (a * b) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end GaloisForLFunctions.HTGeometry
