import GaloisForLFunctions.HTGeometry.SiegelEntryBoundSiegel

/-!
# The weighted isometry is bounded

The weighted isometry `M = U γ (U')⁻¹` carries one Jacobi diagonal to the other, so its inverse is
the weighted transpose: `(M⁻¹)ᵢₖ = dₖ Mₖᵢ / d'ᵢ`.  The inverse is also `U' γ⁻¹ U⁻¹`, and both
triangular factors preserve the order of indices, so an entry of the inverse vanishes as soon as its
row weight exceeds its column weight by more than the integrality threshold of `γ⁻¹`.

Consequently `Mₖᵢ` vanishes whenever `d'ᵢ` exceeds `dₖ` by more than that threshold, and where it does
not vanish the isometry relation bounds it.  So `M` is bounded, and with it `γ = U⁻¹ M U'`.

* `isometryInv` : the weighted transpose.
* `isometryInv_eq` : **it is the inverse.**
* `isometry_entry_zero` : **the vanishing.**
* `entry_abs_mul_le` : an entrywise bound for a product.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The weighted transpose of a matrix relative to two positive diagonals. -/
noncomputable def isometryInv (J J' : JacobiData n) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => J.d k * M k i / J'.d i

/-- **The weighted transpose is a left inverse of a weighted isometry.** -/
theorem isometryInv_mul {J J' : JacobiData n} {M : Matrix (Fin n) (Fin n) ℝ}
    (hiso : Mᵀ * Matrix.diagonal J.d * M = Matrix.diagonal J'.d) :
    isometryInv J J' M * M = 1 := by
  classical
  have hmul : ∀ a b : Fin n, (Mᵀ * Matrix.diagonal J.d) a b = M b a * J.d b := by
    intro a b
    rw [Matrix.mul_apply,
      Finset.sum_eq_single b (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
        (fun hcon => absurd (Finset.mem_univ b) hcon),
      Matrix.transpose_apply, Matrix.diagonal_apply_eq]
  have hexp : ∀ i j : Fin n, (∑ k, M k i * J.d k * M k j) = Matrix.diagonal J'.d i j := by
    intro i j
    have h := congrFun (congrFun hiso i) j
    rw [Matrix.mul_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => by rw [hmul]
  ext i j
  rw [Matrix.mul_apply]
  have hstep : (∑ k, isometryInv J J' M i k * M k j)
      = (∑ k, M k i * J.d k * M k j) / J'.d i := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by
      show J.d k * M k i / J'.d i * M k j = _
      ring
  rw [hstep, hexp i j]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, div_self (ne_of_gt (J'.pos i)), Matrix.one_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, zero_div, Matrix.one_apply_ne hij]

/-- **The weighted transpose is the inverse.** -/
theorem isometryInv_eq {J J' : JacobiData n} {M P : Matrix (Fin n) (Fin n) ℝ}
    (hiso : Mᵀ * Matrix.diagonal J.d * M = Matrix.diagonal J'.d) (hMP : M * P = 1) :
    isometryInv J J' M = P := by
  calc isometryInv J J' M = isometryInv J J' M * (M * P) := by rw [hMP, Matrix.mul_one]
    _ = (isometryInv J J' M * M) * P := by rw [Matrix.mul_assoc]
    _ = P := by rw [isometryInv_mul hiso, Matrix.one_mul]

/-- **An entry of `U' δ U⁻¹` vanishes once its row weight dominates its column weight.**  Both
triangular factors move indices in the direction that improves the weight comparison, so a nonzero
entry of `δ` would contradict the weight gap. -/
theorem triangular_conjugate_entry_zero {J J' : JacobiData n} {t u R : ℝ} (ht : 1 ≤ t)
    (hR : 0 ≤ R) (hS : J.IsSiegel t u) {δ : Matrix (Fin n) (Fin n) ℝ}
    (hδ : ∀ a b : Fin n, δ a b ≠ 0 → J.d a ≤ R * J.d b)
    {i k : Fin n} (hbig : t ^ n * (R * (t ^ n * J.d k)) < J.d i) :
    (J'.U * δ * (J.U)⁻¹) i k = 0 := by
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
          have h4 : R * J.d b ≤ R * (t ^ n * J.d k) := mul_le_mul_of_nonneg_left h3 hR
          have h5 : J.d i ≤ t ^ n * (R * (t ^ n * J.d k)) :=
            le_trans h2 (le_trans (mul_le_mul_of_nonneg_left h1 htn)
              (mul_le_mul_of_nonneg_left h4 htn))
          linarith
        rw [hzero, mul_zero]
    rw [hinner, zero_mul]

/-- An entrywise bound for a product of matrices. -/
theorem entry_abs_mul_le {X Y : Matrix (Fin n) (Fin n) ℝ} {a b : ℝ}
    (hX : ∀ p q, |X p q| ≤ a) (hY : ∀ p q, |Y p q| ≤ b) (k i : Fin n) :
    |(X * Y) k i| ≤ (n : ℝ) * (a * b) := by
  classical
  have ha : (0 : ℝ) ≤ a := le_trans (abs_nonneg _) (hX k i)
  have hb : (0 : ℝ) ≤ b := le_trans (abs_nonneg _) (hY k i)
  rw [Matrix.mul_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ m ∈ (Finset.univ : Finset (Fin n)), |X k m * Y m i| ≤ a * b := by
    intro m _
    rw [abs_mul]
    exact mul_le_mul (hX k m) (hY m i) (abs_nonneg _) ha
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end GaloisForLFunctions.HTGeometry
