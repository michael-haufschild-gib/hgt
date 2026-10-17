import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Fusion

/-!
# The last surviving power of a strictly upper triangular matrix

The top possible power has one path. Its squared Hilbert--Schmidt norm is the
product of adjacent squared entries; finite AM--GM bounds it sharply by total
energy. These are ingredients for the full metric-budget Jordan theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Matrix Finset

theorem strictUpperPower_vanish {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ)
    (hT : ∀ i j, j ≤ i → T i j = 0) (k : ℕ) (i j : Fin d)
    (hij : j.val < i.val + k) : (T ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
    have hne : i ≠ j := by intro h; subst j; omega
    simp [hne]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases h : l.val < i.val + k
    · rw [ih i l h, zero_mul]
    · rw [hT l j (by change j.val ≤ l.val; omega), mul_zero]

theorem strictUpperPower_nilpotent {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ)
    (hT : ∀ i j, j ≤ i → T i j = 0) : T ^ d = 0 := by
  ext i j
  exact strictUpperPower_vanish T hT d i j (by have := j.isLt; omega)

theorem strictUpperPower_path {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ)
    (hT : ∀ i j, j ≤ i → T i j = 0) (k i : ℕ) (hik : i + k < d) :
    (T ^ k) ⟨i, by omega⟩ ⟨i + k, hik⟩ =
      ∏ r : Fin k, T ⟨i + r.val, by omega⟩ ⟨i + r.val + 1, by omega⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_eq_single (⟨i + k, by omega⟩ : Fin d)]
    · rw [ih (by omega), Fin.prod_univ_castSucc]
      rfl
    · intro l _ hl
      by_cases h : l.val < i + k
      · rw [strictUpperPower_vanish T hT k _ l h, zero_mul]
      · have hne : l.val ≠ i + k := by
          intro he
          apply hl
          exact Fin.ext he
        rw [hT l ⟨i + (k + 1), hik⟩ (by change i + (k + 1) ≤ l.val; omega),
          mul_zero]
    · simp

theorem strictUpperPower_top_energy {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hT : ∀ i j, j ≤ i → T i j = 0) :
    matHSNormSq (T ^ n) = ∏ i : Fin n, ‖T i.castSucc i.succ‖ ^ 2 := by
  have hentry : (T ^ n) 0 (Fin.last n) =
      ∏ i : Fin n, T i.castSucc i.succ := by
    convert strictUpperPower_path T hT n 0 (by omega) using 1
    · apply congrArg₂ (fun i j : Fin (n + 1) => (T ^ n) i j) <;> apply Fin.ext <;> simp
    · apply Finset.prod_congr rfl
      intro i _
      congr 1 <;> apply Fin.ext <;> simp
  unfold matHSNormSq
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · rw [Finset.sum_eq_single (Fin.last n)]
    · rw [hentry, norm_prod, Finset.prod_pow]
    · intro j _ hj
      have hjn : j.val < n := by
        have hne : j.val ≠ n := fun h => hj (Fin.ext h)
        have := j.isLt
        omega
      rw [strictUpperPower_vanish T hT n 0 j (by simpa using hjn)]
      simp
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    have hi0 : 0 < i.val := by
      have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    rw [strictUpperPower_vanish T hT n i j (by have := j.isLt; omega)]
    simp
  · simp

theorem adjacentEnergy_le_matHSNormSq {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (∑ i : Fin n, ‖T i.castSucc i.succ‖ ^ 2) ≤ matHSNormSq T := by
  rw [matHSNormSq, Fin.sum_univ_castSucc]
  apply le_trans _ (le_add_of_nonneg_right (by positivity))
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖T i.castSucc j‖)
    (Finset.mem_univ i.succ)

theorem strictUpperPower_sharp_energy_bound {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hT : ∀ i j, j ≤ i → T i j = 0) :
    (n : ℝ) ^ n * matHSNormSq (T ^ n) ≤ matHSNormSq T ^ n := by
  rw [strictUpperPower_top_energy T hT]
  have h := ChronologicalTensor.mass_product_bound n
    (fun i : Fin n => ‖T i.castSucc i.succ‖ ^ 2)
  have habs : ∀ i : Fin n, |‖T i.castSucc i.succ‖ ^ 2| = ‖T i.castSucc i.succ‖ ^ 2 :=
    fun i => abs_of_nonneg (sq_nonneg ‖T i.castSucc i.succ‖)
  simp only [habs] at h
  exact h.trans (pow_le_pow_left₀ (by positivity) (adjacentEnergy_le_matHSNormSq T) n)

end
end GaloisForLFunctions.HTGeometry
