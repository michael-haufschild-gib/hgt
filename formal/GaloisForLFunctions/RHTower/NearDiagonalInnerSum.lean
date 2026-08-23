import GaloisForLFunctions.RHTower.NearDiagonalGeometricCollapse

/-!
# The near-diagonal inner sum bound

Choosing the number of dyadic blocks minimally turns the symbolic top-scale sum into the card's
`B^{3/2}` term, giving equation (4):

`|Σ_{A ≤ m < B} e(F_r(m))| ≪ √(T r / A) + B^{3/2} / √(T r)`.
-/

namespace RHTower

noncomputable section

theorem exists_dyadic_cover_nat (A B : ℕ) (hA : 1 ≤ A) : ∃ J : ℕ, B ≤ A * 2 ^ J := by
  refine ⟨B, ?_⟩
  calc B ≤ 2 ^ B := (Nat.lt_two_pow_self).le
    _ = 1 * 2 ^ B := (one_mul _).symm
    _ ≤ A * 2 ^ B := Nat.mul_le_mul_right _ hA

/-- **Equation (4).**  The inner near-diagonal sum over an arbitrary range. -/
theorem norm_nearDiagonalSum_le_final {T r : ℝ} (hT : 0 < T) (hr : 0 < r) (A B : ℕ)
    (hA : 1 ≤ A) (hrA : r ≤ (A : ℝ)) (hlam : nearDiagonalLambda T r (A : ℝ) ≤ 1) :
    ‖nearDiagonalSum T r A B‖
      ≤ 2500 * Real.sqrt (T * r / (36 * Real.pi * A))
        + 22 * Real.sqrt (36 * Real.pi / (T * r)) * Real.sqrt (((B : ℝ)) ^ 3) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs2 : 0 ≤ Real.sqrt (36 * Real.pi / (T * r)) := Real.sqrt_nonneg _
  have hs1 : 0 ≤ Real.sqrt (T * r / (36 * Real.pi * A)) := Real.sqrt_nonneg _
  by_cases hBA : B ≤ A
  · rw [nearDiagonalSum, Finset.Ico_eq_empty_of_le hBA, Finset.sum_empty, norm_zero]
    have h3 : 0 ≤ Real.sqrt (((B : ℝ)) ^ 3) := Real.sqrt_nonneg _
    nlinarith
  · have hAB : A < B := Nat.lt_of_not_le hBA
    set Jmin := Nat.find (exists_dyadic_cover_nat A B hA) with hJmin
    have hcover : B ≤ A * 2 ^ Jmin := Nat.find_spec (exists_dyadic_cover_nat A B hA)
    have hJpos : 1 ≤ Jmin := by
      by_contra hcon
      have hJ0 : Jmin = 0 := by omega
      rw [hJ0, pow_zero, mul_one] at hcover
      omega
    have htop : (A : ℝ) * 2 ^ Jmin ≤ 2 * (B : ℝ) := by
      obtain ⟨j, hj⟩ : ∃ j, Jmin = j + 1 := ⟨Jmin - 1, by omega⟩
      have hjlt : j < Nat.find (exists_dyadic_cover_nat A B hA) := by
        rw [← hJmin, hj]
        omega
      have hnot : ¬ (B ≤ A * 2 ^ j) := Nat.find_min (exists_dyadic_cover_nat A B hA) hjlt
      have hlt : A * 2 ^ j < B := Nat.lt_of_not_le hnot
      have hcast : ((A * 2 ^ j : ℕ) : ℝ) < (B : ℝ) := by exact_mod_cast hlt
      push_cast at hcast
      rw [hj, show (A : ℝ) * 2 ^ (j + 1) = 2 * ((A : ℝ) * 2 ^ j) by ring]
      linarith
    have hmain := norm_nearDiagonalSum_le hT hr Jmin A B hA hrA hcover hlam
    refine hmain.trans ?_
    have hcol := nearDiagonalTopSum_le A Jmin
    have hmono : Real.sqrt (((A : ℝ) * 2 ^ Jmin) ^ 3) ≤ Real.sqrt ((2 * (B : ℝ)) ^ 3) := by
      refine Real.sqrt_le_sqrt ?_
      have hnn : (0 : ℝ) ≤ (A : ℝ) * 2 ^ Jmin := by positivity
      exact pow_le_pow_left₀ hnn htop 3
    have hcube : Real.sqrt ((2 * (B : ℝ)) ^ 3) = 2 * Real.sqrt 2 * Real.sqrt (((B : ℝ)) ^ 3) := by
      have hB : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
      rw [show (2 * (B : ℝ)) ^ 3 = ((B : ℝ)) ^ 3 * 8 by ring, Real.sqrt_mul (by positivity)]
      have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
        rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]
      rw [h8]
      ring
    have hsq2 : Real.sqrt 2 ≤ 1.5 := by
      rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hfin : nearDiagonalTopSum A Jmin ≤ (9 / 5 : ℝ) * Real.sqrt (((B : ℝ)) ^ 3) := by
      refine hcol.trans ?_
      rw [hcube] at hmono
      have hB3 : 0 ≤ Real.sqrt (((B : ℝ)) ^ 3) := Real.sqrt_nonneg _
      nlinarith [hmono, hB3]
    have hprod : 12 * Real.sqrt (36 * Real.pi / (T * r)) * nearDiagonalTopSum A Jmin
        ≤ 22 * Real.sqrt (36 * Real.pi / (T * r)) * Real.sqrt (((B : ℝ)) ^ 3) := by
      have h12 : (0 : ℝ) ≤ 12 * Real.sqrt (36 * Real.pi / (T * r)) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hfin h12
      have hQB : (0 : ℝ) ≤ Real.sqrt (36 * Real.pi / (T * r)) * Real.sqrt (((B : ℝ)) ^ 3) :=
        mul_nonneg hs2 (Real.sqrt_nonneg _)
      linarith [hmul, hQB]
    linarith [hmain, hprod]

end

end RHTower
