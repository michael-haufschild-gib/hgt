import GaloisForLFunctions.RHTower.NearDiagonalPhaseCurvature

/-!
# The clean dyadic block estimate

The raw second-derivative bound `(2·N·90·λ+3)(3/√λ+1)` on a block of `N ≤ M` unit-spaced points at
scale `M` collapses, using `λ ≤ 1`, to `720 M √λ + 12/√λ`, which is exactly the two-term shape of
the card's equation (3): the first term decreases geometrically along dyadic blocks, the second
increases geometrically.
-/

namespace RHTower

noncomputable section

/-- The clean dyadic block bound `720 √(T r/(36 π M)) + 12 √(36 π M³/(T r))`. -/
def nearDiagonalBlockBound (T r M : ℝ) : ℝ :=
  720 * Real.sqrt (T * r / (36 * Real.pi * M))
    + 12 * Real.sqrt (36 * Real.pi * M ^ 3 / (T * r))

theorem mul_sqrt_nearDiagonalLambda {T r M : ℝ} (hM : 0 < M) :
    M * Real.sqrt (nearDiagonalLambda T r M) = Real.sqrt (T * r / (36 * Real.pi * M)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h : M * Real.sqrt (nearDiagonalLambda T r M)
      = Real.sqrt (M ^ 2 * nearDiagonalLambda T r M) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM.le]
  rw [h]
  congr 1
  rw [nearDiagonalLambda]
  field_simp

theorem inv_sqrt_nearDiagonalLambda {T r M : ℝ} (hT : 0 < T) (hr : 0 < r) (hM : 0 < M) :
    1 / Real.sqrt (nearDiagonalLambda T r M)
      = Real.sqrt (36 * Real.pi * M ^ 3 / (T * r)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlam : 0 < nearDiagonalLambda T r M := nearDiagonalLambda_pos hT hr hM
  rw [one_div, ← Real.sqrt_inv, nearDiagonalLambda]
  congr 1
  field_simp

theorem block_algebra {N M s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hN0 : 0 ≤ N) (hNM : N ≤ M) :
    (2 * N * 90 * s ^ 2 + 3) * (3 / s + 1) ≤ 720 * (M * s) + 12 * (1 / s) := by
  have hM0 : 0 ≤ M := le_trans hN0 hNM
  have hsq : s ^ 2 ≤ s := by nlinarith
  have hinv : 1 ≤ 1 / s := by
    rw [le_div_iff₀ hs0]
    linarith
  have hexp : (2 * N * 90 * s ^ 2 + 3) * (3 / s + 1)
      = 540 * N * s + 180 * N * s ^ 2 + 9 * (1 / s) + 3 := by
    field_simp
    ring
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_right hNM hs0.le, mul_le_mul_of_nonneg_left hsq hN0,
    mul_le_mul_of_nonneg_right hNM (le_of_lt hs0)]

/-- **The clean dyadic block estimate.** -/
theorem norm_nearDiagonalBlock_le_bound {T r M : ℝ} (hT : 0 < T) (hr : 0 < r) (hM : 0 < M)
    (hrM : r ≤ M) {N : ℕ} (hN : 1 ≤ N) (hspan : ((N : ℕ) - 1 : ℕ) ≤ M) (hNM : (N : ℝ) ≤ M)
    (hlam1 : nearDiagonalLambda T r M ≤ 1) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * nearDiagonalPhase T r (M + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ nearDiagonalBlockBound T r M := by
  have hlam0 : 0 < nearDiagonalLambda T r M := nearDiagonalLambda_pos hT hr hM
  set s : ℝ := Real.sqrt (nearDiagonalLambda T r M) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hlam0
  have hs1 : s ≤ 1 := by
    rw [hsdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hlam1
  have hssq : s ^ 2 = nearDiagonalLambda T r M := Real.sq_sqrt hlam0.le
  have hraw := norm_nearDiagonalBlock_le hT hr hM hrM hN hspan hlam1
  refine hraw.trans ?_
  have hgoal : (2 * (N : ℝ) * 90 * nearDiagonalLambda T r M + 3)
      * (3 / s + 1) ≤ 720 * (M * s) + 12 * (1 / s) := by
    have h := block_algebra hs0 hs1 (Nat.cast_nonneg N) hNM
    rwa [hssq] at h
  refine hgoal.trans (le_of_eq ?_)
  rw [nearDiagonalBlockBound, hsdef, mul_sqrt_nearDiagonalLambda hM,
    ← inv_sqrt_nearDiagonalLambda hT hr hM]

end

end RHTower
