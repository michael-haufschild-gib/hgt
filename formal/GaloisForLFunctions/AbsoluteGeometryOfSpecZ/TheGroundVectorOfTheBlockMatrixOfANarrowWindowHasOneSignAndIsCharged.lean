import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGroundVectorOfTheNeutralPartHasOneSignAndIsCharged
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The ground vector of the block matrix of a narrow window has one sign and is charged

The block matrix `m = N + d ⊗ 1 + 1 ⊗ d` adds to the neutral part `N` the product of the two
charges. Between two blocks the neutral part is negative (jets and contacts attract) and the
product of the charges is positive (the poles repel). On a narrow window the jets win.

* **The jet at the distance `n` is at least the degree of `n`** (`blockDegree_le_xLogXDiff`):
  the second difference of `n log n` at `n` is at least `log(1 + 1/n)`, because
  `x ↦ x log(1 + 1/x)` increases (concavity of the logarithm).
* **On a window `(R, R + J]` with `4J ≤ R` the block matrix is negative off the diagonal**
  (`blockMatrix_neg_of_narrow`): for `a < b` in the window,
  `J(a, b) ≥ ½ log(1 + 1/(b − a)) ≥ 1/(2J) ≥ 2/R > d(a) + d(b)`.
* **A ground vector has one sign and is charged** (`blockMatrix_minimizer_one_sign`,
  `charges_mul_pos_of_blockMatrix_minimizer`): a vector that minimises the form of the block
  matrix among the vectors of its length has entries of one sign, since the modulus lowers the
  form strictly on a vector with entries of both signs (`sum_kernel_abs_lt`); if it is not zero,
  both its charges are different from zero and of one sign.

So at every block size the ground vector of the full block matrix of a window of ratio at most
`5/4` is charged.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Degrees and jets -/

/-- `log(1 + 1/n) ≥ 1/(n + 1)`. -/
theorem inv_succ_le_blockDegree {n : ℕ} (hn : 1 ≤ n) : 1 / ((n : ℝ) + 1) ≤ blockDegree n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
  rw [Real.log_div (by positivity) hn0.ne'] at h
  have e2 : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / ((n : ℝ) + 1) := by
    rw [inv_div]
    field_simp
    ring
  rw [e2] at h
  rw [blockDegree, e]
  exact h

/-- `log(1 + 1/n) ≤ 1/n`. -/
theorem blockDegree_le_inv {n : ℕ} (hn : 1 ≤ n) : blockDegree n ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
  rw [Real.log_div (by positivity) hn0.ne'] at h
  have e2 : ((n : ℝ) + 1) / n - 1 = 1 / n := by
    field_simp
    ring
  rw [blockDegree, e]
  linarith

/-- **The jet at the distance `n` is at least the degree of `n`**: the second difference of
`n log n` at `n` is at least `log(1 + 1/n)`. -/
theorem blockDegree_le_xLogXDiff {n : ℕ} (hn : 1 ≤ n) : blockDegree n ≤ xLogXDiff n := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have e1 : blockDegree 1 = Real.log 2 := by
      simp only [blockDegree]
      norm_num
    have e2 : xLogXDiff 1 = 2 * Real.log 2 := by
      simp only [xLogXDiff, xLogX]
      norm_num
    rw [e1, e2]
    linarith
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast h2
      linarith
    have e1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have e2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
    -- concavity of the logarithm between `1` and `n/(n − 1)`
    have hconc := strictConcaveOn_log_Ioi.concaveOn.2
      (show (1 : ℝ) ∈ Set.Ioi 0 from Set.mem_Ioi.mpr one_pos)
      (show (n : ℝ) / ((n : ℝ) - 1) ∈ Set.Ioi (0 : ℝ) from Set.mem_Ioi.mpr (by positivity))
      (show (0 : ℝ) ≤ 1 / n by positivity) (show (0 : ℝ) ≤ ((n : ℝ) - 1) / n by positivity)
      (by field_simp; ring)
    have hmean : (1 / (n : ℝ)) • (1 : ℝ) + (((n : ℝ) - 1) / n) • ((n : ℝ) / ((n : ℝ) - 1)) =
        ((n : ℝ) + 1) / n := by
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [hmean, Real.log_one, smul_zero, zero_add, smul_eq_mul, Real.log_div hn0.ne' hn1.ne',
      Real.log_div (by positivity) hn0.ne'] at hconc
    -- `(n − 1) log(n/(n − 1)) ≤ n log((n + 1)/n)`
    have hmul : ((n : ℝ) - 1) * (Real.log n - Real.log ((n : ℝ) - 1)) ≤
        n * (Real.log ((n : ℝ) + 1) - Real.log n) := by
      have h := mul_le_mul_of_nonneg_left hconc hn0.le
      have e : (n : ℝ) * (((n : ℝ) - 1) / n * (Real.log n - Real.log ((n : ℝ) - 1))) =
          ((n : ℝ) - 1) * (Real.log n - Real.log ((n : ℝ) - 1)) := by field_simp
      linarith
    simp only [xLogXDiff, xLogX, blockDegree]
    rw [e1, e2]
    linarith

/-- **On a narrow window the block matrix is negative off the diagonal.** For `a < b` among the
blocks of `(R, R + J]` with `4J ≤ R` the jets exceed the two degrees. -/
theorem blockMatrix_neg_of_narrow {R J Q a b : ℕ} (hR : 1 ≤ R) (hJ : 4 * J ≤ R) (ha : R ≤ a)
    (hab : a < b) (hb : b < R + J) : blockMatrix Q a b < 0 := by
  rw [blockMatrix_of_lt hab]
  have hC : 0 ≤ floorContact Q a b := Finset.sum_nonneg fun k _ => by
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
    · exact le_rfl
  have ha1 : 1 ≤ a := le_trans hR ha
  have hb1 : 1 ≤ b := by omega
  have hd : 1 ≤ b - a := by omega
  have hJ1 : 1 ≤ J := by omega
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ1
  -- the jets: at least `1/(2J)`
  have hjet : 1 / (2 * (J : ℝ)) ≤ blockJet a b := by
    unfold blockJet
    have h1 := xLogXDiff_pos (n := a + b + 1) (by omega)
    have h2 := blockDegree_le_xLogXDiff hd
    have h3 := inv_succ_le_blockDegree hd
    have h4 : 1 / (J : ℝ) ≤ 1 / (((b - a : ℕ) : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have : b - a + 1 ≤ J := by omega
      exact_mod_cast this
    have e : 1 / (2 * (J : ℝ)) = 1 / (J : ℝ) / 2 := by ring
    rw [e]
    linarith
  -- the degrees: below `2/R ≤ 1/(2J)`
  have hdeg : blockDegree a + blockDegree b < 1 / (2 * (J : ℝ)) := by
    have h1 := blockDegree_le_inv ha1
    have h2 := blockDegree_le_inv hb1
    have ha' : (R : ℝ) ≤ a := by exact_mod_cast ha
    have hb' : (R : ℝ) + 1 ≤ b := by exact_mod_cast (show R + 1 ≤ b by omega)
    have hJ' : 4 * (J : ℝ) ≤ R := by exact_mod_cast hJ
    have h3 : 1 / (a : ℝ) ≤ 1 / R := one_div_le_one_div_of_le hR0 ha'
    have h4 : 1 / (b : ℝ) < 1 / R := one_div_lt_one_div_of_lt hR0 (by linarith)
    have h5 : 2 / (R : ℝ) ≤ 1 / (2 * (J : ℝ)) := by
      rw [div_le_div_iff₀ hR0 (by positivity)]
      linarith
    have e : 2 / (R : ℝ) = 1 / R + 1 / R := by ring
    linarith
  linarith

/-- The entries of the block matrix of a narrow window off the diagonal are negative. -/
theorem blockMatrix_neg_of_window {R J Q : ℕ} (hR : 1 ≤ R) (hJ : 4 * J ≤ R) {j l : ℕ}
    (hj : j < J) (hl : l < J) (hjl : j ≠ l) : blockMatrix Q (R + j) (R + l) < 0 := by
  rcases lt_or_gt_of_ne hjl with h | h
  · exact blockMatrix_neg_of_narrow hR hJ (Nat.le_add_right R j) (by omega) (by omega)
  · rw [blockMatrix_comm]
    exact blockMatrix_neg_of_narrow hR hJ (Nat.le_add_right R l) (by omega) (by omega)

/-! ### A matrix that is negative off the diagonal -/

section Kernel

variable (K : ℕ → ℕ → ℝ) {R J : ℕ}

/-- Termwise, the modulus does not raise the form of a matrix that is negative off the
diagonal. -/
theorem abs_mul_kernel_le (hK : ∀ j l, j < J → l < J → j ≠ l → K (R + j) (R + l) < 0)
    (σ : ℕ → ℝ) {j l : ℕ} (hj : j < J) (hl : l < J) :
    |σ j| * |σ l| * K (R + j) (R + l) ≤ σ j * σ l * K (R + j) (R + l) := by
  by_cases hjl : j = l
  · subst hjl
    rw [abs_mul_abs_self]
  · have hneg := hK j l hj hl hjl
    have habs : σ j * σ l ≤ |σ j| * |σ l| := by
      rw [← abs_mul]
      exact le_abs_self _
    nlinarith

/-- **The modulus lowers the form strictly on a vector with entries of both signs.** -/
theorem sum_kernel_abs_lt (hK : ∀ j l, j < J → l < J → j ≠ l → K (R + j) (R + l) < 0)
    (σ : ℕ → ℝ) {j₀ l₀ : ℕ} (hj : j₀ < J) (hl : l₀ < J) (hpos : 0 < σ j₀) (hneg : σ l₀ < 0) :
    ∑ j ∈ range J, ∑ l ∈ range J, |σ j| * |σ l| * K (R + j) (R + l) <
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * K (R + j) (R + l) := by
  have hne : j₀ ≠ l₀ := by
    rintro rfl
    exact lt_asymm hpos hneg
  have hN := hK j₀ l₀ hj hl hne
  refine Finset.sum_lt_sum
    (fun j hj' => Finset.sum_le_sum fun l hl' =>
      abs_mul_kernel_le K hK σ (Finset.mem_range.mp hj') (Finset.mem_range.mp hl'))
    ⟨j₀, Finset.mem_range.mpr hj,
      Finset.sum_lt_sum (fun l hl' => abs_mul_kernel_le K hK σ hj (Finset.mem_range.mp hl'))
        ⟨l₀, Finset.mem_range.mpr hl, ?_⟩⟩
  rw [abs_of_pos hpos, abs_of_neg hneg]
  have h := mul_pos (mul_pos hpos (neg_pos.mpr hneg)) (neg_pos.mpr hN)
  nlinarith [h]

/-- **A minimiser of the form among the vectors of its length has entries of one sign.** -/
theorem kernel_minimizer_one_sign (hK : ∀ j l, j < J → l < J → j ≠ l → K (R + j) (R + l) < 0)
    {σ : ℕ → ℝ}
    (hmin : ∀ τ : ℕ → ℝ, ∑ j ∈ range J, τ j ^ 2 = ∑ j ∈ range J, σ j ^ 2 →
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * K (R + j) (R + l) ≤
        ∑ j ∈ range J, ∑ l ∈ range J, τ j * τ l * K (R + j) (R + l)) :
    (∀ j, j < J → 0 ≤ σ j) ∨ (∀ j, j < J → σ j ≤ 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨h1, h2⟩ := h
  push Not at h1 h2
  obtain ⟨l₀, hl, hneg⟩ := h1
  obtain ⟨j₀, hj, hpos⟩ := h2
  have hlt := sum_kernel_abs_lt K hK σ hj hl hpos hneg
  have hle := hmin (fun j => |σ j|) (Finset.sum_congr rfl fun j _ => sq_abs (σ j))
  exact absurd hle (not_le.mpr hlt)

end Kernel

/-- A vector with entries of one sign, not zero on the window, has two charges of one sign. -/
theorem charges_mul_pos_of_one_sign {R J : ℕ} (hR : 1 ≤ R) {σ : ℕ → ℝ}
    (h : (∀ j, j < J → 0 ≤ σ j) ∨ (∀ j, j < J → σ j ≤ 0)) {j₀ : ℕ} (hj : j₀ < J)
    (hne : σ j₀ ≠ 0) :
    0 < (∑ j ∈ range J, σ j) * (∑ j ∈ range J, σ j * blockDegree (R + j)) := by
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := charges_pos_of_nonneg hR h hj (lt_of_le_of_ne (h j₀ hj) hne.symm)
    exact mul_pos h1 h2
  · obtain ⟨h1, h2⟩ := charges_pos_of_nonneg (σ := fun j => -σ j) hR
      (fun j hj' => neg_nonneg.mpr (h j hj')) hj
      (neg_pos.mpr (lt_of_le_of_ne (h j₀ hj) hne))
    have h1' : ∑ j ∈ range J, σ j < 0 := by
      have e : ∑ j ∈ range J, -σ j = -∑ j ∈ range J, σ j := Finset.sum_neg_distrib _
      rw [e] at h1
      exact neg_pos.mp h1
    have h2' : ∑ j ∈ range J, σ j * blockDegree (R + j) < 0 := by
      have e : ∑ j ∈ range J, -σ j * blockDegree (R + j) =
          -∑ j ∈ range J, σ j * blockDegree (R + j) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => neg_mul _ _
      rw [e] at h2
      exact neg_pos.mp h2
    exact mul_pos_of_neg_of_neg h1' h2'

/-! ### The ground vector of a narrow window -/

/-- **On a narrow window a ground vector of the block matrix has entries of one sign.** -/
theorem blockMatrix_minimizer_one_sign {Q R J : ℕ} (hR : 1 ≤ R) (hJ : 4 * J ≤ R) {σ : ℕ → ℝ}
    (hmin : ∀ τ : ℕ → ℝ, ∑ j ∈ range J, τ j ^ 2 = ∑ j ∈ range J, σ j ^ 2 →
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) ≤
        ∑ j ∈ range J, ∑ l ∈ range J, τ j * τ l * blockMatrix Q (R + j) (R + l)) :
    (∀ j, j < J → 0 ≤ σ j) ∨ (∀ j, j < J → σ j ≤ 0) :=
  kernel_minimizer_one_sign (blockMatrix Q)
    (fun _ _ hj hl hjl => blockMatrix_neg_of_window hR hJ hj hl hjl) hmin

/-- **On a narrow window a ground vector of the block matrix is charged**: both charges are
different from zero and have one sign. -/
theorem charges_mul_pos_of_blockMatrix_minimizer {Q R J : ℕ} (hR : 1 ≤ R) (hJ : 4 * J ≤ R)
    {σ : ℕ → ℝ}
    (hmin : ∀ τ : ℕ → ℝ, ∑ j ∈ range J, τ j ^ 2 = ∑ j ∈ range J, σ j ^ 2 →
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) ≤
        ∑ j ∈ range J, ∑ l ∈ range J, τ j * τ l * blockMatrix Q (R + j) (R + l))
    {j₀ : ℕ} (hj : j₀ < J) (hne : σ j₀ ≠ 0) :
    0 < (∑ j ∈ range J, σ j) * (∑ j ∈ range J, σ j * blockDegree (R + j)) :=
  charges_mul_pos_of_one_sign hR (blockMatrix_minimizer_one_sign hR hJ hmin) hj hne

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
