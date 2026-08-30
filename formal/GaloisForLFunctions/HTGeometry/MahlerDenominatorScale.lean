import Mathlib

/-!
# Mahler's denominator scale

Pólya's induction for the denominators of the Taylor coefficients of a differentially algebraic
series carries the weight `∏_{j ≤ n} A_j^{⌊n/j⌋}`.  The floor exponents are exactly what makes the
weight *superadditive*: the weights of two indices divide the weight of their sum, so a convolution
of coefficients is controlled by the weight of the total index.  The same weight grows only like
`exp(C n (log n)^2)`, because `∑_{j ≤ n} n/j` is `n` times a harmonic number.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

/-- The denominator weight of Pólya's induction: a geometric factor together with the floor-powers
of the recursion constants. -/
def mahlerScale (C : ℕ) (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  C ^ n * ∏ j ∈ Finset.Icc 1 n, A j ^ (n / j)

theorem mahlerScale_pos {C : ℕ} {A : ℕ → ℕ} (hC : 0 < C) (hA : ∀ j, 0 < A j) (n : ℕ) :
    0 < mahlerScale C A n :=
  mul_pos (pow_pos hC n) (Finset.prod_pos fun j _ => pow_pos (hA j) _)

/-- Extending the product range past `n` changes nothing, because the floor exponents vanish. -/
theorem prod_mahler_extend (A : ℕ → ℕ) {n N : ℕ} (hn : n ≤ N) :
    ∏ j ∈ Finset.Icc 1 N, A j ^ (n / j) = ∏ j ∈ Finset.Icc 1 n, A j ^ (n / j) := by
  classical
  refine (Finset.prod_subset ?_ ?_).symm
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    exact ⟨hj.1, le_trans hj.2 hn⟩
  · intro j hj hjn
    simp only [Finset.mem_Icc] at hj hjn
    have hlt : n < j := by
      by_contra hcon
      exact hjn ⟨hj.1, not_lt.mp hcon⟩
    rw [Nat.div_eq_of_lt hlt, pow_zero]

/-- **Superadditivity.**  The weights of two indices divide the weight of their sum. -/
theorem mahlerScale_mul_dvd (C : ℕ) (A : ℕ → ℕ) (i j : ℕ) :
    mahlerScale C A i * mahlerScale C A j ∣ mahlerScale C A (i + j) := by
  classical
  unfold mahlerScale
  rw [prod_mahler_extend A (n := i) (N := i + j) (Nat.le_add_right _ _) |>.symm,
    prod_mahler_extend A (n := j) (N := i + j) (Nat.le_add_left _ _) |>.symm]
  have hpow : C ^ i * C ^ j = C ^ (i + j) := (pow_add C i j).symm
  calc C ^ i * (∏ k ∈ Finset.Icc 1 (i + j), A k ^ (i / k)) *
        (C ^ j * ∏ k ∈ Finset.Icc 1 (i + j), A k ^ (j / k))
      = C ^ (i + j) * ∏ k ∈ Finset.Icc 1 (i + j), (A k ^ (i / k) * A k ^ (j / k)) := by
        rw [← hpow, Finset.prod_mul_distrib]; ring
    _ ∣ C ^ (i + j) * ∏ k ∈ Finset.Icc 1 (i + j), A k ^ ((i + j) / k) := by
        refine mul_dvd_mul_left _ (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_)
        rw [← pow_add]
        exact pow_dvd_pow _ Nat.div_add_div_le_add_div

/-- **Monotonicity.**  Smaller indices have dividing weights. -/
theorem mahlerScale_dvd_of_le (C : ℕ) (A : ℕ → ℕ) {i n : ℕ} (hin : i ≤ n) :
    mahlerScale C A i ∣ mahlerScale C A n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hin
  exact dvd_trans (Dvd.intro _ rfl) (mahlerScale_mul_dvd C A i k)

theorem mahlerScale_zero (C : ℕ) (A : ℕ → ℕ) : mahlerScale C A 0 = 1 := by
  simp [mahlerScale]

/-- The constant factor is available at every positive index. -/
theorem dvd_mahlerScale_of_pos (C : ℕ) (A : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    C ∣ mahlerScale C A n := by
  refine Dvd.dvd.mul_right ?_ _
  exact dvd_pow_self C (Nat.ne_of_gt hn)

/-- **The one-step growth of the weight.**  Passing from `q - 1` to `q` gains one geometric factor
and one power of the `q`-th constant. -/
theorem mahlerScale_succ_dvd (C : ℕ) (A : ℕ → ℕ) {q : ℕ} (hq : 0 < q) :
    C * A q * mahlerScale C A (q - 1) ∣ mahlerScale C A q := by
  classical
  have hins : Finset.Icc 1 q = insert q (Finset.Icc 1 (q - 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : q ∉ Finset.Icc 1 (q - 1) := by
    simp only [Finset.mem_Icc]
    omega
  have hsplit : ∏ j ∈ Finset.Icc 1 q, A j ^ (q / j)
      = A q * ∏ j ∈ Finset.Icc 1 (q - 1), A j ^ (q / j) := by
    rw [hins, Finset.prod_insert hnot, Nat.div_self hq, pow_one]
  have hmono : (∏ j ∈ Finset.Icc 1 (q - 1), A j ^ ((q - 1) / j))
      ∣ ∏ j ∈ Finset.Icc 1 (q - 1), A j ^ (q / j) := by
    refine Finset.prod_dvd_prod_of_dvd _ _ fun j _ => ?_
    exact pow_dvd_pow _ (Nat.div_le_div_right (by omega))
  have hC : C * C ^ (q - 1) = C ^ q := by
    rw [← pow_succ']
    congr 1
    omega
  unfold mahlerScale
  rw [hsplit]
  obtain ⟨k, hk⟩ := hmono
  refine ⟨k, ?_⟩
  rw [hk, ← hC]
  ring

/-! ### The size of the weight -/

/-- The reciprocal sum over `Icc 1 n` is the `n`-th harmonic number. -/
theorem sum_inv_Icc_eq_harmonic (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, ((j : ℝ))⁻¹ = (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
      rw [Finset.sum_insert (by simp), ih, harmonic_succ]
      push_cast
      ring

/-- The total floor exponent is at most `n (1 + log n)`. -/
theorem sum_div_le_harmonic (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, ((n / j : ℕ) : ℝ) ≤ (n : ℝ) * (1 + Real.log n) := by
  have hstep : ∀ j ∈ Finset.Icc 1 n, ((n / j : ℕ) : ℝ) ≤ (n : ℝ) * ((j : ℝ))⁻¹ := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have h := Nat.cast_div_le (α := ℝ) (m := n) (n := j)
    rw [div_eq_mul_inv] at h
    exact h
  calc ∑ j ∈ Finset.Icc 1 n, ((n / j : ℕ) : ℝ)
      ≤ ∑ j ∈ Finset.Icc 1 n, (n : ℝ) * ((j : ℝ))⁻¹ := Finset.sum_le_sum hstep
    _ = (n : ℝ) * ∑ j ∈ Finset.Icc 1 n, ((j : ℝ))⁻¹ := by rw [Finset.mul_sum]
    _ = (n : ℝ) * (harmonic n : ℝ) := by rw [sum_inv_Icc_eq_harmonic]
    _ ≤ (n : ℝ) * (1 + Real.log n) := by
        refine mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) (Nat.cast_nonneg n)

/-- **The weight grows like `exp(C n (log n)^2)`.** -/
theorem log_mahlerScale_le {C : ℕ} {A : ℕ → ℕ} (hC : 0 < C) (hA : ∀ j, 0 < A j)
    {Cb d : ℝ} (hCb : 0 ≤ Cb) (hd : 0 ≤ d)
    (hbound : ∀ j, 1 ≤ j → Real.log (A j) ≤ Cb + d * Real.log j) (n : ℕ) :
    Real.log (mahlerScale C A n) ≤ (n : ℝ) * Real.log C
      + (n : ℝ) * (1 + Real.log n) * (Cb + d * Real.log n) := by
  have hApos : ∀ j, (0 : ℝ) < (A j : ℝ) := fun j => by exact_mod_cast hA j
  have hprodpos : (0 : ℝ) < ∏ j ∈ Finset.Icc 1 n, ((A j : ℝ)) ^ (n / j) :=
    Finset.prod_pos fun j _ => pow_pos (hApos j) _
  have hCpos : (0 : ℝ) < (C : ℝ) ^ n := pow_pos (by exact_mod_cast hC) n
  have hcast : ((mahlerScale C A n : ℕ) : ℝ)
      = (C : ℝ) ^ n * ∏ j ∈ Finset.Icc 1 n, ((A j : ℝ)) ^ (n / j) := by
    unfold mahlerScale
    push_cast
    ring
  rw [hcast, Real.log_mul (ne_of_gt hCpos) (ne_of_gt hprodpos), Real.log_pow,
    Real.log_prod (fun j _ => ne_of_gt (pow_pos (hApos j) _))]
  have hterm : ∀ j ∈ Finset.Icc 1 n, Real.log (((A j : ℝ)) ^ (n / j))
      ≤ ((n / j : ℕ) : ℝ) * (Cb + d * Real.log n) := by
    intro j hj
    obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.mp hj
    have hlogj : Real.log j ≤ Real.log n := by
      refine Real.log_le_log (by exact_mod_cast hj1) (by exact_mod_cast hjn)
    have h1 : Real.log (A j) ≤ Cb + d * Real.log n :=
      le_trans (hbound j hj1) (by nlinarith [hlogj, hd])
    rw [Real.log_pow]
    refine mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  have hsum : ∑ j ∈ Finset.Icc 1 n, Real.log (((A j : ℝ)) ^ (n / j))
      ≤ (∑ j ∈ Finset.Icc 1 n, ((n / j : ℕ) : ℝ)) * (Cb + d * Real.log n) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  have hlogn : 0 ≤ Real.log n ∨ n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inr h
    · exact Or.inl (Real.log_nonneg (by exact_mod_cast h))
  have hfac : 0 ≤ Cb + d * Real.log n := by
    rcases hlogn with h | h
    · nlinarith
    · subst h; simp [hCb]
  have hharm := sum_div_le_harmonic n
  nlinarith [hsum, hharm, hfac]

end GaloisForLFunctions.HTGeometry
