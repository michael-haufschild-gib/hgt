import GaloisForLFunctions.ArithmeticOrientationTheory.TheRatioPartDecomposesOverCosets

/-!
# The tower odd side is a Cholesky energy minus the mass

The coset law (`towerOddPrimeSide_eq`) writes the odd prime side of the tower of `p` as
`log p · (2 Σ_{a'} T_p(q|_{a'}) − (S_p(q)² − q(1)²))`: one-sided Toeplitz forms with kernel
`r^k`, `r = p^{−1/2}`, on the `p`-free cosets, against one Hankel square.  The Toeplitz form is the
off-diagonal half of the KMS form `Σ_{i,j} r^{|i−j|} u_i u_j`, whose Cholesky (innovation)
decomposition is

  `Σ u_i² + 2 Σ_{k ≥ 1} r^k Σ_i u_i u_{i+k} = v_0² + (1 − r²) Σ_{j ≥ 1} v_j²`,
  `v_j = Σ_{i ≥ j} r^{i−j} u_i`  (`kms_cholesky`).

On the unit coset `v_0 = S_p(q)`: **the frustrating Hankel square is exactly the zeroth Cholesky
mode of the unit coset**, and it cancels.  What remains (`towerOddPrimeSide_eq_cholesky`) is

  `log p · [Σ_{a' ≠ 1} S_p(q|_{a'})² + (1 − 1/p) Σ_{a'} Σ_{j ≥ 1} v_j(q|_{a'})² − Σ_{2 ≤ n ≤ X} q(n)²]`:

a sum of squares minus the `ℓ²` mass of the profile off `1`.  So the tower odd side is at least
`−log p · Σ_{n ≥ 2} q(n)²` (`towerOddPrimeSide_ge`), with all orientation carried by squares.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### The KMS–Cholesky identity -/

/-- Backward weighted tails `v_j = Σ_{j ≤ i ≤ M} r^{i−j} u_i`. -/
def kmsTail (r : ℝ) (u : ℕ → ℝ) (M j : ℕ) : ℝ := ∑ i ∈ Ico j (M + 1), r ^ (i - j) * u i

theorem kmsTail_eq_of_le (r : ℝ) (u : ℕ → ℝ) {M j : ℕ} (hj : j ≤ M) :
    kmsTail r u M j = u j + r * kmsTail r u M (j + 1) := by
  unfold kmsTail
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : j < M + 1), Nat.sub_self, pow_zero, one_mul,
    mul_sum]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [mem_Ico] at hi
  rw [← mul_assoc, ← pow_succ', show i - (j + 1) + 1 = i - j by omega]

theorem kmsTail_eq_zero (r : ℝ) (u : ℕ → ℝ) {M j : ℕ} (hj : M < j) : kmsTail r u M j = 0 := by
  unfold kmsTail; rw [Ico_eq_empty (by omega), sum_empty]

/-- The lag sums are the shifted tails: `Σ_{1 ≤ k ≤ L} r^k u_{i+k} = r v_{i+1}`. -/
theorem lag_sum_eq (r : ℝ) {u : ℕ → ℝ} {M L : ℕ} (hu : ∀ i, M < i → u i = 0) (hL : M ≤ L)
    (i : ℕ) : ∑ k ∈ Icc 1 L, r ^ k * u (i + k) = r * kmsTail r u M (i + 1) := by
  by_cases hi : M ≤ i
  · rw [kmsTail_eq_zero r u (by omega), mul_zero]
    exact sum_eq_zero fun k hk => by rw [mem_Icc] at hk; rw [hu _ (by omega), mul_zero]
  push Not at hi
  unfold kmsTail
  rw [Finset.sum_Ico_eq_sum_range, mul_sum,
    show (Icc 1 L : Finset ℕ) = Ico 1 (M - i + 1) ∪ Ico (M - i + 1) (L + 1) by
      ext k; simp only [mem_Icc, mem_union, mem_Ico]; omega,
    sum_union (disjoint_left.2 fun k hk hk' => by simp only [mem_Ico] at hk hk'; omega)]
  rw [sum_eq_zero (s := Ico (M - i + 1) (L + 1)) fun k hk => by
    rw [mem_Ico] at hk; rw [hu _ (by omega), mul_zero], add_zero,
    Finset.sum_Ico_eq_sum_range, show M - i + 1 - 1 = M + 1 - (i + 1) by omega]
  refine sum_congr rfl fun m _ => ?_
  rw [show i + 1 + m - (i + 1) = m by omega, show i + (1 + m) = i + 1 + m by omega, pow_add,
    pow_one]
  ring

/-- **The KMS–Cholesky identity** for a sequence supported on `[0, M]`, `L ≥ M`. -/
theorem kms_cholesky (r : ℝ) {u : ℕ → ℝ} {M L : ℕ} (hu : ∀ i, M < i → u i = 0) (hL : M ≤ L) :
    ∑ i ∈ range (M + 1), u i ^ 2 + 2 * ∑ k ∈ Icc 1 L, r ^ k * ∑ i ∈ range (M + 1), u i * u (i + k) =
      kmsTail r u M 0 ^ 2 + (1 - r ^ 2) * ∑ j ∈ range M, kmsTail r u M (j + 1) ^ 2 := by
  set v := kmsTail r u M
  have hcross : ∑ k ∈ Icc 1 L, r ^ k * ∑ i ∈ range (M + 1), u i * u (i + k) =
      ∑ i ∈ range (M + 1), u i * (r * v (i + 1)) := by
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [← lag_sum_eq r hu hL i, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have hterm : ∀ i ∈ range (M + 1), u i ^ 2 + 2 * (u i * (r * v (i + 1))) =
      v i ^ 2 - r ^ 2 * v (i + 1) ^ 2 := fun i hi => by
    have hv : v i = u i + r * v (i + 1) :=
      kmsTail_eq_of_le r u (Nat.lt_succ_iff.1 (mem_range.1 hi))
    rw [hv]; ring
  have h0 : v (M + 1) = 0 := kmsTail_eq_zero r u (by omega)
  rw [hcross, mul_sum, ← sum_add_distrib, sum_congr rfl hterm, sum_sub_distrib, ← mul_sum,
    sum_range_succ' (fun i => v i ^ 2), sum_range_succ (fun i => v (i + 1) ^ 2), h0]
  ring

/-! ### The tower odd side -/

/-- The tails of the coset `a'` in the tower of `p`, with `r = p^{−1/2}`. -/
def cosetTail (q : ℕ → ℝ) (p X a' j : ℕ) : ℝ :=
  kmsTail ((p : ℝ) ^ (-(1 / 2 : ℝ))) (fun i => q (p ^ i * a')) (Nat.log p X) j

theorem rpow_neg_half_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p : ℝ) ^ (-(k : ℝ) / 2) = ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact_mod_cast hp.pos.le)]
  congr 1; ring

theorem coset_vanishes {q : ℕ → ℝ} {X : ℕ} (hq : ∀ n, X < n → q n = 0) {p : ℕ} (hp : p.Prime)
    {a' : ℕ} (ha' : 1 ≤ a') (i : ℕ) (hi : Nat.log p X < i) : q (p ^ i * a') = 0 := by
  refine hq _ (lt_of_lt_of_le ?_ (Nat.le_mul_of_pos_right _ ha'))
  exact lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp.one_lt X)
    (Nat.pow_le_pow_right hp.pos hi)

/-- **Cholesky form of a coset Toeplitz form.** -/
theorem two_mul_cosetToeplitz {q : ℕ → ℝ} {X : ℕ} (hq : ∀ n, X < n → q n = 0) {p : ℕ}
    (hp : p.Prime) {L : ℕ} (hL : Nat.log p X ≤ L) {a' : ℕ} (ha' : 1 ≤ a') :
    2 * cosetToeplitz q p X L a' =
      cosetTail q p X a' 0 ^ 2 + (1 - 1 / (p : ℝ)) *
        ∑ j ∈ range (Nat.log p X), cosetTail q p X a' (j + 1) ^ 2 -
        ∑ i ∈ range (Nat.log p X + 1), q (p ^ i * a') ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr2 : ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (p : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num [Real.rpow_neg_one]
  have h := kms_cholesky ((p : ℝ) ^ (-(1 / 2 : ℝ))) (u := fun i => q (p ^ i * a'))
    (M := Nat.log p X) (fun i hi => coset_vanishes hq hp ha' i hi) hL
  rw [hr2] at h
  unfold cosetToeplitz cosetTail
  simp only [rpow_neg_half_pow hp] at *
  simp only [pow_add, mul_assoc] at h ⊢
  linarith

theorem one_mem_pfreeLabels {p X : ℕ} (hp : p.Prime) (hX : 1 ≤ X) : 1 ∈ pfreeLabels p X := by
  simp only [pfreeLabels, mem_filter, mem_Icc]
  exact ⟨⟨le_rfl, hX⟩, hp.not_dvd_one⟩

/-- **The tower odd side is a Cholesky energy minus the mass.**  For a profile supported on `[1, X]`
with `q(p^i) = 0` for `i > K` and `log_p X ≤ 2K`:
`log p · [Σ_{a' ≠ 1} v_0(a')² + (1 − 1/p) Σ_{a'} Σ_{j ≥ 1} v_j(a')² − Σ_{2 ≤ n ≤ X} q(n)²]`. -/
theorem towerOddPrimeSide_eq_cholesky {q : ℕ → ℝ} {X : ℕ} (hX : 1 ≤ X)
    (hq : ∀ n, X < n → q n = 0) {p : ℕ} (hp : p.Prime) {K : ℕ} (hK : ∀ i, K < i → q (p ^ i) = 0)
    (hM : Nat.log p X ≤ 2 * K) :
    towerOddPrimeSide q X p K = Real.log p *
      (∑ a' ∈ (pfreeLabels p X).erase 1, cosetTail q p X a' 0 ^ 2 +
        (1 - 1 / (p : ℝ)) * ∑ a' ∈ pfreeLabels p X,
          ∑ j ∈ range (Nat.log p X), cosetTail q p X a' (j + 1) ^ 2 -
        ∑ n ∈ Icc 2 X, q n ^ 2) := by
  have hlab : ∀ a' ∈ pfreeLabels p X, 1 ≤ a' := fun a' ha' => by
    simp only [pfreeLabels, mem_filter, mem_Icc] at ha'; exact ha'.1.1
  -- the mass sorts into cosets (the ratio correlation at `1`)
  have hmass : ∑ a' ∈ pfreeLabels p X, ∑ i ∈ range (Nat.log p X + 1), q (p ^ i * a') ^ 2 =
      ∑ n ∈ Icc 1 X, q n ^ 2 := by
    have h := ratioCorr_prime_pow_eq_sum_cosets q hq hp 0
    simp only [pow_zero, mul_one, add_zero, ratioCorr] at h
    simp only [sq]
    exact h.symm
  -- the unit coset's zeroth tail is the tower Mellin value
  have hmellin : cosetTail q p X 1 0 = towerMellin q p K := by
    unfold cosetTail kmsTail towerMellin
    simp only [Nat.sub_zero, mul_one]
    set N := Nat.log p X + K
    have hext : ∀ (n : ℕ) (f : ℕ → ℝ), (∀ i, n < i → f i = 0) → n ≤ N →
        ∑ i ∈ range (n + 1), f i = ∑ i ∈ range (N + 1), f i := fun n f hf hn => by
      refine sum_subset (range_subset_range.2 (by omega)) fun i hi hni => ?_
      exact hf i (by simp only [mem_range] at hi hni; omega)
    rw [← Finset.range_eq_Ico, hext (Nat.log p X) _ (fun i hi => by
        rw [show q (p ^ i) = 0 by simpa using coset_vanishes hq hp le_rfl i hi, mul_zero])
        (by omega),
      hext K _ (fun i hi => by rw [hK i hi, zero_mul]) (by omega)]
    refine sum_congr rfl fun i _ => ?_
    rw [rpow_neg_half_pow hp, mul_comm]
  rw [towerOddPrimeSide_eq q hq hp hK, mul_sum, sum_congr rfl fun a' ha' =>
    two_mul_cosetToeplitz hq hp hM (hlab a' ha'), sum_sub_distrib, sum_add_distrib, ← mul_sum,
    hmass, ← add_sum_erase _ _ (one_mem_pfreeLabels hp hX), hmellin,
    show (Icc 1 X : Finset ℕ) = insert 1 (Icc 2 X) by
      ext n; simp only [mem_Icc, mem_insert]; omega,
    sum_insert (by simp)]
  ring

/-- **The orientation is carried by squares**: the tower odd side is at least
`−log p · Σ_{2 ≤ n ≤ X} q(n)²`. -/
theorem towerOddPrimeSide_ge {q : ℕ → ℝ} {X : ℕ} (hX : 1 ≤ X) (hq : ∀ n, X < n → q n = 0)
    {p : ℕ} (hp : p.Prime) {K : ℕ} (hK : ∀ i, K < i → q (p ^ i) = 0)
    (hM : Nat.log p X ≤ 2 * K) :
    -(Real.log p * ∑ n ∈ Icc 2 X, q n ^ 2) ≤ towerOddPrimeSide q X p K := by
  rw [towerOddPrimeSide_eq_cholesky hX hq hp hK hM]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hp1 : 0 ≤ 1 - 1 / (p : ℝ) := by
    rw [sub_nonneg, div_le_one (by exact_mod_cast hp.pos)]; exact_mod_cast hp.one_le
  have h1 : 0 ≤ ∑ a' ∈ (pfreeLabels p X).erase 1, cosetTail q p X a' 0 ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ (1 - 1 / (p : ℝ)) * ∑ a' ∈ pfreeLabels p X,
      ∑ j ∈ range (Nat.log p X), cosetTail q p X a' (j + 1) ^ 2 :=
    mul_nonneg hp1 (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
  nlinarith

end

end GaloisForLFunctions.ArithmeticOrientationTheory
