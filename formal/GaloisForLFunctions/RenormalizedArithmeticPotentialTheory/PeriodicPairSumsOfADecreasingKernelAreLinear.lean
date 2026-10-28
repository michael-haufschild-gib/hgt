import Mathlib

/-!
# Periodic pair sums of a decreasing kernel are linear

Let `ψ` be `q`-periodic with mean zero and `|ψ| ≤ B`, and let `Φ` be a nonnegative decreasing
kernel with `Φ(t) ≤ A(1/t + 1)`. The pair sum
`S = Σ_{1 ≤ m < n ≤ N} (ψ(m)/√m)(ψ(n)/√n) Φ(log n − log m)`
is a priori of size `A N log N`, from the near-diagonal `Φ(log(1 + j/m)) ≈ A m/j`. With mean zero it
is linear (`abs_sum_periodicPair_le`): `|S| ≤ 42 q B² A N`.

The proof is Abel summation twice. For a fixed gap `j = n − m`, the coefficient
`ψ(m)ψ(m + j) − c_j` has bounded partial sums, where `c_j` is the periodic autocorrelation, and the
kernel has total variation `O(A N j^{−3/2})`. The autocorrelation `c_j` is periodic with mean zero
in `j`, and the row sums `T_j` decrease in `j`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### 1. Periodic partial sums and Abel summation -/

/-- The sums of a `q`-periodic sequence over windows of length `q` agree. -/
theorem sum_range_shift_of_periodic {q : ℕ} (u : ℕ → ℝ) (hper : ∀ i, u (i + q) = u i) (s : ℕ) :
    ∑ k ∈ range q, u (s + k) = ∑ k ∈ range q, u k := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    have h1 : ∑ k ∈ range q, u (s + 1 + k) + u s = ∑ k ∈ range q, u (s + k) + u (s + q) := by
      rw [← sum_range_succ (fun k => u (s + k)) q, sum_range_succ' (fun k => u (s + k)) q]
      simp only [add_zero]
      congr 1
      exact sum_congr rfl fun k _ => by ring_nf
    rw [show s + q = s + q from rfl, hper s] at h1
    linarith

/-- **Periodic partial sums**: `|Σ_{i<k} u_i − k μ| ≤ 2qU` for a `q`-periodic `u`, `|u| ≤ U`, with
mean `μ` over a period. -/
theorem abs_sum_range_sub_mul_mean_le {q : ℕ} (hq : 1 ≤ q) {U : ℝ} (u : ℕ → ℝ)
    (hper : ∀ i, u (i + q) = u i) (hU : ∀ i, |u i| ≤ U) (k : ℕ) :
    |∑ i ∈ range k, u i - k * ((∑ i ∈ range q, u i) / q)| ≤ 2 * q * U := by
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hμ : |(∑ i ∈ range q, u i) / q| ≤ U := by
    rw [abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range q, |u i| ≤ ∑ _i ∈ range q, U := sum_le_sum fun i _ => hU i
      _ = U * q := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  set μ := (∑ i ∈ range q, u i) / q
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < q
    · have h1 : |∑ i ∈ range k, u i| ≤ k * U := by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i ∈ range k, |u i| ≤ ∑ _i ∈ range k, U := sum_le_sum fun i _ => hU i
          _ = k * U := by rw [sum_const, card_range, nsmul_eq_mul]
      have hkq : (k : ℝ) ≤ q := by exact_mod_cast hk.le
      have h2 : |(k : ℝ) * μ| ≤ q * U := by
        rw [abs_mul, Nat.abs_cast]; exact mul_le_mul hkq hμ (abs_nonneg _) hq0.le
      calc |∑ i ∈ range k, u i - k * μ| ≤ |∑ i ∈ range k, u i| + |(k : ℝ) * μ| := abs_sub _ _
        _ ≤ k * U + q * U := add_le_add h1 h2
        _ ≤ 2 * q * U := by nlinarith
    · obtain ⟨r, rfl⟩ : ∃ r, k = q + r := ⟨k - q, by omega⟩
      have hsplit : ∑ i ∈ range (q + r), u i = ∑ i ∈ range q, u i + ∑ i ∈ range r, u i := by
        rw [sum_range_add]
        congr 1
        exact sum_congr rfl fun i _ => by rw [add_comm q i, hper]
      have hqμ : ∑ i ∈ range q, u i = q * μ := by simp only [μ]; field_simp
      have := ih r (by omega)
      rw [hsplit, hqμ]
      push_cast
      calc |↑q * μ + ∑ i ∈ range r, u i - (↑q + ↑r) * μ| = |∑ i ∈ range r, u i - r * μ| := by
            ring_nf
        _ ≤ _ := this

/-- **Abel summation**: `|Σ_{i<n} b_i a_i| ≤ P (|b_{n−1}| + Σ_{i<n−1} |b_{i+1} − b_i|)` when the
partial sums of `a` are at most `P`. -/
theorem abs_sum_range_mul_le (a b : ℕ → ℝ) (n : ℕ) {P : ℝ}
    (hP : ∀ k ≤ n, |∑ i ∈ range k, a i| ≤ P) :
    |∑ i ∈ range n, b i * a i| ≤
      P * (|b (n - 1)| + ∑ i ∈ range (n - 1), |b (i + 1) - b i|) := by
  have h := sum_range_by_parts b a n
  simp only [smul_eq_mul] at h
  rw [h]
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hP 0 (Nat.zero_le _))
  have h1 : |b (n - 1) * ∑ i ∈ range n, a i| ≤ |b (n - 1)| * P := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hP n le_rfl) (abs_nonneg _)
  have h2 : |∑ i ∈ range (n - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), a j| ≤
      ∑ i ∈ range (n - 1), |b (i + 1) - b i| * P := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hP (i + 1) (by have := mem_range.mp hi; omega)) (abs_nonneg _)
  calc _ ≤ |b (n - 1) * ∑ i ∈ range n, a i| +
        |∑ i ∈ range (n - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), a j| := abs_sub _ _
    _ ≤ |b (n - 1)| * P + ∑ i ∈ range (n - 1), |b (i + 1) - b i| * P := add_le_add h1 h2
    _ = _ := by rw [← sum_mul]; ring

/-- The variation of a product of an increasing and a decreasing nonnegative sequence is at most
`2UV`. -/
theorem sum_abs_sub_mul_le (u v : ℕ → ℝ) (n : ℕ) {U V : ℝ} (hU0 : 0 ≤ U) (hV0 : 0 ≤ V)
    (hu0 : ∀ i < n, 0 ≤ u i)
    (huU : ∀ i < n, u i ≤ U) (hum : ∀ i, i + 1 < n → u i ≤ u (i + 1)) (hv0 : ∀ i < n, 0 ≤ v i)
    (hvV : ∀ i < n, v i ≤ V) (hvm : ∀ i, i + 1 < n → v (i + 1) ≤ v i) :
    ∑ i ∈ range (n - 1), |u (i + 1) * v (i + 1) - u i * v i| ≤ 2 * U * V := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.zero_sub, range_zero, sum_empty]
    positivity
  have hterm : ∀ i ∈ range (n - 1), |u (i + 1) * v (i + 1) - u i * v i| ≤
      V * (u (i + 1) - u i) + U * (v i - v (i + 1)) := by
    intro i hi
    have hi' : i + 1 < n := by have := mem_range.mp hi; omega
    have hui := hum i hi'
    have hvi := hvm i hi'
    have hv1 := hv0 (i + 1) hi'
    have hu1 := hu0 i (by omega)
    have e : u (i + 1) * v (i + 1) - u i * v i = (u (i + 1) - u i) * v (i + 1) + u i * (v (i + 1) - v i) :=
      by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (mul_nonneg (by linarith) hv1), abs_mul, abs_of_nonneg hu1,
      abs_of_nonpos (by linarith)]
    have h1 : (u (i + 1) - u i) * v (i + 1) ≤ V * (u (i + 1) - u i) := by
      nlinarith [hvV (i + 1) hi']
    have h2 : u i * -(v (i + 1) - v i) ≤ U * (v i - v (i + 1)) := by
      nlinarith [huU i (by omega)]
    linarith
  refine (sum_le_sum hterm).trans ?_
  have hv : ∑ i ∈ range (n - 1), (v i - v (i + 1)) = v 0 - v (n - 1) := by
    have := sum_range_sub (fun i => v i) (n - 1)
    rw [show v 0 - v (n - 1) = -(v (n - 1) - v 0) by ring, ← this, ← sum_neg_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_range_sub (fun i => u i), hv]
  have h1 : u (n - 1) - u 0 ≤ U := by linarith [huU (n - 1) (by omega), hu0 0 hn]
  have h2 : v 0 - v (n - 1) ≤ V := by linarith [hvV 0 hn, hv0 (n - 1) (by omega)]
  nlinarith

/-- For a decreasing nonnegative sequence, `|b_{n−1}| + Σ|b_{i+1} − b_i| = b_0`. -/
theorem abs_last_add_sum_abs_sub_eq (b : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (hb0 : ∀ i < n, 0 ≤ b i)
    (hbm : ∀ i, i + 1 < n → b (i + 1) ≤ b i) :
    |b (n - 1)| + ∑ i ∈ range (n - 1), |b (i + 1) - b i| = b 0 := by
  rw [abs_of_nonneg (hb0 (n - 1) (by omega)),
    sum_congr rfl fun i hi => abs_of_nonpos (by linarith [hbm i (by have := mem_range.mp hi; omega)])]
  have := sum_range_sub (fun i => b i) (n - 1)
  rw [sum_neg_distrib, this]
  ring

/-! ### 2. Elementary bounds -/

/-- `log(a + J) − log a ≥ J/(a + J)`. -/
theorem div_le_log_add_sub_log {a J : ℝ} (ha : 0 < a) (hJ : 0 ≤ J) :
    J / (a + J) ≤ Real.log (a + J) - Real.log a := by
  have h := Real.log_le_sub_one_of_pos (show 0 < a / (a + J) by positivity)
  rw [Real.log_div ha.ne' (by positivity)] at h
  have e : a / (a + J) - 1 = -(J / (a + J)) := by field_simp; ring
  linarith

/-- `1/((J + 1)√(J + 2)) ≤ 3(1/√(J + 1) − 1/√(J + 2))`. -/
theorem one_div_mul_sqrt_le (J : ℕ) :
    1 / (((J : ℝ) + 1) * Real.sqrt ((J : ℝ) + 2)) ≤
      3 * (1 / Real.sqrt ((J : ℝ) + 1) - 1 / Real.sqrt ((J : ℝ) + 2)) := by
  set a := Real.sqrt ((J : ℝ) + 1)
  set b := Real.sqrt ((J : ℝ) + 2)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a ^ 2 = (J : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = (J : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  -- `b − a = 1/(a + b) ≥ 1/(2b)`, and `2b ≤ 3a`
  have hdiff : (b - a) * (a + b) = 1 := by nlinarith
  have h3 : 2 * b ≤ 3 * a := by nlinarith
  rw [show (J : ℝ) + 1 = a ^ 2 from ha2.symm, div_le_iff₀ (by positivity)]
  rw [show 3 * (1 / a - 1 / b) * (a ^ 2 * b) = 3 * a * (b - a) by field_simp]
  nlinarith

theorem sum_one_div_mul_sqrt_le (M : ℕ) :
    ∑ J ∈ range M, 1 / (((J : ℝ) + 1) * Real.sqrt ((J : ℝ) + 2)) ≤ 3 := by
  refine (sum_le_sum fun J _ => one_div_mul_sqrt_le J).trans ?_
  rw [← mul_sum]
  have h := sum_range_sub (fun J : ℕ => -(1 / Real.sqrt ((J : ℝ) + 1))) M
  have e : ∑ J ∈ range M, (1 / Real.sqrt ((J : ℝ) + 1) - 1 / Real.sqrt ((J : ℝ) + 2)) =
      1 - 1 / Real.sqrt ((M : ℝ) + 1) := by
    rw [show ∑ J ∈ range M, (1 / Real.sqrt ((J : ℝ) + 1) - 1 / Real.sqrt ((J : ℝ) + 2)) =
      ∑ J ∈ range M, (-(1 / Real.sqrt (((J + 1 : ℕ) : ℝ) + 1)) - -(1 / Real.sqrt ((J : ℝ) + 1))) from
        sum_congr rfl fun J _ => by push_cast; ring_nf, h]
    simp only [CharP.cast_eq_zero, zero_add, Real.sqrt_one, div_one]
    ring
  rw [e]
  have : 0 ≤ 1 / Real.sqrt ((M : ℝ) + 1) := by positivity
  linarith

/-! ### 3. The pair sum -/

/-- The kernel of the gap `J` at the atom `m`: `Φ(log(m + J) − log m)/(√m √(m + J))`. -/
def gapKernel (Φ : ℝ → ℝ) (m J : ℕ) : ℝ :=
  Φ (Real.log ((m : ℝ) + J) - Real.log m) * (1 / (Real.sqrt m * Real.sqrt ((m : ℝ) + J)))

/-- Reindexing a strict upper sum by the gap. -/
theorem sum_Icc_ite_lt_eq {N m : ℕ} (G : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, (if m < n then G n else 0) = ∑ J ∈ range (N - m), G (m + J + 1) := by
  rw [← sum_filter]
  have hset : (Icc 1 N).filter (fun n => m < n) = Ico (m + 1) (N + 1) := by
    ext n; simp only [mem_filter, mem_Icc, mem_Ico]; omega
  rw [hset, sum_Ico_eq_sum_range, show N + 1 - (m + 1) = N - m by omega]
  exact sum_congr rfl fun J _ => by rw [show m + 1 + J = m + J + 1 by ring]

/-- **Periodic pair sums of a decreasing kernel are linear.** For a `q`-periodic `ψ` with mean zero
and `|ψ| ≤ B`, and a decreasing nonnegative kernel `Φ ≤ A(1/t + 1)` on `(0, ∞)`:
`|Σ_{1 ≤ m < n ≤ N} (ψ(m)/√m)(ψ(n)/√n) Φ(log n − log m)| ≤ 42 q B² A N`. -/
theorem abs_sum_periodicPair_le {q N : ℕ} (hq : 1 ≤ q) {B A : ℝ} (hA : 0 ≤ A) (ψ : ℕ → ℝ)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0) (hB : ∀ n, |ψ n| ≤ B)
    (Φ : ℝ → ℝ) (hΦ0 : ∀ t, 0 < t → 0 ≤ Φ t) (hΦA : ∀ t, 0 < t → Φ t ≤ A * (1 / t + 1))
    (hΦanti : ∀ t₁ t₂, 0 < t₁ → t₁ ≤ t₂ → Φ t₂ ≤ Φ t₁) :
    |∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m < n then
      ψ m / Real.sqrt m * (ψ n / Real.sqrt n) * Φ (Real.log n - Real.log m) else 0)| ≤
      42 * q * B ^ 2 * A * N := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- the kernel along a gap
  have hlogpos : ∀ m J : ℕ, 1 ≤ m → 1 ≤ J →
      0 < Real.log ((m : ℝ) + J) - Real.log m := by
    intro m J hm hJ
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
    have := div_le_log_add_sub_log hm0 hJ0.le
    have : 0 < (J : ℝ) / (m + J) := by positivity
    linarith
  have hF0 : ∀ m J : ℕ, 1 ≤ m → 1 ≤ J → 0 ≤ gapKernel Φ m J := fun m J hm hJ =>
    mul_nonneg (hΦ0 _ (hlogpos m J hm hJ)) (by positivity)
  -- `Φ(log(m + J) − log m) ≤ A(N/J + 1)` when `m + J ≤ N`
  have hΦU : ∀ m J : ℕ, 1 ≤ m → 1 ≤ J → m + J ≤ N →
      Φ (Real.log ((m : ℝ) + J) - Real.log m) ≤ A * (N / J + 1) := by
    intro m J hm hJ hmJ
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
    have ht := hlogpos m J hm hJ
    have h1 := div_le_log_add_sub_log hm0 hJ0.le
    have h2 : 1 / (Real.log ((m : ℝ) + J) - Real.log m) ≤ N / J := by
      rw [div_le_div_iff₀ ht hJ0, one_mul]
      have hmJN : (m : ℝ) + J ≤ N := by exact_mod_cast hmJ
      have := (div_le_iff₀ (show (0 : ℝ) < m + J by positivity)).mp h1
      nlinarith
    exact (hΦA _ ht).trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  -- the kernel decreases along the gap and increases along the atoms
  have htanti : ∀ a J J' : ℝ, 0 < a → 0 ≤ J → J ≤ J' →
      Real.log (a + J) - Real.log a ≤ Real.log (a + J') - Real.log a := fun a J J' ha hJ hJJ' => by
    have := Real.log_le_log (by positivity) (show a + J ≤ a + J' by linarith); linarith
  have htmono : ∀ a J : ℝ, 0 < a → 0 ≤ J →
      Real.log (a + 1 + J) - Real.log (a + 1) ≤ Real.log (a + J) - Real.log a := by
    intro a J ha hJ
    rw [← Real.log_div (by positivity) (by positivity), ← Real.log_div (by positivity) ha.ne']
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) ha]
    nlinarith
  have hFJ : ∀ m J : ℕ, 1 ≤ m → 1 ≤ J → gapKernel Φ m (J + 1) ≤ gapKernel Φ m J := by
    intro m J hm hJ
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    unfold gapKernel
    push_cast
    have h1 : Φ (Real.log ((m : ℝ) + (J + 1)) - Real.log m) ≤ Φ (Real.log ((m : ℝ) + J) - Real.log m) :=
      hΦanti _ _ (hlogpos m J hm hJ) (htanti _ _ _ hm0 (by positivity) (by linarith))
    have h2 : 1 / (Real.sqrt m * Real.sqrt ((m : ℝ) + (J + 1))) ≤
        1 / (Real.sqrt m * Real.sqrt ((m : ℝ) + J)) := by
      have : Real.sqrt ((m : ℝ) + J) ≤ Real.sqrt ((m : ℝ) + (J + 1)) := Real.sqrt_le_sqrt (by linarith)
      have h0 : 0 < Real.sqrt m * Real.sqrt ((m : ℝ) + J) := by positivity
      exact one_div_le_one_div_of_le h0 (mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _))
    have h3 := hlogpos m (J + 1) hm (by omega)
    push_cast at h3
    exact mul_le_mul h1 h2 (by positivity) (hΦ0 _ (hlogpos m J hm hJ))
  -- the reindexing by the gap
  set F : ℕ → ℕ → ℝ := fun i J => ψ (i + 1) * ψ (i + 1 + (J + 1)) * gapKernel Φ (i + 1) (J + 1)
  have hreidx : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m < n then
      ψ m / Real.sqrt m * (ψ n / Real.sqrt n) * Φ (Real.log n - Real.log m) else 0) =
      ∑ J ∈ range (N - 1), ∑ i ∈ range (N - 1 - J), F i J := by
    rw [sum_congr rfl fun m _ => sum_Icc_ite_lt_eq (N := N) (m := m)
      (fun n => ψ m / Real.sqrt m * (ψ n / Real.sqrt n) * Φ (Real.log n - Real.log m))]
    rw [show Icc 1 N = Ico 1 (N + 1) by ext n; simp only [mem_Icc, mem_Ico]; omega,
      sum_Ico_eq_sum_range, show N + 1 - 1 = N by omega]
    rw [sum_comm' (t' := range (N - 1)) (s' := fun J => range (N - 1 - J)) (fun i J => by
      simp only [mem_range]; omega)]
    refine sum_congr rfl fun J _ => sum_congr rfl fun i _ => ?_
    simp only [F, gapKernel]
    rw [show 1 + i + J + 1 = (i + 1) + (J + 1) by ring, show 1 + i = i + 1 by ring]
    push_cast
    ring_nf
  rw [hreidx]
  -- the autocorrelation and the row sums
  set c : ℕ → ℝ := fun J => (∑ i ∈ range q, ψ (i + 1) * ψ (i + 1 + (J + 1))) / q
  set T : ℕ → ℝ := fun J => ∑ i ∈ range (N - 1 - J), gapKernel Φ (i + 1) (J + 1)
  set E : ℕ → ℝ := fun J => ∑ i ∈ range (N - 1 - J),
    (ψ (i + 1) * ψ (i + 1 + (J + 1)) - c J) * gapKernel Φ (i + 1) (J + 1)
  have hsplit : ∀ J, ∑ i ∈ range (N - 1 - J), F i J = c J * T J + E J := fun J => by
    simp only [F, T, E, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [sum_congr rfl fun J _ => hsplit J, sum_add_distrib]
  -- the error of each gap
  have hE : ∀ J ∈ range (N - 1), |E J| ≤
      6 * q * B ^ 2 * (2 * A * N * (1 / (((J : ℝ) + 1) * Real.sqrt ((J : ℝ) + 2)))) := by
    intro J hJ
    have hJN : J + 2 ≤ N := by have := mem_range.mp hJ; omega
    set n := N - 1 - J
    set u' : ℕ → ℝ := fun i => Φ (Real.log (((i + 1 : ℕ) : ℝ) + ((J + 1 : ℕ) : ℝ)) -
      Real.log ((i + 1 : ℕ) : ℝ))
    set v' : ℕ → ℝ := fun i => 1 / (Real.sqrt ((i + 1 : ℕ) : ℝ) *
      Real.sqrt (((i + 1 : ℕ) : ℝ) + ((J + 1 : ℕ) : ℝ)))
    have hb : ∀ i, gapKernel Φ (i + 1) (J + 1) = u' i * v' i := fun i => rfl
    set U := A * (N / ((J + 1 : ℕ) : ℝ) + 1)
    set V := 1 / Real.sqrt (((J + 1 : ℕ) : ℝ) + 1)
    have hU0 : 0 ≤ U := by positivity
    have hV0 : 0 ≤ V := by positivity
    have hu0 : ∀ i < n, 0 ≤ u' i := fun i _ => hΦ0 _ (hlogpos (i + 1) (J + 1) (by omega) (by omega))
    have huU : ∀ i < n, u' i ≤ U := fun i hi =>
      hΦU (i + 1) (J + 1) (by omega) (by omega) (by omega)
    have hum : ∀ i, i + 1 < n → u' i ≤ u' (i + 1) := by
      intro i _
      simp only [u']
      refine hΦanti _ _ (hlogpos (i + 1 + 1) (J + 1) (by omega) (by omega)) ?_
      have := htmono ((i + 1 : ℕ) : ℝ) ((J + 1 : ℕ) : ℝ) (by positivity) (by positivity)
      push_cast at this ⊢
      linarith
    have hv0 : ∀ i < n, 0 ≤ v' i := fun i _ => by positivity
    have hvV : ∀ i < n, v' i ≤ V := by
      intro i _
      simp only [v', V]
      rw [one_div_le_one_div (by positivity) (by positivity)]
      have h1 : 1 ≤ Real.sqrt ((i + 1 : ℕ) : ℝ) := Real.one_le_sqrt.mpr (by push_cast; linarith)
      have h2 : Real.sqrt (((J + 1 : ℕ) : ℝ) + 1) ≤ Real.sqrt (((i + 1 : ℕ) : ℝ) + ((J + 1 : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt (by push_cast; linarith)
      nlinarith [Real.sqrt_nonneg (((J + 1 : ℕ) : ℝ) + 1)]
    have hvm : ∀ i, i + 1 < n → v' (i + 1) ≤ v' i := by
      intro i _
      simp only [v']
      rw [one_div_le_one_div (by positivity) (by positivity)]
      exact mul_le_mul (Real.sqrt_le_sqrt (by push_cast; linarith))
        (Real.sqrt_le_sqrt (by push_cast; linarith)) (by positivity) (by positivity)
    -- the partial sums of the centred coefficient
    have hP : ∀ k ≤ n, |∑ i ∈ range k, (ψ (i + 1) * ψ (i + 1 + (J + 1)) - c J)| ≤ 2 * q * B ^ 2 := by
      intro k _
      have h := abs_sum_range_sub_mul_mean_le hq (U := B ^ 2)
        (fun i => ψ (i + 1) * ψ (i + 1 + (J + 1)))
        (fun i => by
          show ψ (i + q + 1) * ψ (i + q + 1 + (J + 1)) = ψ (i + 1) * ψ (i + 1 + (J + 1))
          rw [show i + q + 1 = (i + 1) + q by ring, hper,
            show i + 1 + q + (J + 1) = (i + 1 + (J + 1)) + q by ring, hper])
        (fun i => by
          show |ψ (i + 1) * ψ (i + 1 + (J + 1))| ≤ B ^ 2
          rw [abs_mul, sq]; exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hB0) k
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      exact h
    have habel := abs_sum_range_mul_le (fun i => ψ (i + 1) * ψ (i + 1 + (J + 1)) - c J)
      (fun i => gapKernel Φ (i + 1) (J + 1)) n hP
    have hTV := sum_abs_sub_mul_le u' v' n hU0 hV0 hu0 huU hum hv0 hvV hvm
    have hlast : |gapKernel Φ (n - 1 + 1) (J + 1)| ≤ U * V := by
      rw [hb, abs_of_nonneg (mul_nonneg (hu0 _ (by omega)) (hv0 _ (by omega)))]
      exact mul_le_mul (huU _ (by omega)) (hvV _ (by omega)) (hv0 _ (by omega)) hU0
    have hUV : U * V ≤ 2 * A * N * (1 / (((J : ℝ) + 1) * Real.sqrt ((J : ℝ) + 2))) := by
      simp only [U, V]
      push_cast
      have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
      have hJN' : (J : ℝ) + 1 ≤ N := by exact_mod_cast (show J + 1 ≤ N by omega)
      rw [show ((J : ℝ) + 1 + 1) = (J : ℝ) + 2 by ring]
      have hs : 0 < Real.sqrt ((J : ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
      rw [mul_one_div, mul_one_div, div_le_div_iff₀ hs (by positivity)]
      have : (N : ℝ) / ((J : ℝ) + 1) + 1 ≤ 2 * N / ((J : ℝ) + 1) := by
        rw [div_add_one hJ1.ne', div_le_div_iff_of_pos_right hJ1]; linarith
      have := mul_le_mul_of_nonneg_left this hA
      calc A * ((N : ℝ) / ((J : ℝ) + 1) + 1) * (((J : ℝ) + 1) * Real.sqrt ((J : ℝ) + 2))
          ≤ A * (2 * N / ((J : ℝ) + 1)) * (((J : ℝ) + 1) * Real.sqrt ((J : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 2 * A * N * Real.sqrt ((J : ℝ) + 2) := by field_simp
    have hE' : |E J| ≤ 2 * q * B ^ 2 * (3 * (U * V)) := by
      have h1 : |E J| = |∑ i ∈ range n, gapKernel Φ (i + 1) (J + 1) *
          (ψ (i + 1) * ψ (i + 1 + (J + 1)) - c J)| := by
        simp only [E]; congr 1; exact sum_congr rfl fun i _ => by ring
      rw [h1]
      refine habel.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have h2 : ∑ i ∈ range (n - 1), |gapKernel Φ (i + 1 + 1) (J + 1) - gapKernel Φ (i + 1) (J + 1)|
          ≤ 2 * U * V := by
        refine le_trans (le_of_eq (sum_congr rfl fun i _ => by rw [hb, hb])) hTV
      linarith
    calc |E J| ≤ 2 * q * B ^ 2 * (3 * (U * V)) := hE'
      _ ≤ 2 * q * B ^ 2 * (3 * (2 * A * N * (1 / (((J : ℝ) + 1) * Real.sqrt ((J : ℝ) + 2))))) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  -- the main term: the autocorrelation against the decreasing row sums
  have hT0 : ∀ J, 0 ≤ T J := fun J => sum_nonneg fun i _ => hF0 _ _ (by omega) (by omega)
  have hTm : ∀ J, T (J + 1) ≤ T J := by
    intro J
    simp only [T]
    calc ∑ i ∈ range (N - 1 - (J + 1)), gapKernel Φ (i + 1) (J + 1 + 1)
        ≤ ∑ i ∈ range (N - 1 - (J + 1)), gapKernel Φ (i + 1) (J + 1) :=
          sum_le_sum fun i _ => hFJ _ _ (by omega) (by omega)
      _ ≤ ∑ i ∈ range (N - 1 - J), gapKernel Φ (i + 1) (J + 1) :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
            fun i _ _ => hF0 _ _ (by omega) (by omega)
  have hT1 : T 0 ≤ 3 * A * N := by
    simp only [T]
    have hterm : ∀ i ∈ range (N - 1 - 0), gapKernel Φ (i + 1) (0 + 1) ≤ 3 * A := by
      intro i _
      have hm0 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
      have ht := hlogpos (i + 1) 1 (by omega) le_rfl
      have h1 := div_le_log_add_sub_log hm0 (show (0 : ℝ) ≤ ((1 : ℕ) : ℝ) by positivity)
      unfold gapKernel
      simp only [Nat.cast_add, Nat.cast_one, zero_add] at ht h1 ⊢
      have hinv : 1 / (Real.log ((i : ℝ) + 1 + 1) - Real.log ((i : ℝ) + 1)) ≤ (i : ℝ) + 2 := by
        rw [div_le_iff₀ ht]
        have := (div_le_iff₀ (show (0 : ℝ) < (i : ℝ) + 1 + 1 by positivity)).mp h1
        nlinarith
      have hΦb := hΦA _ ht
      have hsq : (i : ℝ) + 1 ≤ Real.sqrt ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1 + 1) := by
        rw [← Real.sqrt_mul (by positivity)]
        exact Real.le_sqrt_of_sq_le (by nlinarith)
      have hden : 0 < Real.sqrt ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1 + 1) := by positivity
      calc Φ (Real.log ((i : ℝ) + 1 + 1) - Real.log ((i : ℝ) + 1)) *
            (1 / (Real.sqrt ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1 + 1)))
          ≤ A * ((i : ℝ) + 2 + 1) * (1 / ((i : ℝ) + 1)) := by
            refine mul_le_mul (hΦb.trans (mul_le_mul_of_nonneg_left (by linarith) hA))
              (one_div_le_one_div_of_le (by positivity) hsq) (by positivity) (by positivity)
        _ ≤ 3 * A := by
            rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
    calc ∑ i ∈ range (N - 1 - 0), gapKernel Φ (i + 1) (0 + 1) ≤ ∑ _i ∈ range (N - 1 - 0), 3 * A :=
          sum_le_sum hterm
      _ = 3 * A * ((N - 1 - 0 : ℕ) : ℝ) := by rw [sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ 3 * A * N := mul_le_mul_of_nonneg_left (by exact_mod_cast (show N - 1 - 0 ≤ N by omega))
          (by positivity)
  have hcper : ∀ J, c (J + q) = c J := fun J => by
    simp only [c]
    congr 1
    exact sum_congr rfl fun i _ => by
      rw [show i + 1 + (J + q + 1) = (i + 1 + (J + 1)) + q by ring, hper]
  have hcB : ∀ J, |c J| ≤ B ^ 2 := fun J => by
    simp only [c]
    rw [abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range q, |ψ (i + 1) * ψ (i + 1 + (J + 1))| ≤ ∑ _i ∈ range q, B ^ 2 :=
          sum_le_sum fun i _ => by rw [abs_mul, sq]; exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hB0
      _ = B ^ 2 * q := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hcmean : ∑ J ∈ range q, c J = 0 := by
    simp only [c, ← sum_div]
    rw [sum_comm]
    have : ∀ i ∈ range q, ∑ J ∈ range q, ψ (i + 1) * ψ (i + 1 + (J + 1)) = 0 := fun i _ => by
      rw [← mul_sum, show ∑ J ∈ range q, ψ (i + 1 + (J + 1)) = ∑ J ∈ range q, ψ ((i + 2) + J) from
        sum_congr rfl fun J _ => by rw [show i + 1 + (J + 1) = (i + 2) + J by ring],
        sum_range_shift_of_periodic ψ hper, hmean, mul_zero]
    rw [sum_eq_zero this, zero_div]
  have hPc : ∀ k ≤ N - 1, |∑ J ∈ range k, c J| ≤ 2 * q * B ^ 2 := by
    intro k _
    have h := abs_sum_range_sub_mul_mean_le hq c hcper hcB k
    rwa [hcmean, zero_div, mul_zero, sub_zero] at h
  have hmain : |∑ J ∈ range (N - 1), c J * T J| ≤ 6 * q * B ^ 2 * A * N := by
    rcases Nat.lt_or_ge (N - 1) 1 with hN1 | hN1
    · rw [show N - 1 = 0 by omega, range_zero, sum_empty, abs_zero]; positivity
    have habel := abs_sum_range_mul_le c T (N - 1) hPc
    rw [abs_last_add_sum_abs_sub_eq T hN1 (fun J _ => hT0 J) (fun J _ => hTm J)] at habel
    calc |∑ J ∈ range (N - 1), c J * T J| = |∑ J ∈ range (N - 1), T J * c J| := by
          congr 1; exact sum_congr rfl fun J _ => mul_comm _ _
      _ ≤ 2 * q * B ^ 2 * T 0 := habel
      _ ≤ 2 * q * B ^ 2 * (3 * A * N) := mul_le_mul_of_nonneg_left hT1 (by positivity)
      _ = 6 * q * B ^ 2 * A * N := by ring
  have herr : |∑ J ∈ range (N - 1), E J| ≤ 36 * q * B ^ 2 * A * N := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hE).trans ?_)
    rw [← mul_sum, ← mul_sum]
    have := sum_one_div_mul_sqrt_le (N - 1)
    have h0 : 0 ≤ 6 * q * B ^ 2 * (2 * A * N) := by positivity
    calc 6 * q * B ^ 2 * (2 * A * N * ∑ J ∈ range (N - 1), 1 / (((J : ℝ) + 1) * Real.sqrt ((J : ℝ) + 2)))
        ≤ 6 * q * B ^ 2 * (2 * A * N * 3) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (by positivity))
            (by positivity)
      _ = 36 * q * B ^ 2 * A * N := by ring
  calc |∑ J ∈ range (N - 1), c J * T J + ∑ J ∈ range (N - 1), E J|
      ≤ |∑ J ∈ range (N - 1), c J * T J| + |∑ J ∈ range (N - 1), E J| := abs_add_le _ _
    _ ≤ 6 * q * B ^ 2 * A * N + 36 * q * B ^ 2 * A * N := add_le_add hmain herr
    _ = 42 * q * B ^ 2 * A * N := by ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
