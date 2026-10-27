import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy

/-!
# The tower form of a prime

On a `p`-ladder of orders `c, cp, cp², …, cp^{N−1}` the torsion orbits `O_{cp^i}` meet only at `p`,
and Weil's prime kernel is `P(cp^i, cp^j) = log p · p^{−|i−j|/2}` off the diagonal and `0` on it
(`weilPrimeKernel_ladder`). With its natural diagonal `1` this is the Kac–Murdock–Szegő matrix
`K_q = (q^{|i−j|})`, `q = p^{−1/2}`: the **tower form** of `p`. So on a ladder

    Σ_{i,j} x_i x_j P(cp^i, cp^j) = log p · (K_q(x) − |x|²)            (`ladderForm_eq`).

* **Tower decomposition** (`kmsForm_eq_tail`, `kmsForm_eq_orbit_levels`). With the tails
  `T_k = Σ_{i ≥ k} x_i q^{i−k}`, `K_q(x) = T_0² + (1 − q²) Σ_{k ≥ 1} T_k²`. For `q = p^{−1/2}` the level `k`
  carries weight `φ(p^k)`, the number of points of the torsion orbit `O_{p^k}`:
  `K_q(x) = Σ_k φ(p^k) (Σ_{i ≥ k} x_i p^{−i/2})²`. The finite intersection at `p` is a sum over the
  levels of the `p`-power tower, each counted by its orbit size.
* **Local Hodge index at `p`** (`kmsForm_nonneg`, `kmsForm_lower`, `kmsForm_upper`):
  `(1 − q)/(1 + q) |x|² ≤ K_q(x) ≤ (1 + q)/(1 − q) |x|²` for `0 ≤ q < 1`, from `x_k = T_k − q T_{k+1}`.
* **The local prime form is bounded** (`ladderForm_lower`, `ladderForm_upper`):
  `−(2q/(1 + q)) log p |x|² ≤ Σ x_i x_j P(cp^i, cp^j) ≤ (2q/(1 − q)) log p |x|²`. Weil's prime sum has no
  diagonal term, so the identity is subtracted from a positive form: that is the whole of its
  indefiniteness on one ladder.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

/-! ### The Kac–Murdock–Szegő form -/

/-- The entry `q^{|i − j|}`. -/
def kmsEntry (q : ℝ) (i j : ℕ) : ℝ := q ^ (max i j - min i j)

/-- The tower form `K_q(x) = Σ_{i,j < N} x_i x_j q^{|i−j|}`. -/
def kmsForm (q : ℝ) (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * kmsEntry q i j

/-- The tail `T_k = Σ_{k ≤ i < N} x_i q^{i − k}`. -/
def towerTail (q : ℝ) (N : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (N - k), x (i + k) * q ^ i

theorem kmsEntry_succ_succ (q : ℝ) (i j : ℕ) : kmsEntry q (i + 1) (j + 1) = kmsEntry q i j := by
  simp only [kmsEntry]
  congr 1
  omega

theorem kmsEntry_succ_zero (q : ℝ) (i : ℕ) : kmsEntry q (i + 1) 0 = q ^ (i + 1) := by
  simp [kmsEntry]

theorem kmsEntry_zero_succ (q : ℝ) (j : ℕ) : kmsEntry q 0 (j + 1) = q ^ (j + 1) := by
  simp [kmsEntry]

theorem kmsEntry_self (q : ℝ) (i : ℕ) : kmsEntry q i i = 1 := by simp [kmsEntry]

theorem towerTail_zero_succ (q : ℝ) (N : ℕ) (x : ℕ → ℝ) :
    towerTail q (N + 1) x 0 = x 0 + q * towerTail q N (fun i => x (i + 1)) 0 := by
  simp only [towerTail, Nat.sub_zero, add_zero]
  rw [Finset.sum_range_succ', pow_zero, mul_one, mul_sum, add_comm]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  ring

theorem towerTail_succ_shift (q : ℝ) (N : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    towerTail q (N + 1) x (k + 1) = towerTail q N (fun i => x (i + 1)) k := by
  simp only [towerTail, Nat.add_sub_add_right]
  refine sum_congr rfl fun i _ => ?_
  rw [add_assoc]

theorem towerTail_self (q : ℝ) (N : ℕ) (x : ℕ → ℝ) : towerTail q N x N = 0 := by
  simp [towerTail]

/-- **The recursion `x_k = T_k − q T_{k+1}`.** -/
theorem towerTail_eq (q : ℝ) {N k : ℕ} (hk : k < N) (x : ℕ → ℝ) :
    towerTail q N x k = x k + q * towerTail q N x (k + 1) := by
  simp only [towerTail]
  obtain ⟨M, hM⟩ : ∃ M, N - k = M + 1 := ⟨N - k - 1, by omega⟩
  rw [hM, show N - (k + 1) = M by omega, Finset.sum_range_succ', pow_zero, mul_one, zero_add, mul_sum,
    add_comm]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [show i + 1 + k = i + (k + 1) by ring, pow_succ]
  ring

/-- **The tower decomposition** `K_q(x) = T_0² + (1 − q²) Σ_{k < N} T_{k+1}²`. -/
theorem kmsForm_eq_tail (q : ℝ) (N : ℕ) (x : ℕ → ℝ) :
    kmsForm q N x = towerTail q N x 0 ^ 2 +
      (1 - q ^ 2) * ∑ k ∈ range N, towerTail q N x (k + 1) ^ 2 := by
  induction N generalizing x with
  | zero => simp [kmsForm, towerTail]
  | succ N ih =>
    set y : ℕ → ℝ := fun i => x (i + 1)
    have hK : kmsForm q (N + 1) x = x 0 ^ 2 + 2 * x 0 * (q * towerTail q N y 0) + kmsForm q N y := by
      have hT : q * towerTail q N y 0 = ∑ i ∈ range N, x (i + 1) * q ^ (i + 1) := by
        simp only [towerTail, Nat.sub_zero, add_zero, y, mul_sum]
        exact sum_congr rfl fun i _ => by ring
      have h1 : ∀ i ∈ range N, x (i + 1) * x 0 * q ^ (i + 1) = x 0 * (x (i + 1) * q ^ (i + 1)) :=
        fun i _ => by ring
      have h2 : ∀ j ∈ range N, x 0 * x (j + 1) * q ^ (j + 1) = x 0 * (x (j + 1) * q ^ (j + 1)) :=
        fun j _ => by ring
      rw [hT]
      simp only [kmsForm, Finset.sum_range_succ', kmsEntry_succ_succ, kmsEntry_succ_zero,
        kmsEntry_zero_succ, kmsEntry_self, y, sum_add_distrib]
      rw [sum_congr rfl h1, sum_congr rfl h2, ← mul_sum]
      ring
    have hS : ∑ k ∈ range (N + 1), towerTail q (N + 1) x (k + 1) ^ 2 =
        towerTail q N y 0 ^ 2 + ∑ k ∈ range N, towerTail q N y (k + 1) ^ 2 := by
      simp only [towerTail_succ_shift, y]
      rw [Finset.sum_range_succ', add_comm]
    rw [hK, ih y, hS, towerTail_zero_succ]
    ring

/-- The levels together: `Σ_{k < N} T_k² = T_0² + Σ_{k < N} T_{k+1}²` (the top tail `T_N` is `0`). -/
theorem sum_towerTail_sq (q : ℝ) (N : ℕ) (x : ℕ → ℝ) :
    ∑ k ∈ range N, towerTail q N x k ^ 2 =
      towerTail q N x 0 ^ 2 + ∑ k ∈ range N, towerTail q N x (k + 1) ^ 2 := by
  have h1 := Finset.sum_range_succ (fun k => towerTail q N x k ^ 2) N
  have h2 := Finset.sum_range_succ' (fun k => towerTail q N x k ^ 2) N
  rw [towerTail_self, sq, mul_zero, add_zero] at h1
  linarith

/-- `|x|² = Σ_{k < N} (T_k − q T_{k+1})²`. -/
theorem sum_sq_eq_tail (q : ℝ) (N : ℕ) (x : ℕ → ℝ) :
    ∑ k ∈ range N, x k ^ 2 =
      ∑ k ∈ range N, (towerTail q N x k - q * towerTail q N x (k + 1)) ^ 2 := by
  refine sum_congr rfl fun k hk => ?_
  rw [towerTail_eq q (mem_range.mp hk) x]
  ring

/-- **Local positivity**: the tower form is positive semidefinite for `|q| ≤ 1`. -/
theorem kmsForm_nonneg {q : ℝ} (hq : q ^ 2 ≤ 1) (N : ℕ) (x : ℕ → ℝ) : 0 ≤ kmsForm q N x := by
  rw [kmsForm_eq_tail]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sum_nonneg fun _ _ => sq_nonneg _))

/-- **Lower Kac–Murdock–Szegő bound** `(1 − q)|x|² ≤ (1 + q) K_q(x)` for `0 ≤ q ≤ 1`. -/
theorem kmsForm_lower {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (x : ℕ → ℝ) :
    (1 - q) * ∑ k ∈ range N, x k ^ 2 ≤ (1 + q) * kmsForm q N x := by
  set A := ∑ k ∈ range N, towerTail q N x (k + 1) ^ 2
  set T0 := towerTail q N x 0
  have hA : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hx : ∑ k ∈ range N, x k ^ 2 ≤ (1 + q) * T0 ^ 2 + (1 + q) ^ 2 * A := by
    rw [sum_sq_eq_tail q]
    calc ∑ k ∈ range N, (towerTail q N x k - q * towerTail q N x (k + 1)) ^ 2
        ≤ ∑ k ∈ range N, ((1 + q) * towerTail q N x k ^ 2 +
            q * (1 + q) * towerTail q N x (k + 1) ^ 2) := by
          refine sum_le_sum fun k _ => ?_
          nlinarith [mul_nonneg hq0 (sq_nonneg (towerTail q N x k + towerTail q N x (k + 1)))]
      _ = (1 + q) * T0 ^ 2 + (1 + q) ^ 2 * A := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_towerTail_sq]
          ring
  rw [kmsForm_eq_tail]
  nlinarith [mul_le_mul_of_nonneg_left hx (show 0 ≤ 1 - q by linarith), sq_nonneg T0,
    mul_nonneg hq0 (sq_nonneg T0), mul_nonneg (mul_nonneg hq0 hq0) hA]

/-- **Upper Kac–Murdock–Szegő bound** `(1 − q) K_q(x) ≤ (1 + q)|x|²` for `0 ≤ q ≤ 1`. -/
theorem kmsForm_upper {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (x : ℕ → ℝ) :
    (1 - q) * kmsForm q N x ≤ (1 + q) * ∑ k ∈ range N, x k ^ 2 := by
  set A := ∑ k ∈ range N, towerTail q N x (k + 1) ^ 2
  set T0 := towerTail q N x 0
  have hA : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hx : (1 - q) * T0 ^ 2 + (1 - q) ^ 2 * A ≤ ∑ k ∈ range N, x k ^ 2 := by
    rw [sum_sq_eq_tail q]
    calc (1 - q) * T0 ^ 2 + (1 - q) ^ 2 * A
        = ∑ k ∈ range N, ((1 - q) * towerTail q N x k ^ 2 -
            q * (1 - q) * towerTail q N x (k + 1) ^ 2) := by
          rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_towerTail_sq]
          ring
      _ ≤ ∑ k ∈ range N, (towerTail q N x k - q * towerTail q N x (k + 1)) ^ 2 := by
          refine sum_le_sum fun k _ => ?_
          nlinarith [mul_nonneg hq0 (sq_nonneg (towerTail q N x k - towerTail q N x (k + 1)))]
  rw [kmsForm_eq_tail]
  nlinarith [mul_le_mul_of_nonneg_left hx (show 0 ≤ 1 + q by linarith), sq_nonneg T0,
    mul_nonneg hq0 (sq_nonneg T0), mul_nonneg hq0 hA, mul_nonneg (mul_nonneg hq0 hq0) hA,
    mul_nonneg (mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ 1 - q)) hA]

/-! ### Orbit sizes as level weights -/

/-- For `q = p^{−1/2}` the level `k ≥ 1` has weight `(1 − q²) q^{−2k} = φ(p^k)`. -/
theorem one_sub_inv_mul_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (1 - (1 / Real.sqrt p) ^ 2) * (Real.sqrt p) ^ (2 * (k + 1)) = Nat.totient (p ^ (k + 1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  rw [Nat.totient_prime_pow_succ hp, pow_mul, hs, div_pow, hs, one_pow]
  push_cast
  rw [Nat.cast_sub hp.one_le]
  field_simp
  ring

/-- **The tower form counts levels by orbit sizes**:
`K_{p^{−1/2}}(x) = Σ_{k < N} φ(p^k) (Σ_{k ≤ i < N} x_i p^{−i/2})²`. -/
theorem kmsForm_eq_orbit_levels {p : ℕ} (hp : p.Prime) (N : ℕ) (x : ℕ → ℝ) :
    kmsForm (1 / Real.sqrt p) N x =
      ∑ k ∈ range N, (Nat.totient (p ^ k) : ℝ) *
        (∑ i ∈ Ico k N, x i * (1 / Real.sqrt p) ^ i) ^ 2 := by
  set q := 1 / Real.sqrt p
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  -- the level sum is `q^k T_k`
  have hlev : ∀ k ≤ N, ∑ i ∈ Ico k N, x i * q ^ i = q ^ k * towerTail q N x k := by
    intro k hk
    rw [towerTail, mul_sum, sum_Ico_eq_sum_range]
    refine sum_congr rfl fun i _ => ?_
    rw [add_comm k i, pow_add]
    ring
  have hq : q * Real.sqrt p = 1 := by simp only [q, one_div, inv_mul_cancel₀ hsp.ne']
  rw [kmsForm_eq_tail]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [towerTail]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hk : ∀ k ∈ range M, (Nat.totient (p ^ (k + 1)) : ℝ) *
      (∑ i ∈ Ico (k + 1) (M + 1), x i * q ^ i) ^ 2 =
        (1 - q ^ 2) * towerTail q (M + 1) x (k + 1) ^ 2 := by
    intro k hk
    rw [hlev (k + 1) (by simp at hk; omega), ← one_sub_inv_mul_pow hp k]
    have hpow : (Real.sqrt p) ^ (2 * (k + 1)) * (q ^ (k + 1)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm (k + 1) 2, ← mul_pow, mul_comm, hq, one_pow]
    calc (1 - (1 / Real.sqrt p) ^ 2) * Real.sqrt p ^ (2 * (k + 1)) *
          (q ^ (k + 1) * towerTail q (M + 1) x (k + 1)) ^ 2
        = (1 - q ^ 2) * ((Real.sqrt p) ^ (2 * (k + 1)) * (q ^ (k + 1)) ^ 2) *
            towerTail q (M + 1) x (k + 1) ^ 2 := by ring
      _ = _ := by rw [hpow, mul_one]
  rw [Finset.sum_range_succ (fun k => towerTail q (M + 1) x (k + 1) ^ 2) M, towerTail_self,
    Finset.sum_range_succ' (fun k => (Nat.totient (p ^ k) : ℝ) *
      (∑ i ∈ Ico k (M + 1), x i * q ^ i) ^ 2) M, sum_congr rfl hk, hlev 0 (Nat.zero_le _)]
  simp only [pow_zero, one_mul, Nat.totient_one, Nat.cast_one]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, mul_sum]
  ring

/-! ### Weil's prime kernel on a ladder -/

/-- **Weil's prime kernel on a `p`-ladder**: `P(cp^i, cp^j) = log p · p^{−|i−j|/2}` for `i ≠ j`. -/
theorem weilPrimeKernel_ladder {p c : ℕ} (hp : p.Prime) (hc : 0 < c) (i j : ℕ) :
    weilPrimeKernel (c * p ^ i) (c * p ^ j) =
      if i = j then 0 else Real.log p * kmsEntry (1 / Real.sqrt p) i j := by
  have hpos : ∀ a, 0 < c * p ^ a := fun a => Nat.mul_pos hc (pow_pos hp.pos a)
  have hinj : ∀ a b, c * p ^ a = c * p ^ b ↔ a = b := fun a b => by
    rw [Nat.mul_left_cancel_iff hc]; exact Nat.pow_right_injective hp.two_le |>.eq_iff
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  -- the entry for a ratio `p^d`, `d ≥ 1`
  have hent : ∀ d, 0 < d → Λ (p ^ d) / Real.sqrt ((p ^ d : ℕ) : ℝ) =
      Real.log p * (1 / Real.sqrt p) ^ d := by
    intro d hd
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hsq : Real.sqrt ((p : ℝ) ^ d) = Real.sqrt p ^ d := by
      rw [show ((p : ℝ)) ^ d = (Real.sqrt p ^ d) ^ 2 by
        rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hp0]]
      exact Real.sqrt_sq (by positivity)
    rw [ArithmeticFunction.vonMangoldt_apply_pow hd.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, hsq, one_div_pow,
      div_eq_mul_inv, one_div]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hdvd : c * p ^ i ∣ c * p ^ j := Nat.mul_dvd_mul_left c (pow_dvd_pow p hij.le)
    have hdiv : c * p ^ j / (c * p ^ i) = p ^ (j - i) := by
      rw [Nat.mul_div_mul_left _ _ hc, Nat.pow_div hij.le hp.pos]
    rw [weilPrimeKernel, if_pos ⟨hdvd, (hinj i j).not.mpr hij.ne⟩, hdiv, hent _ (by omega),
      if_neg hij.ne, kmsEntry, max_eq_right hij.le, min_eq_left hij.le]
  · simp [weilPrimeKernel]
  · have hdvd : c * p ^ j ∣ c * p ^ i := Nat.mul_dvd_mul_left c (pow_dvd_pow p hij.le)
    have hndvd : ¬ (c * p ^ i ∣ c * p ^ j ∧ c * p ^ i ≠ c * p ^ j) := by
      rintro ⟨h, -⟩
      have := Nat.le_of_dvd (hpos j) h
      have h2 : c * p ^ j < c * p ^ i :=
        Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hp.one_lt hij) hc
      omega
    have hdiv : c * p ^ i / (c * p ^ j) = p ^ (i - j) := by
      rw [Nat.mul_div_mul_left _ _ hc, Nat.pow_div hij.le hp.pos]
    rw [weilPrimeKernel, if_neg hndvd, if_pos ⟨hdvd, (hinj j i).not.mpr hij.ne⟩, hdiv,
      hent _ (by omega), if_neg hij.ne', kmsEntry, max_eq_left hij.le, min_eq_right hij.le]

/-- The prime form of a cycle on the ladder `c, cp, …, cp^{N−1}`. -/
def ladderForm (p c N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * weilPrimeKernel (c * p ^ i) (c * p ^ j)

/-- **On a ladder Weil's prime form is `log p` times the tower form minus the identity.** -/
theorem ladderForm_eq {p c : ℕ} (hp : p.Prime) (hc : 0 < c) (N : ℕ) (x : ℕ → ℝ) :
    ladderForm p c N x = Real.log p * (kmsForm (1 / Real.sqrt p) N x - ∑ i ∈ range N, x i ^ 2) := by
  simp only [ladderForm, kmsForm, weilPrimeKernel_ladder hp hc, mul_sub, mul_sum]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_erase_add _ _ hi, ← Finset.sum_erase_add (range N) _ hi]
  simp only [if_true, kmsEntry_self]
  have : ∀ j ∈ (range N).erase i, x i * x j * (if i = j then 0 else
      Real.log p * kmsEntry (1 / Real.sqrt p) i j) =
        Real.log p * (x i * x j * kmsEntry (1 / Real.sqrt p) i j) := by
    intro j hj
    rw [if_neg (Ne.symm (ne_of_mem_erase hj))]
    ring
  rw [sum_congr rfl this, ← mul_sum]
  ring

theorem inv_sqrt_prime_nonneg (p : ℕ) : 0 ≤ 1 / Real.sqrt p := by positivity

theorem inv_sqrt_prime_lt_one {p : ℕ} (hp : p.Prime) : 1 / Real.sqrt p < 1 := by
  have h1 : (1 : ℝ) < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast hp.one_lt)
  rw [div_lt_one (by linarith)]
  exact h1

/-- **The local prime form is bounded below**: `(1 + q) · ladder ≥ −2q log p |x|²`, `q = p^{−1/2}`. -/
theorem ladderForm_lower {p c : ℕ} (hp : p.Prime) (hc : 0 < c) (N : ℕ) (x : ℕ → ℝ) :
    -(2 * (1 / Real.sqrt p) * Real.log p * ∑ i ∈ range N, x i ^ 2) ≤
      (1 + 1 / Real.sqrt p) * ladderForm p c N x := by
  set q := 1 / Real.sqrt p
  have hq0 : 0 ≤ q := inv_sqrt_prime_nonneg p
  have hq1 : q < 1 := inv_sqrt_prime_lt_one hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have h := kmsForm_lower hq0 hq1.le N x
  rw [ladderForm_eq hp hc]
  nlinarith [mul_le_mul_of_nonneg_left h hlog]

/-- **The local prime form is bounded above**: `(1 − q) · ladder ≤ 2q log p |x|²`, `q = p^{−1/2}`. -/
theorem ladderForm_upper {p c : ℕ} (hp : p.Prime) (hc : 0 < c) (N : ℕ) (x : ℕ → ℝ) :
    (1 - 1 / Real.sqrt p) * ladderForm p c N x ≤
      2 * (1 / Real.sqrt p) * Real.log p * ∑ i ∈ range N, x i ^ 2 := by
  set q := 1 / Real.sqrt p
  have hq0 : 0 ≤ q := inv_sqrt_prime_nonneg p
  have hq1 : q < 1 := inv_sqrt_prime_lt_one hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have h := kmsForm_upper hq0 hq1.le N x
  rw [ladderForm_eq hp hc]
  nlinarith [mul_le_mul_of_nonneg_left h hlog]

end GaloisForLFunctions.ArithmeticIntersectionTheory
