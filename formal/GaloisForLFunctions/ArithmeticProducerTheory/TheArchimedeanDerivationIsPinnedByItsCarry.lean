import Mathlib

/-!
# The archimedean derivation is pinned by its carry

At a prime `p` the integers carry the Fermat quotient `δ_p(n) = (n − n^p)/p`: the power map
`n ↦ n^p` is `p`-adically close to the identity, and its carry `(m+n)^p − m^p − n^p` is divisible
by `p` (`prime_dvd_add_pow_sub`). At the real place the power maps `x ↦ x^a` approach the identity
as `a → 1`; their generator there is the derivation `D(x) = x log x`, which is multiplicative
(`D(xy) = x D(y) + y D(x)`) and whose carry under addition is the entropy
`(x+y) log (x+y) − x log x − y log y` (`entropyCarry`, `hasDerivAt_powerCarry`).

* `entropyCarry_nonneg`, `entropyCarry_le`: the carry lies in `[0, (x+y) log 2]`; every power carry
  is nonnegative (`pow_add_pow_le_add_pow`).
* `log_choose_le_entropyCarry`: `log C(m+n, m) ≤` entropy carry. By Kummer's theorem the left side
  is `Σ_p (carries of m + n in base p) · log p`: the carries at the finite places are dominated by
  the carry at the real place. This is the comparison behind Chebyshev's bound.
* `eq_mul_log_of_carry_ge` (**rigidity**): let `L` be completely additive. If the carry of
  `n ↦ n · L(n)` is bounded below by `−K (m+n)`, then `L = c · log`.
* `carry_bddBelow_iff`, `exists_carry_lt_and_gt`: a linear lower bound on the carry characterizes
  the multiples of `log`; for every other weighting of the primes the carry is unbounded in both
  directions on the linear scale.

A derivation compatible with the Adams operations is an Euler derivation with one free weight per
prime. The sign of the carry under addition removes this freedom: only the weights `c · log p`
have an entropy.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticProducerTheory

/-! ### The entropy carry -/

/-- The carry of the derivation `x ↦ x log x` under addition, the entropy of the splitting
`x + y` on the scale `x + y`. -/
def entropyCarry (x y : ℝ) : ℝ :=
  (x + y) * Real.log (x + y) - x * Real.log x - y * Real.log y

theorem entropyCarry_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 ≤ entropyCarry x y := by
  have h1 : Real.log x ≤ Real.log (x + y) := Real.log_le_log hx (by linarith)
  have h2 : Real.log y ≤ Real.log (x + y) := Real.log_le_log hy (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h1 hx.le
  have h4 := mul_le_mul_of_nonneg_left h2 hy.le
  rw [entropyCarry]
  linarith

/-- The entropy carry is at most `(x + y) log 2`, by `log t ≤ t − 1` at `t = (x+y)/(2x)` and
`(x+y)/(2y)`. -/
theorem entropyCarry_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    entropyCarry x y ≤ (x + y) * Real.log 2 := by
  have hxy : 0 < x + y := by linarith
  have key : ∀ u : ℝ, 0 < u →
      u * (Real.log (x + y) - (Real.log 2 + Real.log u)) ≤ (x + y) / 2 - u := by
    intro u hu
    have h := Real.log_le_sub_one_of_pos (div_pos hxy (mul_pos two_pos hu))
    rw [Real.log_div hxy.ne' (mul_pos two_pos hu).ne', Real.log_mul two_ne_zero hu.ne'] at h
    have h2 := mul_le_mul_of_nonneg_left h hu.le
    have e : u * ((x + y) / (2 * u) - 1) = (x + y) / 2 - u := by
      rw [mul_sub, mul_one, mul_div_assoc', mul_comm u (x + y), mul_div_mul_right _ _ hu.ne']
    linarith
  have hx' := key x hx
  have hy' := key y hy
  rw [entropyCarry]
  linarith

/-- The entropy carry is the derivative at `a = 1` of the carry of the power map `x ↦ x^a`. -/
theorem hasDerivAt_powerCarry {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun a : ℝ => (x + y) ^ a - x ^ a - y ^ a) (entropyCarry x y) 1 := by
  have h := (((Real.hasStrictDerivAt_const_rpow (by linarith : 0 < x + y) 1).hasDerivAt.sub
    (Real.hasStrictDerivAt_const_rpow hx 1).hasDerivAt).sub
    (Real.hasStrictDerivAt_const_rpow hy 1).hasDerivAt)
  simp only [Real.rpow_one] at h
  exact h

/-- The carry of every power map is nonnegative. -/
theorem pow_add_pow_le_add_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    x ^ k + y ^ k ≤ (x + y) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k _ ih =>
    have h1 : (x ^ k + y ^ k) * (x + y) ≤ (x + y) ^ k * (x + y) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : 0 ≤ x ^ k * y := mul_nonneg (pow_nonneg hx k) hy
    have h3 : 0 ≤ y ^ k * x := mul_nonneg (pow_nonneg hy k) hx
    rw [pow_succ, pow_succ, pow_succ]
    linarith

/-- At a prime `p` the carry of `n ↦ n^p` on the integers is divisible by `p`: the Fermat
quotient has an integral carry. -/
theorem prime_dvd_add_pow_sub (p : ℕ) [Fact p.Prime] (m n : ℤ) :
    (p : ℤ) ∣ (m + n) ^ p - m ^ p - n ^ p := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card, ZMod.pow_card, ZMod.pow_card]
  ring

/-- **The finite carries are dominated by the archimedean carry.** `log C(m+n, m)` is at most the
entropy carry: `C(m+n, m) m^m n^n` is one term of the binomial expansion of `(m+n)^(m+n)`. -/
theorem log_choose_le_entropyCarry {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Real.log ((m + n).choose m) ≤ entropyCarry m n := by
  have hnat : (m + n).choose m * (m ^ m * n ^ n) ≤ (m + n) ^ (m + n) := by
    rw [add_pow]
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega : m < m + n + 1)))
    simp only [Nat.add_sub_cancel_left, Nat.cast_id]
    exact le_of_eq (by ring)
  have hreal : ((m + n).choose m : ℝ) * ((m : ℝ) ^ m * (n : ℝ) ^ n) ≤ ((m : ℝ) + n) ^ (m + n) := by
    exact_mod_cast hnat
  have hc : (0 : ℝ) < (m + n).choose m := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right m n)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmm := pow_pos hm0 m
  have hnn := pow_pos hn0 n
  have hlog := Real.log_le_log (mul_pos hc (mul_pos hmm hnn)) hreal
  rw [Real.log_mul hc.ne' (mul_pos hmm hnn).ne', Real.log_mul hmm.ne' hnn.ne', Real.log_pow,
    Real.log_pow, Real.log_pow] at hlog
  rw [entropyCarry]
  push_cast at hlog
  linarith

/-- The same comparison with the binomial coefficient read through its factorization: the
exponent of `p` is the number of carries of `m + n` in base `p`. -/
theorem sum_factorization_choose_le_entropyCarry {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (((m + n).choose m).factorization.sum fun p t => (t : ℝ) * Real.log p) ≤ entropyCarry m n := by
  rw [← Real.log_nat_eq_sum_factorization]
  exact log_choose_le_entropyCarry hm hn

/-! ### Rigidity -/

/-- The carry under addition of the multiplicative derivation `n ↦ n · L n`. -/
def derivationCarry (L : ℕ → ℝ) (m n : ℕ) : ℝ :=
  ((m : ℝ) + n) * L (m + n) - m * L m - n * L n

/-- The carry of `c · log` is `c` times the entropy carry. -/
theorem derivationCarry_mul_log (c : ℝ) (m n : ℕ) :
    derivationCarry (fun k => c * Real.log k) m n = c * entropyCarry m n := by
  rw [derivationCarry, entropyCarry]
  push_cast
  ring

section Rigidity

variable {L : ℕ → ℝ} {K : ℝ}

private theorem map_one_eq_zero (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L (m * n) = L m + L n) : L 1 = 0 := by
  have h := hmul 1 1 le_rfl le_rfl
  rw [mul_one] at h
  linarith

private theorem map_pow_eq (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L (m * n) = L m + L n) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : L (n ^ k) = k * L n := by
  induction k with
  | zero => simp [map_one_eq_zero hmul]
  | succ k ih =>
    rw [pow_succ, hmul _ _ (Nat.one_le_pow _ _ hn) hn, ih]
    push_cast
    ring

private theorem neg_le_map_two (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L (m * n) = L m + L n) (hcarry : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → -(K * ((m : ℝ) + n)) ≤ derivationCarry L m n) : -K ≤ L 2 := by
  have h := hcarry 1 1 le_rfl le_rfl
  have h1 := map_one_eq_zero hmul
  rw [derivationCarry, show (1 : ℕ) + 1 = 2 from rfl, Nat.cast_one] at h
  linarith

/-- A linear lower bound on the carry gives a logarithmic lower bound on `L`, by splitting
`n` into halves. -/
private theorem neg_mul_clog_le (hK : 0 ≤ K) (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L (m * n) = L m + L n) (hcarry : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → -(K * ((m : ℝ) + n)) ≤ derivationCarry L m n) :
    ∀ n : ℕ, 1 ≤ n → -(K * Nat.clog 2 n) ≤ L n := by
  have h1 := map_one_eq_zero hmul
  have h2 := neg_le_map_two hmul hcarry
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [h1]
    · obtain ⟨h, rfl | rfl⟩ := Nat.even_or_odd' n
      · have hh : 1 ≤ h := by omega
        have ihh := ih h (by omega) hh
        have hc : Nat.clog 2 (2 * h) = Nat.clog 2 h + 1 := by
          rw [Nat.clog_of_two_le (by norm_num) hge]
          have e : (2 * h + 2 - 1) / 2 = h := by omega
          rw [e]
        rw [hmul 2 h (by norm_num) hh, hc]
        push_cast
        linarith
      · have hh : 1 ≤ h := by omega
        have ih1 := ih h (by omega) hh
        have ih2 := ih (h + 1) (by omega) (by omega)
        have hc : Nat.clog 2 (2 * h + 1) = Nat.clog 2 (h + 1) + 1 := by
          rw [Nat.clog_of_two_le (by norm_num) hge]
          have e : (2 * h + 1 + 2 - 1) / 2 = h + 1 := by omega
          rw [e]
        have hmono : (Nat.clog 2 h : ℝ) ≤ Nat.clog 2 (h + 1) := by
          exact_mod_cast Nat.clog_mono_right 2 (Nat.le_succ h)
        have hcar := hcarry h (h + 1) hh (by omega)
        rw [derivationCarry, show h + (h + 1) = 2 * h + 1 by ring] at hcar
        push_cast at hcar
        have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
        have p1 := mul_le_mul_of_nonneg_left ih1 hh0
        have p2 := mul_le_mul_of_nonneg_left ih2 (by linarith : (0 : ℝ) ≤ (h : ℝ) + 1)
        have p3 := mul_le_mul_of_nonneg_left hmono (mul_nonneg hh0 hK)
        have hN : (0 : ℝ) < 2 * (h : ℝ) + 1 := by linarith
        rw [hc]
        push_cast
        refine le_of_mul_le_mul_left ?_ hN
        linarith

/-- One application of the carry bound to `N = M q + r`. -/
private theorem div_step (hK : 0 ≤ K) (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L (m * n) = L m + L n) (hcarry : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → -(K * ((m : ℝ) + n)) ≤ derivationCarry L m n) {N M : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    ((N / M : ℕ) : ℝ) * M * L M - K * (((N / M : ℕ) : ℝ) * M) * Nat.clog 2 (N / M)
      - K * ((N % M : ℕ) : ℝ) * Nat.clog 2 M - K * N ≤ N * L N := by
  have hq : 1 ≤ N / M := Nat.div_pos hMN hM
  have hLq := neg_mul_clog_le hK hmul hcarry (N / M) hq
  have hdec : M * (N / M) + N % M = N := Nat.div_add_mod N M
  have hdecR : (M : ℝ) * ((N / M : ℕ) : ℝ) + ((N % M : ℕ) : ℝ) = N := by exact_mod_cast hdec
  have hMq : L (M * (N / M)) = L M + L (N / M) := hmul _ _ hM hq
  have hq0 : (0 : ℝ) ≤ ((N / M : ℕ) : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ ((N % M : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have p1 := mul_le_mul_of_nonneg_left hLq (mul_nonneg hq0 hM0)
  rcases Nat.eq_zero_or_pos (N % M) with hr | hr
  · have hrR : ((N % M : ℕ) : ℝ) = 0 := by rw [hr, Nat.cast_zero]
    have hNeq : M * (N / M) = N := by
      have h := hdec
      rw [hr, add_zero] at h
      exact h
    have hLN : L N = L M + L (N / M) := by
      rw [← hMq, hNeq]
    have e1 : (N : ℝ) * (L M + L (N / M)) =
        ((N / M : ℕ) : ℝ) * M * L M + ((N / M : ℕ) : ℝ) * M * L (N / M) := by
      rw [← hdecR, hrR]
      ring
    have hKN := mul_nonneg hK hN0
    rw [hLN, e1, hrR]
    linarith
  · have hLr := neg_mul_clog_le hK hmul hcarry (N % M) hr
    have hcr : (Nat.clog 2 (N % M) : ℝ) ≤ Nat.clog 2 M := by
      exact_mod_cast Nat.clog_mono_right 2 (Nat.mod_lt N hM).le
    have hcar := hcarry (M * (N / M)) (N % M) (Nat.mul_pos hM hq) hr
    rw [derivationCarry, hdec, hMq] at hcar
    push_cast at hcar
    rw [hdecR] at hcar
    have p2 := mul_le_mul_of_nonneg_left hLr hr0
    have p3 := mul_le_mul_of_nonneg_left hcr (mul_nonneg hK hr0)
    linarith

/-- Comparing a power of `a` with the power of `b` just below it, at relative precision `1/T`. -/
private theorem power_step (hK : 0 ≤ K) (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L (m * n) = L m + L n) (hcarry : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → -(K * ((m : ℝ) + n)) ≤ derivationCarry L m n) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hy : 0 ≤ L b) {T : ℕ} (hT : 2 ≤ T) (j : ℕ) :
    ∃ k : ℕ, ((k : ℝ) - 1) * Real.log a ≤ Real.log T + j * Real.log b ∧
      ((T : ℝ) - 1) * (j * L b) - T * (K * Nat.clog 2 (a * T)) - K * (j * Nat.clog 2 b) - T * K
        ≤ T * (k * L a) := by
  have ha1 : 1 < a := by omega
  have hbpos : 0 < b ^ j := pow_pos (by omega) j
  have hx : 1 < T * b ^ j :=
    lt_of_lt_of_le (by omega : 1 < T) (Nat.le_mul_of_pos_right T hbpos)
  have hk1 : T * b ^ j ≤ a ^ Nat.clog a (T * b ^ j) := Nat.le_pow_clog ha1 _
  have hkpos : 0 < Nat.clog a (T * b ^ j) := Nat.clog_pos ha1 hx
  have hk2 : a ^ (Nat.clog a (T * b ^ j)).pred < T * b ^ j := Nat.pow_pred_clog_lt_self ha1 hx
  generalize Nat.clog a (T * b ^ j) = k at hk1 hkpos hk2
  rw [Nat.pred_eq_sub_one] at hk2
  have hk3 : a ^ k < a * T * b ^ j := by
    have e : a ^ k = a * a ^ (k - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hkpos]
    rw [e, mul_assoc]
    exact mul_lt_mul_of_pos_left hk2 (by omega)
  refine ⟨k, ?_, ?_⟩
  · have hpos : (0 : ℝ) < (a : ℝ) ^ (k - 1) := pow_pos (by exact_mod_cast (by omega : 0 < a)) _
    have hlt : (a : ℝ) ^ (k - 1) < (T : ℝ) * (b : ℝ) ^ j := by exact_mod_cast hk2
    have hlog := (Real.log_lt_log hpos hlt).le
    have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
    have hb0 : (b : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : b ≠ 0))
    rw [Real.log_pow, Real.log_mul hT0 hb0, Real.log_pow, Nat.cast_pred hkpos] at hlog
    exact hlog
  · have hMN : b ^ j ≤ a ^ k := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hk1
    have hB := div_step hK hmul hcarry hbpos hMN
    have hqa : a ^ k / b ^ j ≤ a * T := ((Nat.div_lt_iff_lt_mul hbpos).mpr hk3).le
    have hcq : (Nat.clog 2 (a ^ k / b ^ j) : ℝ) ≤ Nat.clog 2 (a * T) := by
      exact_mod_cast Nat.clog_mono_right 2 hqa
    have hcM : (Nat.clog 2 (b ^ j) : ℝ) ≤ j * Nat.clog 2 b := by
      have h1 : b ^ j ≤ 2 ^ (j * Nat.clog 2 b) := by
        rw [mul_comm, pow_mul]
        exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) b) j
      exact_mod_cast Nat.clog_le_of_le_pow h1
    rw [map_pow_eq hmul (by omega : 1 ≤ b) j, map_pow_eq hmul (by omega : 1 ≤ a) k] at hB
    have hdecR : ((b ^ j : ℕ) : ℝ) * ((a ^ k / b ^ j : ℕ) : ℝ) + ((a ^ k % b ^ j : ℕ) : ℝ) =
        ((a ^ k : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_add_mod (a ^ k) (b ^ j)
    have hTM : (T : ℝ) * ((b ^ j : ℕ) : ℝ) ≤ ((a ^ k : ℕ) : ℝ) := by exact_mod_cast hk1
    have hrM : ((a ^ k % b ^ j : ℕ) : ℝ) ≤ ((b ^ j : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_lt (a ^ k) hbpos).le
    have hNpos : (0 : ℝ) < ((a ^ k : ℕ) : ℝ) := by
      exact_mod_cast pow_pos (by omega : 0 < a) k
    have hq0 : (0 : ℝ) ≤ ((a ^ k / b ^ j : ℕ) : ℝ) := Nat.cast_nonneg _
    have hr0 : (0 : ℝ) ≤ ((a ^ k % b ^ j : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcq0 : (0 : ℝ) ≤ (Nat.clog 2 (a ^ k / b ^ j) : ℝ) := Nat.cast_nonneg _
    have hcM0 : (0 : ℝ) ≤ (Nat.clog 2 (b ^ j) : ℝ) := Nat.cast_nonneg _
    have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
    have hjy : (0 : ℝ) ≤ (j : ℝ) * L b := mul_nonneg (Nat.cast_nonneg _) hy
    generalize ((a ^ k / b ^ j : ℕ) : ℝ) = qr at hB hdecR hq0
    generalize ((a ^ k % b ^ j : ℕ) : ℝ) = rr at hB hdecR hrM hr0
    generalize ((a ^ k : ℕ) : ℝ) = Nr at hB hdecR hTM hNpos
    generalize ((b ^ j : ℕ) : ℝ) = Mr at hB hdecR hTM hrM
    generalize (Nat.clog 2 (a ^ k / b ^ j) : ℝ) = cq at hB hcq hcq0
    generalize (Nat.clog 2 (b ^ j) : ℝ) = cM at hB hcM hcM0
    have hTr : (T : ℝ) * rr ≤ T * Mr := mul_le_mul_of_nonneg_left hrM hT0
    have hqMN : qr * Mr ≤ Nr := by linarith
    have hd2 : (T : ℝ) * (qr * Mr) = T * Nr - T * rr := by
      rw [← hdecR]
      ring
    have h_i : ((T : ℝ) - 1) * Nr * (j * L b) ≤ T * (qr * Mr) * (j * L b) :=
      mul_le_mul_of_nonneg_right (by linarith) hjy
    have h_ii : (T : ℝ) * (K * (qr * Mr) * cq) ≤ T * (K * Nr * Nat.clog 2 (a * T)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul_of_nonneg_left hqMN hK) hcq hcq0 (mul_nonneg hK hNpos.le)) hT0
    have h_iii : K * ((T : ℝ) * rr) * cM ≤ K * Nr * (j * Nat.clog 2 b) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hTr.trans hTM) hK) hcM hcM0
        (mul_nonneg hK hNpos.le)
    have hB' := mul_le_mul_of_nonneg_left hB hT0
    have key : Nr * (((T : ℝ) - 1) * (j * L b) - T * (K * Nat.clog 2 (a * T))
        - K * (j * Nat.clog 2 b) - T * K) ≤ Nr * (T * (k * L a)) := by
      linarith
    exact le_of_mul_le_mul_left key hNpos

/-- A real number whose multiples by the integers `≥ 2` are bounded above is nonpositive. -/
private theorem nonpos_of_forall_nat_mul_le {A C : ℝ} (h : ∀ j : ℕ, 2 ≤ j → (j : ℝ) * A ≤ C) :
    A ≤ 0 := by
  by_contra hA
  push Not at hA
  obtain ⟨j, hj⟩ := exists_nat_gt (C / A)
  have h1 := h (j + 2) (by omega)
  rw [div_lt_iff₀ hA] at hj
  push_cast at h1
  linarith

/-- Where `L b > 0`, the ratio `L / log` at `a` is at least the ratio at `b`. -/
private theorem log_mul_le_of_pos (hK : 0 ≤ K) (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L (m * n) = L m + L n) (hcarry : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → -(K * ((m : ℝ) + n)) ≤ derivationCarry L m n) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hy : 0 < L b) : L b * Real.log a ≤ L a * Real.log b := by
  have hα : 0 < Real.log a := Real.log_pos (by exact_mod_cast (by omega : 1 < a))
  have hxp0 : 0 ≤ max (L a) 0 := le_max_right _ _
  have hxa : L a ≤ max (L a) 0 := le_max_left _ _
  have step1 : ∀ T : ℕ, 2 ≤ T →
      Real.log a * (((T : ℝ) - 1) * L b) - Real.log a * (K * Nat.clog 2 b)
        - T * (Real.log b * max (L a) 0) ≤ 0 := by
    intro T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
    refine nonpos_of_forall_nat_mul_le
      (C := Real.log a * (T * (K * Nat.clog 2 (a * T))) + Real.log a * (T * K)
        + T * ((Real.log a + Real.log T) * max (L a) 0)) fun j _ => ?_
    obtain ⟨k, hk1, hk2⟩ := power_step hK hmul hcarry ha hb hy.le hT j
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (k : ℝ) * L a ≤ k * max (L a) 0 := mul_le_mul_of_nonneg_left hxa hk0
    have h2 := mul_le_mul_of_nonneg_right hk1 hxp0
    have h3 := mul_le_mul_of_nonneg_left hk2 hα.le
    have h4 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hα.le hTpos.le)
    have h5 := mul_le_mul_of_nonneg_left h2 hTpos.le
    linarith
  have step2 : Real.log a * L b - Real.log b * max (L a) 0 ≤ 0 := by
    refine nonpos_of_forall_nat_mul_le
      (C := Real.log a * L b + Real.log a * (K * Nat.clog 2 b)) fun T hT => ?_
    have h := step1 T hT
    linarith
  rcases le_or_gt (L a) 0 with h | h
  · rw [max_eq_right h] at step2
    have h1 := mul_pos hα hy
    linarith
  · rw [max_eq_left h.le] at step2
    linarith

/-- If `L 2 > 0`, then `L` is proportional to `log`. -/
private theorem mul_log_two_eq (hK : 0 ≤ K) (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L (m * n) = L m + L n) (hcarry : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → -(K * ((m : ℝ) + n)) ≤ derivationCarry L m n) (h2 : 0 < L 2) :
    ∀ n : ℕ, 2 ≤ n → L n * Real.log ((2 : ℕ) : ℝ) = L 2 * Real.log n := by
  intro n hn
  have h1 := log_mul_le_of_pos hK hmul hcarry hn (le_refl 2) h2
  have hn0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hl2 : 0 < Real.log ((2 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  have hLn : 0 < L n := by
    by_contra h
    push Not at h
    have h3 := mul_nonneg (neg_nonneg.mpr h) hl2.le
    have h4 := mul_pos h2 hn0
    linarith
  exact le_antisymm (log_mul_le_of_pos hK hmul hcarry (le_refl 2) hn hLn) h1

end Rigidity

/-- **Rigidity of the archimedean derivation.** Let `L` be completely additive. If the carry of
the derivation `n ↦ n · L n` under addition is bounded below by `−K (m + n)`, then `L` is a
multiple of `log`. After adding a multiple of `log` one has `L 2 > 0`; the carry bound applied
to `a^k = q b^j + r` with `q` of bounded size compares `k L(a)` with `j L(b)`, and `k/j` tends to
`log b / log a`. -/
theorem eq_mul_log_of_carry_ge {L : ℕ → ℝ} {K : ℝ} (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L (m * n) = L m + L n) (hcarry : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → -(K * ((m : ℝ) + n)) ≤ derivationCarry L m n) :
    ∀ n : ℕ, 1 ≤ n → L n = L 2 / Real.log 2 * Real.log n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 := map_one_eq_zero hmul
  have hL2 := neg_le_map_two hmul hcarry
  obtain ⟨c₀, hc₀0, hc₀⟩ : ∃ c₀ : ℝ, 0 ≤ c₀ ∧ c₀ * Real.log 2 = |K| + 1 :=
    ⟨(|K| + 1) / Real.log 2, div_nonneg (by positivity) hl2.le, div_mul_cancel₀ _ hl2.ne'⟩
  obtain ⟨L', hL'⟩ : ∃ L' : ℕ → ℝ, ∀ n : ℕ, L' n = L n + c₀ * Real.log n :=
    ⟨fun n => L n + c₀ * Real.log n, fun _ => rfl⟩
  have hmul' : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L' (m * n) = L' m + L' n := by
    intro m n hm hn
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [hL', hL', hL', hmul m n hm hn, Nat.cast_mul, Real.log_mul hm0 hn0]
    ring
  have hcarry' : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      -(|K| * ((m : ℝ) + n)) ≤ derivationCarry L' m n := by
    intro m n hm hn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := hcarry m n hm hn
    have h2 := mul_nonneg hc₀0 (entropyCarry_nonneg hm0 hn0)
    have h3 := mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith : (0 : ℝ) ≤ (m : ℝ) + n)
    rw [entropyCarry] at h2
    rw [derivationCarry] at h1 ⊢
    rw [hL', hL', hL', Nat.cast_add]
    linarith
  have hL'2 : 0 < L' 2 := by
    rw [hL', Nat.cast_ofNat, hc₀]
    linarith [le_abs_self K]
  have key := mul_log_two_eq (abs_nonneg K) hmul' hcarry' hL'2
  intro n hn
  rcases Nat.lt_or_ge n 2 with h | h
  · have hn1 : n = 1 := by omega
    subst hn1
    simp [hL1]
  · have hk := key n h
    rw [hL' n, hL' 2] at hk
    simp only [Nat.cast_ofNat] at hk
    rw [div_mul_eq_mul_div, eq_div_iff hl2.ne']
    linarith

/-- **Characterization.** For a completely additive `L`, the carry of `n ↦ n · L n` has a linear
lower bound exactly when `L` is a multiple of `log`. -/
theorem carry_bddBelow_iff {L : ℕ → ℝ} (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L (m * n) = L m + L n) :
    (∃ K : ℝ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → -(K * ((m : ℝ) + n)) ≤ derivationCarry L m n) ↔
      ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → L n = c * Real.log n := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨_, eq_mul_log_of_carry_ge hmul hK⟩
  · rintro ⟨c, hc⟩
    refine ⟨|c| * Real.log 2, fun m n hm hn => ?_⟩
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := entropyCarry_nonneg hm0 hn0
    have h2 := entropyCarry_le hm0 hn0
    have h3 := mul_le_mul_of_nonneg_right (neg_abs_le c) h1
    have h4 := mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
    have e : derivationCarry L m n = c * entropyCarry m n := by
      rw [derivationCarry, entropyCarry, hc m hm, hc n hn, hc (m + n) (by omega)]
      push_cast
      ring
    rw [e]
    linarith

/-- **A reweighting of the primes has no entropy.** If a completely additive `L` is not a
multiple of `log`, the carry of `n ↦ n · L n` is unbounded in both directions on the linear
scale. -/
theorem exists_carry_lt_and_gt {L : ℕ → ℝ} (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L (m * n) = L m + L n)
    (hL : ¬ ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → L n = c * Real.log n) (K : ℝ) :
    (∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ derivationCarry L m n < -(K * ((m : ℝ) + n))) ∧
      ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ K * ((m : ℝ) + n) < derivationCarry L m n := by
  constructor
  · by_contra h
    push Not at h
    exact hL ⟨_, eq_mul_log_of_carry_ge hmul h⟩
  · by_contra h
    push Not at h
    obtain ⟨L', hL'⟩ : ∃ L' : ℕ → ℝ, ∀ n : ℕ, L' n = -L n := ⟨fun n => -L n, fun _ => rfl⟩
    have hmul' : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → L' (m * n) = L' m + L' n := by
      intro m n hm hn
      rw [hL', hL', hL', hmul m n hm hn]
      ring
    have hcarry' : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        -(K * ((m : ℝ) + n)) ≤ derivationCarry L' m n := by
      intro m n hm hn
      have h1 := h m n hm hn
      rw [derivationCarry] at h1 ⊢
      rw [hL', hL', hL']
      linarith
    have key := eq_mul_log_of_carry_ge hmul' hcarry'
    refine hL ⟨-(L' 2 / Real.log 2), fun n hn => ?_⟩
    have hk := key n hn
    rw [hL' n] at hk
    linarith

end GaloisForLFunctions.ArithmeticProducerTheory
