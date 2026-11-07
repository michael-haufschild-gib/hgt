import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheOneFifthRateUnderTheRiemannHypothesis
import GaloisForLFunctions.RHTower.MoebiusFloorSummatory

/-!
# Smooth compensation of the large primes

A multiplicity with increments `h` has letters `c = μ ∗ h`. The Möbius family takes `h = δ₁`, so every prime up to `T` is a letter, and every such prime
must then be detected by a far letter of size at least `T` times the far modulus.

Large primes need not be letters. With `T = y²`, take a prime `P ∈ (2y + 2, y²]` and let `h` jump up at `P` and down again at a nearby product `d_P = m t` with
`m, t ≤ 2y + 2` and `d_P ≤ P (1 + 4/y)`. Then

`c(k) = μ(k) + Σ_P μ(k/P) 1_{P ∣ k} − Σ_P μ(k/d_P) 1_{d_P ∣ k}`

vanishes on every `k ≤ T` with a prime factor above `2y + 2`. So all letters are `(2y + 2)`-smooth.

The multiplicity on `[1, T]` is exactly `1` plus short spikes on `[P, d_P)`, up to the drift `θ r`. Past `T` it is governed by the partial sums of `c`, namely
`M(x) + Σ_P (M(⌊x/P⌋) − M(⌊x/d_P⌋))`. The intervals `(x/d_P, x/P]` are short, and a point of `x/n` lies within `4 x/(n y)` of few primes, so trivial counting bounds
the sum over `P` by `5 x (1 + log x)/y`, with no input about primes. **So the compensation costs only `1/y`, and the level `η` of the Mertens function is untouched.**

The harmonic sum is not needed: the drift `θ` is read off at one large point.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The primes in `(2y + 2, y²]`, which the compensation removes from the alphabet. -/
def largePrimes (y : ℕ) : Finset ℕ := (Ioc (2 * y + 2) (y * y)).filter Nat.Prime

theorem mem_largePrimes {y P : ℕ} : P ∈ largePrimes y ↔ (2 * y + 2 < P ∧ P ≤ y * y) ∧ P.Prime := by
  simp only [largePrimes, mem_filter, mem_Ioc]

/-- A compensation: a nearby product of two coprime small factors above each large prime. -/
structure IsCompensation (y : ℕ) (d : ℕ → ℕ) : Prop where
  lt : ∀ P ∈ largePrimes y, P < d P
  le : ∀ P ∈ largePrimes y, (d P : ℝ) ≤ P * (1 + 4 / (y : ℝ))
  split : ∀ P ∈ largePrimes y, ∃ m t, d P = m * t ∧ m ≤ 2 * y + 2 ∧ t ≤ 2 * y + 2 ∧ Nat.Coprime m t

/-- **Compensations exist.** Take a prime `m` just above `P/y`, and a multiple of `m` just above `P`. -/
theorem exists_isCompensation {y : ℕ} (hy : 1 ≤ y) : ∃ d, IsCompensation y d := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hex : ∀ P, ∃ D : ℕ, P ∈ largePrimes y → P < D ∧ (D : ℝ) ≤ P * (1 + 4 / (y : ℝ)) ∧
      ∃ m t, D = m * t ∧ m ≤ 2 * y + 2 ∧ t ≤ 2 * y + 2 ∧ Nat.Coprime m t := by
    intro P
    by_cases hP : P ∈ largePrimes y
    swap
    · exact ⟨0, fun h => absurd h hP⟩
    obtain ⟨⟨hP1, hP2⟩, -⟩ := mem_largePrimes.mp hP
    obtain ⟨n, hn⟩ : ∃ n, n = P / y := ⟨_, rfl⟩
    have hn1 : n ≠ 0 := by
      rw [hn]
      exact (Nat.div_pos (by nlinarith) hy).ne'
    have hny : n ≤ y := by
      rw [hn]
      exact Nat.div_le_of_le_mul hP2
    obtain ⟨m, hm, hnm, hm2⟩ := Nat.exists_prime_lt_and_le_two_mul n hn1
    have hm0 := hm.pos
    have hlt : P < m * y := by
      have := (Nat.div_lt_iff_lt_mul hy).mp (hn ▸ hnm)
      exact this
    have ht₀ : P / m < y := Nat.div_lt_of_lt_mul hlt
    obtain ⟨t, ht⟩ : ∃ t, t = if m ∣ P / m + 1 then P / m + 2 else P / m + 1 := ⟨_, rfl⟩
    have hmt : ¬ m ∣ t := by
      rw [ht]
      split_ifs with h
      · intro h2
        have h3 : m ∣ 1 := by
          have h4 := (Nat.dvd_add_right h).mp (by simpa [add_assoc] using h2 : m ∣ (P / m + 1) + 1)
          exact h4
        have := hm.two_le
        have := Nat.le_of_dvd one_pos h3
        omega
      · exact h
    have ht1 : P / m + 1 ≤ t := by
      rw [ht]
      split_ifs <;> omega
    have ht2 : t ≤ P / m + 2 := by
      rw [ht]
      split_ifs <;> omega
    refine ⟨m * t, fun _ => ⟨?_, ?_, m, t, rfl, by omega, by omega, ?_⟩⟩
    · calc P < m * (P / m + 1) := Nat.lt_mul_div_succ P hm0
        _ ≤ m * t := Nat.mul_le_mul_left m ht1
    · -- `m t ≤ P + 2 m ≤ P + 4 P/y`.
      have h1 : m * t ≤ P + 2 * m := by
        calc m * t ≤ m * (P / m + 2) := Nat.mul_le_mul_left m ht2
          _ = m * (P / m) + 2 * m := by ring
          _ ≤ P + 2 * m := by
              have := Nat.mul_div_le P m
              omega
      have h2 : (m : ℝ) ≤ 2 * ((P : ℝ) / y) := by
        have h3 : (m : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hm2
        have h4 : (n : ℝ) ≤ (P : ℝ) / y := by
          rw [hn]
          exact Nat.cast_div_le
        linarith
      have h5 : ((m * t : ℕ) : ℝ) ≤ (P : ℝ) + 2 * m := by exact_mod_cast h1
      have e : (P : ℝ) * (1 + 4 / (y : ℝ)) = P + 4 * ((P : ℝ) / y) := by ring
      rw [e]
      linarith
    · exact (Nat.Prime.coprime_iff_not_dvd hm).mpr hmt
  choose d hd using hex
  exact ⟨d, ⟨fun P hP => (hd P hP).1, fun P hP => (hd P hP).2.1, fun P hP => (hd P hP).2.2⟩⟩

variable {y : ℕ} {d : ℕ → ℕ}

/-- The letters of the compensated stencil. -/
def compCoeff (y : ℕ) (d : ℕ → ℕ) (k : ℕ) : ℤ :=
  ArithmeticFunction.moebius k +
    ∑ P ∈ largePrimes y, (if P ∣ k then ArithmeticFunction.moebius (k / P) else 0) -
    ∑ P ∈ largePrimes y, (if d P ∣ k then ArithmeticFunction.moebius (k / d P) else 0)

/-- Summing a function over the multiples of `a`, with the Möbius weight of the cofactor. -/
private lemma sum_dvd_moebius {a : ℕ} (ha : 0 < a) (X : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Ioc 0 X, (if a ∣ k then (ArithmeticFunction.moebius (k / a) : ℝ) * F k else 0) =
      ∑ b ∈ Ioc 0 (X / a), (ArithmeticFunction.moebius b : ℝ) * F (a * b) := by
  rw [← sum_filter]
  refine sum_nbij' (fun k => k / a) (fun b => a * b) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨hk1, hk2⟩ := mem_filter.mp hk
    obtain ⟨hk3, hk4⟩ := mem_Ioc.mp hk1
    exact mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hk3 hk2) ha, Nat.div_le_div_right hk4⟩
  · intro b hb
    obtain ⟨hb1, hb2⟩ := mem_Ioc.mp hb
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.mul_pos ha hb1, ?_⟩, dvd_mul_right a b⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le ha).mp hb2
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro b _
    exact Nat.mul_div_cancel_left b ha
  · intro k hk
    rw [Nat.mul_div_cancel' (mem_filter.mp hk).2]

/-- **The letters, expanded.** A sum against the letters splits into three Möbius sums. -/
theorem sum_compCoeff_mul (hc : IsCompensation y d) (X : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Ioc 0 X, (compCoeff y d k : ℝ) * F k =
      ∑ b ∈ Ioc 0 X, (ArithmeticFunction.moebius b : ℝ) * F b +
        ∑ P ∈ largePrimes y, (∑ b ∈ Ioc 0 (X / P), (ArithmeticFunction.moebius b : ℝ) * F (P * b) -
          ∑ b ∈ Ioc 0 (X / d P), (ArithmeticFunction.moebius b : ℝ) * F (d P * b)) := by
  have hterm : ∀ k, (compCoeff y d k : ℝ) * F k = (ArithmeticFunction.moebius k : ℝ) * F k +
      ∑ P ∈ largePrimes y, (if P ∣ k then (ArithmeticFunction.moebius (k / P) : ℝ) * F k else 0) -
      ∑ P ∈ largePrimes y, (if d P ∣ k then (ArithmeticFunction.moebius (k / d P) : ℝ) * F k else 0) := by
    intro k
    simp only [compCoeff, Int.cast_sub, Int.cast_add, Int.cast_sum, Int.cast_ite, Int.cast_zero,
      add_mul, sub_mul, sum_mul, ite_mul, zero_mul]
  rw [sum_congr rfl fun k _ => hterm k, sum_sub_distrib, sum_add_distrib, sum_comm,
    sum_comm (s := Ioc 0 X) (t := largePrimes y) (f := fun k P =>
      if d P ∣ k then (ArithmeticFunction.moebius (k / d P) : ℝ) * F k else 0), add_sub_assoc,
    sum_sub_distrib]
  congr 2
  · refine sum_congr rfl fun P hP => ?_
    exact sum_dvd_moebius (mem_largePrimes.mp hP).2.pos X F
  · refine sum_congr rfl fun P hP => ?_
    have h0 : 0 < d P := lt_of_le_of_lt (Nat.zero_le P) (hc.lt P hP)
    exact sum_dvd_moebius h0 X F

/-- The multiplicity of the compensated stencil before truncation: `1` plus spikes on `[P, d_P)`. -/
def compCount (y : ℕ) (d : ℕ → ℕ) (s : ℕ) : ℝ :=
  1 + ∑ P ∈ largePrimes y, ((if P ≤ s then (1 : ℝ) else 0) - (if d P ≤ s then (1 : ℝ) else 0))

theorem one_le_compCount (hc : IsCompensation y d) (s : ℕ) : 1 ≤ compCount y d s := by
  rw [compCount]
  have : 0 ≤ ∑ P ∈ largePrimes y, ((if P ≤ s then (1 : ℝ) else 0) - (if d P ≤ s then (1 : ℝ) else 0)) := by
    refine sum_nonneg fun P hP => ?_
    have := hc.lt P hP
    split_ifs with h1 h2 h2 <;> first | norm_num | omega
  linarith

/-- The Möbius floor identity below `a`. -/
private lemma sum_moebius_floor_dilate {a : ℕ} (ha : 0 < a) (s : ℕ) :
    ∑ b ∈ Ioc 0 (s / a), (ArithmeticFunction.moebius b : ℝ) * ((s / (a * b) : ℕ) : ℝ) =
      if a ≤ s then 1 else 0 := by
  split_ifs with h
  · have hN : 1 ≤ s / a := (Nat.one_le_div_iff ha).mpr h
    have hset : Ioc 0 (s / a) = Icc 1 (s / a) := by
      ext b
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [hset, ← RHTower.moebius_floor_summatory (s / a) hN]
    refine sum_congr rfl fun b _ => ?_
    rw [Nat.div_div_eq_div_mul]
  · rw [Nat.div_eq_of_lt (not_le.mp h)]
    simp

/-- **The multiplicity below the truncation is exact.** -/
theorem sum_compCoeff_floor (hc : IsCompensation y d) {s : ℕ} (hs : 1 ≤ s) :
    ∑ k ∈ Ioc 0 s, (compCoeff y d k : ℝ) * ((s / k : ℕ) : ℝ) = compCount y d s := by
  rw [sum_compCoeff_mul hc, compCount]
  congr 1
  · have hset : Ioc 0 s = Icc 1 s := by
      ext b
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [hset]
    exact RHTower.moebius_floor_summatory s hs
  · refine sum_congr rfl fun P hP => ?_
    have h0 : 0 < d P := lt_of_le_of_lt (Nat.zero_le P) (hc.lt P hP)
    rw [sum_moebius_floor_dilate (mem_largePrimes.mp hP).2.pos, sum_moebius_floor_dilate h0]

/-- The partial sums of the letters. -/
def compSum (y : ℕ) (d : ℕ → ℕ) (X : ℕ) : ℝ := ∑ k ∈ Ioc 0 X, (compCoeff y d k : ℝ)

theorem compSum_eq (hc : IsCompensation y d) (X : ℕ) :
    compSum y d X = mertens X + ∑ P ∈ largePrimes y, (mertens (X / P) - mertens (X / d P)) := by
  have h := sum_compCoeff_mul hc X fun _ => 1
  simp only [mul_one] at h
  exact h

private lemma abs_moebius_le_one' (b : ℕ) : |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

private lemma abs_mertens_sub_le {u v : ℕ} (h : v ≤ u) :
    |mertens u - mertens v| ≤ ((u : ℝ) - v) := by
  rw [mertens, mertens, ← sum_Ioc_consecutive _ (Nat.zero_le v) h, add_sub_cancel_left]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun b _ => abs_moebius_le_one' b).trans ?_)
  simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub h]

/-- Few large primes lie just below a point. -/
private lemma card_near_le (hc : IsCompensation y d) (hy : 1 ≤ y) (w : ℕ) :
    (((largePrimes y).filter fun P => P ≤ w ∧ w < d P).card : ℝ) ≤
      if 2 * y + 2 < w then 4 * (w : ℝ) / y + 1 else 0 := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  split_ifs with hw
  · have hinj : Set.InjOn (fun P => w - P) (((largePrimes y).filter fun P => P ≤ w ∧ w < d P) : Set ℕ) := by
      intro a ha b hb hab
      have h1 := (mem_filter.mp ha).2.1
      have h2 := (mem_filter.mp hb).2.1
      simp only at hab
      omega
    have hmaps : ∀ P ∈ (largePrimes y).filter (fun P => P ≤ w ∧ w < d P),
        w - P ∈ range (⌊4 * (w : ℝ) / y⌋₊ + 1) := by
      intro P hP
      obtain ⟨hP1, hP2, hP3⟩ := mem_filter.mp hP
      refine mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ?_))
      rw [Nat.cast_sub hP2]
      have h1 := hc.le P hP1
      have h2 : (w : ℝ) ≤ (d P : ℝ) := by exact_mod_cast hP3.le
      have h3 : (P : ℝ) ≤ w := by exact_mod_cast hP2
      have e : (P : ℝ) * (1 + 4 / (y : ℝ)) = P + 4 * (P : ℝ) / y := by ring
      have h4 : 4 * (P : ℝ) / y ≤ 4 * (w : ℝ) / y := by gcongr
      linarith
    have hcard := card_le_card_of_injOn _ hmaps hinj
    rw [card_range] at hcard
    have h5 : (((largePrimes y).filter fun P => P ≤ w ∧ w < d P).card : ℝ) ≤
        ((⌊4 * (w : ℝ) / y⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at h5
    have h6 := Nat.floor_le (by positivity : 0 ≤ 4 * (w : ℝ) / y)
    linarith
  · have hempty : (largePrimes y).filter (fun P => P ≤ w ∧ w < d P) = ∅ := by
      refine filter_eq_empty_iff.mpr fun P hP h => ?_
      have := (mem_largePrimes.mp hP).1.1
      omega
    rw [hempty]
    simp

/-- **The compensation is cheap.** `Σ_P (⌊x/P⌋ − ⌊x/d_P⌋) ≤ 5 x (1 + log x)/y`, by counting alone. -/
theorem sum_floor_sub_le (hc : IsCompensation y d) (hy : 1 ≤ y) {x : ℕ} (hx : 1 ≤ x) :
    ∑ P ∈ largePrimes y, (((x / P : ℕ) : ℝ) - ((x / d P : ℕ) : ℝ)) ≤
      5 * (x : ℝ) * (1 + Real.log x) / y := by
  classical
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hlog : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  -- Each difference counts the `n` between the two floors.
  have hcount : ∀ P ∈ largePrimes y, ((x / P : ℕ) : ℝ) - ((x / d P : ℕ) : ℝ) =
      ∑ n ∈ Ioc 0 x, if x / d P < n ∧ n ≤ x / P then (1 : ℝ) else 0 := by
    intro P hP
    have hP0 := (mem_largePrimes.mp hP).2.pos
    have hle : x / d P ≤ x / P := Nat.div_le_div_left (hc.lt P hP).le hP0
    have hfil : (Ioc 0 x).filter (fun n => x / d P < n ∧ n ≤ x / P) = Ioc (x / d P) (x / P) := by
      ext n
      simp only [mem_filter, mem_Ioc]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · rintro ⟨h1, h2⟩
        exact ⟨⟨lt_of_le_of_lt (Nat.zero_le _) h1, h2.trans (Nat.div_le_self _ _)⟩, h1, h2⟩
    rw [← sum_filter, hfil]
    simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub hle]
  rw [sum_congr rfl hcount, sum_comm]
  -- Each `n` sees few primes.
  have hn : ∀ n ∈ Ioc 0 x, (∑ P ∈ largePrimes y, if x / d P < n ∧ n ≤ x / P then (1 : ℝ) else 0) ≤
      4 * ((x : ℝ) / n) / y + (if 2 * y + 3 ≤ x / n then 1 else 0) := by
    intro n hn
    have hn0 : 0 < n := (mem_Ioc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hsub : (largePrimes y).filter (fun P => x / d P < n ∧ n ≤ x / P) ⊆
        (largePrimes y).filter (fun P => P ≤ x / n ∧ x / n < d P) := by
      intro P hP
      obtain ⟨hP1, hP2, hP3⟩ := mem_filter.mp hP
      have hP0 := (mem_largePrimes.mp hP1).2.pos
      have hd0 : 0 < d P := lt_of_le_of_lt (Nat.zero_le P) (hc.lt P hP1)
      refine mem_filter.mpr ⟨hP1, (Nat.le_div_iff_mul_le hn0).mpr ?_, ?_⟩
      · have := (Nat.le_div_iff_mul_le hP0).mp hP3
        rwa [mul_comm] at this
      · have h1 := (Nat.div_lt_iff_lt_mul hd0).mp hP2
        refine (Nat.div_lt_iff_lt_mul hn0).mpr ?_
        rwa [mul_comm] at h1
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hc1 : (((largePrimes y).filter fun P => x / d P < n ∧ n ≤ x / P).card : ℝ) ≤
        (((largePrimes y).filter fun P => P ≤ x / n ∧ x / n < d P).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    refine hc1.trans ((card_near_le hc hy (x / n)).trans ?_)
    have hw : ((x / n : ℕ) : ℝ) ≤ (x : ℝ) / n := Nat.cast_div_le
    split_ifs with h1 h2 h2
    · have : 4 * ((x / n : ℕ) : ℝ) / y ≤ 4 * ((x : ℝ) / n) / y := by gcongr
      linarith
    · omega
    · have : 0 ≤ 4 * ((x : ℝ) / n) / y := by positivity
      linarith
    · have : 0 ≤ 4 * ((x : ℝ) / n) / y := by positivity
      linarith
  refine (sum_le_sum hn).trans ?_
  rw [sum_add_distrib]
  -- The harmonic part.
  have hH : ∑ n ∈ Ioc 0 x, 4 * ((x : ℝ) / n) / y ≤ 4 * (x : ℝ) * (1 + Real.log x) / y := by
    have h := harmonic_le_one_add_log x
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    have hset : Icc 1 x = Ioc 0 x := by
      ext b
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [hset] at h
    have e : ∑ n ∈ Ioc 0 x, 4 * ((x : ℝ) / n) / y = 4 * (x : ℝ) / y * ∑ n ∈ Ioc 0 x, ((n : ℝ))⁻¹ := by
      rw [mul_sum]
      refine sum_congr rfl fun n _ => ?_
      ring
    rw [e]
    calc _ ≤ 4 * (x : ℝ) / y * (1 + Real.log x) := by gcongr
      _ = _ := by ring
  -- The count of `n` with `x/n` above the small range.
  have hcnt : ∑ n ∈ Ioc 0 x, (if 2 * y + 3 ≤ x / n then (1 : ℝ) else 0) ≤ (x : ℝ) / y := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hsub : (Ioc 0 x).filter (fun n => 2 * y + 3 ≤ x / n) ⊆ Ioc 0 (x / y) := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := mem_filter.mp hn
      have hn0 := (mem_Ioc.mp hn1).1
      refine mem_Ioc.mpr ⟨hn0, (Nat.le_div_iff_mul_le hy).mpr ?_⟩
      have h1 := (Nat.le_div_iff_mul_le hn0).mp hn2
      have h2 : y * n ≤ (2 * y + 3) * n := Nat.mul_le_mul_right n (by omega)
      rw [mul_comm n y]
      omega
    have h3 := card_le_card hsub
    rw [Nat.card_Ioc, Nat.sub_zero] at h3
    calc (((Ioc 0 x).filter fun n => 2 * y + 3 ≤ x / n).card : ℝ) ≤ ((x / y : ℕ) : ℝ) := by
          exact_mod_cast h3
      _ ≤ _ := Nat.cast_div_le
  have h1 : (x : ℝ) / y ≤ (x : ℝ) * (1 + Real.log x) / y := by
    gcongr
    nlinarith
  have e : 5 * (x : ℝ) * (1 + Real.log x) / y = 4 * (x : ℝ) * (1 + Real.log x) / y + (x : ℝ) * (1 + Real.log x) / y := by
    ring
  rw [e]
  linarith

/-- **The partial sums of the letters are as small as the Mertens function, up to `1/y`.** -/
theorem abs_compSum_le (hc : IsCompensation y d) (hy : 1 ≤ y) {η : ℝ}
    (hM : ∀ x, y * y ≤ x → |mertens x| ≤ η * x) {x : ℕ} (hx : y * y ≤ x) :
    |compSum y d x| ≤ (x : ℝ) * (η + 5 * (1 + Real.log x) / y) := by
  have hx1 : 1 ≤ x := le_trans (Nat.mul_pos hy hy) hx
  rw [compSum_eq hc]
  refine (abs_add_le _ _).trans ?_
  have h1 := hM x hx
  have h2 : |∑ P ∈ largePrimes y, (mertens (x / P) - mertens (x / d P))| ≤
      5 * (x : ℝ) * (1 + Real.log x) / y := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun P hP => ?_).trans (sum_floor_sub_le hc hy hx1))
    exact abs_mertens_sub_le (Nat.div_le_div_left (hc.lt P hP).le (mem_largePrimes.mp hP).2.pos)
  have e : (x : ℝ) * (η + 5 * (1 + Real.log x) / y) = η * x + 5 * (x : ℝ) * (1 + Real.log x) / y := by
    ring
  rw [e]
  linarith

/-- The hyperbola method for a general coefficient sequence. -/
private lemma sum_Ioc_mul_floor (c : ℕ → ℝ) (T s : ℕ) :
    ∑ k ∈ Ioc T s, c k * ((s / k : ℕ) : ℝ) =
      ∑ j ∈ Ioc 0 (s / (T + 1)), ∑ k ∈ Ioc T (s / j), c k := by
  classical
  have hcount : ∀ k ∈ Ioc T s, ((s / k : ℕ) : ℝ) =
      ∑ j ∈ Ioc 0 (s / (T + 1)), if k ≤ s / j then (1 : ℝ) else 0 := by
    intro k hk
    obtain ⟨hk1, -⟩ := mem_Ioc.mp hk
    have hk0 : 0 < k := by omega
    have hfil : (Ioc 0 (s / (T + 1))).filter (fun j => k ≤ s / j) = Ioc 0 (s / k) := by
      ext j
      simp only [mem_filter, mem_Ioc]
      constructor
      · rintro ⟨⟨hj0, -⟩, hj⟩
        refine ⟨hj0, (Nat.le_div_iff_mul_le hk0).mpr ?_⟩
        have := (Nat.le_div_iff_mul_le hj0).mp hj
        rwa [mul_comm] at this
      · rintro ⟨hj0, hj⟩
        refine ⟨⟨hj0, hj.trans (Nat.div_le_div_left (by omega) (by omega))⟩,
          (Nat.le_div_iff_mul_le hj0).mpr ?_⟩
        have := (Nat.le_div_iff_mul_le hk0).mp hj
        rwa [mul_comm] at this
    rw [← sum_filter, hfil]
    simp
  have hsw : ∑ k ∈ Ioc T s, c k * ((s / k : ℕ) : ℝ) =
      ∑ j ∈ Ioc 0 (s / (T + 1)), ∑ k ∈ Ioc T s, c k * (if k ≤ s / j then (1 : ℝ) else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun k hk => ?_
    rw [hcount k hk, mul_sum]
  rw [hsw]
  refine sum_congr rfl fun j hj => ?_
  have hj0 := (mem_Ioc.mp hj).1
  have hle : s / j ≤ s := Nat.div_le_self _ _
  have hfil : (Ioc T s).filter (fun k => k ≤ s / j) = Ioc T (s / j) := by
    ext k
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.trans hle⟩, h2⟩
  rw [← hfil, sum_filter]
  refine sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- The letters past the truncation, along floors. -/
def compTail (y : ℕ) (d : ℕ → ℕ) (s : ℕ) : ℝ :=
  ∑ k ∈ Ioc (y * y) s, (compCoeff y d k : ℝ) * ((s / k : ℕ) : ℝ)

/-- **The tail past the truncation.** -/
theorem abs_compTail_le (hc : IsCompensation y d) (hy : 1 ≤ y) {η Y : ℝ} (hY0 : 0 ≤ Y)
    (hM : ∀ x, y * y ≤ x → |mertens x| ≤ η * x) {X s : ℕ} (hsX : s ≤ X) (hX : 1 ≤ X)
    (hY : η + 5 * (1 + Real.log X) / y ≤ Y) :
    |compTail y d s| ≤ Y * (s : ℝ) * (2 + Real.log X) := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlogX := Real.log_nonneg hXR
  have hT : 1 ≤ y * y := Nat.mul_pos hy hy
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  rcases Nat.eq_zero_or_pos (s / (y * y + 1)) with h0 | hpos
  · -- There is nothing past the truncation.
    rw [compTail, sum_Ioc_mul_floor, h0]
    simp only [Ioc_self, sum_empty, abs_zero]
    positivity
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  rw [compTail, sum_Ioc_mul_floor]
  have hblock : ∀ x, y * y ≤ x → x ≤ X → |compSum y d x| ≤ Y * x := by
    intro x hx hxX
    have hx1 : 1 ≤ x := hT.trans hx
    have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx1
    refine (abs_compSum_le hc hy hM hx).trans ?_
    have hlogle : Real.log (x : ℝ) ≤ Real.log X := Real.log_le_log (by linarith) (by exact_mod_cast hxX)
    have h1 : η + 5 * (1 + Real.log x) / y ≤ Y := by
      refine le_trans ?_ hY
      gcongr
    calc (x : ℝ) * (η + 5 * (1 + Real.log x) / y) ≤ (x : ℝ) * Y :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = _ := mul_comm _ _
  have hterm : ∀ j ∈ Ioc 0 (s / (y * y + 1)),
      |∑ k ∈ Ioc (y * y) (s / j), (compCoeff y d k : ℝ)| ≤ Y * (s : ℝ) * (1 / (j : ℝ)) + Y * ((y * y : ℕ) : ℝ) := by
    intro j hj
    obtain ⟨hj0, hj1⟩ := mem_Ioc.mp hj
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
    have hle : y * y ≤ s / j := by
      refine (Nat.le_div_iff_mul_le hj0).mpr ?_
      have := (Nat.le_div_iff_mul_le (by omega : 0 < y * y + 1)).mp hj1
      nlinarith
    have hsj : s / j ≤ X := (Nat.div_le_self _ _).trans hsX
    have heq : ∑ k ∈ Ioc (y * y) (s / j), (compCoeff y d k : ℝ) = compSum y d (s / j) - compSum y d (y * y) := by
      rw [compSum, compSum, ← sum_Ioc_consecutive _ (Nat.zero_le (y * y)) hle, add_sub_cancel_left]
    rw [heq]
    have hTX : y * y ≤ X := hle.trans hsj
    have h1 := hblock _ hle hsj
    have h2 := hblock _ le_rfl hTX
    have h3 : ((s / j : ℕ) : ℝ) ≤ (s : ℝ) / j := Nat.cast_div_le
    have h4 : Y * ((s / j : ℕ) : ℝ) ≤ Y * (s : ℝ) * (1 / (j : ℝ)) := by
      calc Y * ((s / j : ℕ) : ℝ) ≤ Y * ((s : ℝ) / j) := mul_le_mul_of_nonneg_left h3 hY0
        _ = _ := by ring
    calc _ ≤ |compSum y d (s / j)| + |compSum y d (y * y)| := abs_sub _ _
      _ ≤ _ := by linarith
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  -- The harmonic sum, and the count of blocks.
  have hH : ∑ j ∈ Ioc 0 (s / (y * y + 1)), 1 / (j : ℝ) ≤ 1 + Real.log X := by
    have h := harmonic_le_one_add_log (s / (y * y + 1))
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    have hset : Icc 1 (s / (y * y + 1)) = Ioc 0 (s / (y * y + 1)) := by
      ext b
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [hset] at h
    simp only [one_div]
    refine h.trans ?_
    have hle : ((s / (y * y + 1) : ℕ) : ℝ) ≤ X := by
      exact_mod_cast (Nat.div_le_self _ _).trans hsX
    have hpos' : (0 : ℝ) < ((s / (y * y + 1) : ℕ) : ℝ) := by exact_mod_cast hpos
    have := Real.log_le_log hpos' hle
    linarith
  have hB : ((s / (y * y + 1) : ℕ) : ℝ) * (Y * ((y * y : ℕ) : ℝ)) ≤ Y * (s : ℝ) := by
    have h1 : (s / (y * y + 1)) * (y * y) ≤ s := by
      calc (s / (y * y + 1)) * (y * y) ≤ (s / (y * y + 1)) * (y * y + 1) :=
            Nat.mul_le_mul_left _ (by omega)
        _ ≤ s := Nat.div_mul_le_self _ _
    have h2 : ((s / (y * y + 1) : ℕ) : ℝ) * ((y * y : ℕ) : ℝ) ≤ s := by exact_mod_cast h1
    calc _ = Y * (((s / (y * y + 1) : ℕ) : ℝ) * ((y * y : ℕ) : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hY0
  have hYs : 0 ≤ Y * (s : ℝ) := by positivity
  calc _ ≤ Y * (s : ℝ) * (1 + Real.log X) + Y * (s : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hH hYs) hB
    _ = _ := by ring

/-- The near part of the compensated sawtooth, on the letters up to `y²`. -/
def compNear (y : ℕ) (d : ℕ → ℕ) (r : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 (y * y), (-(compCoeff y d k : ℝ) / k) * ((r % k : ℕ) : ℝ)

/-- The drift of the truncated letters. -/
def compTheta (y : ℕ) (d : ℕ → ℕ) : ℝ := ∑ k ∈ Ioc 0 (y * y), (compCoeff y d k : ℝ) / k

/-- The mass of the letters. -/
def compMass (y : ℕ) (d : ℕ → ℕ) : ℝ := ∑ k ∈ Icc 2 (y * y), |(compCoeff y d k : ℝ)|

theorem compMass_nonneg : 0 ≤ compMass y d := sum_nonneg fun _ _ => abs_nonneg _

theorem abs_compNear_le (r : ℕ) : |compNear y d r| ≤ compMass y d := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk2 := (mem_Icc.mp hk).1
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hmod : ((r % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt r (by omega)).le
  rw [abs_mul, abs_div, abs_neg, abs_of_pos hkR, Nat.abs_cast]
  have h0 := abs_nonneg (compCoeff y d k : ℝ)
  calc |(compCoeff y d k : ℝ)| / k * ((r % k : ℕ) : ℝ) ≤ |(compCoeff y d k : ℝ)| / k * k := by gcongr
    _ = _ := by field_simp

/-- The near part in terms of floors and the drift. -/
private lemma compNear_eq_floor (hy : 1 ≤ y) (r : ℕ) :
    compNear y d r = ∑ k ∈ Ioc 0 (y * y), (compCoeff y d k : ℝ) * ((r / k : ℕ) : ℝ) - compTheta y d * r := by
  have hT : 1 ≤ y * y := Nat.mul_pos hy hy
  have hset : Ioc 0 (y * y) = insert 1 (Icc 2 (y * y)) := by
    ext k
    simp only [mem_Ioc, mem_insert, mem_Icc]
    omega
  have h1 : (1 : ℕ) ∉ Icc 2 (y * y) := by simp
  rw [compTheta, hset, sum_insert h1, sum_insert h1, compNear]
  have hrest : ∑ k ∈ Icc 2 (y * y), (-(compCoeff y d k : ℝ) / k) * ((r % k : ℕ) : ℝ) =
      ∑ k ∈ Icc 2 (y * y), (compCoeff y d k : ℝ) * ((r / k : ℕ) : ℝ) -
        (∑ k ∈ Icc 2 (y * y), (compCoeff y d k : ℝ) / k) * r := by
    rw [sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hk).1; omega)
    have hd : (r : ℝ) = (k : ℝ) * ((r / k : ℕ) : ℝ) + ((r % k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod r k).symm
    have hm : ((r % k : ℕ) : ℝ) = (r : ℝ) - (k : ℝ) * ((r / k : ℕ) : ℝ) := by linarith
    rw [hm]
    field_simp
    ring
  rw [hrest]
  simp only [Nat.div_one, Nat.cast_one, div_one]
  ring

/-- **The near part splits into the count, the tail and the drift.** -/
theorem compNear_eq (hc : IsCompensation y d) (hy : 1 ≤ y) {r : ℕ} (hr : 1 ≤ r) :
    compNear y d r = compCount y d r - compTail y d r - compTheta y d * r := by
  rw [compNear_eq_floor hy, ← sum_compCoeff_floor hc hr, compTail]
  rcases le_total (y * y) r with h | h
  · rw [← sum_Ioc_consecutive _ (Nat.zero_le (y * y)) h]
    ring
  · have htail : Ioc (y * y) r = ∅ := Ioc_eq_empty (by omega)
    rw [htail, ← sum_Ioc_consecutive (fun k => (compCoeff y d k : ℝ) * ((r / k : ℕ) : ℝ)) (Nat.zero_le r) h]
    have hz : ∑ k ∈ Ioc r (y * y), (compCoeff y d k : ℝ) * ((r / k : ℕ) : ℝ) = 0 := by
      refine sum_eq_zero fun k hk => ?_
      rw [Nat.div_eq_of_lt (mem_Ioc.mp hk).1]
      simp
    rw [hz]
    simp

/-- The count past every large prime and its compensation is `1`. -/
private lemma compCount_eq_one {n : ℕ} (hn : ∀ P ∈ largePrimes y, d P ≤ n) (hc : IsCompensation y d) :
    compCount y d n = 1 := by
  rw [compCount, sum_eq_zero, add_zero]
  intro P hP
  have h1 := hn P hP
  have h2 := hc.lt P hP
  rw [if_pos (by omega), if_pos h1, sub_self]

/-- **The drift is read off at one large point.** -/
theorem abs_compTheta_le (hc : IsCompensation y d) (hy : 1 ≤ y) {η Y : ℝ} (hY0 : 0 ≤ Y)
    (hM : ∀ x, y * y ≤ x → |mertens x| ≤ η * x) {X n : ℕ} (hnX : n ≤ X) (hn1 : 1 ≤ n) (hX : 1 ≤ X)
    (hn : ∀ P ∈ largePrimes y, d P ≤ n) (hY : η + 5 * (1 + Real.log X) / y ≤ Y) :
    |compTheta y d| ≤ (1 + compMass y d) / n + Y * (2 + Real.log X) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have h := compNear_eq hc hy hn1
  rw [compCount_eq_one hn hc] at h
  have hval : compTheta y d * n = 1 - compTail y d n - compNear y d n := by linarith
  have hT := abs_compTail_le hc hy hY0 hM hnX hX hY
  have hN := abs_compNear_le (y := y) (d := d) n
  have habs : |compTheta y d| * n ≤ 1 + Y * (n : ℝ) * (2 + Real.log X) + compMass y d := by
    have e : |compTheta y d| * n = |compTheta y d * n| := by
      rw [abs_mul, Nat.abs_cast]
    rw [e, hval]
    have h1 : |1 - compTail y d n - compNear y d n| ≤ |1 - compTail y d n| + |compNear y d n| := abs_sub _ _
    have h2 : |1 - compTail y d n| ≤ |(1 : ℝ)| + |compTail y d n| := abs_sub _ _
    rw [abs_one] at h2
    linarith
  rw [← le_div_iff₀ hnR] at habs
  refine habs.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The near law of the compensated stencil.** Up to `X`, the near part equals the count, up to `s (2 Y (2 + log X) + (1 + mass)/n)`. -/
theorem abs_compNear_sub_le (hc : IsCompensation y d) (hy : 1 ≤ y) {η Y : ℝ} (hY0 : 0 ≤ Y)
    (hM : ∀ x, y * y ≤ x → |mertens x| ≤ η * x) {X n : ℕ} (hnX : n ≤ X) (hn1 : 1 ≤ n) (hX : 1 ≤ X)
    (hn : ∀ P ∈ largePrimes y, d P ≤ n) (hY : η + 5 * (1 + Real.log X) / y ≤ Y) {s : ℕ} (hs : 1 ≤ s)
    (hsX : s ≤ X) :
    |compNear y d s - compCount y d s| ≤
      (s : ℝ) * (2 * Y * (2 + Real.log X) + (1 + compMass y d) / n) := by
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have h := compNear_eq hc hy hs
  have hval : compNear y d s - compCount y d s = -compTail y d s - compTheta y d * s := by linarith
  rw [hval]
  have h1 := abs_compTail_le hc hy hY0 hM hsX hX hY
  have h2 := abs_compTheta_le hc hy hY0 hM hnX hn1 hX hn hY
  have h3 : |compTheta y d * s| ≤ (s : ℝ) * ((1 + compMass y d) / n + Y * (2 + Real.log X)) := by
    rw [abs_mul, Nat.abs_cast, mul_comm]
    exact mul_le_mul_of_nonneg_left h2 hs0
  have h4 : |-compTail y d s - compTheta y d * s| ≤ |compTail y d s| + |compTheta y d * s| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_neg]
  refine h4.trans ?_
  have e : (s : ℝ) * (2 * Y * (2 + Real.log X) + (1 + compMass y d) / n) =
      Y * (s : ℝ) * (2 + Real.log X) + (s : ℝ) * ((1 + compMass y d) / n + Y * (2 + Real.log X)) := by
    ring
  rw [e]
  linarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
