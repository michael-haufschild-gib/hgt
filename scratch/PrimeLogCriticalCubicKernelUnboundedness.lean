import GaloisForLFunctions.RHTower.Sieve.VonMangoldtHarmonicSquareAsymptotic

/-!
# Critical prime-log cubic-kernel block growth

The critical inverse-heat endpoint has prime weight `log(p)/p`.  Its mass on
`n < p <= n^2` grows at least linearly in `log n`; this is the arithmetic input to the
unbounded finite-compression theorem.
-/

namespace RHTower

noncomputable section

open Finset

/-- Prime packet between `n` and `n^2`. -/
def primeLogCriticalBlock (n : ℕ) : Finset ℕ :=
  Nat.primesLE (n ^ 2) \ Nat.primesLE n

/-- Critical first-clock mass on a multiplicative prime packet. -/
def primeLogCriticalBlockMass (n : ℕ) : ℝ :=
  ∑ p ∈ primeLogCriticalBlock n, Real.log (p : ℝ) / (p : ℝ)

/-- Existing explicit Mangoldt-square laws force linear logarithmic growth of the critical
prime mass on `n < p <= n^2`. -/
theorem primeLogCriticalBlockMass_growth
    (n : ℕ) (hn : 2 ≤ n) :
    (3 / 2 : ℝ) * Real.log n ^ 2 - 117 * Real.log n - 50 ≤
      2 * Real.log n * primeLogCriticalBlockMass n := by
  have hn1 : 1 ≤ n := hn.trans' (by norm_num)
  have hnn : n ≤ n ^ 2 := by
    nlinarith
  have hsubset : Nat.primesLE n ⊆ Nat.primesLE (n ^ 2) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans hnn, hp.2⟩
  have hn2one : 1 ≤ n ^ 2 := by nlinarith
  have hlarge := Sieve.sum_prime_log_sq_div_ge (n ^ 2) hn2one
  have hsmallPrime :=
    Sieve.sum_prime_log_sq_div_le_vonMangoldtHarmonicSquareSum n hn1
  have hsmallVM := Sieve.abs_vonMangoldtHarmonicSquareSum_sub_le n hn1
  rw [abs_le] at hsmallVM
  have hlogpow : Real.log ((n ^ 2 : ℕ) : ℝ) = 2 * Real.log (n : ℝ) := by
    norm_num [Nat.cast_pow, Real.log_pow]
  rw [hlogpow] at hlarge
  have hsmall :
      ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ) ^ 2 / (p : ℝ) ≤
        Real.log n ^ 2 / 2 + 39 * Real.log n + 25 := by
    exact hsmallPrime.trans (by linarith [hsmallVM.2])
  have hsplit := Finset.sum_sdiff hsubset
    (f := fun p : ℕ => Real.log (p : ℝ) ^ 2 / (p : ℝ))
  have hblockSq :
      (3 / 2 : ℝ) * Real.log n ^ 2 - 117 * Real.log n - 50 ≤
        ∑ p ∈ primeLogCriticalBlock n,
          Real.log (p : ℝ) ^ 2 / (p : ℝ) := by
    rw [primeLogCriticalBlock]
    nlinarith [hlarge, hsmall, hsplit]
  refine hblockSq.trans ?_
  rw [primeLogCriticalBlockMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [primeLogCriticalBlock] at hp
  rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.2.pos
  have hlog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.1.2.one_lt.le)
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hple : (p : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast hp.1.1
  have hlogle : Real.log (p : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    calc
      Real.log (p : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log hp0 hple
      _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
  calc
    Real.log (p : ℝ) ^ 2 / (p : ℝ) =
        Real.log (p : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by ring
    _ ≤ (2 * Real.log (n : ℝ)) * (Real.log (p : ℝ) / (p : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hlogle (div_nonneg hlog0 hp0.le)
    _ = 2 * Real.log (n : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by ring

/-- Critical cubic Cauchy correlation of two prime-log clocks. -/
def primeLogCriticalCubicCorrelation (p q : ℕ) : ℝ :=
  (2 * Real.sqrt (Real.log (p : ℝ) * Real.log (q : ℝ)) /
    (Real.log (p : ℝ) + Real.log (q : ℝ))) ^ 3

/-- Every pair in one multiplicative critical block retains a uniform cubic correlation. -/
theorem primeLogCriticalCubicCorrelation_ge
    (n : ℕ) (hn : 2 ≤ n) {p q : ℕ}
    (hp : p ∈ primeLogCriticalBlock n)
    (hq : q ∈ primeLogCriticalBlock n) :
    (1 / 8 : ℝ) ≤ primeLogCriticalCubicCorrelation p q := by
  rw [primeLogCriticalBlock, Finset.mem_sdiff] at hp hq
  rcases Nat.mem_primesLE.mp hp.1 with ⟨hpn2, hpprime⟩
  rcases Nat.mem_primesLE.mp hq.1 with ⟨hqn2, hqprime⟩
  have hnp : n < p := lt_of_not_ge fun hpn =>
    hp.2 (Nat.mem_primesLE.mpr ⟨hpn, hpprime⟩)
  have hnq : n < q := lt_of_not_ge fun hqn =>
    hq.2 (Nat.mem_primesLE.mpr ⟨hqn, hqprime⟩)
  let L := Real.log (n : ℝ)
  let x := Real.log (p : ℝ)
  let y := Real.log (q : ℝ)
  have hnR : (0 : ℝ) < n := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hn)
  have hxpos : 0 < x := by
    dsimp [x]
    exact Real.log_pos (by exact_mod_cast hpprime.one_lt)
  have hypos : 0 < y := by
    dsimp [y]
    exact Real.log_pos (by exact_mod_cast hqprime.one_lt)
  have hLx : L ≤ x := by
    exact Real.log_le_log hnR (by exact_mod_cast hnp.le)
  have hLy : L ≤ y := by
    exact Real.log_le_log hnR (by exact_mod_cast hnq.le)
  have hx2L : x ≤ 2 * L := by
    calc
      x ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log hpR (by exact_mod_cast hpn2)
      _ = 2 * L := by dsimp [L]; rw [Real.log_pow]; norm_num
  have hy2L : y ≤ 2 * L := by
    calc
      y ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log hqR (by exact_mod_cast hqn2)
      _ = 2 * L := by dsimp [L]; rw [Real.log_pow]; norm_num
  have hprod : L ^ 2 ≤ x * y := by
    have hxy := mul_nonneg (sub_nonneg.mpr hLx) (sub_nonneg.mpr hLy)
    nlinarith
  have hsqrt : L ≤ Real.sqrt (x * y) := by
    have h := Real.sqrt_le_sqrt hprod
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hLpos] at h
    exact h
  have hden : x + y ≤ 4 * L := by linarith
  have hratio : (1 / 2 : ℝ) ≤ 2 * Real.sqrt (x * y) / (x + y) := by
    rw [le_div_iff₀ (add_pos hxpos hypos)]
    nlinarith
  rw [primeLogCriticalCubicCorrelation]
  change (1 / 8 : ℝ) ≤ (2 * Real.sqrt (x * y) / (x + y)) ^ 3
  calc
    (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 3 := by norm_num
    _ ≤ (2 * Real.sqrt (x * y) / (x + y)) ^ 3 := by gcongr

/-- Critical prime mass escapes every bounded set. -/
theorem tendsto_primeLogCriticalBlockMass_atTop :
    Filter.Tendsto primeLogCriticalBlockMass Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hhalf : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / 2)
      Filter.atTop Filter.atTop := hlog.atTop_div_const (by norm_num)
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hhalf
  filter_upwards [Filter.eventually_ge_atTop 2,
      hlog.eventually (Filter.eventually_ge_atTop (300 : ℝ))] with n hn hL
  have hgrowth := primeLogCriticalBlockMass_growth n hn
  have hLpos : 0 < Real.log (n : ℝ) := by linarith
  nlinarith

/-- Quadratic form of the critical cubic Cauchy kernel on its canonical finite block vector. -/
def primeLogCriticalCubicRayleighNumerator (n : ℕ) : ℝ :=
  ∑ p ∈ primeLogCriticalBlock n, ∑ q ∈ primeLogCriticalBlock n,
    (Real.log (p : ℝ) / (p : ℝ)) *
      (Real.log (q : ℝ) / (q : ℝ)) *
        primeLogCriticalCubicCorrelation p q

/-- Cubic correlation turns critical block mass into a quadratic Rayleigh lower bound. -/
theorem primeLogCriticalCubicRayleighNumerator_ge
    (n : ℕ) (hn : 2 ≤ n) :
    (1 / 8 : ℝ) * primeLogCriticalBlockMass n ^ 2 ≤
      primeLogCriticalCubicRayleighNumerator n := by
  rw [primeLogCriticalCubicRayleighNumerator]
  calc
    (1 / 8 : ℝ) * primeLogCriticalBlockMass n ^ 2 =
        ∑ p ∈ primeLogCriticalBlock n, ∑ q ∈ primeLogCriticalBlock n,
          (1 / 8 : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) *
            (Real.log (q : ℝ) / (q : ℝ)) := by
      rw [primeLogCriticalBlockMass, pow_two]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      ring
    _ ≤ ∑ p ∈ primeLogCriticalBlock n, ∑ q ∈ primeLogCriticalBlock n,
          (Real.log (p : ℝ) / (p : ℝ)) *
            (Real.log (q : ℝ) / (q : ℝ)) *
              primeLogCriticalCubicCorrelation p q := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have hp' := hp
      have hq' := hq
      rw [primeLogCriticalBlock, Finset.mem_sdiff, Nat.mem_primesLE] at hp' hq'
      have hp0 : (0 : ℝ) ≤ Real.log (p : ℝ) / (p : ℝ) := by
        exact div_nonneg
          (Real.log_nonneg (by exact_mod_cast hp'.1.2.one_lt.le))
          (by exact_mod_cast hp'.1.2.pos.le)
      have hq0 : (0 : ℝ) ≤ Real.log (q : ℝ) / (q : ℝ) := by
        exact div_nonneg
          (Real.log_nonneg (by exact_mod_cast hq'.1.2.one_lt.le))
          (by exact_mod_cast hq'.1.2.pos.le)
      have hc := primeLogCriticalCubicCorrelation_ge n hn hp hq
      exact mul_le_mul_of_nonneg_left hc (mul_nonneg hp0 hq0)

/-- The raw critical endpoint admits no uniform finite-compression Rayleigh bound. -/
theorem not_exists_primeLogCriticalCubicRayleigh_bound :
    ¬ ∃ C : ℝ, ∀ n : ℕ,
      primeLogCriticalCubicRayleighNumerator n ≤
        C * primeLogCriticalBlockMass n := by
  rintro ⟨C, hC⟩
  have hlarge := tendsto_primeLogCriticalBlockMass_atTop.eventually
    (Filter.eventually_gt_atTop (8 * |C| + 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hlarge
  let n := max N 2
  have hnN : N ≤ n := le_max_left _ _
  have hn2 : 2 ≤ n := le_max_right _ _
  have hmass := hN n hnN
  have hlower := primeLogCriticalCubicRayleighNumerator_ge n hn2
  have hupper := hC n
  have hCle : C ≤ |C| := le_abs_self C
  nlinarith [sq_nonneg (primeLogCriticalBlockMass n)]

end

end RHTower
