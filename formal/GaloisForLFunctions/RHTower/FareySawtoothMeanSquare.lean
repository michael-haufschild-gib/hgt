import GaloisForLFunctions.RHTower.FareyCountMertensIdentity
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Mean square of the Farey sawtooth and the size of the Farey set

The Farey sawtooth `S_n(x) = Σ_{k ≤ n} ψ(k x) M(n/k)` has, by Franel's correlation
`∫_0^1 ψ(kx)ψ(k'x) dx = gcd(k,k')²/(12kk')`, the mean square
`Σ_{k,k'} M(n/k) M(n/k') gcd(k,k')²/(12kk')`.  If `|M(n/k)| k^a ≤ B n^a` with `a ≥ ½`, then
`gcd(k,k') ≤ √(kk') ≤ (kk')^a` bounds each term by `B² n^{2a} gcd(k,k')/(12kk')`, and Gauss's
identity `gcd = Σ_{g ∣ gcd} φ(g)` gives `Σ_{k,k' ≤ n} gcd(k,k')/(kk') ≤ (1 + log n)³`.  Under the
Riemann hypothesis such a bound holds for every `a > ½`.

The Farey set has `Σ_{q ≤ n} φ(q)` elements, and `Σ_{k ≤ n} Φ(n/k) = n(n+1)/2` together with
`Φ(N) ≤ N(N+1)/2` and `Σ_{k ≥ 2} 1/k² ≤ 3/4` gives `|F_n| ≥ n²/16` for `n ≥ 256`.
-/

open Finset

open RHTower.Sieve (fareySet mem_fareySet)

namespace RHTower

noncomputable section

/-- The Farey sawtooth `S_n(x) = Σ_{k ≤ n} ψ(k x) M(n/k)`. -/
def fareySawtooth (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Ioc 0 n, centeredFract ((k : ℝ) * x) * (mertensIoc (n / k) : ℝ)

/-- **Mean square of a sawtooth combination.** -/
theorem integral_sq_sum_centeredFract (n : ℕ) (c : ℕ → ℝ) :
    ∫ x in (0 : ℝ)..1, (∑ k ∈ Ioc 0 n, centeredFract ((k : ℝ) * x) * c k) ^ 2
      = ∑ k ∈ Ioc 0 n, ∑ k' ∈ Ioc 0 n,
          c k * c k' * (((Nat.gcd k k' : ℕ) : ℝ) ^ 2 / (12 * k * k')) := by
  have hexp : ∀ x : ℝ, (∑ k ∈ Ioc 0 n, centeredFract ((k : ℝ) * x) * c k) ^ 2
      = ∑ k ∈ Ioc 0 n, ∑ k' ∈ Ioc 0 n,
          c k * c k' * (centeredFract ((k : ℝ) * x) * centeredFract ((k' : ℝ) * x)) := by
    intro x
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun k _ => sum_congr rfl fun k' _ => by ring
  simp_rw [hexp]
  have hint : ∀ k k' : ℕ, IntervalIntegrable (fun x : ℝ => c k * c k' *
      (centeredFract ((k : ℝ) * x) * centeredFract ((k' : ℝ) * x))) MeasureTheory.volume 0 1 := by
    intro k k'
    have := intervalIntegrable_centeredFract_mul (k : ℝ) 0 (k' : ℝ) 0 0 1
    simp only [add_zero] at this
    exact this.const_mul _
  rw [intervalIntegral.integral_finsetSum fun k _ => by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum (Ioc 0 n) fun k' _ => hint k k']
  refine sum_congr rfl fun k hk => ?_
  rw [intervalIntegral.integral_finsetSum fun k' _ => hint k k']
  refine sum_congr rfl fun k' hk' => ?_
  rw [intervalIntegral.integral_const_mul,
    integral_centeredFract_mul_mul (mem_Ioc.mp hk).1 (mem_Ioc.mp hk').1]

/-- Gauss's identity on an initial segment: `gcd(a, b) = Σ_{g ≤ n, g ∣ a, g ∣ b} φ(g)`. -/
theorem natCast_gcd_eq_sum_totient {n a b : ℕ} (ha : 1 ≤ a) (han : a ≤ n) :
    ((Nat.gcd a b : ℕ) : ℝ)
      = ∑ g ∈ Ioc 0 n, if g ∣ a ∧ g ∣ b then (Nat.totient g : ℝ) else 0 := by
  have hdiv : (Nat.gcd a b).divisors = (Ioc 0 n).filter (fun g => g ∣ a ∧ g ∣ b) := by
    ext g
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hga, hgb⟩, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hga ha, le_trans (Nat.le_of_dvd ha hga) han⟩, hga, hgb⟩
    · rintro ⟨_, hga, hgb⟩
      exact ⟨⟨hga, hgb⟩, (Nat.gcd_pos_of_pos_left b ha).ne'⟩
  rw [← sum_filter, ← hdiv]
  have := Nat.sum_totient (Nat.gcd a b)
  exact_mod_cast this.symm

/-- **Weighted Gauss identity.**
`Σ_{k,k' ≤ n} gcd(k,k') w_k w_{k'} = Σ_{g ≤ n} φ(g) (Σ_{k ≤ n, g ∣ k} w_k)²`. -/
theorem sum_sum_gcd_mul_eq (n : ℕ) (w : ℕ → ℝ) :
    ∑ k ∈ Ioc 0 n, ∑ k' ∈ Ioc 0 n, ((Nat.gcd k k' : ℕ) : ℝ) * (w k * w k')
      = ∑ g ∈ Ioc 0 n, (Nat.totient g : ℝ) *
          (∑ k ∈ (Ioc 0 n).filter (fun k => g ∣ k), w k) ^ 2 := by
  have h1 : ∀ k ∈ Ioc 0 n, ∀ k' ∈ Ioc 0 n, ((Nat.gcd k k' : ℕ) : ℝ) * (w k * w k')
      = ∑ g ∈ Ioc 0 n, (Nat.totient g : ℝ) *
          ((if g ∣ k then w k else 0) * (if g ∣ k' then w k' else 0)) := by
    intro k hk k' _
    rw [natCast_gcd_eq_sum_totient (mem_Ioc.mp hk).1 (mem_Ioc.mp hk).2, sum_mul]
    refine sum_congr rfl fun g _ => ?_
    by_cases h1 : g ∣ k <;> by_cases h2 : g ∣ k' <;> simp [h1, h2]
  rw [sum_congr rfl fun k hk => sum_congr rfl fun k' hk' => h1 k hk k' hk',
    sum_congr rfl fun k _ => sum_comm, sum_comm]
  refine sum_congr rfl fun g _ => ?_
  rw [sum_filter, sq, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]

/-- `Σ_{k ≤ n, g ∣ k} 1/k ≤ (1 + log n)/g`. -/
theorem sum_filter_dvd_one_div_le {n g : ℕ} (hg : 1 ≤ g) :
    ∑ k ∈ (Ioc 0 n).filter (fun k => g ∣ k), (1 / (k : ℝ)) ≤ (1 + Real.log n) / g := by
  have himage : (Ioc 0 n).filter (fun k => g ∣ k) = (Icc 1 (n / g)).image (fun j => g * j) := by
    ext k
    simp only [mem_filter, mem_Ioc, mem_image, mem_Icc]
    constructor
    · rintro ⟨⟨hk0, hkn⟩, ⟨j, rfl⟩⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with h | h
        · rw [h, mul_zero] at hk0; omega
        · exact h
      · rw [Nat.le_div_iff_mul_le (by omega), mul_comm]; exact hkn
    · rintro ⟨j, ⟨hj1, hjn⟩, rfl⟩
      refine ⟨⟨by positivity, ?_⟩, dvd_mul_right g j⟩
      have := (Nat.le_div_iff_mul_le (by omega)).mp hjn
      rwa [mul_comm] at this
  rw [himage, sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left (by omega) hab)]
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have e : ∑ j ∈ Icc 1 (n / g), 1 / (((g * j : ℕ)) : ℝ)
      = (∑ j ∈ Icc 1 (n / g), 1 / (j : ℝ)) / g := by
    rw [sum_div]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    rw [div_div, mul_comm]
  rw [e]
  refine div_le_div_of_nonneg_right ?_ hg0.le
  refine (RHTower.Sieve.sum_Icc_one_div_le_one_add_log (n / g)).trans ?_
  have : Real.log ((n / g : ℕ) : ℝ) ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos (n / g) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg n
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.div_le_self n g)
  linarith

/-- **The gcd harmonic sum.**  `Σ_{k,k' ≤ n} gcd(k,k')/(kk') ≤ (1 + log n)³`. -/
theorem sum_sum_gcd_div_le (n : ℕ) :
    ∑ k ∈ Ioc 0 n, ∑ k' ∈ Ioc 0 n, ((Nat.gcd k k' : ℕ) : ℝ) / ((k : ℝ) * k')
      ≤ (1 + Real.log n) ^ 3 := by
  have h := sum_sum_gcd_mul_eq n (fun k => 1 / (k : ℝ))
  have e : ∀ k k' : ℕ, ((Nat.gcd k k' : ℕ) : ℝ) / ((k : ℝ) * k')
      = ((Nat.gcd k k' : ℕ) : ℝ) * (1 / (k : ℝ) * (1 / (k' : ℝ))) := by
    intro k k'
    rw [one_div_mul_one_div, mul_one_div]
  simp_rw [e]
  rw [h]
  have hlog : 0 ≤ 1 + Real.log n := by have := Real.log_natCast_nonneg n; linarith
  calc ∑ g ∈ Ioc 0 n, (Nat.totient g : ℝ) *
          (∑ k ∈ (Ioc 0 n).filter (fun k => g ∣ k), 1 / (k : ℝ)) ^ 2
      ≤ ∑ g ∈ Ioc 0 n, (1 + Real.log n) ^ 2 * (1 / (g : ℝ)) := by
        refine sum_le_sum fun g hg => ?_
        have hg1 : 1 ≤ g := (mem_Ioc.mp hg).1
        have hg0 : (0 : ℝ) < g := by exact_mod_cast hg1
        have hin := sum_filter_dvd_one_div_le (n := n) hg1
        have hnn : 0 ≤ ∑ k ∈ (Ioc 0 n).filter (fun k => g ∣ k), 1 / (k : ℝ) :=
          sum_nonneg fun k _ => by positivity
        have hphi : (Nat.totient g : ℝ) ≤ g := by exact_mod_cast Nat.totient_le g
        have hsq := pow_le_pow_left₀ hnn hin 2
        calc (Nat.totient g : ℝ) * (∑ k ∈ (Ioc 0 n).filter (fun k => g ∣ k), 1 / (k : ℝ)) ^ 2
            ≤ g * ((1 + Real.log n) / g) ^ 2 := mul_le_mul hphi hsq (sq_nonneg _) hg0.le
          _ = (1 + Real.log n) ^ 2 * (1 / (g : ℝ)) := by field_simp
    _ = (1 + Real.log n) ^ 2 * ∑ g ∈ Ioc 0 n, 1 / (g : ℝ) := by rw [mul_sum]
    _ ≤ (1 + Real.log n) ^ 2 * (1 + Real.log n) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [show Ioc 0 n = Icc 1 n by ext; simp only [mem_Ioc, mem_Icc]; omega]
        exact RHTower.Sieve.sum_Icc_one_div_le_one_add_log n
    _ = (1 + Real.log n) ^ 3 := by ring

/-- **The Farey sawtooth mean square under a Mertens bound.**  If `|M(n/k)| k^a ≤ B n^a` for
`1 ≤ k ≤ n` with `a ≥ ½`, then `∫_0^1 S_n² ≤ (B²/12) n^{2a} (1 + log n)³`. -/
theorem integral_sq_fareySawtooth_le {B a : ℝ} (hB : 0 ≤ B) (ha : 1 / 2 ≤ a) (n : ℕ)
    (hM : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      |(mertensIoc (n / k) : ℝ)| * (k : ℝ) ^ a ≤ B * (n : ℝ) ^ a) :
    ∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2
      ≤ B ^ 2 / 12 * ((n : ℝ) ^ a) ^ 2 * (1 + Real.log n) ^ 3 := by
  unfold fareySawtooth
  rw [integral_sq_sum_centeredFract]
  have hterm : ∀ k ∈ Ioc 0 n, ∀ k' ∈ Ioc 0 n,
      (mertensIoc (n / k) : ℝ) * (mertensIoc (n / k') : ℝ)
          * (((Nat.gcd k k' : ℕ) : ℝ) ^ 2 / (12 * k * k'))
        ≤ B ^ 2 / 12 * ((n : ℝ) ^ a) ^ 2 * (((Nat.gcd k k' : ℕ) : ℝ) / ((k : ℝ) * k')) := by
    intro k hk k' hk'
    obtain ⟨hk1, hkn⟩ := mem_Ioc.mp hk
    obtain ⟨hk'1, hk'n⟩ := mem_Ioc.mp hk'
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hk'0 : (0 : ℝ) < k' := by exact_mod_cast hk'1
    set gR : ℝ := ((Nat.gcd k k' : ℕ) : ℝ) with hgR
    set c := (mertensIoc (n / k) : ℝ)
    set c' := (mertensIoc (n / k') : ℝ)
    have hg0 : 0 ≤ gR := by positivity
    have hgk : gR ≤ k := by rw [hgR]; exact_mod_cast Nat.gcd_le_left k' hk1
    have hgk' : gR ≤ k' := by rw [hgR]; exact_mod_cast Nat.gcd_le_right (n := k') k hk'1
    have hsq : gR ≤ (k : ℝ) ^ a * (k' : ℝ) ^ a := by
      have h1 : gR ≤ √(k : ℝ) * √(k' : ℝ) := by
        rw [← Real.sqrt_mul hk0.le, ← Real.sqrt_mul_self hg0]
        exact Real.sqrt_le_sqrt (mul_le_mul hgk hgk' hg0 hk0.le)
      have h2 : √(k : ℝ) ≤ (k : ℝ) ^ a := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk1) ha
      have h3 : √(k' : ℝ) ≤ (k' : ℝ) ^ a := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk'1) ha
      exact h1.trans (mul_le_mul h2 h3 (Real.sqrt_nonneg _) (by positivity))
    have hprod : |c| * |c'| * gR ≤ B ^ 2 * ((n : ℝ) ^ a) ^ 2 := by
      calc |c| * |c'| * gR ≤ |c| * |c'| * ((k : ℝ) ^ a * (k' : ℝ) ^ a) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (|c| * (k : ℝ) ^ a) * (|c'| * (k' : ℝ) ^ a) := by ring
        _ ≤ (B * (n : ℝ) ^ a) * (B * (n : ℝ) ^ a) :=
            mul_le_mul (hM k hk1 hkn) (hM k' hk'1 hk'n) (by positivity) (by positivity)
        _ = B ^ 2 * ((n : ℝ) ^ a) ^ 2 := by ring
    have hq : 0 ≤ gR / ((k : ℝ) * k') := by positivity
    calc c * c' * (gR ^ 2 / (12 * k * k'))
        ≤ |c| * |c'| * (gR ^ 2 / (12 * k * k')) := by
          have := le_abs_self (c * c')
          rw [abs_mul] at this
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = (|c| * |c'| * gR) * (gR / ((k : ℝ) * k')) / 12 := by
          field_simp
      _ ≤ (B ^ 2 * ((n : ℝ) ^ a) ^ 2) * (gR / ((k : ℝ) * k')) / 12 := by
          gcongr
      _ = B ^ 2 / 12 * ((n : ℝ) ^ a) ^ 2 * (gR / ((k : ℝ) * k')) := by ring
  calc ∑ k ∈ Ioc 0 n, ∑ k' ∈ Ioc 0 n,
        (mertensIoc (n / k) : ℝ) * (mertensIoc (n / k') : ℝ)
          * (((Nat.gcd k k' : ℕ) : ℝ) ^ 2 / (12 * k * k'))
      ≤ ∑ k ∈ Ioc 0 n, ∑ k' ∈ Ioc 0 n,
          B ^ 2 / 12 * ((n : ℝ) ^ a) ^ 2 * (((Nat.gcd k k' : ℕ) : ℝ) / ((k : ℝ) * k')) :=
        sum_le_sum fun k hk => sum_le_sum fun k' hk' => hterm k hk k' hk'
    _ = B ^ 2 / 12 * ((n : ℝ) ^ a) ^ 2 * ∑ k ∈ Ioc 0 n, ∑ k' ∈ Ioc 0 n,
          ((Nat.gcd k k' : ℕ) : ℝ) / ((k : ℝ) * k') := by
        rw [mul_sum]
        exact sum_congr rfl fun k _ => by rw [mul_sum]
    _ ≤ B ^ 2 / 12 * ((n : ℝ) ^ a) ^ 2 * (1 + Real.log n) ^ 3 :=
        mul_le_mul_of_nonneg_left (sum_sum_gcd_div_le n) (by positivity)

/-- **A Mertens power bound in scaled form.**  If `|M(N)| ≤ C (N+1)^a` for all `N` with
`0 ≤ a ≤ 1`, then `|M(n/k)| k^a ≤ 2C n^a` for all `1 ≤ k ≤ n`. -/
theorem abs_mertensIoc_div_mul_rpow_le_of_bound {a C : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hC : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ a) {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    |(mertensIoc (n / k) : ℝ)| * (k : ℝ) ^ a ≤ 2 * C * (n : ℝ) ^ a := by
  have hN1 : 1 ≤ n / k := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hkn)
  have hM : |(mertensIoc (n / k) : ℝ)| ≤ C * (((n / k : ℕ) : ℝ) + 1) ^ a := by
    have := hC (n / k)
    rwa [mobiusMertensPartialSum_eq_mertensIoc, Complex.norm_intCast] at this
  have hC0 : 0 ≤ C := by
    have h0 := (abs_nonneg _).trans hM
    have hp : 0 < (((n / k : ℕ) : ℝ) + 1) ^ a := by positivity
    by_contra hneg
    have : C * (((n / k : ℕ) : ℝ) + 1) ^ a < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hp
    linarith
  have hN1R : (1 : ℝ) ≤ ((n / k : ℕ) : ℝ) := by exact_mod_cast hN1
  have h1 : (((n / k : ℕ) : ℝ) + 1) ^ a ≤ 2 * ((n / k : ℕ) : ℝ) ^ a := by
    calc (((n / k : ℕ) : ℝ) + 1) ^ a ≤ (2 * ((n / k : ℕ) : ℝ)) ^ a :=
          Real.rpow_le_rpow (by positivity) (by linarith) ha0
      _ = (2 : ℝ) ^ a * ((n / k : ℕ) : ℝ) ^ a := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * ((n / k : ℕ) : ℝ) ^ a := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (2 : ℝ) ^ a ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
            _ = 2 := Real.rpow_one 2
  have h2 : ((n / k : ℕ) : ℝ) ^ a * (k : ℝ) ^ a ≤ (n : ℝ) ^ a := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ ha0
    exact_mod_cast Nat.div_mul_le_self n k
  calc |(mertensIoc (n / k) : ℝ)| * (k : ℝ) ^ a
      ≤ C * (((n / k : ℕ) : ℝ) + 1) ^ a * (k : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hM (by positivity)
    _ ≤ C * (2 * ((n / k : ℕ) : ℝ) ^ a) * (k : ℝ) ^ a := by gcongr
    _ = 2 * C * (((n / k : ℕ) : ℝ) ^ a * (k : ℝ) ^ a) := by ring
    _ ≤ 2 * C * (n : ℝ) ^ a := by gcongr

/-- **The Mertens bound under the Riemann hypothesis, in scaled form.**  For `0 < δ ≤ ½` there is
`B` with `|M(n/k)| k^{½+δ} ≤ B n^{½+δ}` for all `1 ≤ k ≤ n`. -/
theorem exists_abs_mertensIoc_div_mul_rpow_le (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
      |(mertensIoc (n / k) : ℝ)| * (k : ℝ) ^ ((1 / 2 : ℝ) + δ)
        ≤ B * (n : ℝ) ^ ((1 / 2 : ℝ) + δ) := by
  obtain ⟨C, hC0, hC⟩ := riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound hRH δ hδ
  exact ⟨2 * C, by positivity, fun n k hk hkn =>
    abs_mertensIoc_div_mul_rpow_le_of_bound (by positivity) (by linarith) hC hk hkn⟩

/-- The Farey set of order `n` has `Σ_{q ≤ n} φ(q)` elements. -/
theorem card_fareySet_eq_sum_totient (n : ℕ) :
    (fareySet n).card = ∑ q ∈ Ioc 0 n, Nat.totient q := by
  rw [card_eq_sum_ones, sum_fareySet_eq_sum_sum n (fun _ => (1 : ℕ)),
    show Icc 1 n = Ioc 0 n by ext; simp only [mem_Icc, mem_Ioc]; omega]
  refine sum_congr rfl fun q _ => ?_
  rw [← card_eq_sum_ones, ← Nat.filter_coprime_Ico_eq_totient q 1]
  congr 1
  ext a
  simp only [mem_filter, mem_Icc, mem_Ico, Nat.coprime_comm (n := a)]
  omega

/-- `Σ_{k ≤ n} Φ(n/k) = Σ_{m ≤ n} m`, where `Φ(N) = Σ_{q ≤ N} φ(q)`. -/
theorem sum_sum_totient_div_eq (n : ℕ) :
    ∑ k ∈ Ioc 0 n, ∑ q ∈ Ioc 0 (n / k), Nat.totient q = ∑ m ∈ Ioc 0 n, m := by
  set φA : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩ with hφA
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum ArithmeticFunction.zeta φA n
  have h1 : ∀ m ∈ Ioc 0 n, (ArithmeticFunction.zeta * φA) m = m := by
    intro m _
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal' (fun a b => ArithmeticFunction.zeta a * φA b)]
    calc ∑ d ∈ m.divisors, ArithmeticFunction.zeta (m / d) * φA d
        = ∑ d ∈ m.divisors, Nat.totient d := sum_congr rfl fun d hd => by
          have : m / d ≠ 0 :=
            (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
          simp [ArithmeticFunction.zeta_apply, this, hφA]
      _ = m := Nat.sum_totient m
  rw [sum_congr rfl h1] at h
  rw [h]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by have := (mem_Ioc.mp hk).1; omega
  simp [ArithmeticFunction.zeta_apply, hk0, hφA]

/-- `Σ_{q ≤ N} q = N(N+1)/2`. -/
theorem sum_Ioc_natCast_eq (N : ℕ) : ∑ q ∈ Ioc 0 N, (q : ℝ) = (N : ℝ) * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ m ih => rw [sum_Ioc_succ_top (by omega), ih]; push_cast; ring

/-- `Σ_{2 ≤ k ≤ n} 1/k² ≤ 3/4`. -/
theorem sum_Ioc_one_one_div_sq_le (n : ℕ) : ∑ k ∈ Ioc 1 n, 1 / (k : ℝ) ^ 2 ≤ 3 / 4 := by
  have key : ∀ m : ℕ, 2 ≤ m → ∑ k ∈ Ioc 1 m, 1 / (k : ℝ) ^ 2 ≤ 3 / 4 - 1 / (m : ℝ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num [show Ioc 1 2 = {2} from rfl]
    | succ m hm ih =>
      rw [sum_Ioc_succ_top (by omega)]
      have hm0 : (0 : ℝ) < m := by positivity
      have e : 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) = 1 / ((m : ℝ) * (m + 1)) := by
        field_simp; ring
      have h2 : 1 / ((m : ℝ) + 1) ^ 2 ≤ 1 / ((m : ℝ) * (m + 1)) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
      push_cast
      linarith
  rcases le_or_gt 2 n with hn | hn
  · have h1 := key n hn
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith
  · rw [show Ioc 1 n = ∅ by ext k; simp only [mem_Ioc, notMem_empty, iff_false]; omega]
    norm_num

/-- `Σ_{2 ≤ k ≤ n} 1/k ≤ log n`. -/
theorem sum_Ioc_one_one_div_le_log (n : ℕ) : ∑ k ∈ Ioc 1 n, 1 / (k : ℝ) ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp
  have h := RHTower.Sieve.sum_Icc_one_div_le_one_add_log n
  rw [show Icc 1 n = insert 1 (Ioc 1 n) by ext k; simp only [mem_Icc, mem_insert, mem_Ioc]; omega,
    sum_insert (by simp)] at h
  simp only [Nat.cast_one, div_one] at h
  linarith

/-- **The size of the Farey set.**  `|F_n| ≥ n²/16` for `n ≥ 256`. -/
theorem card_fareySet_ge {n : ℕ} (hn : 256 ≤ n) : (n : ℝ) ^ 2 / 16 ≤ (fareySet n).card := by
  have hn1 : 1 ≤ n := by omega
  have hsum := congrArg (fun z : ℕ => (z : ℝ)) (sum_sum_totient_div_eq n)
  simp only [Nat.cast_sum] at hsum
  rw [sum_Ioc_natCast_eq,
    show Ioc 0 n = insert 1 (Ioc 1 n) by ext k; simp only [mem_Ioc, mem_insert]; omega,
    sum_insert (by simp), Nat.div_one] at hsum
  have hcard : ((fareySet n).card : ℝ) = ∑ q ∈ Ioc 0 n, (Nat.totient q : ℝ) := by
    rw [card_fareySet_eq_sum_totient]; push_cast; rfl
  have hΦle : ∀ N : ℕ, ∑ q ∈ Ioc 0 N, (Nat.totient q : ℝ) ≤ (N : ℝ) * (N + 1) / 2 := by
    intro N
    rw [← sum_Ioc_natCast_eq]
    exact sum_le_sum fun q _ => by exact_mod_cast Nat.totient_le q
  have hrest : ∑ k ∈ Ioc 1 n, ∑ q ∈ Ioc 0 (n / k), (Nat.totient q : ℝ)
      ≤ ((n : ℝ) ^ 2 * (3 / 4) + n * Real.log n) / 2 := by
    calc ∑ k ∈ Ioc 1 n, ∑ q ∈ Ioc 0 (n / k), (Nat.totient q : ℝ)
        ≤ ∑ k ∈ Ioc 1 n, ((n : ℝ) ^ 2 * (1 / (k : ℝ) ^ 2) + n * (1 / (k : ℝ))) / 2 := by
          refine sum_le_sum fun k hk => ?_
          have hk0 : (0 : ℝ) < k := by have := (mem_Ioc.mp hk).1; positivity
          have hNk : ((n / k : ℕ) : ℝ) ≤ n / k := Nat.cast_div_le
          have hN0 : (0 : ℝ) ≤ ((n / k : ℕ) : ℝ) := by positivity
          calc ∑ q ∈ Ioc 0 (n / k), (Nat.totient q : ℝ)
              ≤ ((n / k : ℕ) : ℝ) * (((n / k : ℕ) : ℝ) + 1) / 2 := hΦle _
            _ ≤ (n / k) * (n / k + 1) / 2 := by gcongr
            _ = ((n : ℝ) ^ 2 * (1 / (k : ℝ) ^ 2) + n * (1 / (k : ℝ))) / 2 := by
                field_simp
      _ = ((n : ℝ) ^ 2 * ∑ k ∈ Ioc 1 n, 1 / (k : ℝ) ^ 2
            + n * ∑ k ∈ Ioc 1 n, 1 / (k : ℝ)) / 2 := by
          rw [← sum_div, sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ ((n : ℝ) ^ 2 * (3 / 4) + n * Real.log n) / 2 := by
          gcongr
          · exact sum_Ioc_one_one_div_sq_le n
          · exact sum_Ioc_one_one_div_le_log n
  have hlog : Real.log n ≤ 2 * √(n : ℝ) := by
    have := Real.log_le_rpow_div (x := n) (by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at this
    linarith
  have hsqrt : 16 ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have : (256 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by positivity)
  have hnsq : (n : ℝ) * √(n : ℝ) ≤ (n : ℝ) ^ 2 / 16 := by
    have h0 : 0 ≤ (n : ℝ) * √(n : ℝ) := by positivity
    nlinarith
  have hnlog : (n : ℝ) * Real.log n ≤ (n : ℝ) * (2 * √(n : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  rw [hcard]
  nlinarith

/-- The Farey set of order `n` has at most `n²` elements. -/
theorem card_fareySet_le (n : ℕ) : (fareySet n).card ≤ n ^ 2 := by
  unfold RHTower.Sieve.fareySet
  refine (card_filter_le _ _).trans ?_
  rw [card_product, Nat.card_Icc, sq]
  simp

end

end RHTower
