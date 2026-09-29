import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanSourceMeanValue
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAllIntervalLongWindow
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPerronFactorization

/-!
# The Dirichlet polynomial of the all-interval `E₃` sum

Matomäki–Teräväinen §7 writes the `E₃` window sum
`∑_{p₁ ∼ P₁} ∑_{p₂ ∼ R} ∑_{x < p₁p₂n ≤ x+h} ρ⁻(n)` as the window sum of the coefficients
`c(n) = ∑_{p₁ ∈ B₁} ∑_{p₂ ∈ B₂} [p₁p₂ ∣ n] s(n/(p₁p₂))`, whose Dirichlet polynomial is the product
`P₁(s) P₂(s) P(s)`.  The coefficients are real and bounded by `156 (log₂ n)²`, so the polynomial
is conjugate-symmetric on the line `σ = 1`.  The dyadic prime polynomial
`P₂(1+it) = ∑_{⌊R⌋ < p ≤ ⌊2R⌋} p^{-1-it}` has the improved mean value
`∫_{-T}^{T}|P₂(1+it)|² ≪ T/(R log R) + (log R)^{-2}`, from the sifted mean value theorem with the
prime indicator as coefficients.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Summing a function of `n/d` over the multiples of `d` in `(a, b]`, any additive target. -/
theorem sum_Ioc_ite_dvd_eq {M : Type*} [AddCommMonoid M] {a b d : ℕ} (hd : 0 < d) (f : ℕ → M) :
    ∑ n ∈ Finset.Ioc a b, (if d ∣ n then f (n / d) else 0) = ∑ m ∈ Finset.Ioc (a / d) (b / d), f m := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun m => d * m) (fun n => n / d) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_Ioc] at hm
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right d m⟩
    · have := (Nat.div_lt_iff_lt_mul hd).1 hm.1; linarith [mul_comm m d]
    · have := (Nat.le_div_iff_mul_le hd).1 hm.2; linarith [mul_comm m d]
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    simp only [Finset.mem_Ioc]
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
    rw [Nat.mul_div_cancel_left k hd]
    exact ⟨(Nat.div_lt_iff_lt_mul hd).2 (by linarith [mul_comm k d]),
      (Nat.le_div_iff_mul_le hd).2 (by linarith [mul_comm k d])⟩
  · intro m _; exact Nat.mul_div_cancel_left m hd
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _; rw [Nat.mul_div_cancel_left m hd]

/-- The coefficients of `P₁ P₂ P`: `c(n) = ∑_{p₁ ∈ B₁} ∑_{p₂ ∈ B₂} [p₁p₂ ∣ n] s(n/(p₁p₂))`. -/
def mtAllIntervalCoeff (B₁ B₂ : Finset ℕ) (s : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p₁ ∈ B₁, ∑ p₂ ∈ B₂, if p₁ * p₂ ∣ n then s (n / (p₁ * p₂)) else 0

/-- **The window sum of the coefficients.** -/
theorem sum_Ioc_mtAllIntervalCoeff {B₁ B₂ : Finset ℕ} (hB₁ : ∀ p ∈ B₁, 0 < p)
    (hB₂ : ∀ p ∈ B₂, 0 < p) (s : ℕ → ℂ) (a b : ℕ) :
    ∑ n ∈ Finset.Ioc a b, mtAllIntervalCoeff B₁ B₂ s n =
      ∑ p₁ ∈ B₁, ∑ p₂ ∈ B₂, ∑ m ∈ Finset.Ioc (a / (p₁ * p₂)) (b / (p₁ * p₂)), s m := by
  unfold mtAllIntervalCoeff
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p₁ hp₁ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p₂ hp₂ => ?_
  exact sum_Ioc_ite_dvd_eq (M := ℂ) (Nat.mul_pos (hB₁ p₁ hp₁) (hB₂ p₂ hp₂)) s

/-- **The Dirichlet polynomial of the coefficients factors.** -/
theorem perronPoly_mtAllIntervalCoeff {B₁ B₂ : Finset ℕ} (hB₁ : ∀ p ∈ B₁, 0 < p)
    (hB₂ : ∀ p ∈ B₂, 0 < p) {s : ℕ → ℂ} {N M : ℕ} (hs : ∀ m, s m ≠ 0 → m ∈ Finset.Icc 1 N)
    (hM : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂, p₁ * p₂ * N ≤ M) (t : ℝ) :
    perronPoly (mtAllIntervalCoeff B₁ B₂ s) M 1 t =
      (∑ p₁ ∈ B₁, (p₁ : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
        (∑ p₂ ∈ B₂, (p₂ : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
          perronPoly s N 1 t := by
  classical
  set z : ℂ := -(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) with hz
  set PS : ℂ := perronPoly s N 1 t with hPS
  have hIccN : Finset.Icc 1 N = Finset.Ioc 0 N := by ext n; simp; omega
  have hPSdef : PS = ∑ m ∈ Finset.Ioc 0 N, s m * (m : ℂ) ^ z := by
    rw [hPS, perronPoly, hIccN]
  -- one prime pair
  have key : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂,
      ∑ n ∈ Finset.Ioc 0 M, (if p₁ * p₂ ∣ n then s (n / (p₁ * p₂)) else 0) * (n : ℂ) ^ z =
        (p₁ : ℂ) ^ z * ((p₂ : ℂ) ^ z * PS) := by
    intro p₁ hp₁ p₂ hp₂
    have hq : 0 < p₁ * p₂ := Nat.mul_pos (hB₁ p₁ hp₁) (hB₂ p₂ hp₂)
    have hstep : ∀ n ∈ Finset.Ioc 0 M,
        (if p₁ * p₂ ∣ n then s (n / (p₁ * p₂)) else 0) * (n : ℂ) ^ z =
        if p₁ * p₂ ∣ n then (fun m => s m * ((p₁ * p₂ * m : ℕ) : ℂ) ^ z) (n / (p₁ * p₂)) else 0 := by
      intro n _
      split_ifs with h
      · simp only
        rw [Nat.mul_div_cancel' h]
      · simp
    rw [Finset.sum_congr rfl hstep,
      sum_Ioc_ite_dvd_eq (M := ℂ) hq (fun m => s m * ((p₁ * p₂ * m : ℕ) : ℂ) ^ z), Nat.zero_div]
    have hsub : ∀ m ∈ Finset.Ioc 0 (M / (p₁ * p₂)), m ∉ Finset.Ioc 0 N →
        s m * ((p₁ * p₂ * m : ℕ) : ℂ) ^ z = 0 := by
      intro m _ hm
      have : s m = 0 := by
        by_contra h
        have := hs m h
        rw [hIccN] at this
        exact hm this
      rw [this, zero_mul]
    have hNsub : Finset.Ioc 0 N ⊆ Finset.Ioc 0 (M / (p₁ * p₂)) := by
      intro m hm
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hm
      refine Finset.mem_Ioc.2 ⟨h1, (Nat.le_div_iff_mul_le hq).2 ?_⟩
      calc m * (p₁ * p₂) ≤ N * (p₁ * p₂) := Nat.mul_le_mul_right _ h2
        _ = p₁ * p₂ * N := by ring
        _ ≤ M := hM p₁ hp₁ p₂ hp₂
    rw [← Finset.sum_subset hNsub hsub, hPSdef, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.cast_mul (p₁ * p₂) m, Complex.natCast_mul_natCast_cpow, Nat.cast_mul p₁ p₂,
      Complex.natCast_mul_natCast_cpow]
    ring
  have hIcc : Finset.Icc 1 M = Finset.Ioc 0 M := by ext n; simp; omega
  calc perronPoly (mtAllIntervalCoeff B₁ B₂ s) M 1 t
      = ∑ n ∈ Finset.Ioc 0 M, ∑ p₁ ∈ B₁, ∑ p₂ ∈ B₂,
          (if p₁ * p₂ ∣ n then s (n / (p₁ * p₂)) else 0) * (n : ℂ) ^ z := by
        rw [perronPoly, hIcc]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [mtAllIntervalCoeff, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p₁ _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ p₁ ∈ B₁, ∑ p₂ ∈ B₂, ∑ n ∈ Finset.Ioc 0 M,
          (if p₁ * p₂ ∣ n then s (n / (p₁ * p₂)) else 0) * (n : ℂ) ^ z := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p₁ _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ p₁ ∈ B₁, ∑ p₂ ∈ B₂, (p₁ : ℂ) ^ z * ((p₂ : ℂ) ^ z * PS) :=
        Finset.sum_congr rfl fun p₁ hp₁ => Finset.sum_congr rfl fun p₂ hp₂ => key p₁ hp₁ p₂ hp₂
    _ = _ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p₁ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p₂ _ => ?_
        ring

/-- The `E₃` window sum over arbitrary sets of small and large primes:
`∑_{p₁ ∈ B₁} ∑_{p₂ ∈ B₂} ∑_{x < p₁p₂n ≤ x+h} ρ⁻(n)`. -/
def mtAllIntervalSumOn (B₁ B₂ : Finset ℕ) (z Q D E : ℕ) (x h : ℝ) : ℝ :=
  ∑ p₁ ∈ B₁, ∑ p₂ ∈ B₂,
    ∑ n ∈ Finset.Ioc ⌊x / (p₁ * p₂)⌋₊ ⌊(x + h) / (p₁ * p₂)⌋₊, (rhoMinus z Q D E n : ℝ)

theorem mtAllIntervalSum_eq_on (z Q D E : ℕ) (P₁ R x h : ℝ) :
    mtAllIntervalSum z Q D E P₁ R x h =
      mtAllIntervalSumOn ((Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime)
        ((Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime) z Q D E x h := rfl

/-- **The window sum is the `E₃` sum.**  When every cofactor `m` of the window lies in
`(Y/2, 4Y]`, the coefficient window sum with the Harman source equals the `E₃` window sum. -/
theorem mtAllIntervalSumOn_eq_sum_coeff {B₁ B₂ : Finset ℕ} (hB₁ : ∀ p ∈ B₁, 0 < p)
    (hB₂ : ∀ p ∈ B₂, 0 < p) {z Q D E Y : ℕ} {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h)
    (hrange : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂,
      ∀ m ∈ Finset.Ioc (⌊x⌋₊ / (p₁ * p₂)) (⌊x + h⌋₊ / (p₁ * p₂)),
        (Y : ℝ) / 2 < m ∧ (m : ℝ) ≤ 4 * Y) :
    ((mtAllIntervalSumOn B₁ B₂ z Q D E x h : ℝ) : ℂ) =
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, mtAllIntervalCoeff B₁ B₂
        (fun n => mtHarmanProposition22SourceAF z Q D E Y n) n := by
  rw [sum_Ioc_mtAllIntervalCoeff hB₁ hB₂, mtAllIntervalSumOn]
  push_cast
  refine Finset.sum_congr rfl fun p₁ hp₁ => Finset.sum_congr rfl fun p₂ hp₂ => ?_
  have hfl : ∀ y : ℝ, 0 ≤ y → ⌊y / ((p₁ : ℝ) * (p₂ : ℝ))⌋₊ = ⌊y⌋₊ / (p₁ * p₂) := by
    intro y _
    rw [show ((p₁ : ℝ) * (p₂ : ℝ)) = ((p₁ * p₂ : ℕ) : ℝ) by push_cast; ring, Nat.floor_div_natCast]
  rw [hfl x hx, hfl (x + h) (by linarith)]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hlo, hhi⟩ := hrange p₁ hp₁ p₂ hp₂ m hm
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hlo
    exact_mod_cast this
  rw [mtHarmanProposition22SourceAF, mtRealIntervalAF_apply_of_pos _ _ _ hm0, if_pos ⟨hlo, hhi⟩]

/-- At most `log₂ n` primes of a set divide `n ≥ 1`. -/
theorem card_filter_prime_dvd_le_log {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {n : ℕ} (hn : 0 < n) :
    (B.filter (· ∣ n)).card ≤ Nat.log 2 n := by
  classical
  have hsub : B.filter (· ∣ n) ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hpB, hpn⟩ := Finset.mem_filter.1 hp
    exact Nat.mem_primeFactors.2 ⟨hB p hpB, hpn, hn.ne'⟩
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  calc 2 ^ (B.filter (· ∣ n)).card ≤ 2 ^ n.primeFactors.card :=
        Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card hsub)
    _ = ∏ _p ∈ n.primeFactors, 2 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, p :=
        Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- **Coefficient bound.**  `|c(n)| ≤ S (log₂ n)²` when `|s| ≤ S` and `B₁, B₂` are sets of primes. -/
theorem norm_mtAllIntervalCoeff_le {B₁ B₂ : Finset ℕ} (hB₁ : ∀ p ∈ B₁, p.Prime)
    (hB₂ : ∀ p ∈ B₂, p.Prime) {s : ℕ → ℂ} {S : ℝ} (hS : ∀ m, ‖s m‖ ≤ S) {n : ℕ} (hn : 0 < n) :
    ‖mtAllIntervalCoeff B₁ B₂ s n‖ ≤ S * (Nat.log 2 n : ℝ) ^ 2 := by
  classical
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  unfold mtAllIntervalCoeff
  have hterm : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂,
      ‖(if p₁ * p₂ ∣ n then s (n / (p₁ * p₂)) else 0)‖ ≤
        (if p₁ ∣ n then 1 else 0) * ((if p₂ ∣ n then 1 else 0) * S) := by
    intro p₁ _ p₂ _
    split_ifs with h h1 h2 h2 h1 h2
    · simpa using hS _
    · exact absurd (dvd_trans (dvd_mul_left p₂ p₁) h) h2
    · exact absurd (dvd_trans (dvd_mul_right p₁ p₂) h) h1
    · exact absurd (dvd_trans (dvd_mul_right p₁ p₂) h) h1
    all_goals simp [hS0]
  calc ‖∑ p₁ ∈ B₁, ∑ p₂ ∈ B₂, (if p₁ * p₂ ∣ n then s (n / (p₁ * p₂)) else 0)‖
      ≤ ∑ p₁ ∈ B₁, ∑ p₂ ∈ B₂, ‖(if p₁ * p₂ ∣ n then s (n / (p₁ * p₂)) else 0)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun p₁ _ => norm_sum_le _ _)
    _ ≤ ∑ p₁ ∈ B₁, ∑ p₂ ∈ B₂, (if p₁ ∣ n then 1 else 0) * ((if p₂ ∣ n then 1 else 0) * S) :=
        Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ => hterm p₁ hp₁ p₂ hp₂
    _ = ((B₁.filter (· ∣ n)).card : ℝ) * (((B₂.filter (· ∣ n)).card : ℝ) * S) := by
        rw [← Finset.sum_mul_sum]
        simp [Finset.sum_ite]
    _ ≤ (Nat.log 2 n : ℝ) * ((Nat.log 2 n : ℝ) * S) := by
        have h1 : ((B₁.filter (· ∣ n)).card : ℝ) ≤ Nat.log 2 n := by
          exact_mod_cast card_filter_prime_dvd_le_log hB₁ hn
        have h2 : ((B₂.filter (· ∣ n)).card : ℝ) ≤ Nat.log 2 n := by
          exact_mod_cast card_filter_prime_dvd_le_log hB₂ hn
        gcongr
    _ = S * (Nat.log 2 n : ℝ) ^ 2 := by ring

/-- Real coefficients: `P(σ - it)` is the conjugate of `P(σ + it)`. -/
theorem perronPoly_neg_eq_conj {c : ℕ → ℂ} (hc : ∀ n, starRingEnd ℂ (c n) = c n) (M : ℕ)
    (σ t : ℝ) : perronPoly c M σ (-t) = starRingEnd ℂ (perronPoly c M σ t) := by
  unfold perronPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, hc n]
  congr 1
  have harg : ((n : ℕ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_pos.ne
  have hconj : -((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) =
      starRingEnd ℂ (-((σ : ℂ) + ((t : ℝ) : ℂ) * Complex.I)) := by
    rw [map_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  rw [hconj, Complex.cpow_conj _ _ harg, Complex.conj_natCast]

/-- Real coefficients: `|P(σ - it)| = |P(σ + it)|`. -/
theorem norm_perronPoly_neg {c : ℕ → ℂ} (hc : ∀ n, starRingEnd ℂ (c n) = c n) (M : ℕ)
    (σ t : ℝ) : ‖perronPoly c M σ (-t)‖ = ‖perronPoly c M σ t‖ := by
  rw [perronPoly_neg_eq_conj hc, Complex.norm_conj]

theorem conj_mtAllIntervalCoeff {B₁ B₂ : Finset ℕ} {s : ℕ → ℂ}
    (hs : ∀ m, starRingEnd ℂ (s m) = s m) (n : ℕ) :
    starRingEnd ℂ (mtAllIntervalCoeff B₁ B₂ s n) = mtAllIntervalCoeff B₁ B₂ s n := by
  unfold mtAllIntervalCoeff
  simp only [map_sum]
  refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => ?_
  split_ifs
  · exact hs _
  · exact map_zero _

theorem conj_mtHarmanProposition22SourceAF (z Q D E Y n : ℕ) :
    starRingEnd ℂ (mtHarmanProposition22SourceAF z Q D E Y n) =
      mtHarmanProposition22SourceAF z Q D E Y n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [ArithmeticFunction.map_zero, map_zero]
  rw [mtHarmanProposition22SourceAF, mtRealIntervalAF_apply_of_pos _ _ _ hn0]
  split_ifs
  · exact map_intCast _ _
  · exact map_zero _

/-- The primes of `(⌊R⌋, ⌊2R⌋]` lie in `(⌊R⌋/2, 4⌊R⌋]` and above every prime `< ⌊R⌋ + 1`. -/
theorem primeSet_floor_facts {R : ℝ} (hR : 1 ≤ R) {p : ℕ}
    (hp : p ∈ (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime) :
    0 < p ∧ ((⌊R⌋₊ : ℕ) : ℝ) / 2 < p ∧ (p : ℝ) ≤ 4 * ((⌊R⌋₊ : ℕ) : ℝ) ∧
      ∀ q, q.Prime → q < ⌊R⌋₊ + 1 → ¬ q ∣ p := by
  obtain ⟨hpI, hpp⟩ := Finset.mem_filter.1 hp
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.1 hpI
  have hR1 : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR)
  have hfl2 : ⌊2 * R⌋₊ ≤ 2 * ⌊R⌋₊ + 1 := by
    have h1 : (⌊2 * R⌋₊ : ℝ) ≤ 2 * R := Nat.floor_le (by linarith)
    have h2 : R < (⌊R⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one R
    have : (⌊2 * R⌋₊ : ℝ) < ((2 * ⌊R⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.1 this
    omega
  refine ⟨hpp.pos, ?_, ?_, ?_⟩
  · have : ((⌊R⌋₊ : ℕ) : ℝ) < p := by exact_mod_cast hlo
    have h0 : (0 : ℝ) ≤ ((⌊R⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  · have : p ≤ 4 * ⌊R⌋₊ := by omega
    exact_mod_cast this
  · intro q hq hqR hqp
    have := (Nat.prime_dvd_prime_iff_eq hq hpp).1 hqp
    omega

/-- **The improved mean value theorem for a dyadic prime polynomial.**
`∫_{-T}^{T} |∑_{⌊R⌋ < p ≤ ⌊2R⌋} p^{-1-it}|² dt ≤ C (T/(R log R) + (log R)^{-2})` for
`1 ≤ T ≤ R^{201/200}`: the sifted mean value theorem with the prime indicator as coefficients. -/
theorem eventually_integral_normSq_primeSet_floor_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℝ in Filter.atTop, ∀ T : ℝ, 1 ≤ T → T ≤ R ^ (201 / 200 : ℝ) →
      ∫ t in Set.Icc (-T) T,
          ‖∑ p ∈ (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime,
            (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ^ 2 ≤
        C * (T / (R * Real.log R) + 1 / Real.log R ^ 2) := by
  classical
  obtain ⟨C, hC, hev⟩ := eventually_integral_normSq_LSeries_rough_le
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨16 * C, by positivity, ?_⟩
  have hgap : (0 : ℝ) < 100 / 99 - 201 / 200 := by norm_num
  filter_upwards [Filter.eventually_ge_atTop (max 4 (2 * max X₀ 1)),
    (tendsto_rpow_atTop hgap).eventually_ge_atTop ((2 : ℝ) ^ (100 / 99 : ℝ))]
    with R hR hRgap
  intro T hT hTR
  have hR4 : 4 ≤ R := le_trans (le_max_left _ _) hR
  have hR0 : 0 < R := by linarith
  set Y : ℕ := ⌊R⌋₊ with hYdef
  have hYR : (Y : ℝ) ≤ R := Nat.floor_le hR0.le
  have hRY : R / 2 ≤ (Y : ℝ) := by
    have := Nat.lt_floor_add_one R
    rw [← hYdef] at this
    linarith
  have hY2 : (2 : ℝ) ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  set X : ℝ := (Y : ℝ) ^ (100 / 99 : ℝ) with hXdef
  have hXY : X ^ (99 / 100 : ℝ) = Y := by
    rw [hXdef, ← Real.rpow_mul hY0.le]; norm_num
  have hYX : (Y : ℝ) ≤ X := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Y)
      (by norm_num : (1 : ℝ) ≤ 100 / 99)
    rwa [Real.rpow_one] at this
  have hX₀X : X₀ ≤ X := by
    have h1 : X₀ ≤ R / 2 := by
      have := le_trans (le_max_right _ _) hR
      have h2 := le_max_left X₀ 1
      linarith
    linarith
  have hz : X ^ (1 / 10 : ℝ) < ((Y + 1 : ℕ) : ℝ) := by
    have h1 : X ^ (1 / 10 : ℝ) = (Y : ℝ) ^ (10 / 99 : ℝ) := by
      rw [hXdef, ← Real.rpow_mul hY0.le]; norm_num
    have h2 : (Y : ℝ) ^ (10 / 99 : ℝ) ≤ (Y : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Y)
        (by norm_num : (10 / 99 : ℝ) ≤ 1)
      rwa [Real.rpow_one] at this
    push_cast; linarith
  have hTX : T ≤ X := by
    refine hTR.trans ?_
    -- `R^{201/200} ≤ (R/2)^{100/99} ≤ Y^{100/99}`
    have h1 : R ^ (201 / 200 : ℝ) ≤ (R / 2) ^ (100 / 99 : ℝ) := by
      rw [Real.div_rpow hR0.le (by norm_num), le_div_iff₀ (by positivity)]
      have hsplit : R ^ (100 / 99 : ℝ) = R ^ (201 / 200 : ℝ) * R ^ ((100 / 99 : ℝ) - 201 / 200) := by
        rw [← Real.rpow_add hR0]; norm_num
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hRgap (by positivity)
    exact h1.trans (Real.rpow_le_rpow (by positivity) hRY (by norm_num))
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℂ,
      S = fun n => if n ∈ (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime then 1 else 0 := ⟨_, rfl⟩
  have hSval : ∀ n, S n = if n ∈ (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime then 1 else 0 :=
    fun n => by rw [hSdef]
  have hmemS : ∀ n, S n ≠ 0 → n ∈ (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime := by
    intro n hn
    by_contra h
    exact hn (by rw [hSval, if_neg h])
  have hS : ∀ n, S n ≠ 0 → 0 < n ∧ (Y : ℝ) / 2 < n ∧ (n : ℝ) ≤ 4 * Y := by
    intro n hn
    obtain ⟨h1, h2, h3, -⟩ := primeSet_floor_facts (by linarith) (hmemS n hn)
    exact ⟨h1, h2, h3⟩
  have hSrough : ∀ n, S n ≠ 0 → ∀ p, p.Prime → p < Y + 1 → ¬ p ∣ n := fun n hn =>
    (primeSet_floor_facts (by linarith) (hmemS n hn)).2.2.2
  have hSb : ∀ n, ‖S n‖ ≤ 156 := by
    intro n
    rw [hSval]
    split_ifs <;> norm_num
  have hmain := hX₀ X hX₀X S (Y + 1) Y hz hS hSrough hSb (le_of_eq hXY) hYX T hT hTX
  have hB0 : (0 : ℕ) ∉ (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime := by simp
  have hfun : ∀ t : ℝ, ∑ p ∈ (Finset.Ioc Y ⌊2 * R⌋₊).filter Nat.Prime,
      (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) =
        LSeries S (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) := fun t => by
    rw [hSdef]; exact sum_primeSet_eq_LSeries hB0 t
  simp_rw [hfun]
  refine hmain.trans ?_
  -- `log X ≥ log Y ≥ (log R)/2`
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hlogY : Real.log R / 2 ≤ Real.log Y := by
    have h1 : Real.log (R / 2) ≤ Real.log Y := Real.log_le_log (by positivity) hRY
    have h2 : Real.log (R / 2) = Real.log R - Real.log 2 := Real.log_div hR0.ne' (by norm_num)
    have h3 : 2 * Real.log 2 ≤ Real.log R := by
      rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
      exact Real.log_le_log (by positivity) (by norm_num; linarith)
    linarith
  have hlogX : Real.log Y ≤ Real.log X := Real.log_le_log hY0 hYX
  have hL : Real.log R / 2 ≤ Real.log X := hlogY.trans hlogX
  have hLpos : 0 < Real.log R / 2 := by positivity
  have hLX : 0 < Real.log X := lt_of_lt_of_le hLpos hL
  have h1 : T / ((Y : ℝ) * Real.log X) ≤ 4 * (T / (R * Real.log R)) := by
    rw [div_le_iff₀ (mul_pos hY0 hLX)]
    have : R * Real.log R ≤ 4 * ((Y : ℝ) * Real.log X) := by
      have := mul_le_mul hRY hL hLpos.le hY0.le
      nlinarith
    calc T = 4 * (T / (R * Real.log R)) * (R * Real.log R) / 4 := by field_simp
      _ ≤ 4 * (T / (R * Real.log R)) * (4 * ((Y : ℝ) * Real.log X)) / 4 := by
          gcongr
      _ = 4 * (T / (R * Real.log R)) * ((Y : ℝ) * Real.log X) := by ring
  have h2 : 1 / Real.log X ^ 2 ≤ 4 * (1 / Real.log R ^ 2) := by
    rw [div_le_iff₀ (pow_pos hLX 2)]
    have : Real.log R ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
    calc (1 : ℝ) = 4 * (1 / Real.log R ^ 2) * Real.log R ^ 2 / 4 := by field_simp
      _ ≤ 4 * (1 / Real.log R ^ 2) * (4 * Real.log X ^ 2) / 4 := by gcongr
      _ = 4 * (1 / Real.log R ^ 2) * Real.log X ^ 2 := by ring
  calc C * (T / ((Y : ℝ) * Real.log X) + 1 / Real.log X ^ 2)
      ≤ C * (4 * (T / (R * Real.log R)) + 4 * (1 / Real.log R ^ 2)) := by gcongr
    _ ≤ 16 * C * (T / (R * Real.log R) + 1 / Real.log R ^ 2) := by
        have : 0 ≤ T / (R * Real.log R) := by positivity
        have : 0 ≤ 1 / Real.log R ^ 2 := by positivity
        nlinarith

end

end RHTower.Sieve
