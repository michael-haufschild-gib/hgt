import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveWithTheMontgomeryVaughanConstant

/-!
# The count sees the edited primes

Let `a = 1 * u` be a real sequence (`a(n) = Σ_{d ∣ n} u(d)`) with count `N(x) = Σ_{n ≤ x} a(n)`
and remainder `R(x) = N(x) − A x`.  For a system of generalized integers `a(n)` is the number of
integers of norm `n` and `u` is the coefficient sequence of `ζ_B / ζ`.

A prime `p` is *seen* (`IsSeen`) if on every multiple `p n` the divisors divisible by `p` carry
at least the mass `a(n)`, with one sign for all `n`:

* a *deleted* prime (`a` nonnegative and zero on the multiples of `p`) is seen with the sign `−`
  (`isSeen_of_deleted`);
* a *doubled* prime (`u(p d) = u(d)` for all `d`) is seen with the sign `+`
  (`isSeen_of_mul_invariant`).

Results.

* **Peak** (`peak_le_norm`).  For a seen prime `p` the exponential sum of the remainder over
  `(X, 2X]` at the frequency `1/p` has absolute value at least `A X / (8π)`, as soon as
  `A + A p + 4E + W_p ≤ (3/4) A X / p`, where `E` bounds `|R|` up to `2X` and
  `W_p = Σ_{d ≤ 2X} |u(d)| min(p, X/d + 1)`.  Summation by parts turns `Σ R(n) e(n/p)` into
  `Σ (a(n) − A) e(n/p)` divided by `1 − e(1/p)`; the divisors prime to `p` are equidistributed
  over the classes up to `W_p` (the multiples of `d` give a geometric sum, at most `p` and at
  most their number), and the divisors divisible by `p` leave a term of absolute value at least
  `A X / p` on the class `0`.
* **Rankin** (`sum_abs_mul_min_le`).  If `Σ_{d ≤ 2X} |u(d)| d^{−θ} ≤ Z` then
  `W_p ≤ 3 Z X^θ p^{1−θ}`.
* **Large sieve** (`card_mul_sq_le`, `card_le_of_scale`).  The frequencies `1/p` are Farey
  points, so the peaks are square-summable against `(X + Q²) Σ |R(n)|²`.  If `16 Q² ≤ X`,
  `64 Q E ≤ A X` and `48 Z Q^{2−θ} X^θ ≤ A X`, at most `128 π² (E/A)²` primes up to `Q` are seen.
* **Power form** (`card_le_rpow`).  If `|R(x)| ≤ C x^β` and `Σ_d |u(d)| d^{−θ} ≤ Z` with
  `θ < 1`, the seen primes up to `Q` number at most `c Q^{2β(2−θ)/(1−θ)}`.
* **Chebyshev** (`sum_Ioc_half_le`).  For `u ≥ 0` the mass of `u` on `(x/2, x]` is at most
  `N(x) − 2 N(x/2)`.

So a count remainder of small exponent leaves room for few edited primes: the count sees them.
-/

open Finset RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.CountSieve

/-! ## Roots of unity -/

theorem norm_one_sub_pow_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) (j : ℕ) : ‖1 - ζ ^ j‖ ≤ j * ‖1 - ζ‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : 1 - ζ ^ (j + 1) = (1 - ζ ^ j) + ζ ^ j * (1 - ζ) := by ring
    rw [h]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_pow, hζ, one_pow, one_mul]
    push_cast
    linarith

theorem sum_range_natCast (p : ℕ) : ∑ j ∈ range p, (j : ℝ) = (p : ℝ) * ((p : ℝ) - 1) / 2 := by
  induction p with
  | zero => simp
  | succ p ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- A root of unity `ζ ≠ 1` of order dividing `p` has `2 / |ζ − 1| ≤ p`: the powers of `ζ` sum
to zero, so `p = |Σ_{j < p} (1 − ζ^j)| ≤ |1 − ζ| p (p − 1) / 2`. -/
theorem two_div_norm_sub_one_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) {p : ℕ} (hp : 1 ≤ p) (hpow : ζ ^ p = 1)
    (hne : ζ ≠ 1) : 2 / ‖ζ - 1‖ ≤ p := by
  have hpos : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hsum : ∑ j ∈ range p, ζ ^ j = 0 := by rw [geom_sum_eq hne, hpow, sub_self, zero_div]
  have hp' : (p : ℂ) = ∑ j ∈ range p, (1 - ζ ^ j) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hnorm : (p : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 1) / 2 * ‖ζ - 1‖ := by
    calc (p : ℝ) = ‖(p : ℂ)‖ := (Complex.norm_natCast p).symm
      _ = ‖∑ j ∈ range p, (1 - ζ ^ j)‖ := by rw [← hp']
      _ ≤ ∑ j ∈ range p, ‖1 - ζ ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range p, (j : ℝ) * ‖1 - ζ‖ :=
          Finset.sum_le_sum fun j _ => norm_one_sub_pow_le hζ j
      _ = (p : ℝ) * ((p : ℝ) - 1) / 2 * ‖ζ - 1‖ := by
          rw [← Finset.sum_mul, sum_range_natCast, norm_sub_rev]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_iff₀ hpos]
  by_contra hlt
  have hlt' : (p : ℝ) * ‖ζ - 1‖ < 2 := not_le.mp hlt
  nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hlt'.le)]

/-! ## The frequency `1/p` -/

theorem norm_one_sub_circleFreq_le (x : ℝ) : ‖1 - circleFreq x‖ ≤ 2 * Real.pi * |x| := by
  rw [norm_sub_rev, circleFreq, mul_comm ((2 * Real.pi * x : ℝ) : ℂ) Complex.I]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem circleFreq_one : circleFreq 1 = 1 := by
  rw [circleFreq, mul_one]
  push_cast
  exact Complex.exp_two_pi_mul_I

theorem circleFreq_inv_pow_self {p : ℕ} (hp : 0 < p) : circleFreq (1 / (p : ℝ)) ^ p = 1 := by
  rw [circleFreq_pow, mul_one_div_cancel (Nat.cast_ne_zero.mpr hp.ne'), circleFreq_one]

theorem circleFreq_inv_pow_ne_one {p d : ℕ} (hp : 0 < p) (hd : ¬ p ∣ d) :
    circleFreq (1 / (p : ℝ)) ^ d ≠ 1 := by
  intro h
  rw [circleFreq_pow] at h
  obtain ⟨k, hk⟩ := exists_int_of_circleFreq_eq_one h
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have h2 : (d : ℝ) = (k : ℝ) * (p : ℝ) := by
    rw [← hk]
    field_simp
  have h3 : (d : ℤ) = k * (p : ℤ) := by exact_mod_cast h2
  exact hd (Int.natCast_dvd_natCast.mp ⟨k, by rw [h3, mul_comm]⟩)

/-! ## Summation by parts and progressions -/

/-- Summation by parts against the powers of `ω`. -/
theorem one_sub_mul_sum_pow (R : ℕ → ℂ) (ω : ℂ) (X : ℕ) {M : ℕ} (hM : X ≤ M) :
    (1 - ω) * ∑ n ∈ Ioc X M, R n * ω ^ n =
      ∑ n ∈ Ioc X M, (R n - R (n - 1)) * ω ^ n + R X * ω ^ (X + 1) - R M * ω ^ (M + 1) := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top hM, Finset.sum_Ioc_succ_top hM, mul_add, ih, Nat.add_sub_cancel]
    ring

theorem Ico_succ_succ' (a b : ℕ) : Ico (a + 1) (b + 1) = Ioc a b := by
  ext m
  simp only [mem_Ico, mem_Ioc]
  omega

/-- The multiples of `d` in `(X, Y]`. -/
theorem filter_dvd_Ioc (d : ℕ) (hd : 0 < d) (X Y : ℕ) :
    (Ioc X Y).filter (fun n => d ∣ n) = (Ioc (X / d) (Y / d)).image (fun m => d * m) := by
  ext n
  simp only [mem_filter, mem_Ioc, mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, m, rfl⟩
    exact ⟨m, ⟨(Nat.div_lt_iff_lt_mul hd).mpr (by rwa [Nat.mul_comm] at h1),
      (Nat.le_div_iff_mul_le hd).mpr (by rwa [Nat.mul_comm] at h2)⟩, rfl⟩
  · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, dvd_mul_right d m⟩
    · have := (Nat.div_lt_iff_lt_mul hd).mp h1
      rwa [Nat.mul_comm] at this
    · have := (Nat.le_div_iff_mul_le hd).mp h2
      rwa [Nat.mul_comm] at this

theorem sum_filter_dvd {M : Type*} [AddCommMonoid M] (d : ℕ) (hd : 0 < d) (X Y : ℕ)
    (f : ℕ → M) :
    ∑ n ∈ (Ioc X Y).filter (fun n => d ∣ n), f n = ∑ m ∈ Ioc (X / d) (Y / d), f (d * m) := by
  rw [filter_dvd_Ioc d hd, Finset.sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd h]

/-- A geometric sum over the multiples of `d` in an interval, at a `p`-th root of unity whose
`d`-th power is not `1`, is at most `p`. -/
theorem norm_sum_filter_dvd_pow_le {ω : ℂ} (hω : ‖ω‖ = 1) {p d : ℕ} (hp : 1 ≤ p) (hd : 0 < d)
    (hpow : ω ^ p = 1) (hne : ω ^ d ≠ 1) (X Y : ℕ) :
    ‖∑ n ∈ (Ioc X Y).filter (fun n => d ∣ n), ω ^ n‖ ≤ p := by
  have h1 : ‖ω ^ d‖ = 1 := by rw [norm_pow, hω, one_pow]
  have hpow' : (ω ^ d) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]
  rw [sum_filter_dvd d hd, ← Ico_succ_succ']
  calc ‖∑ m ∈ Ico (X / d + 1) (Y / d + 1), ω ^ (d * m)‖
      = ‖∑ m ∈ Ico (X / d + 1) (Y / d + 1), (ω ^ d) ^ m‖ := by simp only [pow_mul]
    _ ≤ 2 / ‖ω ^ d - 1‖ := norm_geom_sum_Ico_le h1.le hne _ _
    _ ≤ p := two_div_norm_sub_one_le h1 hp hpow' hne

/-- The same sum is at most the number of multiples of `d` in the interval. -/
theorem norm_sum_filter_dvd_pow_le_card {ω : ℂ} (hω : ‖ω‖ = 1) {d : ℕ} (hd : 0 < d) {X Y : ℕ}
    (hXY : X ≤ Y) :
    ‖∑ n ∈ (Ioc X Y).filter (fun n => d ∣ n), ω ^ n‖ ≤ ((Y : ℝ) - X) / d + 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcard : (((Ioc X Y).filter (fun n => d ∣ n)).card : ℝ) ≤ ((Y : ℝ) - X) / d + 1 := by
    rw [filter_dvd_Ioc d hd,
      Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hd h),
      Nat.card_Ioc, Nat.cast_sub (Nat.div_le_div_right hXY)]
    have h1 : ((Y / d : ℕ) : ℝ) ≤ (Y : ℝ) / d := Nat.cast_div_le
    have h2 : (X : ℝ) / d - 1 ≤ ((X / d : ℕ) : ℝ) := by
      have h := Nat.lt_mul_div_succ X hd
      have h' : (X : ℝ) < (d : ℝ) * (((X / d : ℕ) : ℝ) + 1) := by exact_mod_cast h
      rw [sub_le_iff_le_add, div_le_iff₀ hdR]
      linarith
    have e : ((Y : ℝ) - X) / d = (Y : ℝ) / d - (X : ℝ) / d := by ring
    linarith
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ (Ioc X Y).filter (fun n => d ∣ n), ‖ω ^ n‖
      = ∑ n ∈ (Ioc X Y).filter (fun n => d ∣ n), (1 : ℝ) :=
        Finset.sum_congr rfl fun n _ => by rw [norm_pow, hω, one_pow]
    _ = (((Ioc X Y).filter (fun n => d ∣ n)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((Y : ℝ) - X) / d + 1 := hcard

/-! ## Divisor sums prime to `p` -/

/-- The divisor sum of `u` over the divisors prime to `p`. -/
def coprimePart (u : ℕ → ℝ) (p n : ℕ) : ℝ := ∑ d ∈ n.divisors.filter (fun d => ¬ p ∣ d), u d

theorem coprimePart_of_not_dvd (u : ℕ → ℝ) {p n : ℕ} (h : ¬ p ∣ n) :
    coprimePart u p n = ∑ d ∈ n.divisors, u d := by
  have hall : ∀ d ∈ n.divisors, ¬ p ∣ d :=
    fun d hd hpd => h (hpd.trans (Nat.dvd_of_mem_divisors hd))
  unfold coprimePart
  rw [Finset.filter_true_of_mem hall]

theorem coprimePart_mul (u : ℕ → ℝ) {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    coprimePart u p (p * m) = coprimePart u p m := by
  unfold coprimePart
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hpd⟩
    have hcop : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm
    exact ⟨⟨hcop.dvd_of_dvd_mul_left hd, hm⟩, hpd⟩
  · rintro ⟨⟨hd, -⟩, hpd⟩
    exact ⟨⟨hd.mul_left p, mul_ne_zero hp.ne_zero hm⟩, hpd⟩

/-- If `a = 1 * u` is nonnegative and vanishes on the multiples of `p`, the divisor sum prime to
`p` is nonnegative and dominates `a`: it is `a` at the part of `n` prime to `p`. -/
theorem coprimePart_ge {a u : ℕ → ℝ} (hau : ∀ n, 1 ≤ n → a n = ∑ d ∈ n.divisors, u d)
    (ha : ∀ n, 0 ≤ a n) {p : ℕ} (hp : p.Prime) (hdel : ∀ n, 1 ≤ n → p ∣ n → a n = 0) :
    ∀ n, 1 ≤ n → 0 ≤ coprimePart u p n ∧ a n ≤ coprimePart u p n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm : m ≠ 0 := by
        rintro rfl
        simp at hn
      have hlt : m < p * m := by
        have := hp.two_le
        nlinarith [Nat.pos_of_ne_zero hm]
      rw [coprimePart_mul u hp hm, hdel _ hn (dvd_mul_right p m)]
      have h := (ih m hlt (Nat.pos_of_ne_zero hm)).1
      exact ⟨h, h⟩
    · rw [coprimePart_of_not_dvd u hpn, ← hau n hn]
      exact ⟨ha n, le_rfl⟩

/-- The divisors of `p n` divisible by `p` are `p` times the divisors of `n`. -/
theorem filter_dvd_divisors_mul {p n : ℕ} (hp : 0 < p) (hn : n ≠ 0) :
    (p * n).divisors.filter (fun d => p ∣ d) = n.divisors.image (fun d => p * d) := by
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, k, rfl⟩
    exact ⟨k, ⟨(Nat.mul_dvd_mul_iff_left hp).mp hd, hn⟩, rfl⟩
  · rintro ⟨k, ⟨hk, -⟩, rfl⟩
    exact ⟨⟨Nat.mul_dvd_mul_left p hk, mul_ne_zero hp.ne' hn⟩, dvd_mul_right p k⟩

/-- On a multiple `p n` the divisors divisible by `p` carry `Σ_{d ∣ n} u(p d)`. -/
theorem sum_divisors_sub_coprimePart (u : ℕ → ℝ) {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ (p * n).divisors, u d) - coprimePart u p (p * n) = ∑ d ∈ n.divisors, u (p * d) := by
  unfold coprimePart
  rw [← Finset.sum_filter_add_sum_filter_not (p * n).divisors (fun d => p ∣ d),
    add_sub_cancel_right, filter_dvd_divisors_mul hp.pos hn,
    Finset.sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h]

/-! ## Seen primes -/

/-- A prime is *seen* by `a = 1 * u` if on every multiple `p n` the divisors divisible by `p`
carry at least the mass `a(n)`, with one sign for all `n`. -/
def IsSeen (a u : ℕ → ℝ) (p : ℕ) : Prop :=
  (∀ n, 1 ≤ n → a (p * n) - coprimePart u p (p * n) ≤ -a n) ∨
    ∀ n, 1 ≤ n → a n ≤ a (p * n) - coprimePart u p (p * n)

/-- A deleted prime is seen, with the sign `−`. -/
theorem isSeen_of_deleted {a u : ℕ → ℝ} (hau : ∀ n, 1 ≤ n → a n = ∑ d ∈ n.divisors, u d)
    (ha : ∀ n, 0 ≤ a n) {p : ℕ} (hp : p.Prime) (hdel : ∀ n, 1 ≤ n → p ∣ n → a n = 0) :
    IsSeen a u p := by
  refine Or.inl fun n hn => ?_
  rw [hdel (p * n) (Nat.mul_pos hp.pos hn) (dvd_mul_right p n),
    coprimePart_mul u hp (by omega), zero_sub]
  exact neg_le_neg (coprimePart_ge hau ha hp hdel n hn).2

/-- A prime with `u(p d) = u(d)` for all `d` is seen, with the sign `+`. -/
theorem isSeen_of_mul_invariant {a u : ℕ → ℝ} (hau : ∀ n, 1 ≤ n → a n = ∑ d ∈ n.divisors, u d)
    {p : ℕ} (hp : p.Prime) (hinv : ∀ d, 1 ≤ d → u (p * d) = u d) : IsSeen a u p := by
  refine Or.inr fun n hn => ?_
  rw [hau (p * n) (Nat.mul_pos hp.pos hn), sum_divisors_sub_coprimePart u hp (by omega), hau n hn]
  exact (Finset.sum_congr rfl fun d hd => hinv d (Nat.pos_of_mem_divisors hd)).ge

/-- On an interval the sum of `a(n) ω^n` is the sum of the divisor sums prime to `p`, plus the
mass of the divisors divisible by `p` on the multiples of `p`. -/
theorem sum_mul_pow_eq {a u : ℕ → ℝ} (hau : ∀ n, 1 ≤ n → a n = ∑ d ∈ n.divisors, u d)
    {p : ℕ} {ω : ℂ} (hpow : ω ^ p = 1) (X Y : ℕ) :
    ∑ n ∈ Ioc X Y, (a n : ℂ) * ω ^ n =
      ∑ n ∈ Ioc X Y, (coprimePart u p n : ℂ) * ω ^ n +
        ((∑ n ∈ (Ioc X Y).filter (fun n => p ∣ n), (a n - coprimePart u p n) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := by
    have := (mem_Ioc.mp hn).1
    omega
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    obtain ⟨k, rfl⟩ := hpn
    rw [pow_mul, hpow, one_pow]
    push_cast
    ring
  · rw [if_neg hpn, coprimePart_of_not_dvd u hpn, ← hau n hn1]
    simp

/-- The sum of the divisor sums prime to `p` against `ω^n`, ordered by the divisor. -/
theorem sum_coprimePart_mul_pow (u : ℕ → ℝ) (p : ℕ) (ω : ℂ) (X Y : ℕ) :
    ∑ n ∈ Ioc X Y, (coprimePart u p n : ℂ) * ω ^ n =
      ∑ d ∈ (Ioc 0 Y).filter (fun d => ¬ p ∣ d),
        (u d : ℂ) * ∑ n ∈ (Ioc X Y).filter (fun n => d ∣ n), ω ^ n := by
  have h1 : ∀ n ∈ Ioc X Y, (coprimePart u p n : ℂ) * ω ^ n =
      ∑ d ∈ (Ioc 0 Y).filter (fun d => ¬ p ∣ d), if d ∣ n then (u d : ℂ) * ω ^ n else 0 := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hn
    have hset : n.divisors.filter (fun d => ¬ p ∣ d) =
        ((Ioc 0 Y).filter (fun d => ¬ p ∣ d)).filter (fun d => d ∣ n) := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, mem_Ioc]
      constructor
      · rintro ⟨⟨hd, -⟩, hpd⟩
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),
          (Nat.le_of_dvd (by omega) hd).trans hn2⟩, hpd⟩, hd⟩
      · rintro ⟨⟨-, hpd⟩, hd⟩
        exact ⟨⟨hd, by omega⟩, hpd⟩
    unfold coprimePart
    rw [hset, Finset.sum_filter, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]

/-- The classes prime to `p` are equidistributed up to the weighted mass of `u`: the multiples
of each `d` give a geometric sum, at most `p` and at most their number. -/
theorem norm_sum_coprimePart_mul_pow_le (u : ℕ → ℝ) {p : ℕ} (hp : 1 ≤ p) {ω : ℂ}
    (hω : ‖ω‖ = 1) (hpow : ω ^ p = 1) (hne : ∀ d, ¬ p ∣ d → ω ^ d ≠ 1) {X Y : ℕ}
    (hXY : X ≤ Y) :
    ‖∑ n ∈ Ioc X Y, (coprimePart u p n : ℂ) * ω ^ n‖ ≤
      ∑ d ∈ Ioc 0 Y, |u d| * min (p : ℝ) (((Y : ℝ) - X) / d + 1) := by
  have hYX : (0 : ℝ) ≤ (Y : ℝ) - X := sub_nonneg.mpr (by exact_mod_cast hXY)
  rw [sum_coprimePart_mul_pow]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun d hd => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d _ _ =>
      mul_nonneg (abs_nonneg _) (le_min (Nat.cast_nonneg p)
        (add_nonneg (div_nonneg hYX (Nat.cast_nonneg d)) zero_le_one)))
  obtain ⟨hd1, hd2⟩ := mem_filter.mp hd
  have hd0 : 0 < d := (mem_Ioc.mp hd1).1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (le_min
    (norm_sum_filter_dvd_pow_le hω hp hd0 hpow (hne d hd2) X Y)
    (norm_sum_filter_dvd_pow_le_card hω hd0 hXY)) (abs_nonneg _)

/-! ## Rankin's bound for the weighted mass -/

theorem two_mul_rpow_le {x e : ℝ} (hx : 0 ≤ x) (he : e ≤ 1) : (2 * x) ^ e ≤ 2 * x ^ e := by
  rw [Real.mul_rpow (by norm_num) hx]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hx _)
  calc (2 : ℝ) ^ e ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = 2 := Real.rpow_one 2

theorem min_le_rpow_mul_rpow {a b θ : ℝ} (ha : 0 < a) (hb : 0 < b) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) : min a b ≤ a ^ (1 - θ) * b ^ θ := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    calc a = a ^ (1 - θ) * a ^ θ := by rw [← Real.rpow_add ha, sub_add_cancel, Real.rpow_one]
      _ ≤ a ^ (1 - θ) * b ^ θ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le h hθ0) (Real.rpow_nonneg ha.le _)
  · rw [min_eq_right h]
    calc b = b ^ (1 - θ) * b ^ θ := by rw [← Real.rpow_add hb, sub_add_cancel, Real.rpow_one]
      _ ≤ a ^ (1 - θ) * b ^ θ :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hb.le h (by linarith))
            (Real.rpow_nonneg hb.le _)

/-- **Rankin's bound.**  `Σ_{d ≤ 2X} |u(d)| min(p, X/d + 1) ≤ 3 Z X^θ p^{1−θ}` if
`Σ_{d ≤ 2X} |u(d)| d^{−θ} ≤ Z`: `min(p, X/d) ≤ p^{1−θ} (X/d)^θ` and `1 ≤ (2X/d)^θ`. -/
theorem sum_abs_mul_min_le {u : ℕ → ℝ} {θ Z : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {X p : ℕ}
    (hX : 1 ≤ X) (hp : 1 ≤ p)
    (hZ : ∑ d ∈ Ioc 0 (2 * X), |u d| * (d : ℝ) ^ (-θ) ≤ Z) :
    ∑ d ∈ Ioc 0 (2 * X), |u d| * min (p : ℝ) ((((2 * X : ℕ) : ℝ) - X) / d + 1) ≤
      3 * Z * (X : ℝ) ^ θ * (p : ℝ) ^ (1 - θ) := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hpθ : 1 ≤ (p : ℝ) ^ (1 - θ) := Real.one_le_rpow hpR (by linarith)
  have hXθ : 0 ≤ (X : ℝ) ^ θ := Real.rpow_nonneg hXR.le _
  have hcast : ((2 * X : ℕ) : ℝ) - X = X := by push_cast; ring
  have hterm : ∀ d ∈ Ioc 0 (2 * X),
      |u d| * min (p : ℝ) ((((2 * X : ℕ) : ℝ) - X) / d + 1) ≤
        (|u d| * (d : ℝ) ^ (-θ)) * (3 * (X : ℝ) ^ θ * (p : ℝ) ^ (1 - θ)) := by
    intro d hd
    obtain ⟨hd0, hd2⟩ := mem_Ioc.mp hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hd2R : (d : ℝ) ≤ 2 * X := by exact_mod_cast hd2
    have hxd : (0 : ℝ) < (X : ℝ) / d := div_pos hXR hdR
    have h1 : min (p : ℝ) ((X : ℝ) / d + 1) ≤ min (p : ℝ) ((X : ℝ) / d) + 1 := by
      rcases le_total (p : ℝ) ((X : ℝ) / d) with h | h
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans (by linarith)
      · rw [min_eq_right h]
        exact min_le_right _ _
    have h2 := min_le_rpow_mul_rpow hp0 hxd hθ0 hθ1
    have h3 : ((X : ℝ) / d) ^ θ = (X : ℝ) ^ θ * (d : ℝ) ^ (-θ) := by
      rw [Real.div_rpow hXR.le hdR.le, Real.rpow_neg hdR.le, div_eq_mul_inv]
    have hw : 0 ≤ (X : ℝ) ^ θ * (d : ℝ) ^ (-θ) := mul_nonneg hXθ (Real.rpow_nonneg hdR.le _)
    have h4 : (1 : ℝ) ≤ 2 * ((X : ℝ) ^ θ * (d : ℝ) ^ (-θ)) := by
      have h5 : (1 : ℝ) ≤ (2 * (X : ℝ) / d) ^ θ :=
        Real.one_le_rpow ((one_le_div hdR).mpr hd2R) hθ0
      have h6 : (2 * (X : ℝ) / d) ^ θ ≤ 2 * ((X : ℝ) / d) ^ θ := by
        rw [mul_div_assoc]
        exact two_mul_rpow_le hxd.le hθ1
      rw [← h3]
      linarith
    have h7 : min (p : ℝ) ((X : ℝ) / d + 1) ≤
        3 * (X : ℝ) ^ θ * (p : ℝ) ^ (1 - θ) * (d : ℝ) ^ (-θ) := by
      rw [h3] at h2
      nlinarith [mul_le_mul_of_nonneg_right hpθ hw]
    rw [hcast]
    calc |u d| * min (p : ℝ) ((X : ℝ) / d + 1)
        ≤ |u d| * (3 * (X : ℝ) ^ θ * (p : ℝ) ^ (1 - θ) * (d : ℝ) ^ (-θ)) :=
          mul_le_mul_of_nonneg_left h7 (abs_nonneg _)
      _ = (|u d| * (d : ℝ) ^ (-θ)) * (3 * (X : ℝ) ^ θ * (p : ℝ) ^ (1 - θ)) := by ring
  calc ∑ d ∈ Ioc 0 (2 * X), |u d| * min (p : ℝ) ((((2 * X : ℕ) : ℝ) - X) / d + 1)
      ≤ ∑ d ∈ Ioc 0 (2 * X),
          (|u d| * (d : ℝ) ^ (-θ)) * (3 * (X : ℝ) ^ θ * (p : ℝ) ^ (1 - θ)) :=
        Finset.sum_le_sum hterm
    _ = (∑ d ∈ Ioc 0 (2 * X), |u d| * (d : ℝ) ^ (-θ)) *
          (3 * (X : ℝ) ^ θ * (p : ℝ) ^ (1 - θ)) := by rw [Finset.sum_mul]
    _ ≤ Z * (3 * (X : ℝ) ^ θ * (p : ℝ) ^ (1 - θ)) :=
        mul_le_mul_of_nonneg_right hZ (by positivity)
    _ = 3 * Z * (X : ℝ) ^ θ * (p : ℝ) ^ (1 - θ) := by ring

/-! ## The count and its remainder -/

/-- The count of a sequence. -/
def cnt (a : ℕ → ℝ) (x : ℕ) : ℝ := ∑ n ∈ Ioc 0 x, a n

theorem cnt_sub_cnt (a : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) : cnt a n - cnt a (n - 1) = a n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold cnt
  rw [Nat.add_sub_cancel, Finset.sum_Ioc_succ_top (Nat.zero_le m)]
  ring

/-- The remainder of the count against `A x`. -/
def rem (a : ℕ → ℝ) (A : ℝ) (x : ℕ) : ℂ := ((cnt a x - A * x : ℝ) : ℂ)

theorem rem_sub_rem (a : ℕ → ℝ) (A : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    rem a A n - rem a A (n - 1) = (a n : ℂ) - (A : ℂ) := by
  unfold rem
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub]
  congr 1
  have hc := cnt_sub_cnt a hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
  rw [hcast]
  linarith

theorem norm_rem (a : ℕ → ℝ) (A : ℝ) (x : ℕ) : ‖rem a A x‖ = |cnt a x - A * x| := by
  unfold rem
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- At a seen prime the divisors divisible by `p` carry, on the multiples of `p` in `(X, 2X]`,
at least the count of the interval `(X/p, 2X/p]`. -/
theorem abs_sum_filter_sub_ge {a u : ℕ → ℝ} {A E : ℝ} {X : ℕ} (hA : 0 ≤ A)
    (hE : ∀ x, x ≤ 2 * X → |cnt a x - A * x| ≤ E)
    {p : ℕ} (hp : p.Prime) (hseen : IsSeen a u p) :
    A * (X / p - 1) - 2 * E ≤
      |∑ n ∈ (Ioc X (2 * X)).filter (fun n => p ∣ n), (a n - coprimePart u p n)| := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  rw [sum_filter_dvd p hp0]
  have hm1 : ∀ m ∈ Ioc (X / p) (2 * X / p), 1 ≤ m := fun m hm =>
    Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hm).1)
  have h1 : ∑ m ∈ Ioc (X / p) (2 * X / p), a m ≤
      |∑ m ∈ Ioc (X / p) (2 * X / p), (a (p * m) - coprimePart u p (p * m))| := by
    rcases hseen with h | h
    · have hle : ∑ m ∈ Ioc (X / p) (2 * X / p), (a (p * m) - coprimePart u p (p * m)) ≤
          -∑ m ∈ Ioc (X / p) (2 * X / p), a m := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum fun m hm => h m (hm1 m hm)
      have habs :=
        neg_le_abs (∑ m ∈ Ioc (X / p) (2 * X / p), (a (p * m) - coprimePart u p (p * m)))
      linarith
    · exact (Finset.sum_le_sum fun m hm => h m (hm1 m hm)).trans (le_abs_self _)
  have hle : X / p ≤ 2 * X / p := Nat.div_le_div_right (by omega)
  have h2 : ∑ m ∈ Ioc (X / p) (2 * X / p), a m = cnt a (2 * X / p) - cnt a (X / p) := by
    unfold cnt
    rw [← Finset.sum_Ioc_consecutive a (Nat.zero_le _) hle]
    ring
  have h3 := abs_le.mp (hE (2 * X / p) (Nat.div_le_self _ _))
  have h4 := abs_le.mp (hE (X / p) ((Nat.div_le_self _ _).trans (by omega)))
  have h5 : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / p := Nat.cast_div_le
  have h6 : 2 * (X : ℝ) / p - 1 ≤ ((2 * X / p : ℕ) : ℝ) := by
    have h := Nat.lt_mul_div_succ (2 * X) hp0
    have h' : ((2 * X : ℕ) : ℝ) < (p : ℝ) * (((2 * X / p : ℕ) : ℝ) + 1) := by exact_mod_cast h
    rw [sub_le_iff_le_add, div_le_iff₀ hpR]
    push_cast at h'
    linarith
  have h7 : (X : ℝ) / p - 1 ≤ ((2 * X / p : ℕ) : ℝ) - ((X / p : ℕ) : ℝ) := by
    have e : 2 * (X : ℝ) / p = (X : ℝ) / p + (X : ℝ) / p := by ring
    linarith
  have h8 := mul_le_mul_of_nonneg_left h7 hA
  linarith [h3.1, h4.2]

/-! ## The peak at a seen prime -/

/-- **The peak.**  For a seen prime `p` and a primitive `p`-th root of unity `ω` close to `1`,
the sum of the remainder against `ω^n` over `(X, 2X]` is at least `A X / (8π)`. -/
theorem peak_le_norm {a u : ℕ → ℝ} {A E : ℝ} {X : ℕ}
    (hau : ∀ n, 1 ≤ n → a n = ∑ d ∈ n.divisors, u d) (hA : 0 ≤ A)
    (hE : ∀ x, x ≤ 2 * X → |cnt a x - A * x| ≤ E)
    {p : ℕ} (hp : p.Prime) (hseen : IsSeen a u p)
    (hcond : A + A * p + 4 * E +
      ∑ d ∈ Ioc 0 (2 * X), |u d| * min (p : ℝ) ((((2 * X : ℕ) : ℝ) - X) / d + 1) ≤
        3 / 4 * (A * X / p))
    {ω : ℂ} (hω : ‖ω‖ = 1) (hpow : ω ^ p = 1) (hne : ∀ d, ¬ p ∣ d → ω ^ d ≠ 1)
    (h1ω : ‖1 - ω‖ ≤ 2 * Real.pi / p) :
    A * X / (8 * Real.pi) ≤ ‖∑ n ∈ Ioc X (2 * X), rem a A n * ω ^ n‖ := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hne1 : ω ≠ 1 := by
    have h := hne 1 fun h => hp.one_lt.ne' (Nat.dvd_one.mp h)
    rwa [pow_one] at h
  -- summation by parts: `(1 − ω) Σ R(n) ω^n = Σ (a(n) − A) ω^n + boundary`
  have hparts := one_sub_mul_sum_pow (rem a A) ω X (show X ≤ 2 * X by omega)
  have hdiff : ∑ n ∈ Ioc X (2 * X), (rem a A n - rem a A (n - 1)) * ω ^ n =
      ∑ n ∈ Ioc X (2 * X), (a n : ℂ) * ω ^ n - (A : ℂ) * ∑ n ∈ Ioc X (2 * X), ω ^ n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [rem_sub_rem a A (by have := (mem_Ioc.mp hn).1; omega)]
    ring
  have hS := sum_mul_pow_eq (p := p) hau hpow X (2 * X)
  have hB := norm_sum_coprimePart_mul_pow_le u hp0 hω hpow hne (show X ≤ 2 * X by omega)
  have hM := abs_sum_filter_sub_ge hA hE hp hseen
  have hgeom : ‖∑ n ∈ Ioc X (2 * X), ω ^ n‖ ≤ p := by
    rw [← Ico_succ_succ']
    exact (norm_geom_sum_Ico_le hω.le hne1 _ _).trans (two_div_norm_sub_one_le hω hp0 hpow hne1)
  -- the mass on the multiples of `p`, expressed by the other terms
  have hid : ((∑ n ∈ (Ioc X (2 * X)).filter (fun n => p ∣ n),
      (a n - coprimePart u p n) : ℝ) : ℂ) =
      (1 - ω) * ∑ n ∈ Ioc X (2 * X), rem a A n * ω ^ n
        - ∑ n ∈ Ioc X (2 * X), (coprimePart u p n : ℂ) * ω ^ n
        + (A : ℂ) * ∑ n ∈ Ioc X (2 * X), ω ^ n - rem a A X * ω ^ (X + 1)
        + rem a A (2 * X) * ω ^ (2 * X + 1) := by
    rw [hparts, hdiff, hS]
    ring
  have hnorm : |∑ n ∈ (Ioc X (2 * X)).filter (fun n => p ∣ n), (a n - coprimePart u p n)| ≤
      2 * Real.pi / p * ‖∑ n ∈ Ioc X (2 * X), rem a A n * ω ^ n‖ +
        ∑ d ∈ Ioc 0 (2 * X), |u d| * min (p : ℝ) ((((2 * X : ℕ) : ℝ) - X) / d + 1) +
        A * p + E + E := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hid]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_))
      ?_)) ?_)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right h1ω (norm_nonneg _)
    · exact hB
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
      exact mul_le_mul_of_nonneg_left hgeom hA
    · rw [norm_mul, norm_pow, hω, one_pow, mul_one, norm_rem]
      exact hE X (by omega)
    · rw [norm_mul, norm_pow, hω, one_pow, mul_one, norm_rem]
      exact hE (2 * X) le_rfl
  generalize ‖∑ n ∈ Ioc X (2 * X), rem a A n * ω ^ n‖ = g at hnorm ⊢
  have hkey : A * X / p / 4 ≤ 2 * Real.pi / p * g := by
    have e : A * ((X : ℝ) / p - 1) = A * X / p - A := by ring
    linarith
  have h2 : 2 * Real.pi / p * g * p = 2 * Real.pi * g := by field_simp
  have h3 : A * X / p / 4 * p = A * X / 4 := by field_simp
  have h4 := mul_le_mul_of_nonneg_right hkey hpR.le
  rw [h2, h3] at h4
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * Real.pi)]
  linarith

/-! ## The large sieve over the seen primes -/

/-- **Large sieve over the seen primes.** -/
theorem card_mul_sq_le {a u : ℕ → ℝ} {A E : ℝ} {X Q : ℕ} {D : Finset ℕ}
    (hau : ∀ n, 1 ≤ n → a n = ∑ d ∈ n.divisors, u d) (hA : 0 ≤ A)
    (hE : ∀ x, x ≤ 2 * X → |cnt a x - A * x| ≤ E) (hQ : 2 ≤ Q)
    (hD : ∀ p ∈ D, p.Prime ∧ p ≤ Q ∧ IsSeen a u p ∧
      A + A * p + 4 * E +
        ∑ d ∈ Ioc 0 (2 * X), |u d| * min (p : ℝ) ((((2 * X : ℕ) : ℝ) - X) / d + 1) ≤
          3 / 4 * (A * X / p)) :
    (D.card : ℝ) * (A * X / (8 * Real.pi)) ^ 2 ≤
      ((X : ℝ) + (Q : ℝ) ^ 2 - 1) * (X * E ^ 2) := by
  classical
  have hset : Icc (X + 1) (X + X) = Ioc X (2 * X) := by
    ext m
    simp only [mem_Icc, mem_Ioc]
    omega
  have hls := largeSieve_fareySet_sharp X X hQ (rem a A)
  rw [hset] at hls
  have h0 : 0 ≤ A * X / (8 * Real.pi) :=
    div_nonneg (mul_nonneg hA (Nat.cast_nonneg X)) (by positivity)
  have hright : ∑ n ∈ Ioc X (2 * X), ‖rem a A n‖ ^ 2 ≤ X * E ^ 2 := by
    calc ∑ n ∈ Ioc X (2 * X), ‖rem a A n‖ ^ 2 ≤ ∑ n ∈ Ioc X (2 * X), E ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [norm_rem]
          exact pow_le_pow_left₀ (abs_nonneg _) (hE n (mem_Ioc.mp hn).2) 2
      _ = X * E ^ 2 := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * X - X = X by omega]
  have hleft : (D.card : ℝ) * (A * X / (8 * Real.pi)) ^ 2 ≤
      ∑ q ∈ fareySet Q, ‖∑ n ∈ Ioc X (2 * X),
        rem a A n * circleFreq ((n : ℝ) * ((q.1 : ℝ) / (q.2 : ℝ)))‖ ^ 2 := by
    have hsub : D.image (fun p => ((1 : ℕ), p)) ⊆ fareySet Q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      obtain ⟨hpp, hpQ, -, -⟩ := hD p hp
      exact mem_fareySet.mpr ⟨⟨le_rfl, by omega⟩, ⟨hpp.one_lt.le, hpQ⟩, hpp.one_lt.le,
        Nat.coprime_one_left p⟩
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity)
    rw [Finset.sum_image fun p _ p' _ h => (Prod.mk.inj h).2, ← nsmul_eq_mul,
      ← Finset.sum_const]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hpp, -, hseen, hcond⟩ := hD p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have h1ω : ‖1 - circleFreq (1 / (p : ℝ))‖ ≤ 2 * Real.pi / p := by
      have h := norm_one_sub_circleFreq_le (1 / (p : ℝ))
      rwa [abs_of_pos (one_div_pos.mpr hpR), mul_one_div] at h
    have hpeak := peak_le_norm hau hA hE hpp hseen hcond (norm_circleFreq _)
      (circleFreq_inv_pow_self hpp.pos) (fun d hd => circleFreq_inv_pow_ne_one hpp.pos hd) h1ω
    calc (A * X / (8 * Real.pi)) ^ 2
        ≤ ‖∑ n ∈ Ioc X (2 * X), rem a A n * circleFreq (1 / (p : ℝ)) ^ n‖ ^ 2 :=
          pow_le_pow_left₀ h0 hpeak 2
      _ = _ := by
          congr 2
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [circleFreq_pow]
          simp only [Nat.cast_one]
  calc (D.card : ℝ) * (A * X / (8 * Real.pi)) ^ 2
      ≤ ∑ q ∈ fareySet Q, ‖∑ n ∈ Ioc X (2 * X),
          rem a A n * circleFreq ((n : ℝ) * ((q.1 : ℝ) / (q.2 : ℝ)))‖ ^ 2 := hleft
    _ ≤ ((X : ℝ) + (Q : ℝ) ^ 2 - 1) * ∑ n ∈ Ioc X (2 * X), ‖rem a A n‖ ^ 2 := hls
    _ ≤ ((X : ℝ) + (Q : ℝ) ^ 2 - 1) * (X * E ^ 2) := by
        refine mul_le_mul_of_nonneg_left hright ?_
        have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
        nlinarith [Nat.cast_nonneg (α := ℝ) X]

/-- **The count sees the edited primes.**  If `16 Q² ≤ X`, `64 Q E ≤ A X` and
`48 Z Q^{2−θ} X^θ ≤ A X`, where `E` bounds the remainder up to `2X` and `Z` bounds
`Σ_{d ≤ 2X} |u(d)| d^{−θ}`, then at most `128 π² (E/A)²` primes up to `Q` are seen. -/
theorem card_le_of_scale {a u : ℕ → ℝ} {A E Z θ : ℝ} {X Q : ℕ} {D : Finset ℕ}
    (hau : ∀ n, 1 ≤ n → a n = ∑ d ∈ n.divisors, u d) (hA : 0 < A) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hE : ∀ x, x ≤ 2 * X → |cnt a x - A * x| ≤ E)
    (hZ : ∑ d ∈ Ioc 0 (2 * X), |u d| * (d : ℝ) ^ (-θ) ≤ Z) (hQ : 2 ≤ Q)
    (hQX : 16 * Q ^ 2 ≤ X) (hQE : 64 * Q * E ≤ A * X)
    (hQZ : 48 * Z * (Q : ℝ) ^ (2 - θ) * (X : ℝ) ^ θ ≤ A * X)
    (hD : ∀ p ∈ D, p.Prime ∧ p ≤ Q ∧ IsSeen a u p) :
    (D.card : ℝ) * A ^ 2 ≤ 128 * Real.pi ^ 2 * E ^ 2 := by
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE 0 (Nat.zero_le _))
  have hZ0 : 0 ≤ Z := (Finset.sum_nonneg fun d _ =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)).trans hZ
  have hXQ : (16 : ℝ) * (Q : ℝ) ^ 2 ≤ X := by exact_mod_cast hQX
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hX0 : (0 : ℝ) < X := by nlinarith
  have hX1 : 1 ≤ X := by exact_mod_cast hX0
  have hXθ : 0 ≤ (X : ℝ) ^ θ := Real.rpow_nonneg hX0.le _
  have hD' : ∀ p ∈ D, p.Prime ∧ p ≤ Q ∧ IsSeen a u p ∧
      A + A * p + 4 * E +
        ∑ d ∈ Ioc 0 (2 * X), |u d| * min (p : ℝ) ((((2 * X : ℕ) : ℝ) - X) / d + 1) ≤
          3 / 4 * (A * X / p) := by
    intro p hp
    obtain ⟨hpp, hpQ, hseen⟩ := hD p hp
    refine ⟨hpp, hpQ, hseen, ?_⟩
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hpQR : (p : ℝ) ≤ Q := by exact_mod_cast hpQ
    have hp0 : (0 : ℝ) < p := by linarith
    have hpp2 : (p : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 := pow_le_pow_left₀ hp0.le hpQR 2
    have h1 : (p : ℝ) * A ≤ (p : ℝ) ^ 2 * A / 2 := by
      nlinarith [mul_nonneg (mul_nonneg hp0.le hA.le) (sub_nonneg.mpr hp2)]
    have h2 : (p : ℝ) ^ 2 * A ≤ (Q : ℝ) ^ 2 * A := mul_le_mul_of_nonneg_right hpp2 hA.le
    have h3 : (p : ℝ) * E ≤ (Q : ℝ) * E := mul_le_mul_of_nonneg_right hpQR hE0
    -- the weighted mass: `p W_p ≤ 3 Z X^θ p^{2−θ} ≤ A X / 16`
    have hW := sum_abs_mul_min_le hθ0 hθ1 hX1 hpp.one_lt.le hZ
    have hpow : (p : ℝ) * (p : ℝ) ^ (1 - θ) = (p : ℝ) ^ (2 - θ) := by
      rw [show (2 : ℝ) - θ = 1 + (1 - θ) by ring, Real.rpow_add hp0, Real.rpow_one]
    have hpQθ : (p : ℝ) ^ (2 - θ) ≤ (Q : ℝ) ^ (2 - θ) :=
      Real.rpow_le_rpow hp0.le hpQR (by linarith)
    have h4 : (p : ℝ) *
        ∑ d ∈ Ioc 0 (2 * X), |u d| * min (p : ℝ) ((((2 * X : ℕ) : ℝ) - X) / d + 1) ≤
          A * X / 16 := by
      calc (p : ℝ) *
            ∑ d ∈ Ioc 0 (2 * X), |u d| * min (p : ℝ) ((((2 * X : ℕ) : ℝ) - X) / d + 1)
          ≤ (p : ℝ) * (3 * Z * (X : ℝ) ^ θ * (p : ℝ) ^ (1 - θ)) :=
            mul_le_mul_of_nonneg_left hW hp0.le
        _ = 3 * Z * (X : ℝ) ^ θ * (p : ℝ) ^ (2 - θ) := by rw [← hpow]; ring
        _ ≤ 3 * Z * (X : ℝ) ^ θ * (Q : ℝ) ^ (2 - θ) :=
            mul_le_mul_of_nonneg_left hpQθ (mul_nonneg (mul_nonneg (by norm_num) hZ0) hXθ)
        _ ≤ A * X / 16 := by linarith
    have h5 : (16 : ℝ) * (Q : ℝ) ^ 2 * A ≤ X * A := mul_le_mul_of_nonneg_right hXQ hA.le
    have h6 : 0 ≤ A * X := mul_nonneg hA.le hX0.le
    rw [mul_div_assoc', le_div_iff₀ hp0]
    nlinarith
  have h := card_mul_sq_le hau hA.le hE hQ hD'
  have hπ : 0 < Real.pi := Real.pi_pos
  have h1 : (D.card : ℝ) * A ^ 2 * (X : ℝ) ^ 2 ≤
      64 * Real.pi ^ 2 * (((X : ℝ) + (Q : ℝ) ^ 2 - 1) * (X * E ^ 2)) := by
    have e : (D.card : ℝ) * (A * X / (8 * Real.pi)) ^ 2 =
        (D.card : ℝ) * A ^ 2 * (X : ℝ) ^ 2 / (64 * Real.pi ^ 2) := by ring
    rw [e, div_le_iff₀ (by positivity)] at h
    linarith
  have hE2 : 0 ≤ (X : ℝ) * E ^ 2 := by positivity
  have h2 : ((X : ℝ) + (Q : ℝ) ^ 2 - 1) * (X * E ^ 2) ≤ 2 * (X : ℝ) ^ 2 * E ^ 2 := by
    calc ((X : ℝ) + (Q : ℝ) ^ 2 - 1) * (X * E ^ 2) ≤ (2 * X) * (X * E ^ 2) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hE2
      _ = 2 * (X : ℝ) ^ 2 * E ^ 2 := by ring
  have h3 : (D.card : ℝ) * A ^ 2 * (X : ℝ) ^ 2 ≤ 128 * Real.pi ^ 2 * E ^ 2 * (X : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 64 * Real.pi ^ 2)
    linarith
  exact le_of_mul_le_mul_right h3 (by positivity)

/-! ## The power form -/

/-- **The count sees the edited primes, power form.**  If the remainder is `O(x^β)` and
`Σ_d |u(d)| d^{−θ} ≤ Z`, `0 ≤ θ < 1`, then at most `c Q^{2β(2−θ)/(1−θ)}` primes up to `Q` are
seen. -/
theorem card_le_rpow {a u : ℕ → ℝ} {A C Z β θ : ℝ}
    (hau : ∀ n, 1 ≤ n → a n = ∑ d ∈ n.divisors, u d)
    (hA : 0 < A) (hC : 0 ≤ C) (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hβθ : β + (1 - θ) / (2 - θ) < 1)
    (hN : ∀ x : ℕ, 1 ≤ x → |cnt a x - A * x| ≤ C * (x : ℝ) ^ β)
    (hZ : ∀ y : ℕ, ∑ d ∈ Ioc 0 y, |u d| * (d : ℝ) ^ (-θ) ≤ Z) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Q : ℕ) (D : Finset ℕ), 2 ≤ Q →
      (∀ p ∈ D, p.Prime ∧ p ≤ Q ∧ IsSeen a u p) →
      (D.card : ℝ) ≤ c * (Q : ℝ) ^ (2 * β * (2 - θ) / (1 - θ)) := by
  have h1θ : 0 < 1 - θ := by linarith
  have h1θ' : 1 - θ ≠ 0 := h1θ.ne'
  have h2θ : 0 < 2 - θ := by linarith
  have hZ0 : 0 ≤ Z := (Finset.sum_nonneg fun d _ =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)).trans (hZ 1)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (2 - θ) / (1 - θ) := ⟨_, rfl⟩
  have hγ2 : 2 ≤ γ := by
    rw [hγ, le_div_iff₀ h1θ]
    linarith
  have hγ0 : 0 < γ := by linarith
  have hγinv : 1 / γ = (1 - θ) / (2 - θ) := by rw [hγ, one_div_div]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 - β - 1 / γ := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ, hγinv]; linarith
  have hβ1 : β ≤ 1 := by
    have : 0 ≤ (1 - θ) / (2 - θ) := div_nonneg h1θ.le h2θ.le
    linarith
  obtain ⟨M, hM16, hMK, hMC⟩ : ∃ M : ℝ, 16 ≤ M ∧ (48 * Z / A) ^ (1 / (1 - θ)) ≤ M ∧
      (128 * C / A) ^ (1 / δ) ≤ M :=
    ⟨max 16 (max ((48 * Z / A) ^ (1 / (1 - θ))) ((128 * C / A) ^ (1 / δ))), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  have hM0 : 0 < M := by linarith
  refine ⟨128 * Real.pi ^ 2 * (C / A) ^ 2 * (4 * M) ^ (2 * β),
    mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _), fun Q D hQ hD => ?_⟩
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQγ : (Q : ℝ) ^ 2 ≤ (Q : ℝ) ^ γ := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hγ2
  have hQγ1 : 1 ≤ (Q : ℝ) ^ γ := Real.one_le_rpow (by linarith) (by linarith)
  have hQγ0 : 0 ≤ (Q : ℝ) ^ γ := by linarith
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ, X = ⌈M * (Q : ℝ) ^ γ⌉₊ := ⟨_, rfl⟩
  have hXlo : M * (Q : ℝ) ^ γ ≤ X := by
    rw [hXdef]
    exact Nat.le_ceil _
  have hXhi : (X : ℝ) < M * (Q : ℝ) ^ γ + 1 := by
    rw [hXdef]
    exact Nat.ceil_lt_add_one (mul_nonneg hM0.le hQγ0)
  have hX16 : 16 * (Q : ℝ) ^ 2 ≤ X := (mul_le_mul hM16 hQγ (sq_nonneg _) hM0.le).trans hXlo
  have hXM : M ≤ X := (le_mul_of_one_le_right hM0.le hQγ1).trans hXlo
  have hXQγ : (Q : ℝ) ^ γ ≤ X := (le_mul_of_one_le_left hQγ0 (by linarith)).trans hXlo
  have hX0 : (0 : ℝ) < X := by linarith
  have hcast : ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) := by push_cast; ring
  -- the bounds at the scale `X`
  have hE : ∀ x, x ≤ 2 * X → |cnt a x - A * x| ≤ C * ((2 * X : ℕ) : ℝ) ^ β := by
    intro x hx
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · have h0 : cnt a 0 - A * ((0 : ℕ) : ℝ) = 0 := by simp [cnt]
      rw [h0, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · exact (hN x hx0).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg x) (by exact_mod_cast hx) hβ) hC)
  have hXθ0 : 0 ≤ (X : ℝ) ^ θ := Real.rpow_nonneg hX0.le _
  have hXβ0 : 0 ≤ (X : ℝ) ^ β := Real.rpow_nonneg hX0.le _
  -- `48 Z Q^{2−θ} X^θ ≤ A X`
  have hQZ : 48 * Z * (Q : ℝ) ^ (2 - θ) * (X : ℝ) ^ θ ≤ A * X := by
    have hXθ : 48 * Z / A * (Q : ℝ) ^ (2 - θ) ≤ (X : ℝ) ^ (1 - θ) := by
      have h1 : (M * (Q : ℝ) ^ γ) ^ (1 - θ) ≤ (X : ℝ) ^ (1 - θ) :=
        Real.rpow_le_rpow (mul_nonneg hM0.le hQγ0) hXlo h1θ.le
      have h2 : (M * (Q : ℝ) ^ γ) ^ (1 - θ) = M ^ (1 - θ) * (Q : ℝ) ^ (2 - θ) := by
        rw [Real.mul_rpow hM0.le hQγ0, ← Real.rpow_mul hQ0.le, hγ, div_mul_cancel₀ _ h1θ']
      have h3 : 48 * Z / A ≤ M ^ (1 - θ) := by
        have h := Real.rpow_le_rpow (by positivity) hMK h1θ.le
        rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel h1θ', Real.rpow_one] at h
      calc 48 * Z / A * (Q : ℝ) ^ (2 - θ) ≤ M ^ (1 - θ) * (Q : ℝ) ^ (2 - θ) :=
            mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hQ0.le _)
        _ = (M * (Q : ℝ) ^ γ) ^ (1 - θ) := h2.symm
        _ ≤ (X : ℝ) ^ (1 - θ) := h1
    have h1 : 48 * Z * (Q : ℝ) ^ (2 - θ) ≤ A * (X : ℝ) ^ (1 - θ) := by
      have h := mul_le_mul_of_nonneg_left hXθ hA.le
      rwa [show A * (48 * Z / A * (Q : ℝ) ^ (2 - θ)) = 48 * Z * (Q : ℝ) ^ (2 - θ) by
        field_simp] at h
    have hAX : A * X = A * (X : ℝ) ^ (1 - θ) * (X : ℝ) ^ θ := by
      rw [mul_assoc, ← Real.rpow_add hX0, sub_add_cancel, Real.rpow_one]
    rw [hAX]
    exact mul_le_mul_of_nonneg_right h1 hXθ0
  -- `64 Q E ≤ A X`
  have hQE : 64 * Q * (C * ((2 * X : ℕ) : ℝ) ^ β) ≤ A * X := by
    have hQW : (Q : ℝ) ≤ (X : ℝ) ^ (1 / γ) := by
      have h := Real.rpow_le_rpow hQγ0 hXQγ (one_div_pos.mpr hγ0).le
      rwa [← Real.rpow_mul hQ0.le, mul_one_div_cancel hγ0.ne', Real.rpow_one] at h
    have hXδ : 128 * C / A ≤ (X : ℝ) ^ δ := by
      have h := Real.rpow_le_rpow (by positivity) hMC hδ0.le
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hδ0.ne', Real.rpow_one] at h
      exact h.trans (Real.rpow_le_rpow hM0.le hXM hδ0.le)
    have hAX : A * X = A * ((X : ℝ) ^ (1 / γ) * (X : ℝ) ^ β * (X : ℝ) ^ δ) := by
      rw [← Real.rpow_add hX0, ← Real.rpow_add hX0,
        show 1 / γ + β + δ = 1 by rw [hδ]; ring, Real.rpow_one]
    have h2β : ((2 * X : ℕ) : ℝ) ^ β ≤ 2 * (X : ℝ) ^ β := by
      rw [hcast]
      exact two_mul_rpow_le hX0.le hβ1
    have hW0 : 0 ≤ (X : ℝ) ^ (1 / γ) := Real.rpow_nonneg hX0.le _
    have f1 : 64 * (Q : ℝ) * C * ((2 * X : ℕ) : ℝ) ^ β ≤ 64 * (Q : ℝ) * C * (2 * (X : ℝ) ^ β) :=
      mul_le_mul_of_nonneg_left h2β (by positivity)
    have f2 : (Q : ℝ) * (C * (X : ℝ) ^ β) ≤ (X : ℝ) ^ (1 / γ) * (C * (X : ℝ) ^ β) :=
      mul_le_mul_of_nonneg_right hQW (mul_nonneg hC hXβ0)
    have f3 : 128 * C ≤ A * (X : ℝ) ^ δ := (div_le_iff₀' hA).mp hXδ
    have f4 := mul_le_mul_of_nonneg_right f3 (mul_nonneg hW0 hXβ0)
    rw [hAX]
    linarith
  have hQX : 16 * Q ^ 2 ≤ X := by exact_mod_cast hX16
  have hmain := card_le_of_scale hau hA hθ hθ1.le hE (hZ (2 * X)) hQ hQX hQE hQZ hD
  -- back to the scale `Q`
  have h2X : ((2 * X : ℕ) : ℝ) ≤ 4 * M * (Q : ℝ) ^ γ := by
    rw [hcast]
    nlinarith [mul_le_mul_of_nonneg_left hQγ1 hM0.le]
  have hpow : (((2 * X : ℕ) : ℝ) ^ β) ^ 2 ≤
      (4 * M) ^ (2 * β) * (Q : ℝ) ^ (2 * β * (2 - θ) / (1 - θ)) := by
    have e1 : (((2 * X : ℕ) : ℝ) ^ β) ^ 2 = ((2 * X : ℕ) : ℝ) ^ (2 * β) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      push_cast
      ring
    have e2 : (4 * M * (Q : ℝ) ^ γ) ^ (2 * β) =
        (4 * M) ^ (2 * β) * (Q : ℝ) ^ (2 * β * (2 - θ) / (1 - θ)) := by
      rw [Real.mul_rpow (by linarith) hQγ0, ← Real.rpow_mul hQ0.le, hγ, div_mul_eq_mul_div]
      congr 2
      ring
    rw [e1, ← e2]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) h2X (by linarith)
  have hA2 : 0 < A ^ 2 := by positivity
  have h3 : (D.card : ℝ) ≤ 128 * Real.pi ^ 2 * (C / A) ^ 2 * (((2 * X : ℕ) : ℝ) ^ β) ^ 2 := by
    have e : 128 * Real.pi ^ 2 * (C / A) ^ 2 * (((2 * X : ℕ) : ℝ) ^ β) ^ 2 =
        128 * Real.pi ^ 2 * (C * ((2 * X : ℕ) : ℝ) ^ β) ^ 2 / A ^ 2 := by ring
    rw [e, le_div_iff₀ hA2]
    exact hmain
  calc (D.card : ℝ) ≤ 128 * Real.pi ^ 2 * (C / A) ^ 2 * (((2 * X : ℕ) : ℝ) ^ β) ^ 2 := h3
    _ ≤ 128 * Real.pi ^ 2 * (C / A) ^ 2 *
          ((4 * M) ^ (2 * β) * (Q : ℝ) ^ (2 * β * (2 - θ) / (1 - θ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 128 * Real.pi ^ 2 * (C / A) ^ 2 * (4 * M) ^ (2 * β) *
          (Q : ℝ) ^ (2 * β * (2 - θ) / (1 - θ)) := by ring

/-! ## Nonnegative twin coefficients: Chebyshev's identity -/

/-- The count of `a = 1 * u` is `Σ_{d ≤ x} u(d) ⌊x/d⌋`. -/
theorem cnt_eq_sum_mul_div {a u : ℕ → ℝ} (hau : ∀ n, 1 ≤ n → a n = ∑ d ∈ n.divisors, u d)
    (x : ℕ) : cnt a x = ∑ d ∈ Ioc 0 x, u d * ((x / d : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Ioc 0 x, a n = ∑ d ∈ Ioc 0 x, if d ∣ n then u d else 0 := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hn
    rw [hau n hn1, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn1, (Nat.le_of_dvd hn1 hd).trans hn2⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  unfold cnt
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul,
    mul_comm]

/-- **Chebyshev's identity.**  For nonnegative twin coefficients the mass of `u` on `(x/2, x]` is
at most `N(x) − 2 N(x/2)`: `⌊x/d⌋ − 2 ⌊x/(2d)⌋` is `0` or `1`, and it is `1` for `x/2 < d ≤ x`. -/
theorem sum_Ioc_half_le {a u : ℕ → ℝ} (hau : ∀ n, 1 ≤ n → a n = ∑ d ∈ n.divisors, u d)
    (hu : ∀ d, 0 ≤ u d) (x : ℕ) :
    ∑ d ∈ Ioc (x / 2) x, u d ≤ cnt a x - 2 * cnt a (x / 2) := by
  have hsub : Ioc 0 (x / 2) ⊆ Ioc 0 x := fun d hd =>
    mem_Ioc.mpr ⟨(mem_Ioc.mp hd).1, (mem_Ioc.mp hd).2.trans (Nat.div_le_self x 2)⟩
  have h2 : cnt a (x / 2) = ∑ d ∈ Ioc 0 x, u d * ((x / (2 * d) : ℕ) : ℝ) := by
    have e1 : ∑ d ∈ Ioc 0 (x / 2), u d * ((x / 2 / d : ℕ) : ℝ) =
        ∑ d ∈ Ioc 0 (x / 2), u d * ((x / (2 * d) : ℕ) : ℝ) :=
      Finset.sum_congr rfl fun d _ => by rw [Nat.div_div_eq_div_mul]
    rw [cnt_eq_sum_mul_div hau (x / 2), e1]
    refine Finset.sum_subset hsub fun d hd hd' => ?_
    have hlt : x < 2 * d := by
      have h1 := (mem_Ioc.mp hd).1
      have h3 : ¬ d ≤ x / 2 := fun h => hd' (mem_Ioc.mpr ⟨h1, h⟩)
      omega
    rw [Nat.div_eq_of_lt hlt, Nat.cast_zero, mul_zero]
  have hfilter : ∑ d ∈ Ioc (x / 2) x, u d = ∑ d ∈ Ioc 0 x, if x / 2 < d then u d else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [mem_Ioc, mem_filter]
    omega
  rw [hfilter, cnt_eq_sum_mul_div hau x, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun d hd => ?_
  obtain ⟨hd0, hdx⟩ := mem_Ioc.mp hd
  have hq : 2 * (x / (2 * d)) ≤ x / d := by
    rw [Nat.mul_comm 2 d, ← Nat.div_div_eq_div_mul]
    exact Nat.mul_div_le _ 2
  have hqR : 2 * ((x / (2 * d) : ℕ) : ℝ) ≤ ((x / d : ℕ) : ℝ) := by exact_mod_cast hq
  split_ifs with h
  · have h1 : x / d = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h0 : x / (2 * d) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h1, h0]
    simp
  · nlinarith [mul_nonneg (hu d) (sub_nonneg.mpr hqR)]

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.CountSieve
