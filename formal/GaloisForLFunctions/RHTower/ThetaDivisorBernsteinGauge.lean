import GaloisForLFunctions.RHTower.ThetaPrimePowerBernsteinGauge

/-!
# Divisor Bernstein cone and two-anchor rigidity of symmetric integer-scale theta gauges

For real `c` with `∑ |c_n| √n < ∞` let `g = c₁ k + ∑_{n ≥ 2} c_n (k(· + log n) + k(· - log n))`
(`thetaDivisorGauge c`), with `Q_b = ∑_{n ≥ 2, b ∣ n} c_n/√n` and
`R_a = c₁ + Q₁ + ∑_{n ≥ 2, n ∣ a} c_n √n`.

* **Bernstein cone.**  `b_g` is completely monotone iff `Q_b ≥ 0` for all `b ≥ 2` and `R_a ≥ 0`
  for all `a ≥ 1`; the rate weights are `2π(a/b)² Q_b` at reduced `π(a/b)²` and `2π a² R_a` at
  `π a²`.
* **Divisor Möbius weights.**  `β(d) = ∑_{e ∣ d} μ(d/e)(√e - 1)²` satisfies `β(1) = 0` and
  `β(d) = φ(d) - 2 J_{1/2}(d) > 0` for `d > 1`, with
  `φ(d)/J_{1/2}(d) = ∏_{p^e ∥ d} p^{(e-1)/2}(√p + 1)` and `J_{1/2}(d) = √d ∏_{p ∣ d}(1 - 1/√p)`.
* **Divisor-Abel identity.**  `M_{1/2} - M₀ = ∑_{d ≥ 2} β(d) Q_d`, and
  `∑_{k ≥ 1} μ(k) Q_{nk} = c_n/√n` for `n ≥ 2`.
* **Rigidity.**  Complete monotonicity forces `M_{1/2} ≥ M₀` with equality iff `c_n = 0` for
  `n ≥ 2`; with both anchors of `k` it forces `g = k`.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry
open ArithmeticFunction

namespace RHTower

/-! ## The divisor Möbius transform of the Abel weight -/

theorem real_sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  rw [show x ^ n = (Real.sqrt x ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx],
    Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg x) n)]


/-- The divisor Abel weight `F(n) = (√n - 1)²`. -/
noncomputable def divisorAbelWeight (n : ℕ) : ℝ := (Real.sqrt n - 1) ^ 2

/-- The divisor Möbius transform `β(d) = ∑_{e ∣ d} μ(d/e) F(e)`. -/
noncomputable def divisorMoebiusWeight (d : ℕ) : ℝ :=
  ∑ x ∈ d.divisorsAntidiagonal, (moebius x.1 : ℝ) * divisorAbelWeight x.2

/-- Möbius inversion: `F(n) = ∑_{d ∣ n} β(d)`. -/
theorem sum_divisors_divisorMoebiusWeight {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, divisorMoebiusWeight d = divisorAbelWeight n :=
  (sum_eq_iff_sum_mul_moebius_eq (f := divisorMoebiusWeight) (g := divisorAbelWeight)).mpr
    (fun _ _ => rfl) n hn

theorem divisorMoebiusWeight_one : divisorMoebiusWeight 1 = 0 := by
  simp [divisorMoebiusWeight, divisorAbelWeight]

/-- `n ↦ n` as a real arithmetic function. -/
noncomputable def realIdArith : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ), by simp⟩

/-- `n ↦ √n` as a real arithmetic function. -/
noncomputable def realSqrtArith : ArithmeticFunction ℝ := ⟨fun n => Real.sqrt n, by simp⟩

theorem realIdArith_apply (n : ℕ) : realIdArith n = n := rfl

theorem realSqrtArith_apply (n : ℕ) : realSqrtArith n = Real.sqrt n := rfl

theorem isMultiplicative_realIdArith : realIdArith.IsMultiplicative :=
  ⟨by simp [realIdArith_apply], fun {m n} _ => by simp [realIdArith_apply]⟩

theorem isMultiplicative_realSqrtArith : realSqrtArith.IsMultiplicative :=
  ⟨by simp [realSqrtArith_apply], fun {m n} _ => by
    simp [realSqrtArith_apply, Real.sqrt_mul (Nat.cast_nonneg _)]⟩

/-- The Möbius transform `μ * (n ↦ n)`; it equals Euler's totient. -/
noncomputable def divisorTotient : ArithmeticFunction ℝ := (moebius : ArithmeticFunction ℝ) * realIdArith

/-- The half Jordan function `J_{1/2} = μ * (n ↦ √n)`. -/
noncomputable def divisorJordanHalf : ArithmeticFunction ℝ :=
  (moebius : ArithmeticFunction ℝ) * realSqrtArith

theorem isMultiplicative_divisorTotient : divisorTotient.IsMultiplicative :=
  isMultiplicative_moebius.intCast.mul isMultiplicative_realIdArith

theorem isMultiplicative_divisorJordanHalf : divisorJordanHalf.IsMultiplicative :=
  isMultiplicative_moebius.intCast.mul isMultiplicative_realSqrtArith

/-- The Möbius transform of any arithmetic function at a prime power `p^k`, `k ≥ 1`. -/
theorem moebius_mul_apply_prime_pow (f : ArithmeticFunction ℝ) {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) :
    ((moebius : ArithmeticFunction ℝ) * f) (p ^ k) = f (p ^ k) - f (p ^ (k - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => ((moebius : ArithmeticFunction ℝ) a) * f b),
    Nat.divisors_prime_pow hp, Finset.sum_map, Finset.sum_range_succ', Finset.sum_range_succ']
  have hzero : ∀ i ∈ Finset.range j, ((moebius : ArithmeticFunction ℝ) (p ^ (i + 1 + 1))) *
      f (p ^ (j + 1) / p ^ (i + 1 + 1)) = 0 := by
    intro i _
    rw [intCoe_apply, moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_eq_zero hzero]
  have e1 : p ^ (j + 1) / p = p ^ j := by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  have e2 : moebius p = -1 := by simpa using moebius_apply_prime_pow hp one_ne_zero
  simp only [intCoe_apply, pow_zero, moebius_apply_one, zero_add, pow_one, Nat.div_one, e1, e2,
    add_tsub_cancel_right]
  push_cast
  ring

theorem divisorTotient_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    divisorTotient (p ^ k) = Real.sqrt p ^ (k - 1) * Real.sqrt p ^ (k - 1) *
      ((Real.sqrt p - 1) * (Real.sqrt p + 1)) := by
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  rw [divisorTotient, moebius_mul_apply_prime_pow _ hp hk, realIdArith_apply, realIdArith_apply]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  push_cast
  have h2 : Real.sqrt p ^ j * Real.sqrt p ^ j = (p : ℝ) ^ j := by
    rw [← mul_pow, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have h3 : (Real.sqrt p - 1) * (Real.sqrt p + 1) = (p : ℝ) - 1 := by
    linear_combination hs
  rw [h2, h3]
  ring

theorem divisorJordanHalf_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    divisorJordanHalf (p ^ k) = Real.sqrt p ^ (k - 1) * (Real.sqrt p - 1) := by
  rw [divisorJordanHalf, moebius_mul_apply_prime_pow _ hp hk, realSqrtArith_apply,
    realSqrtArith_apply]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  push_cast
  rw [real_sqrt_pow_eq (Nat.cast_nonneg _), real_sqrt_pow_eq (Nat.cast_nonneg _)]
  ring

/-- The prime-power ratio `φ(p^k)/J_{1/2}(p^k) = p^{(k-1)/2}(√p + 1)`. -/
theorem divisorTotient_apply_prime_pow_eq {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    divisorTotient (p ^ k) = divisorJordanHalf (p ^ k) *
      (Real.sqrt p ^ (k - 1) * (Real.sqrt p + 1)) := by
  rw [divisorTotient_apply_prime_pow hp hk, divisorJordanHalf_apply_prime_pow hp hk]
  ring

theorem one_lt_sqrt_prime {p : ℕ} (hp : p.Prime) : 1 < Real.sqrt p :=
  Real.lt_sqrt (by norm_num) |>.mpr (by rw [one_pow]; exact_mod_cast hp.one_lt)

theorem divisorJordanHalf_pos {n : ℕ} (hn : n ≠ 0) : 0 < divisorJordanHalf n := by
  rw [IsMultiplicative.multiplicative_factorization _ isMultiplicative_divisorJordanHalf hn,
    Finsupp.prod]
  refine Finset.prod_pos fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  rw [divisorJordanHalf_apply_prime_pow hpp hk]
  have := one_lt_sqrt_prime hpp
  exact mul_pos (pow_pos (by linarith) _) (by linarith)

/-- **Totient–Jordan ratio.**  `φ(d) = J_{1/2}(d) ∏_{p^e ∥ d} p^{(e-1)/2}(√p + 1)`. -/
theorem divisorTotient_eq_jordan_mul_prod {n : ℕ} (hn : n ≠ 0) :
    divisorTotient n = divisorJordanHalf n * ∏ p ∈ n.primeFactors,
      (Real.sqrt p ^ (n.factorization p - 1) * (Real.sqrt p + 1)) := by
  rw [IsMultiplicative.multiplicative_factorization _ isMultiplicative_divisorTotient hn,
    IsMultiplicative.multiplicative_factorization _ isMultiplicative_divisorJordanHalf hn,
    Finsupp.prod,
    Finsupp.prod, Nat.support_factorization, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  exact divisorTotient_apply_prime_pow_eq (Nat.prime_of_mem_primeFactors hp)
    (Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization]))

/-- The totient transform is Euler's totient. -/
theorem divisorTotient_eq_totient {n : ℕ} (hn : 0 < n) : divisorTotient n = Nat.totient n := by
  have h := (sum_eq_iff_sum_mul_moebius_eq (f := fun n => (Nat.totient n : ℝ))
    (g := fun n => (n : ℝ))).mp (fun m _ => by exact_mod_cast Nat.sum_totient m) n hn
  rw [← h, divisorTotient, mul_apply]
  rfl

/-- The half Jordan function is `J_{1/2}(d) = √d ∏_{p ∣ d} (1 - 1/√p)`. -/
theorem divisorJordanHalf_eq_prod {n : ℕ} (hn : n ≠ 0) :
    divisorJordanHalf n = Real.sqrt n * ∏ p ∈ n.primeFactors, (1 - 1 / Real.sqrt p) := by
  have hmul : (realSqrtArith.pmul (prodPrimeFactors fun p => 1 - 1 / Real.sqrt p)).IsMultiplicative :=
    isMultiplicative_realSqrtArith.pmul (IsMultiplicative.prodPrimeFactors _)
  have heq : divisorJordanHalf =
      realSqrtArith.pmul (prodPrimeFactors fun p => 1 - 1 / Real.sqrt p) := by
    refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ isMultiplicative_divisorJordanHalf _
      hmul).mpr fun p i hp => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, isMultiplicative_divisorJordanHalf.map_one]
      exact hmul.map_one.symm
    · rw [divisorJordanHalf_apply_prime_pow hp hi.ne', pmul_apply, realSqrtArith_apply,
        prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow hi.ne' hp,
        Finset.prod_singleton]
      push_cast
      rw [real_sqrt_pow_eq (Nat.cast_nonneg _)]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have := one_lt_sqrt_prime hp
      rw [add_tsub_cancel_right]
      field_simp
      ring
  rw [heq, pmul_apply, realSqrtArith_apply, prodPrimeFactors_apply hn]

/-- For `d > 1`, `β(d) = φ(d) - 2 J_{1/2}(d)`. -/
theorem divisorMoebiusWeight_eq {d : ℕ} (hd : 1 < d) :
    divisorMoebiusWeight d = divisorTotient d - 2 * divisorJordanHalf d := by
  have hz : ∑ x ∈ d.divisorsAntidiagonal, (moebius x.1 : ℝ) = 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f d)
      (coe_moebius_mul_coe_zeta (R := ℝ))
    simp only [mul_apply, one_apply_ne hd.ne'] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [intCoe_apply, natCoe_apply, zeta_apply_ne (Nat.pos_of_mem_divisors
      (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).ne', Nat.cast_one, mul_one]
  rw [divisorMoebiusWeight, divisorTotient, divisorJordanHalf, mul_apply, mul_apply,
    Finset.mul_sum, ← sub_zero (∑ x ∈ _, _ * divisorAbelWeight _), ← hz, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [intCoe_apply, realIdArith_apply, realSqrtArith_apply, divisorAbelWeight,
    sub_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

/-- **Positivity of the divisor Möbius weight.**  `β(d) > 0` for every `d > 1`. -/
theorem divisorMoebiusWeight_pos {d : ℕ} (hd : 1 < d) : 0 < divisorMoebiusWeight d := by
  have hd0 : d ≠ 0 := by omega
  rw [divisorMoebiusWeight_eq hd, divisorTotient_eq_jordan_mul_prod hd0]
  have hJ := divisorJordanHalf_pos hd0
  obtain ⟨p₀, hp₀⟩ := Nat.nonempty_primeFactors.mpr hd
  have hlam : ∀ p ∈ d.primeFactors, 1 ≤ Real.sqrt p ^ (d.factorization p - 1) * (Real.sqrt p + 1) := by
    intro p hp
    have := one_lt_sqrt_prime (Nat.prime_of_mem_primeFactors hp)
    nlinarith [(one_le_pow₀ this.le : (1 : ℝ) ≤ Real.sqrt p ^ (d.factorization p - 1))]
  have hlam₀ : 2 < Real.sqrt p₀ ^ (d.factorization p₀ - 1) * (Real.sqrt p₀ + 1) := by
    have := one_lt_sqrt_prime (Nat.prime_of_mem_primeFactors hp₀)
    nlinarith [(one_le_pow₀ this.le : (1 : ℝ) ≤ Real.sqrt p₀ ^ (d.factorization p₀ - 1))]
  have hprod : 2 < ∏ p ∈ d.primeFactors,
      (Real.sqrt p ^ (d.factorization p - 1) * (Real.sqrt p + 1)) := by
    classical
    rw [← Finset.mul_prod_erase _ _ hp₀]
    have h1 : 1 ≤ ∏ p ∈ d.primeFactors.erase p₀,
        (Real.sqrt p ^ (d.factorization p - 1) * (Real.sqrt p + 1)) :=
      Finset.one_le_prod fun p hp => hlam p (Finset.mem_of_mem_erase hp)
    nlinarith
  nlinarith

theorem divisorMoebiusWeight_nonneg (d : ℕ) : 0 ≤ divisorMoebiusWeight d := by
  rcases lt_or_ge 1 d with hd | hd
  · exact (divisorMoebiusWeight_pos hd).le
  · interval_cases d
    · simp [divisorMoebiusWeight]
    · rw [divisorMoebiusWeight_one]

theorem sum_divisorsAntidiagonal_moebius (t : ℕ) :
    ∑ x ∈ t.divisorsAntidiagonal, (moebius x.1 : ℝ) = if t = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f t) (coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [mul_apply, one_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [intCoe_apply, natCoe_apply, zeta_apply_ne (Nat.pos_of_mem_divisors
    (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).ne', Nat.cast_one, mul_one]

/-- Summability of a nonnegative family from summability of its fibre sums. -/
theorem summable_of_nonneg_of_fiberwise {α β : Type*} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a)
    (g : α → β) (hfib : ∀ b, Summable fun x : {x // g x = b} => f x)
    (hsum : Summable fun b => ∑' x : {x // g x = b}, f x) : Summable f := by
  rw [← (Equiv.sigmaFiberEquiv g).summable_iff]
  exact (summable_sigma_of_nonneg (fun x => hf _)).mpr ⟨hfib, hsum⟩

/-- Fibre data along `(d, k) ↦ d k` for a family vanishing on the axes. -/
theorem divisorFiber_tsum {f : ℕ × ℕ → ℝ} (h0 : ∀ q : ℕ × ℕ, (q.1 = 0 ∨ q.2 = 0) → f q = 0)
    (N : ℕ) :
    Summable (fun x : {x : ℕ × ℕ // x.1 * x.2 = N} => f x) ∧
      ∑' x : {x : ℕ × ℕ // x.1 * x.2 = N}, f x = ∑ q ∈ N.divisorsAntidiagonal, f q := by
  have hsupp : ∀ q ∉ N.divisorsAntidiagonal,
      ({x : ℕ × ℕ | x.1 * x.2 = N} : Set (ℕ × ℕ)).indicator f q = 0 := by
    intro q hq
    by_cases hqN : q.1 * q.2 = N
    · rw [Set.indicator_of_mem (by exact hqN)]
      apply h0
      by_contra hne
      push Not at hne
      exact hq (Nat.mem_divisorsAntidiagonal.mpr ⟨hqN, by
        rw [← hqN]; exact mul_ne_zero hne.1 hne.2⟩)
    · rw [Set.indicator_of_notMem (by exact hqN)]
  constructor
  · exact summable_subtype_iff_indicator.mpr (summable_of_ne_finset_zero hsupp)
  · show ∑' x : ({x : ℕ × ℕ | x.1 * x.2 = N} : Set (ℕ × ℕ)), f x = _
    rw [tsum_subtype ({x : ℕ × ℕ | x.1 * x.2 = N} : Set (ℕ × ℕ)) f, tsum_eq_sum hsupp]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Set.indicator_of_mem (by exact (Nat.mem_divisorsAntidiagonal.mp hq).1)]

/-! ## The symmetric integer-scale gauge -/

/-- Shift of the symmetric divisor gauge, `j ↦ sign(j) log(|j| + 1)`. -/
noncomputable def divisorShift (j : ℤ) : ℝ := (Int.sign j : ℝ) * Real.log (j.natAbs + 1)

/-- Coefficient of the symmetric divisor gauge, `j ↦ c_{|j|+1}`. -/
def divisorGaugeCoeff (c : ℕ → ℝ) (j : ℤ) : ℝ := c (j.natAbs + 1)

theorem divisorShift_zero : divisorShift 0 = 0 := by simp [divisorShift]

theorem divisorShift_succ (n : ℕ) : divisorShift ((n : ℤ) + 1) = Real.log (n + 2) := by
  unfold divisorShift
  rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
    Int.sign_natCast_of_ne_zero (by omega), Int.natAbs_natCast]
  push_cast
  ring_nf

theorem divisorShift_neg_succ (n : ℕ) : divisorShift (-((n : ℤ) + 1)) = -Real.log (n + 2) := by
  unfold divisorShift
  rw [Int.sign_neg, Int.natAbs_neg, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
    Int.sign_natCast_of_ne_zero (by omega), Int.natAbs_natCast]
  push_cast
  ring_nf

theorem divisorGaugeCoeff_succ (c : ℕ → ℝ) (n : ℕ) : divisorGaugeCoeff c ((n : ℤ) + 1) = c (n + 2) := by
  unfold divisorGaugeCoeff
  congr 1

theorem divisorGaugeCoeff_neg_succ (c : ℕ → ℝ) (n : ℕ) :
    divisorGaugeCoeff c (-((n : ℤ) + 1)) = c (n + 2) := by
  unfold divisorGaugeCoeff
  congr 1

theorem exp_half_log_nat_add_two (n : ℕ) : Real.exp (Real.log (n + 2) / 2) = Real.sqrt (n + 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
  ring_nf

theorem exp_abs_half_divisorShift (j : ℤ) :
    Real.exp (|divisorShift j| / 2) = Real.sqrt (j.natAbs + 1) := by
  unfold divisorShift
  rcases lt_trichotomy j 0 with hj | rfl | hj
  · rw [Int.sign_eq_neg_one_of_neg hj, abs_mul]
    push_cast
    rw [abs_neg, abs_one, one_mul, abs_of_nonneg (Real.log_nonneg (by
      have : (0 : ℝ) ≤ j.natAbs := Nat.cast_nonneg _
      linarith)), Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    ring_nf
  · simp
  · rw [Int.sign_eq_one_of_pos hj, abs_mul]
    push_cast
    rw [abs_one, one_mul, abs_of_nonneg (Real.log_nonneg (by
      have : (0 : ℝ) ≤ j.natAbs := Nat.cast_nonneg _
      linarith)), Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    ring_nf

theorem divisor_gauge_admissible {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n) :
    Summable fun j : ℤ => |divisorGaugeCoeff c j| * Real.exp (|divisorShift j| / 2) := by
  simp_rw [exp_abs_half_divisorShift]
  unfold divisorGaugeCoeff
  have h1 : Summable fun n : ℕ => |c (n + 1)| * Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    (summable_nat_add_iff 1).mpr hc
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine h1.congr fun n => ?_
    simp
  · refine ((summable_nat_add_iff 1).mpr h1).congr fun n => ?_
    rw [Int.natAbs_neg, show ((n : ℤ) + 1).natAbs = n + 1 by omega]
    push_cast
    ring_nf

/-- The symmetric integer-scale gauge `c₁ k + ∑_{n ≥ 2} c_n (k(· + log n) + k(· - log n))`. -/
noncomputable def thetaDivisorGauge (c : ℕ → ℝ) : ℝ → ℝ :=
  thetaTranslationGauge (divisorGaugeCoeff c) divisorShift

theorem thetaDivisorGauge_apply {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n)
    (x : ℝ) :
    thetaDivisorGauge c x = c 1 * thetaCuspFullSource x + ∑' n : ℕ, c (n + 2) *
      (thetaCuspFullSource (x + Real.log (n + 2)) + thetaCuspFullSource (x - Real.log (n + 2))) := by
  have hA := summable_thetaTranslationGauge (s := divisorShift)
    (summable_abs_of_gauge (divisor_gauge_admissible hc)) x
  unfold thetaDivisorGauge thetaTranslationGauge
  rw [tsum_int_eq_zero_add_pairs hA, divisorShift_zero, add_zero]
  congr 1
  refine tsum_congr fun n => ?_
  rw [divisorShift_succ, divisorShift_neg_succ, divisorGaugeCoeff_succ, divisorGaugeCoeff_neg_succ,
    ← sub_eq_add_neg]
  ring

/-! ## Rate coefficients of the divisor gauge -/

/-- The denominator tail `Q_b = ∑_{n ≥ 2, b ∣ n} c_n/√n`. -/
noncomputable def divisorTail (c : ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑' n : ℕ, if 2 ≤ n ∧ b ∣ n then c n / Real.sqrt n else 0

/-- The integer-rate weight `R_a = c₁ + Q₁ + ∑_{n ≥ 2, n ∣ a} c_n √n`. -/
noncomputable def divisorIntegerWeight (c : ℕ → ℝ) (a : ℕ) : ℝ :=
  c 1 + divisorTail c 1 + ∑ n ∈ a.divisors, if 2 ≤ n then c n * Real.sqrt n else 0

theorem tsum_nat_add_two_eq (h : ℕ → ℝ) :
    ∑' n : ℕ, h (n + 2) = ∑' n : ℕ, if 2 ≤ n then h n else 0 := by
  have hinj : Function.Injective fun n : ℕ => n + 2 := add_left_injective 2
  rw [← hinj.tsum_eq (f := fun n : ℕ => if 2 ≤ n then h n else 0)]
  · exact tsum_congr fun n => by simp
  · intro n hn
    have h2 : 2 ≤ n := by
      by_contra h'
      exact hn (by simp only; rw [if_neg h'])
    exact ⟨n - 2, by simp only; omega⟩

theorem tsum_shift_two {F G : ℕ → ℝ} (hFG : ∀ n, F n = G (n + 2)) (hG : ∀ n, n < 2 → G n = 0) :
    ∑' n, F n = ∑' n, G n := by
  have hinj : Function.Injective fun n : ℕ => n + 2 := add_left_injective 2
  rw [← hinj.tsum_eq (f := G)]
  · exact tsum_congr hFG
  · intro n hn
    have h2 : 2 ≤ n := by
      by_contra h'
      exact hn (hG n (by omega))
    exact ⟨n - 2, by simp only; omega⟩

theorem summable_divisor_half {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n) :
    Summable fun n : ℕ => |c (n + 2)| * Real.sqrt (n + 2) :=
  ((summable_nat_add_iff 2).mpr hc).congr fun n => by push_cast; ring_nf

theorem summable_divisor_inv_half {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n) :
    Summable fun n : ℕ => |c (n + 2)| / Real.sqrt (n + 2) := by
  refine (summable_divisor_half hc).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have h1 : (1 : ℝ) ≤ Real.sqrt (n + 2) :=
    Real.one_le_sqrt.mpr (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  have hs : Real.sqrt (n + 2) * Real.sqrt (n + 2) = n + 2 := Real.mul_self_sqrt (by positivity)
  rw [div_le_iff₀ (by linarith), mul_assoc, hs]
  nlinarith [abs_nonneg (c (n + 2))]

open Classical in
theorem divisorRateCoeff_eq {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n)
    (r : ℝ) :
    thetaGaugeRateCoeff (divisorGaugeCoeff c) divisorShift r =
      (if ∃ m : ℕ, (m : ℝ) = r then c 1 else 0) +
      ∑' n : ℕ, ((if ∃ m : ℕ, (m : ℝ) * (n + 2) = r then c (n + 2) * Real.sqrt (n + 2) else 0) +
        (if ∃ m : ℕ, (m : ℝ) / (n + 2) = r then c (n + 2) / Real.sqrt (n + 2) else 0)) := by
  have hadm := divisor_gauge_admissible hc
  have hsum : Summable fun j : ℤ => if ∃ m : ℕ, (m : ℝ) * Real.exp (divisorShift j) = r then
      divisorGaugeCoeff c j * Real.exp (divisorShift j / 2) else 0 := by
    refine Summable.of_norm_bounded hadm fun j => ?_
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        have := le_abs_self (divisorShift j); linarith)) (abs_nonneg _)
    · rw [norm_zero]; positivity
  unfold thetaGaugeRateCoeff
  rw [tsum_int_eq_zero_add_pairs hsum]
  have hpos : ∀ n : ℕ, (0 : ℝ) < n + 2 := fun n => by positivity
  simp only [divisorShift_zero, Real.exp_zero, mul_one, zero_div, divisorShift_succ,
    divisorShift_neg_succ, divisorGaugeCoeff_succ, divisorGaugeCoeff_neg_succ, Real.exp_log (hpos _),
    exp_half_log_nat_add_two, Real.exp_neg, neg_div]
  congr 1

theorem exists_nat_mul_eq_iff_dvd (n a : ℕ) :
    (∃ m : ℕ, (m : ℝ) * (n + 2) = a) ↔ (n + 2) ∣ a := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by exact_mod_cast (by rw [← hm]; push_cast; ring :
      ((a : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) * m)⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by push_cast; ring⟩

/-- For a reduced fraction `a/b`, `m/n = a/b` has a natural solution `m` iff `b ∣ n`. -/
theorem exists_nat_div_eq_iff_dvd {a b : ℕ} (hab : a.Coprime b) (hb : 0 < b) (n : ℕ) :
    (∃ m : ℕ, (m : ℝ) / (n + 2) = a / b) ↔ b ∣ (n + 2) := by
  have hn : (0 : ℝ) < n + 2 := by positivity
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · rintro ⟨m, hm⟩
    rw [div_eq_div_iff hn.ne' hb'.ne'] at hm
    have hm' : m * b = a * (n + 2) := by exact_mod_cast hm
    exact hab.symm.dvd_of_dvd_mul_left ⟨m, by rw [← hm']; ring⟩
  · rintro ⟨t, ht⟩
    refine ⟨a * t, ?_⟩
    have ht' : (n : ℝ) + 2 = b * t := by exact_mod_cast ht
    have htpos : (0 : ℝ) < t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · rw [Nat.cast_zero, mul_zero] at ht'; linarith
      · exact_mod_cast h
    rw [ht']
    push_cast
    field_simp

theorem not_exists_nat_eq_frac {a b : ℕ} (hab : a.Coprime b) (hb : 2 ≤ b) {m n : ℕ} :
    (m : ℝ) * n ≠ a / b := by
  intro h
  have hb' : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  rw [eq_div_iff hb'.ne'] at h
  have h' : m * n * b = a := by exact_mod_cast h
  have hdvd : b ∣ a := ⟨m * n, by rw [← h']; ring⟩
  have := Nat.Coprime.eq_one_of_dvd hab.symm hdvd
  omega

open Classical in
/-- **Integer rates.**  The rate coefficient at `r = a ≥ 1` is `R_a`. -/
theorem divisorRateCoeff_nat {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n)
    {a : ℕ} (ha : 0 < a) :
    thetaGaugeRateCoeff (divisorGaugeCoeff c) divisorShift a = divisorIntegerWeight c a := by
  rw [divisorRateCoeff_eq hc, if_pos ⟨a, rfl⟩]
  have hA : Summable fun n : ℕ => if ∃ m : ℕ, (m : ℝ) * (n + 2) = a then
      c (n + 2) * Real.sqrt (n + 2) else 0 :=
    Summable.of_norm_bounded (summable_divisor_half hc) fun n => by
      split_ifs
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      · rw [norm_zero]; positivity
  have hB : Summable fun n : ℕ => if ∃ m : ℕ, (m : ℝ) / (n + 2) = a then
      c (n + 2) / Real.sqrt (n + 2) else 0 :=
    Summable.of_norm_bounded (summable_divisor_inv_half hc) fun n => by
      split_ifs
      · rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      · rw [norm_zero]; positivity
  rw [hA.tsum_add hB]
  unfold divisorIntegerWeight
  have e1 : (∑' n : ℕ, if ∃ m : ℕ, (m : ℝ) / (n + 2) = a then
      c (n + 2) / Real.sqrt (n + 2) else 0) = divisorTail c 1 := by
    unfold divisorTail
    refine tsum_shift_two (fun n => ?_) (fun n hn => if_neg (by omega))
    rw [if_pos ⟨a * (n + 2), by push_cast; field_simp⟩, if_pos ⟨by omega, one_dvd _⟩]
    push_cast; rfl
  have e2 : (∑' n : ℕ, if ∃ m : ℕ, (m : ℝ) * (n + 2) = a then
      c (n + 2) * Real.sqrt (n + 2) else 0) =
      ∑ n ∈ a.divisors, if 2 ≤ n then c n * Real.sqrt n else 0 := by
    rw [tsum_shift_two (G := fun n => if 2 ≤ n ∧ n ∣ a then c n * Real.sqrt n else 0)
      (fun n => ?_) (fun n hn => if_neg (by omega))]
    · rw [tsum_eq_sum (s := a.divisors)]
      · refine Finset.sum_congr rfl fun n hn => ?_
        by_cases h2 : 2 ≤ n
        · rw [if_pos ⟨h2, Nat.dvd_of_mem_divisors hn⟩, if_pos h2]
        · rw [if_neg (fun h => h2 h.1), if_neg h2]
      · intro n hn
        rw [if_neg]
        exact fun h => hn (Nat.mem_divisors.mpr ⟨h.2, ha.ne'⟩)
    · by_cases hd : (n + 2) ∣ a
      · rw [if_pos ((exists_nat_mul_eq_iff_dvd n a).mpr hd), if_pos ⟨by omega, hd⟩]
        push_cast; rfl
      · rw [if_neg (fun h => hd ((exists_nat_mul_eq_iff_dvd n a).mp h)),
          if_neg (fun h => hd h.2)]
  rw [e1, e2]
  ring

open Classical in
/-- **Fractional rates.**  At a reduced fraction `a/b` with `b ≥ 2` the rate coefficient is
`Q_b`. -/
theorem divisorRateCoeff_frac {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n)
    {a b : ℕ} (hab : a.Coprime b) (hb : 2 ≤ b) :
    thetaGaugeRateCoeff (divisorGaugeCoeff c) divisorShift ((a : ℝ) / b) = divisorTail c b := by
  rw [divisorRateCoeff_eq hc, if_neg (fun ⟨m, hm⟩ => not_exists_nat_eq_frac (m := m) (n := 1)
    hab hb (by rw [Nat.cast_one, mul_one]; exact hm)), zero_add]
  unfold divisorTail
  refine tsum_shift_two (fun n => ?_) (fun n hn => if_neg (by omega))
  rw [if_neg (fun ⟨m, hm⟩ => not_exists_nat_eq_frac (m := m) (n := n + 2) hab hb
    (by push_cast; exact hm)), zero_add]
  by_cases hd : b ∣ (n + 2)
  · rw [if_pos ((exists_nat_div_eq_iff_dvd hab (by omega) n).mpr hd), if_pos ⟨by omega, hd⟩]
    push_cast; rfl
  · rw [if_neg (fun h => hd ((exists_nat_div_eq_iff_dvd hab (by omega) n).mp h)),
      if_neg (fun h => hd h.2)]

/-- A positive real hit by some `m/(n+2)` is a fraction `a/b` in lowest terms. -/
theorem exists_reduced_of_div {r : ℝ} {m n : ℕ} (hm : (m : ℝ) / (n + 2) = r) :
    ∃ a b : ℕ, a.Coprime b ∧ 0 < b ∧ r = a / b := by
  set q : ℚ := (m : ℚ) / (n + 2)
  have hq0 : 0 ≤ q := by positivity
  refine ⟨q.num.natAbs, q.den, q.reduced, q.den_pos, ?_⟩
  rw [← hm, show ((m : ℝ) / (n + 2)) = ((q : ℚ) : ℝ) by simp [q], Rat.cast_def]
  congr 1
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast Rat.num_nonneg.mpr hq0)]

open Classical in
/-- **Divisor Bernstein cone.**  The flux of the symmetric integer-scale gauge is completely
monotone iff `Q_b ≥ 0` for every `b ≥ 2` and `R_a ≥ 0` for every `a ≥ 1`. -/
theorem completelyMonotoneOn_divisorGauge_iff {c : ℕ → ℝ}
    (hc : Summable fun n : ℕ => |c n| * Real.sqrt n) :
    CompletelyMonotoneOn (thetaNormalizedFlux (thetaDivisorGauge c)) ↔
      (∀ b, 2 ≤ b → 0 ≤ divisorTail c b) ∧ (∀ a, 1 ≤ a → 0 ≤ divisorIntegerWeight c a) := by
  unfold thetaDivisorGauge
  rw [completelyMonotoneOn_thetaNormalizedFlux_gauge_iff_rateCoeff (divisor_gauge_admissible hc)]
  constructor
  · intro h
    refine ⟨fun b hb => ?_, fun a ha => ?_⟩
    · have := h ((1 : ℕ) / b) (by positivity)
      rwa [divisorRateCoeff_frac hc (Nat.coprime_one_left b) hb] at this
    · have := h a (by exact_mod_cast ha)
      rwa [divisorRateCoeff_nat hc ha] at this
  · rintro ⟨hQ, hR⟩ r hr
    by_cases hnat : ∃ a : ℕ, (a : ℝ) = r
    · obtain ⟨a, rfl⟩ := hnat
      have ha : 1 ≤ a := by exact_mod_cast hr
      rw [divisorRateCoeff_nat hc ha]
      exact hR a ha
    · by_cases hfrac : ∃ n m : ℕ, (m : ℝ) / (n + 2) = r
      · obtain ⟨n, m, hm⟩ := hfrac
        obtain ⟨a, b, hab, hb0, rfl⟩ := exists_reduced_of_div hm
        have hb : 2 ≤ b := by
          by_contra h'
          have hb1 : b = 1 := by omega
          exact hnat ⟨a, by rw [hb1, Nat.cast_one, div_one]⟩
        rw [divisorRateCoeff_frac hc hab hb]
        exact hQ b hb
      · rw [divisorRateCoeff_eq hc, if_neg hnat, zero_add]
        refine le_of_eq (Eq.symm ((tsum_congr fun n => ?_).trans tsum_zero))
        rw [if_neg (fun ⟨m, hm⟩ => hnat ⟨m * (n + 2), by push_cast; exact hm⟩),
          if_neg (fun ⟨m, hm⟩ => hfrac ⟨n, m, hm⟩), add_zero]

/-- **Rate weights.**  The Bernstein measure of the flux has weight `2π(a/b)² Q_b` at the rate
`π(a/b)²` for `a/b` reduced with `b ≥ 2`, and weight `2π a² R_a` at the integer rate `π a²`. -/
theorem divisorGauge_rate_weights {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n) :
    (∀ a b : ℕ, a.Coprime b → 2 ≤ b →
      (∑' q : ℤ × ℕ, if thetaGaugeAtomRate divisorShift q = Real.pi * ((a : ℝ) / b) ^ 2 then
        thetaGaugeAtomWeight (divisorGaugeCoeff c) divisorShift q else 0) =
        2 * Real.pi * ((a : ℝ) / b) ^ 2 * divisorTail c b) ∧
    (∀ a : ℕ, 1 ≤ a →
      (∑' q : ℤ × ℕ, if thetaGaugeAtomRate divisorShift q = Real.pi * (a : ℝ) ^ 2 then
        thetaGaugeAtomWeight (divisorGaugeCoeff c) divisorShift q else 0) =
        2 * Real.pi * (a : ℝ) ^ 2 * divisorIntegerWeight c a) := by
  refine ⟨fun a b hab hb => ?_, fun a ha => ?_⟩
  · have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · rw [Nat.coprime_zero_left] at hab; omega
      · exact h
    rw [grouped_thetaGaugeAtom_eq _ _ (by positivity), divisorRateCoeff_frac hc hab hb]
  · rw [grouped_thetaGaugeAtom_eq _ _ (by positivity), divisorRateCoeff_nat hc ha]

/-- **Flux of the divisor gauge.**
`b_g(t) = c₁ b_k(t) + ∑_{n ≥ 2} c_n [n^{5/2} b_k(n² t) + n^{-5/2} b_k(n^{-2} t)]`. -/
theorem thetaNormalizedFlux_thetaDivisorGauge {c : ℕ → ℝ}
    (hc : Summable fun n : ℕ => |c n| * Real.sqrt n) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaDivisorGauge c) t =
      c 1 * thetaNormalizedFlux thetaCuspFullSource t + ∑' n : ℕ, c (n + 2) *
        (((n : ℝ) + 2) ^ (5 / 2 : ℝ) *
            thetaNormalizedFlux thetaCuspFullSource (((n : ℝ) + 2) ^ 2 * t) +
          ((n : ℝ) + 2) ^ (-(5 / 2) : ℝ) *
            thetaNormalizedFlux thetaCuspFullSource ((((n : ℝ) + 2) ^ 2)⁻¹ * t)) := by
  have hadm := divisor_gauge_admissible hc
  have hsum : Summable fun j : ℤ => divisorGaugeCoeff c j * (Real.exp (5 * divisorShift j / 2) *
      thetaNormalizedFlux thetaCuspFullSource (Real.exp (2 * divisorShift j) * t)) := by
    have h := (summable_abs_thetaGaugeAtom hadm ht)
    have hs : Summable fun q : ℤ × ℕ => thetaGaugeAtomWeight (divisorGaugeCoeff c) divisorShift q *
        Real.exp (-thetaGaugeAtomRate divisorShift q * t) :=
      Summable.of_norm (h.congr fun q => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)])
    exact hs.prod.congr fun j =>
      (hasSum_thetaGaugeAtom_fiber (divisorGaugeCoeff c) divisorShift j ht).tsum_eq
  unfold thetaDivisorGauge
  rw [thetaNormalizedFlux_thetaTranslationGauge hadm ht, tsum_int_eq_zero_add_pairs hsum]
  have hpos : ∀ n : ℕ, (0 : ℝ) < n + 2 := fun n => by positivity
  simp only [divisorShift_zero, mul_zero, zero_div, Real.exp_zero, one_mul, divisorGaugeCoeff_succ,
    divisorGaugeCoeff_neg_succ, divisorShift_succ, divisorShift_neg_succ]
  congr 1
  refine tsum_congr fun n => ?_
  rw [← mul_add]
  congr 1
  rw [Real.rpow_def_of_pos (hpos n), Real.rpow_def_of_pos (hpos n),
    show 2 * -Real.log ((n : ℝ) + 2) = -(2 * Real.log ((n : ℝ) + 2)) by ring,
    Real.exp_neg, show 2 * Real.log ((n : ℝ) + 2) = (2 : ℕ) * Real.log ((n : ℝ) + 2) by norm_num,
    Real.exp_nat_mul, Real.exp_log (hpos n)]
  ring_nf

/-! ## Multipliers, anchors and the divisor-Abel identity -/

/-- Ordinary multiplier `M₀ = c₁ + 2 ∑_{n ≥ 2} c_n`. -/
noncomputable def divisorGaugeMass (c : ℕ → ℝ) : ℝ := c 1 + 2 * ∑' n : ℕ, c (n + 2)

/-- Critical multiplier `M_{1/2} = c₁ + ∑_{n ≥ 2} c_n (√n + 1/√n)`. -/
noncomputable def divisorGaugeCharge (c : ℕ → ℝ) : ℝ :=
  c 1 + ∑' n : ℕ, c (n + 2) * (Real.sqrt (n + 2) + 1 / Real.sqrt (n + 2))

/-- The half-density coefficient `v_n = c_n/√n`. -/
noncomputable def divisorHalfCoeff (c : ℕ → ℝ) (n : ℕ) : ℝ := c n / Real.sqrt n

theorem summable_divisor_coeff {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n) :
    Summable fun n : ℕ => c (n + 2) :=
  Summable.of_norm_bounded (summable_divisor_half hc) fun n => by
    rw [Real.norm_eq_abs]
    have h1 : (1 : ℝ) ≤ Real.sqrt (n + 2) :=
      Real.one_le_sqrt.mpr (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
    nlinarith [abs_nonneg (c (n + 2))]

theorem divisorGauge_integral {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n) :
    (∫ x, thetaDivisorGauge c x) = divisorGaugeMass c * ∫ x, thetaCuspFullSource x := by
  have hadm := divisor_gauge_admissible hc
  have h := (integral_exp_mul_thetaTranslationGauge hadm (w := 0) (by norm_num)).2
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, mul_one] at h
  unfold thetaDivisorGauge
  rw [h, tsum_int_eq_zero_add_pairs (summable_abs_of_gauge hadm).of_abs]
  congr 1
  unfold divisorGaugeMass
  simp only [divisorGaugeCoeff_succ, divisorGaugeCoeff_neg_succ]
  rw [← tsum_mul_left]
  congr 1
  exact tsum_congr fun n => by ring

theorem divisorGauge_integral_exp_half {c : ℕ → ℝ}
    (hc : Summable fun n : ℕ => |c n| * Real.sqrt n) :
    (∫ x, Real.exp (x / 2) * thetaDivisorGauge c x) =
      divisorGaugeCharge c * ∫ x, Real.exp (x / 2) * thetaCuspFullSource x := by
  have hadm := divisor_gauge_admissible hc
  have h := (integral_exp_mul_thetaTranslationGauge hadm (w := 1 / 2)
    (by norm_num [abs_of_pos])).2
  have e1 : ∀ x : ℝ, 1 / 2 * x = x / 2 := fun x => by ring
  simp only [e1] at h
  have hs : Summable fun j : ℤ => divisorGaugeCoeff c j * Real.exp (-(divisorShift j / 2)) :=
    Summable.of_norm ((summable_abs_mul_exp_of_gauge hadm (σ := -(1 / 2))
      (by norm_num [abs_of_pos])).congr fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]; ring_nf)
  unfold thetaDivisorGauge
  rw [h, tsum_int_eq_zero_add_pairs hs]
  congr 1
  unfold divisorGaugeCharge
  simp only [divisorGaugeCoeff_succ, divisorGaugeCoeff_neg_succ, divisorShift_zero, divisorShift_succ,
    divisorShift_neg_succ, zero_div, neg_zero, Real.exp_zero, mul_one, neg_div, neg_neg,
    Real.exp_neg, exp_half_log_nat_add_two]
  congr 1
  exact tsum_congr fun n => by ring

/-- `M_{1/2} - M₀ = ∑_{n ≥ 2} v_n F(n)`. -/
theorem divisorGaugeCharge_sub_mass {c : ℕ → ℝ}
    (hc : Summable fun n : ℕ => |c n| * Real.sqrt n) :
    divisorGaugeCharge c - divisorGaugeMass c =
      ∑' n : ℕ, if 2 ≤ n then divisorHalfCoeff c n * divisorAbelWeight n else 0 := by
  have h0 := summable_divisor_coeff hc
  have h1 : Summable fun n : ℕ => c (n + 2) * (Real.sqrt (n + 2) + 1 / Real.sqrt (n + 2)) := by
    refine Summable.of_norm_bounded ((summable_divisor_half hc).mul_left 2) fun n => ?_
    have h1 : (1 : ℝ) ≤ Real.sqrt (n + 2) :=
      Real.one_le_sqrt.mpr (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_pos (show 0 < Real.sqrt (n + 2) + 1 / Real.sqrt (n + 2) by positivity)]
    have : 1 / Real.sqrt (n + 2) ≤ Real.sqrt (n + 2) := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith [abs_nonneg (c (n + 2))]
  unfold divisorGaugeCharge divisorGaugeMass
  rw [add_sub_add_left_eq_sub, ← tsum_mul_left, ← h1.tsum_sub (h0.mul_left 2)]
  refine tsum_shift_two (fun n => ?_) (fun n hn => if_neg (by omega))
  rw [if_pos (by omega)]
  unfold divisorHalfCoeff divisorAbelWeight
  have hs : Real.sqrt ((n : ℝ) + 2) ^ 2 = n + 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 < Real.sqrt ((n : ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
  push_cast
  field_simp
  ring

theorem abs_divisorHalfCoeff_mul_le (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |divisorHalfCoeff c n| * divisorAbelWeight n ≤ |c n| * Real.sqrt n := by
  have h1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
  unfold divisorHalfCoeff divisorAbelWeight
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt n), div_mul_eq_mul_div,
    div_le_iff₀ (by linarith), mul_assoc, hs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  nlinarith

theorem abs_divisorHalfCoeff_le (c : ℕ → ℝ) (n : ℕ) :
    |divisorHalfCoeff c n| ≤ |c n| * Real.sqrt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [divisorHalfCoeff]
  · have h1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
    unfold divisorHalfCoeff
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt n), div_le_iff₀ (by linarith),
      mul_assoc]
    nlinarith [abs_nonneg (c n), mul_le_mul h1 h1 zero_le_one (by linarith)]

theorem divisorTail_eq_tsum_mul (c : ℕ → ℝ) {d : ℕ} (hd : 0 < d) :
    divisorTail c d = ∑' k : ℕ, if 2 ≤ d * k then divisorHalfCoeff c (d * k) else 0 := by
  unfold divisorTail
  have hinj : Function.Injective fun k : ℕ => d * k := mul_right_injective₀ hd.ne'
  rw [← hinj.tsum_eq (f := fun n => if 2 ≤ n ∧ d ∣ n then c n / Real.sqrt n else 0)]
  · refine tsum_congr fun k => ?_
    simp only [dvd_mul_right, and_true]
    rfl
  · intro n hn
    have h : d ∣ n := by
      by_contra h'
      exact hn (by simp only; rw [if_neg (fun h => h' h.2)])
    obtain ⟨k, rfl⟩ := h
    exact ⟨k, rfl⟩

/-- **Divisor-Abel identity.**  `M_{1/2} - M₀ = ∑_{d ≥ 2} β(d) Q_d`, absolutely convergent. -/
theorem hasSum_divisorChargeGap {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n) :
    HasSum (fun d => divisorMoebiusWeight d * divisorTail c d)
      (divisorGaugeCharge c - divisorGaugeMass c) := by
  set φ : ℕ × ℕ → ℝ := fun q => divisorMoebiusWeight q.1 *
    (if 2 ≤ q.1 * q.2 then divisorHalfCoeff c (q.1 * q.2) else 0)
  have h0 : ∀ q : ℕ × ℕ, (q.1 = 0 ∨ q.2 = 0) → φ q = 0 := by
    intro q hq
    have : q.1 * q.2 = 0 := by rcases hq with h | h <;> simp [h]
    simp only [φ, this]
    simp
  have hβ := divisorMoebiusWeight_nonneg
  have hfib : ∀ N, ∑ q ∈ N.divisorsAntidiagonal, φ q =
      if 2 ≤ N then divisorHalfCoeff c N * divisorAbelWeight N else 0 := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [Finset.sum_congr rfl fun q hq => by
        rw [show φ q = divisorMoebiusWeight q.1 * (if 2 ≤ N then divisorHalfCoeff c N else 0) by
          simp only [φ, (Nat.mem_divisorsAntidiagonal.mp hq).1]], ← Finset.sum_mul,
        Nat.sum_divisorsAntidiagonal (fun a _ => divisorMoebiusWeight a),
        sum_divisors_divisorMoebiusWeight hN]
      split_ifs <;> ring
  have hfibabs : ∀ N, ∑ q ∈ N.divisorsAntidiagonal, |φ q| =
      if 2 ≤ N then |divisorHalfCoeff c N| * divisorAbelWeight N else 0 := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [Finset.sum_congr rfl fun q hq => by
        rw [show |φ q| = divisorMoebiusWeight q.1 * (if 2 ≤ N then |divisorHalfCoeff c N| else 0) by
          simp only [φ, (Nat.mem_divisorsAntidiagonal.mp hq).1, abs_mul, abs_of_nonneg (hβ _)]
          split_ifs <;> simp], ← Finset.sum_mul,
        Nat.sum_divisorsAntidiagonal (fun a _ => divisorMoebiusWeight a),
        sum_divisors_divisorMoebiusWeight hN]
      split_ifs <;> ring
  have habs0 : ∀ q : ℕ × ℕ, (q.1 = 0 ∨ q.2 = 0) → |φ q| = 0 := fun q hq => by rw [h0 q hq, abs_zero]
  have hφabs : Summable fun q => |φ q| := by
    refine summable_of_nonneg_of_fiberwise (fun q => abs_nonneg _) (fun q : ℕ × ℕ => q.1 * q.2)
      (fun N => (divisorFiber_tsum habs0 N).1) ?_
    simp_rw [fun N => (divisorFiber_tsum habs0 N).2, hfibabs]
    refine Summable.of_nonneg_of_le (fun N => by
      split_ifs
      · exact mul_nonneg (abs_nonneg _) (by unfold divisorAbelWeight; positivity)
      · exact le_rfl) (fun N => ?_) hc
    split_ifs with h2
    · exact abs_divisorHalfCoeff_mul_le c (by omega)
    · positivity
  have hφ : Summable φ := Summable.of_norm (hφabs.congr fun q => (Real.norm_eq_abs _).symm)
  have hreg := hasSum_divisorsAntidiagonal_regroup hφ h0
  simp_rw [hfib] at hreg
  have key : divisorGaugeCharge c - divisorGaugeMass c = ∑' q, φ q := by
    rw [divisorGaugeCharge_sub_mass hc]
    exact hreg.tsum_eq
  rw [key]
  have hv : Summable (divisorHalfCoeff c) := Summable.of_norm_bounded hc fun n => by
    rw [Real.norm_eq_abs]; exact abs_divisorHalfCoeff_le c n
  refine hφ.hasSum.prod_fiberwise fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz : divisorMoebiusWeight 0 = 0 := by simp [divisorMoebiusWeight]
    simp only [φ, hz, zero_mul]
    exact hasSum_zero
  · rw [divisorTail_eq_tsum_mul c hd]
    have hrow : Summable fun k : ℕ => if 2 ≤ d * k then divisorHalfCoeff c (d * k) else 0 := by
      have := hv.comp_injective (mul_right_injective₀ hd.ne')
      refine Summable.of_norm_bounded this.norm fun k => ?_
      simp only [Function.comp_apply]
      split_ifs
      · exact le_rfl
      · rw [norm_zero]; exact norm_nonneg _
    simp only [φ]
    exact hrow.hasSum.mul_left _

theorem card_divisorsAntidiagonal_le (N : ℕ) : (N.divisorsAntidiagonal.card : ℝ) ≤ N := by
  rw [← Nat.map_div_right_divisors, Finset.card_map]
  exact_mod_cast Nat.card_divisors_le_self N

/-- **Möbius inversion over multiples.**  For `n ≥ 1`, `∑_{k ≥ 1} μ(k) Q_{nk} = v_n` if `n ≥ 2`
and `0` if `n = 1`. -/
theorem hasSum_moebius_divisorTail {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n)
    {n : ℕ} (hn : 0 < n) :
    HasSum (fun k => (moebius k : ℝ) * divisorTail c (n * k))
      (if 2 ≤ n then divisorHalfCoeff c n else 0) := by
  set ψ : ℕ × ℕ → ℝ := fun q => (moebius q.1 : ℝ) *
    (if 2 ≤ n * (q.1 * q.2) then divisorHalfCoeff c (n * (q.1 * q.2)) else 0)
  set χ : ℕ × ℕ → ℝ := fun q =>
    if 2 ≤ n * (q.1 * q.2) then |divisorHalfCoeff c (n * (q.1 * q.2))| else 0
  have h0 : ∀ q : ℕ × ℕ, (q.1 = 0 ∨ q.2 = 0) → ψ q = 0 := by
    intro q hq
    have : q.1 * q.2 = 0 := by rcases hq with h | h <;> simp [h]
    simp [ψ, this]
  have hχ0 : ∀ q : ℕ × ℕ, (q.1 = 0 ∨ q.2 = 0) → χ q = 0 := by
    intro q hq
    have : q.1 * q.2 = 0 := by rcases hq with h | h <;> simp [h]
    simp [χ, this]
  have hχnn : ∀ q, 0 ≤ χ q := fun q => by simp only [χ]; split_ifs <;> positivity
  have hψχ : ∀ q, ‖ψ q‖ ≤ χ q := by
    intro q
    simp only [ψ, χ, Real.norm_eq_abs, abs_mul]
    have hμ : |(moebius q.1 : ℝ)| ≤ 1 := by
      have := abs_moebius_le_one (n := q.1)
      exact_mod_cast this
    split_ifs
    · exact mul_le_of_le_one_left (abs_nonneg _) hμ
    · simp
  have hχfib : ∀ N, ∑ q ∈ N.divisorsAntidiagonal, χ q =
      N.divisorsAntidiagonal.card *
        (if 2 ≤ n * N then |divisorHalfCoeff c (n * N)| else 0) := by
    intro N
    rw [Finset.sum_congr rfl fun q hq => by
      rw [show χ q = if 2 ≤ n * N then |divisorHalfCoeff c (n * N)| else 0 by
        simp only [χ, (Nat.mem_divisorsAntidiagonal.mp hq).1]], Finset.sum_const, nsmul_eq_mul]
  have hχs : Summable χ := by
    refine summable_of_nonneg_of_fiberwise hχnn (fun q : ℕ × ℕ => q.1 * q.2)
      (fun N => (divisorFiber_tsum hχ0 N).1) ?_
    simp_rw [fun N => (divisorFiber_tsum hχ0 N).2, hχfib]
    have hmaj : Summable fun N : ℕ => |c (n * N)| * Real.sqrt ((n * N : ℕ) : ℝ) :=
      hc.comp_injective (mul_right_injective₀ hn.ne')
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_) hmaj
    split_ifs with h2
    · have hnN : 1 ≤ n * N := by omega
      have hs1 : (1 : ℝ) ≤ Real.sqrt ((n * N : ℕ) : ℝ) :=
        Real.one_le_sqrt.mpr (by exact_mod_cast hnN)
      have hss : Real.sqrt ((n * N : ℕ) : ℝ) * Real.sqrt ((n * N : ℕ) : ℝ) = ((n * N : ℕ) : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg _)
      have hN : (N : ℝ) ≤ ((n * N : ℕ) : ℝ) := by
        push_cast
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      calc (N.divisorsAntidiagonal.card : ℝ) * |divisorHalfCoeff c (n * N)|
          ≤ ((n * N : ℕ) : ℝ) * |divisorHalfCoeff c (n * N)| :=
            mul_le_mul_of_nonneg_right ((card_divisorsAntidiagonal_le N).trans hN) (abs_nonneg _)
        _ = |c (n * N)| * Real.sqrt ((n * N : ℕ) : ℝ) := by
            have hpos : (0 : ℝ) < Real.sqrt ((n * N : ℕ) : ℝ) := by linarith
            unfold divisorHalfCoeff
            rw [abs_div, abs_of_pos hpos, mul_div_assoc', div_eq_iff hpos.ne', mul_assoc, hss,
              mul_comm]
    · rw [mul_zero]; positivity
  have hψ : Summable ψ := Summable.of_norm_bounded hχs hψχ
  have hreg := hasSum_divisorsAntidiagonal_regroup hψ h0
  have hψfib : ∀ N, ∑ q ∈ N.divisorsAntidiagonal, ψ q =
      if N = 1 then (if 2 ≤ n then divisorHalfCoeff c n else 0) else 0 := by
    intro N
    rw [Finset.sum_congr rfl fun q hq => by
      rw [show ψ q = (moebius q.1 : ℝ) *
          (if 2 ≤ n * N then divisorHalfCoeff c (n * N) else 0) by
        simp only [ψ, (Nat.mem_divisorsAntidiagonal.mp hq).1]], ← Finset.sum_mul,
      sum_divisorsAntidiagonal_moebius]
    split_ifs with h1 <;> simp_all
  simp_rw [hψfib] at hreg
  have hval : ∑' q, ψ q = if 2 ≤ n then divisorHalfCoeff c n else 0 := by
    rw [← hreg.tsum_eq, tsum_eq_single 1 (fun N hN => if_neg hN), if_pos rfl]
  rw [← hval]
  have hv : Summable (divisorHalfCoeff c) := Summable.of_norm_bounded hc fun m => by
    rw [Real.norm_eq_abs]; exact abs_divisorHalfCoeff_le c m
  refine hψ.hasSum.prod_fiberwise fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [ψ, ArithmeticFunction.map_zero, Int.cast_zero, zero_mul]
    exact hasSum_zero
  · have hnk : 0 < n * k := Nat.mul_pos hn hk
    rw [divisorTail_eq_tsum_mul c hnk]
    have hrow : Summable fun j : ℕ => if 2 ≤ n * k * j then divisorHalfCoeff c (n * k * j)
        else 0 := by
      have := hv.comp_injective (mul_right_injective₀ hnk.ne')
      refine Summable.of_norm_bounded this.norm fun j => ?_
      simp only [Function.comp_apply]
      split_ifs
      · exact le_rfl
      · rw [norm_zero]; exact norm_nonneg _
    have hrw : (fun j => ψ (k, j)) = fun j => (moebius k : ℝ) *
        (if 2 ≤ n * k * j then divisorHalfCoeff c (n * k * j) else 0) := by
      funext j
      simp only [ψ, mul_assoc]
    rw [hrw]
    exact hrow.hasSum.mul_left _

/-- **Charge monotonicity.**  Complete monotonicity forces `M_{1/2} ≥ M₀`. -/
theorem divisorChargeGap_nonneg {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n)
    (hCM : CompletelyMonotoneOn (thetaNormalizedFlux (thetaDivisorGauge c))) :
    0 ≤ divisorGaugeCharge c - divisorGaugeMass c := by
  have hQ := ((completelyMonotoneOn_divisorGauge_iff hc).mp hCM).1
  refine (hasSum_divisorChargeGap hc).nonneg fun d => ?_
  rcases lt_or_ge 1 d with hd | hd
  · exact mul_nonneg (divisorMoebiusWeight_nonneg d) (hQ d hd)
  · interval_cases d
    · simp [divisorMoebiusWeight]
    · simp [divisorMoebiusWeight_one]

/-- **Equality case.**  Under complete monotonicity, `M_{1/2} = M₀` iff `c_n = 0` for every
`n ≥ 2`. -/
theorem divisorChargeGap_eq_zero_iff {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n)
    (hCM : CompletelyMonotoneOn (thetaNormalizedFlux (thetaDivisorGauge c))) :
    divisorGaugeCharge c - divisorGaugeMass c = 0 ↔ ∀ n, 2 ≤ n → c n = 0 := by
  have hQ := ((completelyMonotoneOn_divisorGauge_iff hc).mp hCM).1
  constructor
  · intro hΔ
    have hS := hasSum_divisorChargeGap hc
    rw [hΔ] at hS
    have hterm : ∀ d, 0 ≤ divisorMoebiusWeight d * divisorTail c d := by
      intro d
      rcases lt_or_ge 1 d with hd | hd
      · exact mul_nonneg (divisorMoebiusWeight_nonneg d) (hQ d hd)
      · interval_cases d
        · simp [divisorMoebiusWeight]
        · simp [divisorMoebiusWeight_one]
    have hz := (hasSum_zero_iff_of_nonneg hterm).mp hS
    have hQ0 : ∀ d, 2 ≤ d → divisorTail c d = 0 := fun d hd =>
      (mul_eq_zero.mp (congrFun hz d)).resolve_left (divisorMoebiusWeight_pos hd).ne'
    intro n hn
    have h := hasSum_moebius_divisorTail hc (n := n) (by omega)
    rw [if_pos hn] at h
    have hzero : (fun k => (moebius k : ℝ) * divisorTail c (n * k)) = fun _ => 0 := by
      funext k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [hQ0 _ (by nlinarith), mul_zero]
    rw [hzero] at h
    have hv : divisorHalfCoeff c n = 0 := (h.unique hasSum_zero)
    unfold divisorHalfCoeff at hv
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
    exact (div_eq_zero_iff.mp hv).resolve_right hs.ne'
  · intro h
    unfold divisorGaugeCharge divisorGaugeMass
    have h2 : ∀ n : ℕ, c (n + 2) = 0 := fun n => h _ (by omega)
    simp [h2]

/-- **Two-anchor rigidity.**  A symmetric integer-scale gauge with completely monotone flux, the
ordinary mass of `k` and the critical half-density charge of `k` is `k`. -/
theorem divisorGauge_rigidity {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n| * Real.sqrt n)
    (hCM : CompletelyMonotoneOn (thetaNormalizedFlux (thetaDivisorGauge c)))
    (hmass : ∫ x, thetaDivisorGauge c x = ∫ x, thetaCuspFullSource x)
    (hcharge : ∫ x, Real.exp (x / 2) * thetaDivisorGauge c x =
      ∫ x, Real.exp (x / 2) * thetaCuspFullSource x) :
    thetaDivisorGauge c = thetaCuspFullSource ∧ c 1 = 1 ∧ ∀ n, 2 ≤ n → c n = 0 := by
  have hk0 : 0 < ∫ x, thetaCuspFullSource x := by
    simpa using integral_exp_mul_thetaCuspFullSource_pos 0
  have hk1 : 0 < ∫ x, Real.exp (x / 2) * thetaCuspFullSource x := by
    have := integral_exp_mul_thetaCuspFullSource_pos (1 / 2)
    simpa only [show ∀ x : ℝ, 1 / 2 * x = x / 2 from fun x => by ring] using this
  have hM0 : divisorGaugeMass c = 1 := by
    rw [divisorGauge_integral hc] at hmass
    exact (mul_eq_right₀ hk0.ne').mp hmass
  have hM1 : divisorGaugeCharge c = 1 := by
    rw [divisorGauge_integral_exp_half hc] at hcharge
    exact (mul_eq_right₀ hk1.ne').mp hcharge
  have hzero := (divisorChargeGap_eq_zero_iff hc hCM).mp (by rw [hM0, hM1, sub_self])
  have hc1 : c 1 = 1 := by
    rw [← hM0]
    unfold divisorGaugeMass
    simp [hzero _ (by omega : 2 ≤ _ + 2)]
  refine ⟨funext fun x => ?_, hc1, hzero⟩
  rw [thetaDivisorGauge_apply hc, hc1, one_mul]
  simp [hzero _ (by omega : 2 ≤ _ + 2)]

/-- On a prime-power chain the divisor Möbius weight is the Abel increment:
`β(p^j) = F(p^j) - F(p^{j-1})`. -/
theorem divisorMoebiusWeight_prime_pow {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) :
    divisorMoebiusWeight (p ^ j) = divisorAbelWeight (p ^ j) - divisorAbelWeight (p ^ (j - 1)) := by
  set Fa : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else divisorAbelWeight n, by simp⟩
  have h := moebius_mul_apply_prime_pow Fa hp hj
  have hFa : ∀ n, n ≠ 0 → Fa n = divisorAbelWeight n := fun n hn => by
    show (if n = 0 then 0 else divisorAbelWeight n) = _
    rw [if_neg hn]
  rw [hFa _ (pow_ne_zero _ hp.ne_zero), hFa _ (pow_ne_zero _ hp.ne_zero), mul_apply] at h
  rw [← h, divisorMoebiusWeight]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [intCoe_apply, hFa _ (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).ne']

end RHTower
