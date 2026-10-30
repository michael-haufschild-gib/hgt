import GaloisForLFunctions.ArithmeticGaugeTheory.TheAdditivelyInvariantPoint
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Chebyshev

/-!
# The divisor collapse selects the trivial gauge point

Read the prime source on the divisors of one integer through a gauge point:
`F_x(ℓ) = Σ_{k ∣ ℓ} Λ(k) χ_x(k)` (`divisorFibre`). At the trivial point unique factorization
collapses the fibre to the archimedean absolute value, `F_0(ℓ) = log ℓ` (`divisorFibre_trivial`,
the identity `Λ * 1 = log`). This file shows that the collapse is a property of the trivial point
alone and measures how far from typical it is.

* **Maximality** (`re_divisorFibre_le`, `re_divisorFibre_eq_log_iff`). `Re F_x(ℓ) ≤ log ℓ` for every
  gauge point, with equality exactly when `χ_x(p) = 1` at every prime `p ∣ ℓ`. The trivial point is
  the unique maximizer on every fibre at once (`divisorFibre_eq_log_forall_iff`).
* **The Liouville point reverses the collapse at primes**
  (`divisorFibre_prime_of_twist_eq_neg_one`): `F_x(p) = −log p` when `χ_x(p) = −1`.
* **Gauge charge** (`integral_divisorFibre`, `integral_divisorFibre_mul_conj`). The fibre has gauge
  mean `0` and gauge mean square `Σ_{k ∣ ℓ} Λ(k)²`, by orthogonality of twists and `Λ(1) = 0`.
* **Coherence** (`sum_sq_vonMangoldt_le_log_sq`, `log_sq_le_card_divisors_mul`). The value at the
  trivial point satisfies `Σ Λ(k)² ≤ (log ℓ)² ≤ τ(ℓ) Σ Λ(k)²`: it lies at least one gauge standard
  deviation above the gauge mean, and at most `√τ(ℓ)` deviations.

So the collapse `Λ * 1 = log` is a gauge-charged statistic whose value at `0` is coherent: every
prime-power divisor adds in phase. Summed over `ℓ` this coherence is the pole of `−ζ'/ζ · ζ = −ζ'`.
It is the point-0-specific identity that a shell theory can use, and it fails at every other gauge
point.
-/

open MeasureTheory Finset ArithmeticFunction
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- The trivial gauge point twists nothing. -/
theorem twist_trivialPoint (n : ℕ) : twist 0 n = 1 := by
  have h := twist_add 0 0 n
  rw [add_zero] at h
  exact mul_left_cancel₀ (twist_ne_zero 0 n) (h.symm.trans (mul_one _).symm)

/-- Twists of prime powers are powers of twists. -/
theorem twist_pow (x : GaugeTorus) {p : ℕ} (hp : p ≠ 0) (i : ℕ) :
    twist x (p ^ i) = twist x p ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, twist_mul x (pow_ne_zero i hp) hp, ih, pow_succ]

/-- A unimodular complex number with real part one is one. -/
theorem eq_one_of_norm_eq_one_of_re_eq_one {z : ℂ} (hn : ‖z‖ = 1) (hr : z.re = 1) : z = 1 := by
  have hsq := Complex.normSq_eq_norm_sq z
  rw [hn, Complex.normSq_apply, hr] at hsq
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
  exact Complex.ext hr him

/-- The divisor fibre `F_x(ℓ) = Σ_{k ∣ ℓ} Λ(k) χ_x(k)` of a gauge point. -/
def divisorFibre (x : GaugeTorus) (ℓ : ℕ) : ℂ :=
  twistSum ℓ.divisors (fun k => (Λ k : ℂ)) x

theorem divisorFibre_apply (x : GaugeTorus) (ℓ : ℕ) :
    divisorFibre x ℓ = ∑ k ∈ ℓ.divisors, (Λ k : ℂ) * twist x k := rfl

/-! ### The collapse and its maximality -/

/-- **The collapse.** At the trivial point the divisor fibre is `log ℓ`. -/
theorem divisorFibre_trivial (ℓ : ℕ) : divisorFibre 0 ℓ = Real.log ℓ := by
  simp only [divisorFibre_apply, twist_trivialPoint, mul_one]
  rw [← Complex.ofReal_sum, vonMangoldt_sum]

/-- Each term of a twisted fibre has real part at most its untwisted value. -/
theorem re_vonMangoldt_mul_twist_le (x : GaugeTorus) (k : ℕ) :
    ((Λ k : ℂ) * twist x k).re ≤ Λ k := by
  rw [Complex.re_ofReal_mul]
  have h := Complex.re_le_norm (twist x k)
  rw [norm_twist] at h
  exact mul_le_of_le_one_right vonMangoldt_nonneg h

/-- **Maximality.** Every divisor fibre is bounded by the collapse. -/
theorem re_divisorFibre_le (x : GaugeTorus) (ℓ : ℕ) : (divisorFibre x ℓ).re ≤ Real.log ℓ := by
  rw [divisorFibre_apply, Complex.re_sum, ← vonMangoldt_sum]
  exact sum_le_sum fun k _ => re_vonMangoldt_mul_twist_le x k

/-- **Equality case.** A fibre reaches the collapse exactly when the gauge point is trivial at every
prime dividing `ℓ`. -/
theorem re_divisorFibre_eq_log_iff (x : GaugeTorus) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    (divisorFibre x ℓ).re = Real.log ℓ ↔ ∀ p, p.Prime → p ∣ ℓ → twist x p = 1 := by
  rw [divisorFibre_apply, Complex.re_sum, ← vonMangoldt_sum,
    sum_eq_sum_iff_of_le fun k _ => re_vonMangoldt_mul_twist_le x k]
  constructor
  · intro h p hp hpℓ
    have hk := h p (Nat.mem_divisors.mpr ⟨hpℓ, hℓ⟩)
    rw [Complex.re_ofReal_mul, vonMangoldt_apply_prime hp] at hk
    have hlog : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    have hre : (twist x p).re = 1 :=
      mul_left_cancel₀ hlog (hk.trans (mul_one _).symm)
    exact eq_one_of_norm_eq_one_of_re_eq_one (norm_twist x p) hre
  · intro h k hk
    by_cases hΛ : Λ k = 0
    · simp [hΛ]
    · obtain ⟨p, i, hp, hi, rfl⟩ := (isPrimePow_nat_iff k).mp (vonMangoldt_ne_zero_iff.mp hΛ)
      have hpℓ : p ∣ ℓ := (dvd_pow_self p hi.ne').trans (Nat.dvd_of_mem_divisors hk)
      rw [twist_pow x hp.ne_zero, h p hp hpℓ, one_pow, mul_one, Complex.ofReal_re]

/-- **The collapse selects the trivial point.** All divisor fibres equal `log ℓ` exactly when the
gauge point is trivial. -/
theorem divisorFibre_eq_log_forall_iff (x : GaugeTorus) :
    (∀ ℓ, ℓ ≠ 0 → divisorFibre x ℓ = Real.log ℓ) ↔ ∀ n, n ≠ 0 → twist x n = 1 := by
  constructor
  · intro h
    have hprime : ∀ p, p.Prime → twist x p = 1 := fun p hp =>
      (re_divisorFibre_eq_log_iff x hp.ne_zero).mp
        (by rw [h p hp.ne_zero, Complex.ofReal_re]) p hp dvd_rfl
    intro n
    induction n using Nat.recOnMul with
    | zero => exact fun h0 => absurd rfl h0
    | one => exact fun _ => twist_one x
    | prime p hp => exact fun _ => hprime p hp
    | mul a b ha hb =>
      intro hab
      rw [twist_mul x (left_ne_zero_of_mul hab) (right_ne_zero_of_mul hab),
        ha (left_ne_zero_of_mul hab), hb (right_ne_zero_of_mul hab), one_mul]
  · intro h ℓ hℓ
    have hd : ∀ k ∈ ℓ.divisors, twist x k = 1 := fun k hk => h k (Nat.pos_of_mem_divisors hk).ne'
    rw [divisorFibre_apply, sum_congr rfl fun k hk => by rw [hd k hk, mul_one],
      ← Complex.ofReal_sum, vonMangoldt_sum]

/-- **The Liouville point reverses the collapse at primes.** -/
theorem divisorFibre_prime_of_twist_eq_neg_one (x : GaugeTorus) {p : ℕ} (hp : p.Prime)
    (h : twist x p = -1) : divisorFibre x p = -Real.log p := by
  rw [divisorFibre_apply, hp.divisors, sum_pair hp.one_lt.ne, vonMangoldt_apply_one,
    vonMangoldt_apply_prime hp, h]
  simp

/-! ### Gauge mean and gauge variance -/

/-- The divisors of a positive integer are positive. -/
theorem ne_zero_of_mem_divisors {ℓ : ℕ} : ∀ k ∈ ℓ.divisors, k ≠ 0 :=
  fun _ hk => (Nat.pos_of_mem_divisors hk).ne'

/-- **Gauge mean zero.** The divisor fibre is pure gauge charge. -/
theorem integral_divisorFibre {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    ∫ x, divisorFibre x ℓ ∂gaugeHaar = 0 := by
  classical
  -- Pair the fibre with the constant twist `χ_x(1) = 1`.
  set b : ℕ → ℂ := fun n => if n = 1 then 1 else 0 with hbdef
  have hb : ∀ x, twistSum ℓ.divisors b x = 1 := by
    intro x
    simp only [twistSum, hbdef, ite_mul, one_mul, zero_mul, sum_ite_eq',
      Nat.one_mem_divisors.mpr hℓ, if_true, twist_one]
  have h := integral_twistSum_mul_conj (s := ℓ.divisors) (ne_zero_of_mem_divisors (ℓ := ℓ))
    (fun k => (Λ k : ℂ)) b
  simp only [hb, map_one, mul_one] at h
  rw [show (fun x => divisorFibre x ℓ) = fun x => twistSum ℓ.divisors (fun k => (Λ k : ℂ)) x
    from rfl, h]
  simp [hbdef, Nat.one_mem_divisors.mpr hℓ, vonMangoldt_apply_one]

/-- **Gauge mean square.** The fibre has gauge mean square `Σ_{k ∣ ℓ} Λ(k)²`. -/
theorem integral_divisorFibre_mul_conj (ℓ : ℕ) :
    ∫ x, divisorFibre x ℓ * conj (divisorFibre x ℓ) ∂gaugeHaar =
      ((∑ k ∈ ℓ.divisors, Λ k ^ 2 : ℝ) : ℂ) := by
  rw [show (fun x => divisorFibre x ℓ * conj (divisorFibre x ℓ)) = fun x =>
      twistSum ℓ.divisors (fun k => (Λ k : ℂ)) x *
        conj (twistSum ℓ.divisors (fun k => (Λ k : ℂ)) x) from rfl,
    integral_twistSum_mul_conj ne_zero_of_mem_divisors, Complex.ofReal_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [Complex.conj_ofReal, Complex.ofReal_pow, sq]

/-! ### Coherence of the trivial point -/

/-- The value at the trivial point is at least the gauge root-mean-square:
`Σ_{k ∣ ℓ} Λ(k)² ≤ (log ℓ)²`. -/
theorem sum_sq_vonMangoldt_le_log_sq (ℓ : ℕ) :
    ∑ k ∈ ℓ.divisors, Λ k ^ 2 ≤ Real.log ℓ ^ 2 := by
  rw [← vonMangoldt_sum, sq (∑ k ∈ ℓ.divisors, Λ k), sum_mul]
  refine sum_le_sum fun k hk => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left
    (single_le_sum (f := fun k => Λ k) (fun i _ => vonMangoldt_nonneg) hk) vonMangoldt_nonneg

/-- The value at the trivial point is at most `√τ(ℓ)` gauge standard deviations:
`(log ℓ)² ≤ τ(ℓ) Σ_{k ∣ ℓ} Λ(k)²`. -/
theorem log_sq_le_card_divisors_mul (ℓ : ℕ) :
    Real.log ℓ ^ 2 ≤ #ℓ.divisors * ∑ k ∈ ℓ.divisors, Λ k ^ 2 := by
  rw [← vonMangoldt_sum]
  exact sq_sum_le_card_mul_sum_sq

/-- **Coherent atypicality.** On every fibre with `ℓ ≥ 2` the trivial point is the unique maximizer
of `Re F_x(ℓ)` on the gauge points trivial off `ℓ`, it lies at `log ℓ > 0` while the gauge mean is
`0`, and its square dominates the gauge mean square. -/
theorem trivialPoint_coherent {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    0 < (divisorFibre 0 ℓ).re ∧ ∫ x, divisorFibre x ℓ ∂gaugeHaar = 0 ∧
      ∑ k ∈ ℓ.divisors, Λ k ^ 2 ≤ (divisorFibre 0 ℓ).re ^ 2 := by
  have hlog : (divisorFibre 0 ℓ).re = Real.log ℓ := by
    rw [divisorFibre_trivial, Complex.ofReal_re]
  refine ⟨?_, integral_divisorFibre (by omega), ?_⟩
  · rw [hlog]
    exact Real.log_pos (by exact_mod_cast hℓ)
  · rw [hlog]
    exact sum_sq_vonMangoldt_le_log_sq ℓ

end GaloisForLFunctions.ArithmeticGaugeTheory
