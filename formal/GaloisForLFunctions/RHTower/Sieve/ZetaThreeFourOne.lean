import GaloisForLFunctions.RHTower.Sieve.ZetaLogPrimeSum
import Mathlib.NumberTheory.ZetaValues

/-!
# The three-four-one inequality for the prime sums of zeta

The real part of a prime power is `p^{-σ} cos(t log p)`, so the combination that Mertens' device
produces,

`3 + 4cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`,

makes the weighted sum of three prime sums nonnegative:

`0 ≤ 3 ∑'_p Re(p^{-σ}) + 4 ∑'_p Re(p^{-σ-it}) + ∑'_p Re(p^{-σ-2it})`.

This is the classical inequality behind the zero-free region, here as a statement about the prime
sums themselves; combined with the bridge to `log‖ζ‖` it becomes the inequality on
`|ζ(σ)³ζ(σ+it)⁴ζ(σ+2it)|`.
-/

namespace RHTower.Sieve

open Complex

/-- **The real part of a prime power.** -/
theorem re_prime_cpow_neg {p : ℕ} (hp : 0 < p) (s : ℂ) :
    (((p : ℕ) : ℂ) ^ (-s)).re
      = Real.exp (-(Real.log p) * s.re) * Real.cos (Real.log p * s.im) := by
  have hne : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hlog : Complex.log ((p : ℕ) : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]
  rw [Complex.cpow_def_of_ne_zero hne, Complex.exp_re, hlog]
  have hre : (((Real.log p : ℝ) : ℂ) * -s).re = -(Real.log p) * s.re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
    ring
  have him : (((Real.log p : ℝ) : ℂ) * -s).im = -(Real.log p * s.im) := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
    ring
  rw [hre, him, Real.cos_neg]

/-- The three-four-one weight of a prime, at a shifted frequency, is nonnegative. -/
theorem zero_le_three_four_one_term {p : ℕ} (hp : 0 < p) {σ t : ℝ} :
    0 ≤ 3 * (((p : ℕ) : ℂ) ^ (-((σ : ℂ)))).re
      + 4 * (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re
      + (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (2 * t : ℂ) * Complex.I))).re := by
  rw [re_prime_cpow_neg hp, re_prime_cpow_neg hp, re_prime_cpow_neg hp]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num
  have hkey : 3 + 4 * Real.cos (Real.log p * t) + Real.cos (2 * (Real.log p * t))
      = 2 * (1 + Real.cos (Real.log p * t)) ^ 2 := by
    rw [Real.cos_two_mul]
    ring
  have hrw : Real.log p * (2 * t) = 2 * (Real.log p * t) := by ring
  rw [hrw]
  have hfactor : 3 * Real.exp (-(Real.log p * σ))
      + 4 * (Real.exp (-(Real.log p * σ)) * Real.cos (Real.log p * t))
      + Real.exp (-(Real.log p * σ)) * Real.cos (2 * (Real.log p * t))
      = Real.exp (-(Real.log p * σ))
        * (3 + 4 * Real.cos (Real.log p * t) + Real.cos (2 * (Real.log p * t))) := by ring
  rw [hfactor, hkey]
  positivity

/-- The real parts of the prime powers are summable. -/
theorem summable_prime_cpow_re {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => (((p : ℕ) : ℂ) ^ (-s)).re) := by
  have h := (summable_prime_cpow hs).map Complex.reAddGroupHom Complex.continuous_re
  exact h

/-- **The three-four-one inequality for the prime sums.** -/
theorem zero_le_three_four_one_tsum {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ)))).re)
      + 4 * (∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re)
      + (∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (2 * t : ℂ) * Complex.I))).re) := by
  have hre0 : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
  have hre1 : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have hre2 : ((σ : ℂ) + (2 * t : ℂ) * Complex.I).re = σ := by simp
  have h0 : Summable (fun p : Nat.Primes => (((p : ℕ) : ℂ) ^ (-((σ : ℂ)))).re) :=
    summable_prime_cpow_re (by rw [hre0]; exact hσ)
  have h1 : Summable
      (fun p : Nat.Primes => (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re) :=
    summable_prime_cpow_re (by rw [hre1]; exact hσ)
  have h2 : Summable
      (fun p : Nat.Primes => (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (2 * t : ℂ) * Complex.I))).re) :=
    summable_prime_cpow_re (by rw [hre2]; exact hσ)
  have hcomb : 3 * (∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ)))).re)
      + 4 * (∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re)
      + (∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (2 * t : ℂ) * Complex.I))).re)
      = ∑' p : Nat.Primes,
          (3 * (((p : ℕ) : ℂ) ^ (-((σ : ℂ)))).re
            + 4 * (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re
            + (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (2 * t : ℂ) * Complex.I))).re) := by
    rw [((h0.mul_left 3).add (h1.mul_left 4)).tsum_add h2,
      (h0.mul_left 3).tsum_add (h1.mul_left 4), h0.tsum_mul_left, h1.tsum_mul_left]
  rw [hcomb]
  refine tsum_nonneg fun p => ?_
  exact zero_le_three_four_one_term p.2.pos

/-- The squared-norm sum depends only on the real part. -/
theorem tsum_norm_sq_eq {s : ℂ} :
    (∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2)
      = ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * s.re)) :=
  tsum_congr fun p => norm_prime_cpow_sq_eq p.2.pos s

/-- **The three-four-one inequality for zeta.**  With `E = ∑'_p p^{-2σ}`, which is under `1`,

`3 log‖ζ(σ)‖ + 4 log‖ζ(σ+it)‖ + log‖ζ(σ+2it)‖ ≥ −8E`.

This is the classical inequality forcing a zero-free region, with an explicit constant and uniform
in the frequency. -/
theorem three_four_one_log_zeta {σ t : ℝ} (hσ : 1 < σ) :
    -(8 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ)))
      ≤ 3 * Real.log ‖riemannZeta (σ : ℂ)‖
        + 4 * Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        + Real.log ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ := by
  have hre0 : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
  have hre1 : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have hre2 : ((σ : ℂ) + (2 * t : ℂ) * Complex.I).re = σ := by simp
  have key : ∀ s : ℂ, s.re = σ →
      ∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-s)).re
        - (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ)))
      ≤ Real.log ‖riemannZeta s‖ := by
    intro s hs
    have hbridge := abs_log_norm_riemannZeta_sub_tsum_re_le (s := s) (by rw [hs]; exact hσ)
    have hsum : (∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2)
        = ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
      rw [tsum_norm_sq_eq, hs]
    rw [hsum] at hbridge
    have := (abs_le.1 hbridge).1
    linarith
  have h0 := key ((σ : ℂ)) hre0
  have h1 := key ((σ : ℂ) + (t : ℂ) * Complex.I) hre1
  have h2 := key ((σ : ℂ) + (2 * t : ℂ) * Complex.I) hre2
  have hsum := zero_le_three_four_one_tsum (σ := σ) (t := t) hσ
  linarith

/-- The prime tail of the `2σ`-series is at most `ζ(2)`. -/
theorem tsum_prime_rpow_le {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ))) ≤ Real.pi ^ 2 / 6 := by
  have hzeta : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hgsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hzeta.summable
  have hterm : ∀ p : Nat.Primes,
      ((p : ℕ) : ℝ) ^ (-(2 * σ)) ≤ (1 : ℝ) / (((p : ℕ) : ℕ) : ℝ) ^ 2 := by
    intro p
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have hbase : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by linarith
    have hexp : -(2 * σ) ≤ -2 := by linarith
    have hmono : ((p : ℕ) : ℝ) ^ (-(2 * σ)) ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase hexp
    have hval : ((p : ℕ) : ℝ) ^ (-2 : ℝ) = 1 / ((p : ℕ) : ℝ) ^ 2 := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith),
        Real.rpow_natCast]
      exact (one_div _).symm
    rw [hval] at hmono
    exact hmono
  have hfsum : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * σ))) := by
    have : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * σ))) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact this.comp_injective Nat.Primes.coe_nat_injective
  refine le_trans (Summable.tsum_le_tsum hterm hfsum
    (hgsum.comp_injective Nat.Primes.coe_nat_injective)) ?_
  have hsub : (∑' p : Nat.Primes, (1 : ℝ) / (((p : ℕ) : ℕ) : ℝ) ^ 2)
      ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
    exact (hgsum.comp_injective Nat.Primes.coe_nat_injective).tsum_le_tsum_of_inj
      (fun p : Nat.Primes => (p : ℕ)) Nat.Primes.coe_nat_injective
      (fun c _ => by positivity) (fun p => le_rfl) hgsum
  rw [hzeta.tsum_eq] at hsub
  exact hsub

/-- **The three-four-one inequality with a numeric constant.** -/
theorem three_four_one_log_zeta_const {σ t : ℝ} (hσ : 1 < σ) :
    -22 ≤ 3 * Real.log ‖riemannZeta (σ : ℂ)‖
        + 4 * Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        + Real.log ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ := by
  have hbase := three_four_one_log_zeta (σ := σ) (t := t) hσ
  have hE := tsum_prime_rpow_le (le_of_lt hσ)
  have hpi : Real.pi ^ 2 / 6 ≤ 8 / 3 := by
    have h := Real.pi_le_four
    nlinarith [Real.pi_pos, h]
  linarith

/-- **The usable form.**  Upper bounds at `σ` and at `σ + 2it` give a lower bound at `σ + it`.
This is the shape a zero-free region argument consumes: the pole at `σ → 1⁺` supplies `A`, and a
growth estimate in the strip supplies `B`. -/
theorem log_norm_zeta_shift_ge {σ t A B : ℝ} (hσ : 1 < σ)
    (hA : Real.log ‖riemannZeta (σ : ℂ)‖ ≤ A)
    (hB : Real.log ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ B) :
    (-22 - 3 * A - B) / 4
      ≤ Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hbase := three_four_one_log_zeta_const (σ := σ) (t := t) hσ
  linarith

end RHTower.Sieve
