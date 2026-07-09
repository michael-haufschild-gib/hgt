/-
Vertical periodicity of zeros on the finite-prime sector of multiplicative Dirichlet data.

Fix a multiplicative arithmetic function `a` whose coefficient support consists of numbers
composed of finitely many primes `P`, absolutely summable at every point of the open right
half-plane `{0 < Re s}`. Then every zero of `LSeries a` in that half-plane lies on a full
two-sided vertical arithmetic progression of zeros.

The mechanism is Euler factorisation over the finite prime index set: multiplicativity turns
`LSeries a` into the finite product `∏_{p ∈ P} ∑'_k a(p^k)·(p^{-s})^k`, one column factor per
prime, obtained from the mathlib Euler product for a norm-summable multiplicative term function
with support restricted to the `P`-factored numbers. A zero of a finite product is a zero of some
column factor; each column depends on `s` only through the single exponential `p^{-s}`, which has
vertical period `2π/log p` (invariance of `p^{-s}` under `s ↦ s + k·(2π/log p)·i`). The shift is
purely imaginary, so it fixes `Re s`; summability and the factorisation therefore persist at every
point of the progression, and the vanishing column carries the zero along the whole progression.

No differential-algebraicity is assumed and the column series may have infinite support, so the
sector contains hypertranscendental members. The divisor's aperiodicity, where it occurs, is thus a
phenomenon of infinite prime support alone: finitely many column clocks can only produce clockwork
zeros, whatever the transcendence of the individual columns.
-/
import GaloisForLFunctions.RHTower.DAColumnDivisor
import GaloisForLFunctions.RHTower.PeriodicityDichotomy
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Exponential

noncomputable section

namespace RHTower

open Complex

/-- For a positive natural base `n`, raising the exponential `n^{-s}` to a natural power `k` is the
same as evaluating the exponential at the power base: `(n^{-s})^k = (n^k)^{-s}`. The identity is
unconditional because `n^{-s} = exp(log n · (−s))` with `log n` real, so natural powers merely scale
the exponent by `k`, matched by `log (n^k) = k · log n`. -/
private theorem natCast_cpow_neg_pow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (k : ℕ) :
    ((n : ℂ) ^ (-s)) ^ k = ((n ^ k : ℕ) : ℂ) ^ (-s) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℕ) < n from hn).ne'
  have hnk0 : ((n ^ k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero k (show n ≠ 0 by omega))
  have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (n : ℝ)), Complex.ofReal_natCast]
  have hlognk : Complex.log ((n ^ k : ℕ) : ℂ) = (k : ℂ) * Complex.log (n : ℂ) := by
    have h1 : Complex.log ((n ^ k : ℕ) : ℂ) = ((Real.log ((n ^ k : ℕ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_log (by positivity), Complex.ofReal_natCast]
    rw [h1, hlogn, show ((n ^ k : ℕ) : ℝ) = (n : ℝ) ^ k by push_cast; ring, Real.log_pow]
    push_cast; ring
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_nat_mul, Complex.cpow_def_of_ne_zero hnk0]
  congr 1
  rw [hlognk]; ring

/-- **Finite-prime Euler factorisation on the right half-plane.** If `a` is multiplicative, its
coefficient support lies in the `P`-factored numbers for a finite set `P` of primes, and its `L`-term
family is norm-summable throughout `{0 < Re s}`, then on that half-plane the `L`-series equals the
finite product over `P` of prime columns `∑'_k a(p^k)·(p^{-s})^k`. The identity is the mathlib Euler
product `EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers` for the multiplicative term
function `n ↦ a n · n^{-s}`: the product over the primes of `P` equals the sum over the `P`-factored
numbers, which is the whole `L`-series because the support is `P`-factored; each factor is rewritten
into the pure column variable `p^{-s}` via `(p^k)^{-s} = (p^{-s})^k`. -/
theorem finitePrime_lseries_factor {a : ArithmeticFunction ℂ} {P : Finset ℕ}
    (hmul : a.IsMultiplicative) (hP : ∀ p ∈ P, Nat.Prime p)
    (hsupp : ∀ n, a n ≠ 0 → n ∈ Nat.factoredNumbers P)
    (hsum : ∀ s : ℂ, 0 < s.re → Summable (fun n => ‖LSeries.term (fun n => a n) s n‖)) :
    ∀ s : ℂ, 0 < s.re →
      LSeries (fun n => a n) s = ∏ p ∈ P, ∑' k : ℕ, a (p ^ k) * ((p : ℂ) ^ (-s)) ^ k := by
  intro s hs
  set f : ℕ → ℂ := LSeries.term (fun n => a n) s with hf
  have hterm : ∀ m, f m = a m * ((m : ℂ) ^ (-s)) := by
    intro m; rw [hf, LSeries.term_def₀ (by simp) s]
  have hf1 : f 1 = 1 := by rw [hterm]; simp [hmul.map_one]
  have hfmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hcop
    simp only [hterm]
    rw [hmul.map_mul_of_coprime hcop, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]; ring
  have hsummable : Summable (fun x => ‖f x‖) := hsum s hs
  have hEP := EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers hf1 hfmul hsummable P
  have hsub : Function.support f ⊆ Nat.factoredNumbers P := by
    intro n hn
    rw [Function.mem_support] at hn
    have hane : a n ≠ 0 := by intro h; apply hn; rw [hterm, h]; simp
    exact hsupp n hane
  have hfilter : Finset.filter Nat.Prime P = P := Finset.filter_true_of_mem hP
  rw [show LSeries (fun n => a n) s = ∑' n, f n from rfl,
      ← tsum_subtype_eq_of_support_subset hsub, ← hEP, hfilter]
  apply Finset.prod_congr rfl
  intro p hp
  apply tsum_congr
  intro k
  rw [hterm, natCast_cpow_neg_pow p (hP p hp).pos s k]

/-- **Column shift invariance with infinite support.** A prime column `∑'_e a(p^e)·(p^{-s})^e` is
invariant under the vertical shift `s ↦ s + k·(2π/log p)·i`, for every integer `k` and any base
`2 ≤ p`. The invariance is termwise: `p^{-s}` has period `2π/log p`, so `(p^{-s})^e` is unchanged and
the two term families are literally equal — no convergence argument is needed and the support may be
infinite. -/
theorem finitePrime_column_shift_invariant {a : ArithmeticFunction ℂ} {p : ℕ} (hp : 2 ≤ p)
    (s : ℂ) (k : ℤ) :
    ∑' e : ℕ, a (p ^ e) * ((p : ℂ) ^ (-(s + (k * (2 * Real.pi / Real.log p)) * Complex.I))) ^ e
      = ∑' e : ℕ, a (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
  apply tsum_congr
  intro e
  rw [exp_shift_invariant hp s k]

/-- **Zeros on the finite-prime sector are vertically periodic.** If `a` is multiplicative with
`P`-factored support and half-plane-summable `L`-terms, then every zero `s₀` of `LSeries a` with
`0 < Re s₀` sits on a full two-sided vertical arithmetic progression of zeros of real period
`T = 2π/log p > 0`, for a prime `p ∈ P` responsible for the zero.

Factoring at `s₀` and applying `Finset.prod_eq_zero_iff` selects a vanishing column `p`. The shift by
`k·T·i` is purely imaginary, so it preserves the real part; positivity of `Re` persists, the
factorisation applies at the shifted point, and the `p`-column there equals its value at `s₀` by
shift invariance, so the product vanishes along the whole progression. -/
theorem finitePrime_zero_periodic {a : ArithmeticFunction ℂ} {P : Finset ℕ}
    (hmul : a.IsMultiplicative) (hP : ∀ p ∈ P, Nat.Prime p)
    (hsupp : ∀ n, a n ≠ 0 → n ∈ Nat.factoredNumbers P)
    (hsum : ∀ s : ℂ, 0 < s.re → Summable (fun n => ‖LSeries.term (fun n => a n) s n‖))
    {s₀ : ℂ} (hs₀ : 0 < s₀.re) (h0 : LSeries (fun n => a n) s₀ = 0) :
    ∃ T : ℝ, 0 < T ∧ ∀ k : ℤ, LSeries (fun n => a n) (s₀ + (k * T) * Complex.I) = 0 := by
  have hfac0 := finitePrime_lseries_factor hmul hP hsupp hsum s₀ hs₀
  rw [h0] at hfac0
  obtain ⟨p, hp, hpcol⟩ := (Finset.prod_eq_zero_iff).mp hfac0.symm
  have hp2 : 2 ≤ p := (hP p hp).two_le
  refine ⟨2 * Real.pi / Real.log p, ?_, ?_⟩
  · apply div_pos (by have := Real.pi_pos; linarith)
    exact Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  · intro k
    have hTc : ((2 * Real.pi / Real.log p : ℝ) : ℂ)
        = 2 * (Real.pi : ℂ) / (Real.log p : ℂ) := by push_cast; ring
    have hre : (s₀ + (↑k * ↑(2 * Real.pi / Real.log p)) * Complex.I).re = s₀.re := by
      simp only [Complex.add_re, Complex.mul_I_re, Complex.mul_im, Complex.intCast_im,
        Complex.ofReal_im, Complex.intCast_re, Complex.ofReal_re, mul_zero, zero_mul, add_zero,
        neg_zero]
    rw [finitePrime_lseries_factor hmul hP hsupp hsum _ (by rw [hre]; exact hs₀)]
    apply Finset.prod_eq_zero hp
    rw [hTc, finitePrime_column_shift_invariant hp2 s₀ k]
    exact hpcol

/-- **The finite-prime sector satisfies the periodicity dichotomy.** If a datum `f` agrees with
`LSeries a` throughout the open critical strip `0 < Re s < 1`, where `a` is multiplicative with
`P`-factored support and half-plane-summable `L`-terms, then `f` satisfies the vertical periodicity
dichotomy — always through the right disjunct: every strip zero rides a full vertical progression.

A strip zero of `f` transfers to `LSeries a` at the same point (agreement on the strip); the
progression of that zero has purely imaginary shifts, hence stays at the same real part and thus
inside the strip, so each progression point transfers back to a zero of `f`. The critical-line clause
is never needed. -/
theorem finitePrime_periodicityDichotomy {a : ArithmeticFunction ℂ} {P : Finset ℕ}
    (hmul : a.IsMultiplicative) (hP : ∀ p ∈ P, Nat.Prime p)
    (hsupp : ∀ n, a n ≠ 0 → n ∈ Nat.factoredNumbers P)
    (hsum : ∀ s : ℂ, 0 < s.re → Summable (fun n => ‖LSeries.term (fun n => a n) s n‖))
    {f : ℂ → ℂ}
    (hrep : ∀ s : ℂ, 0 < s.re → s.re < 1 → f s = LSeries (fun n => a n) s) :
    PeriodicityDichotomy f := by
  intro ρ hpos hlt1 h0
  refine Or.inr ?_
  have hLρ : LSeries (fun n => a n) ρ = 0 := by rw [← hrep ρ hpos hlt1]; exact h0
  obtain ⟨T, hT, hprog⟩ := finitePrime_zero_periodic hmul hP hsupp hsum hpos hLρ
  refine ⟨T, hT, fun k => ?_⟩
  have hre : (ρ + (↑k * ↑T) * Complex.I).re = ρ.re := by
    simp only [Complex.add_re, Complex.mul_I_re, Complex.mul_im, Complex.intCast_im,
      Complex.ofReal_im, Complex.intCast_re, Complex.ofReal_re, mul_zero, zero_mul, add_zero,
      neg_zero]
  rw [hrep _ (by rw [hre]; exact hpos) (by rw [hre]; exact hlt1)]
  exact hprog k

end RHTower
