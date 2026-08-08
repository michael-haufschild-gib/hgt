/-
The zero-generating function `−ζ'/ζ`, its weld-spectral frequencies, and the infinite-tail
necessity of the zeros.

The nontrivial zeros of `ζ` are the poles of the logarithmic derivative `−ζ'/ζ`, which on
`Re s > 1` is the von Mangoldt Dirichlet series `∑ Λ(n) n^{-s}` (mathlib's
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`).  Writing `n^{-s} = e^{-s·log n}`, the *frequencies*
of this series are the reals `log n` for which `Λ(n) ≠ 0` — i.e. `n` a prime power `p^k`, whence
`log n = k·log p`.  Every such frequency lies in the weld spectrum
`primeLogLattice = ⟨log p : p prime⟩` — the `ad(∂_s)`-spectrum of the archimedean–difference weld.

So the object whose poles are the zeta zeros is a Dirichlet series *all of whose frequencies are
weld rates*: the zero-generating function is welded to the `ad(∂_s)`-spectrum.  This is the exact
sense in which the zeros are dual to the weld's prime-log lattice.

A companion, purely local fact: every finite truncation of the Euler product is zero-free on the
open right half-plane `Re s > 0` (`euler_truncation_zerofree`).  Each factor `(1 − p^{-s})⁻¹` is a
unit there because `‖p^{-s}‖ = p^{-Re s} < 1`.  Hence no zero of `ζ` — on or off the critical line —
is produced by any finite set of primes; a zero is a phenomenon of the *whole* infinite tail.  Read
against the weld frequencies above, an off-line pole is therefore a resonance of the infinite prime
lattice, not of any finite algebraic sub-collection.
-/
import Mathlib
import GaloisForLFunctions.HTGeometry.WeldClassTable

open Complex

namespace GaloisForLFunctions.RHTower

/-! ### §1 The frequencies of the zero-generating function are weld rates -/

/-- **Every frequency of `−ζ'/ζ` lies in the weld spectrum.**  If the von Mangoldt value `Λ(n)` is
nonzero then `n = p^k` is a prime power and `log n = k·log p ∈ primeLogLattice`.  Since the
coefficients of the Dirichlet series `−ζ'/ζ(s) = ∑ Λ(n) n^{-s}` are exactly `Λ(n)`, its frequency
set `{log n : Λ(n) ≠ 0}` is contained in the `ad(∂_s)`-spectrum `⟨log p⟩`. -/
theorem vonMangoldt_freq_mem_primeLogLattice {n : ℕ}
    (h : ArithmeticFunction.vonMangoldt n ≠ 0) : Real.log n ∈ primeLogLattice := by
  obtain ⟨p, k, hp, hk, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h
  have hpp : p.Prime := Nat.prime_iff.mpr hp
  have hlp : Real.log (p : ℝ) ∈ primeLogLattice := primeLog_mem_primeLogLattice hpp
  have hcast : Real.log ((p ^ k : ℕ) : ℝ) = k • Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow, nsmul_eq_mul]
  rw [hcast]
  exact nsmul_mem hlp k

/-- **The zero-generating function is welded to the `ad(∂_s)`-spectrum.**  On `Re s > 1`, the
logarithmic derivative `−ζ'/ζ` equals the von Mangoldt Dirichlet series, and every frequency `log n`
occurring in that series (`Λ(n) ≠ 0`) is a weld rate.  The function whose poles are the zeta zeros is
thus a Dirichlet series supported on the weld's prime-log lattice. -/
theorem zeta_logDeriv_frequencies_weld {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s
        = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
      ∧ ∀ n : ℕ, ArithmeticFunction.vonMangoldt n ≠ 0 → Real.log n ∈ primeLogLattice :=
  ⟨(ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm,
    fun _ hn => vonMangoldt_freq_mem_primeLogLattice hn⟩

/-! ### §2 No finite set of primes produces a zero -/

/-- **Finite Euler truncations are zero-free on the right half-plane.**  For any finite set `S` of
primes and any `s` with `Re s > 0`, the partial Euler product `∏_{p∈S} (1 − p^{-s})⁻¹` is nonzero.
Each factor is a unit because `‖p^{-s}‖ = p^{-Re s} < 1` (as `p ≥ 2` and `Re s > 0`), so `p^{-s} ≠ 1`
and `1 − p^{-s} ≠ 0`.  Consequently every zero of `ζ` — on or off the critical line — requires the
full infinite product: no finite prime collection can create one. -/
theorem euler_truncation_zerofree (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {s : ℂ}
    (hs : 0 < s.re) : ∏ p ∈ S, (1 - (p : ℂ) ^ (-s))⁻¹ ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hp2 : 2 ≤ p := (hS p hp).two_le
  have hppos : 0 < p := by omega
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s).re := norm_natCast_cpow_of_pos hppos (-s)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp2
  have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [hnorm, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hne1 : (p : ℂ) ^ (-s) ≠ 1 := by
    intro h; rw [h, norm_one] at hlt; exact lt_irrefl 1 hlt
  have hsub : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := sub_ne_zero.mpr hne1.symm
  exact inv_ne_zero hsub

end GaloisForLFunctions.RHTower
