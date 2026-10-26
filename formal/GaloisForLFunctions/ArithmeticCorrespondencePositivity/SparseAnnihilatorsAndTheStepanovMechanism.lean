import GaloisForLFunctions.HTGeometry.CharZeroShiftedSubgroupStepanov
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheLocalGeometryOfAReflectionPair

/-!
# Sparse annihilators and the Stepanov mechanism

Stepanov's proof of the Hasse–Weil bound builds an auxiliary polynomial that vanishes to high order
at every point of `C(𝔽_q)`. Its engine is a **sparse annihilator**: `X^q − X`, two monomials, kills
every element of `𝔽_q`, because the Frobenius spectrum lies on a lattice (`x^q = x`). This file
reads the mechanism on correspondences of `ℤ`, where the Hecke operator `T_p` acts at a zero `ρ` by
its symbol `p^{ρ − ½}`.

* **Sparse polynomials vanish to bounded order** (`rootMultiplicity_lt_card_support`): a nonzero
  polynomial with `K` monomials vanishes to order `< K` at every nonzero point, whatever its
  degree (HTGeometry, characteristic zero). A long correspondence with few terms cannot kill a
  zero symbol to high order.
* **What `1 − T_p^N` annihilates** (`heckeSymbol_pow_eq_one_iff`). The two-term correspondence
  `1 − T_p^N` kills the symbol of `ρ` iff `Re ρ = ½` and `N · Im ρ · log p ∈ 2πℤ`: exactly the
  critical points on a lattice of heights. It never kills an off-line symbol
  (`heckeSymbol_pow_ne_one_of_re_ne`), whose modulus is `p^{N(σ − ½)} ≠ 1`.

So the Stepanov mechanism requires a spectrum on a lattice. Over `𝔽_q` the Frobenius spectrum of
a curve has finite Kronecker rank and is annihilated by `X^N − c`-type sparse polynomials at the
arithmetic scales. The zero symbols of `ζ` at one prime would have to lie on one lattice of heights
for `1 − T_p^N` to annihilate them, and no sparse annihilator kills an off-line symbol at all. An
arithmetic Stepanov method over `ℤ` must therefore produce its auxiliary sections from a source
other than a lattice of the spectrum.
-/

open Complex Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- **Sparse polynomials vanish to bounded order** at nonzero points. -/
theorem rootMultiplicity_lt_card_support {P : ℂ[X]} (hP : P ≠ 0) {β : ℂ} (hβ : β ≠ 0) :
    P.rootMultiplicity β < P.support.card :=
  HTGeometry.ShiftedSubgroup.rootMultiplicity_lt_card_support_of_ne_zero hβ hP

/-- The `N`-th power of the Hecke symbol is the symbol of the `N`-th power. -/
theorem heckeSymbol_pow (p : ℝ) (s : ℂ) (N : ℕ) :
    heckeSymbol p s ^ N = Complex.exp (N * ((s - 1 / 2) * Real.log p)) := by
  rw [heckeSymbol, ← Complex.exp_nat_mul]

/-- **What `1 − T_p^N` annihilates**: the symbol of `ρ` is an `N`-th root of unity iff `ρ` is
critical and `N · Im ρ · log p ∈ 2πℤ`. -/
theorem heckeSymbol_pow_eq_one_iff {p : ℝ} (hp : 1 < p) {N : ℕ} (hN : 1 ≤ N) (ρ : ℂ) :
    heckeSymbol p ρ ^ N = 1 ↔
      ρ.re = 1 / 2 ∧ ∃ k : ℤ, (N : ℝ) * ρ.im * Real.log p = 2 * Real.pi * k := by
  have hl : 0 < Real.log p := Real.log_pos hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [heckeSymbol_pow, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    have hre := congrArg Complex.re hk
    have him := congrArg Complex.im hk
    simp [Complex.mul_re, Complex.mul_im] at hre him
    refine ⟨?_, k, ?_⟩
    · have : (N : ℝ) * ((ρ.re - 1 / 2) * Real.log p) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hN0.ne'
      · rcases mul_eq_zero.mp h with h' | h'
        · linarith
        · exact absurd h' hl.ne'
    · linarith
  · rintro ⟨hre, k, hk⟩
    refine ⟨k, ?_⟩
    apply Complex.ext
    · simp [Complex.mul_re, hre]
    · simp [Complex.mul_im]; linarith

/-- **No sparse root of unity kills an off-line symbol.** -/
theorem heckeSymbol_pow_ne_one_of_re_ne {p : ℝ} (hp : 1 < p) {N : ℕ} (hN : 1 ≤ N) {ρ : ℂ}
    (hρ : ρ.re ≠ 1 / 2) : heckeSymbol p ρ ^ N ≠ 1 :=
  fun h => hρ ((heckeSymbol_pow_eq_one_iff hp hN ρ).mp h).1

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
