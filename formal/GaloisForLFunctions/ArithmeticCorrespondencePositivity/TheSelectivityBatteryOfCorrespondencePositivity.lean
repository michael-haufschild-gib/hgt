import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheSpectrumOfSymmetricSquaresIsTheSign

/-!
# The selectivity battery of correspondence positivity

The battery of the corpus has two kinds of off-line zeros. **Real** off-line points `σ ≠ ½`
(the pole-order-two real stray `ζ(s)(s − β)(s − 1 + β)/(s(s − 1))`, the Siegel family
`ζ(s)/ζ(s + 1 − β)`, the golden datum's real Frobenius pair) and **non-real** ones (the refunded
complex quartet, the complex fake, and every off-line candidate of `ζ`). The invariants of ACP
separate them as follows.

* **Symmetric Hecke positivity on real even fibres** is blind to real points at every prime
  (`real_point_resonant_at_every_prime`): the symbol is real, so only the phase condition
  `Re z² ≥ 0` is imposed. It sees a non-real off-line point at every prime but at most one
  (`not_resonant_at_two_primes`).
* **Kernel counts** see real off-line pairs (golden: `deg(2 − F) = −1`) and are blind to complex
  quartets (complex fake): `KernelCountsAreBlindToComplexQuartets`.
* **The spectrum of symmetric squares** sees both at every prime: a real symbol `β ≠ ±1` gives the
  negative value `−(β − β⁻¹)²/4` at `c = (β + β⁻¹)/2` (`symSquare_neg_of_real`), a non-real symbol
  off the unit circle a non-real value (`symSquare_not_real_of_nonreal`).

So every invariant of the programme that is weaker than the spectral sign misses one class of the
battery, and the class `ζ` would need excluded — non-real off-line points — is exactly the one
missed by kernel counts and caught by Hecke positivity only through hyperbolicity.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- **Real points resonate at every prime**: their symmetric Hecke symbol is real. -/
theorem real_point_resonant_at_every_prime (p : ℝ) (σ : ℝ) :
    (symHeckeSymbol p (σ : ℂ)).im = 0 :=
  symHeckeSymbol_im_of_im_eq_zero p (Complex.ofReal_im σ)

/-- **The spectral sign sees a real symbol off the unit circle**: at `c = (β + β⁻¹)/2` the value
`(β − c)(β⁻¹ − c) = −(β − β⁻¹)²/4` is negative. -/
theorem symSquare_neg_of_real {β : ℝ} (hβ0 : β ≠ 0) (hβ : |β| ≠ 1) :
    ((β : ℂ) - ((β + β⁻¹) / 2 : ℝ)) * ((β : ℂ)⁻¹ - ((β + β⁻¹) / 2 : ℝ)) =
      ((-(β - β⁻¹) ^ 2 / 4 : ℝ) : ℂ) ∧ -(β - β⁻¹) ^ 2 / 4 < 0 := by
  refine ⟨by push_cast; field_simp; ring, ?_⟩
  have hne : β - β⁻¹ ≠ 0 := by
    intro h
    have : β * β = 1 := by
      have := congrArg (· * β) h
      simp only [sub_mul, inv_mul_cancel₀ hβ0, zero_mul] at this
      linarith
    apply hβ
    have hsq : |β| ^ 2 = 1 := by rw [sq_abs, sq]; exact this
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).mp hsq
  have := sq_pos_of_ne_zero hne
  linarith

/-- **The spectral sign sees a non-real symbol off the unit circle**: some `(β − c)(β⁻¹ − c)` is not
a nonnegative real. -/
theorem symSquare_not_real_of_nonreal {β : ℂ} (hβ : β ≠ 0) (hn : ‖β‖ ≠ 1) :
    ¬ ∀ c : ℝ, ∃ r : ℝ, 0 ≤ r ∧ (β - c) * (β⁻¹ - c) = r :=
  fun h => hn ((symSquare_local_nonneg_iff hβ).mp h)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
