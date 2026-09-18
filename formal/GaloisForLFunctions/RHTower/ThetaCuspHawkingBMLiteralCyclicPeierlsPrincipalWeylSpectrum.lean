import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinFullCuspSectorAssembly

/-!
Exact Weyl-spectrum audit for the two literal principal cusp faces left by
the cyclic Peierls cap substitution.  It rules out a decay-only disposal of
the B2 residual: on the critical line both faces occupy the same three
growing real-³⁄₄ channels, so any closure must be coefficientwise and
must retain the contact contribution.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsPrincipalWeylSpectrum

set_option autoImplicit false
noncomputable section

/-- Shift of the squared literal source at an original Xi parameter. -/
def sourceParameter (q : ℂ) : ℂ := q - 1 / 2

/-- Physical reader parameter fixed by the literal cutoff calibration. -/
def readerParameter (q : ℂ) : ℂ := (q - 1) / 2

/-- Weyl exponent of an ordered principal term in the cap angular flux,
after the reader's forced nonzero Weyl branch is selected. -/
def capWeylExponent (q : ℂ) (e₁ e₂ : Bool) : ℂ :=
  -1 + d4BMCompletedEisensteinCuspWeylExponent (sourceParameter q) e₁ +
    d4BMCompletedEisensteinCuspWeylExponent (sourceParameter q) e₂ +
    d4BMCompletedEisensteinCuspWeylExponent (readerParameter q) false

/-- Weyl exponent of the matching square-reader principal flux. -/
def squareReaderWeylExponent (q : ℂ) (e₁ e₂ : Bool) : ℂ :=
  d4BMCompletedEisensteinCuspWeylExponent (sourceParameter q) e₁ +
    d4BMCompletedEisensteinCuspWeylExponent (sourceParameter q) e₂ +
    (d4BMCompletedEisensteinCuspWeylExponent (readerParameter q) false - 1)

/-- The two literal principal residual faces have identical ordered Weyl
exponents.  Thus exponent mismatch cannot kill the cap term. -/
theorem squareReaderWeylExponent_eq_capWeylExponent (q : ℂ) (e₁ e₂ : Bool) :
    squareReaderWeylExponent q e₁ e₂ = capWeylExponent q e₁ e₂ := by
  unfold squareReaderWeylExponent capWeylExponent
  ring

/-- Double-minus source channel. -/
theorem capWeylExponent_false_false (q : ℂ) :
    capWeylExponent q false false = 2 - (5 / 2 : ℂ) * q := by
  simp [capWeylExponent, sourceParameter, readerParameter,
    d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign]
  ring

/-- Mixed source channels; the ordered pair has one common exponent. -/
theorem capWeylExponent_false_true (q : ℂ) :
    capWeylExponent q false true = 1 - q / 2 := by
  simp [capWeylExponent, sourceParameter, readerParameter,
    d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign]
  ring

theorem capWeylExponent_true_false (q : ℂ) :
    capWeylExponent q true false = 1 - q / 2 := by
  simp [capWeylExponent, sourceParameter, readerParameter,
    d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign]
  ring

/-- Double-plus source channel. -/
theorem capWeylExponent_true_true (q : ℂ) :
    capWeylExponent q true true = (3 / 2 : ℂ) * q := by
  simp [capWeylExponent, sourceParameter, readerParameter,
    d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign]
  ring

/-- All three distinct principal channels have real part `3/4` on the
critical line.  They are growing cusp modes, not a decaying remainder. -/
theorem capWeylExponent_re_eq_three_quarters (q : ℂ) (hq : q.re = 1 / 2)
    (e₁ e₂ : Bool) :
    (capWeylExponent q e₁ e₂).re = 3 / 4 := by
  cases e₁ <;> cases e₂
  · rw [capWeylExponent_false_false]
    norm_num [Complex.sub_re, Complex.mul_re, Complex.div_re]
    linarith
  · rw [capWeylExponent_false_true]
    norm_num [Complex.sub_re, Complex.div_re]
    linarith
  · rw [capWeylExponent_true_false]
    norm_num [Complex.sub_re, Complex.div_re]
    linarith
  · rw [capWeylExponent_true_true]
    norm_num [Complex.mul_re, Complex.div_re]
    linarith

end
end RHTower.D4BMLiteralCyclicPeierlsPrincipalWeylSpectrum
