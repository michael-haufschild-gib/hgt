import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Source-retaining conjugate reflection and exact recovery

The residual `A z - B conj z` must retain its source when comparing
reflection multipliers.  Its real-linear determinant is `|A|² - |B|²`.
An exact recovery identity, quantitative norm bounds, and the complete
injectivity classification hold for arbitrary coefficients and sources.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex
open scoped ComplexConjugate

noncomputable section

/-- The reflection residual before any source is divided out. -/
def conjugateReflectionResidual (A B z : ℂ) : ℂ := A * z - B * conj z

/-- Cleared-denominator recovery of the original complex source. -/
theorem conjugateReflectionResidual_recovery (A B z : ℂ) :
    conj A * conjugateReflectionResidual A B z +
      B * conj (conjugateReflectionResidual A B z) =
        ((Complex.normSq A - Complex.normSq B : ℝ) : ℂ) * z := by
  simp only [conjugateReflectionResidual, map_sub, map_mul, conj_conj,
    Complex.ofReal_sub, Complex.normSq_eq_conj_mul_self]
  ring

/-- The determinant also appears on two complementary kernel candidates. -/
theorem conjugateReflectionResidual_real_candidate (A B : ℂ) :
    conjugateReflectionResidual A B (conj A + B) =
      ((Complex.normSq A - Complex.normSq B : ℝ) : ℂ) := by
  simp only [conjugateReflectionResidual, map_add, conj_conj,
    Complex.ofReal_sub, Complex.normSq_eq_conj_mul_self]
  ring

theorem conjugateReflectionResidual_imag_candidate (A B : ℂ) :
    conjugateReflectionResidual A B (I * (conj A - B)) =
      I * ((Complex.normSq A - Complex.normSq B : ℝ) : ℂ) := by
  simp only [conjugateReflectionResidual, map_sub, map_mul, conj_I, conj_conj,
    Complex.ofReal_sub, Complex.normSq_eq_conj_mul_self]
  ring

/-- Reflection recovery is injective exactly when the two coefficient
moduli differ.  This classification includes zero coefficients. -/
theorem conjugateReflectionResidual_injective_iff (A B : ℂ) :
    Function.Injective (conjugateReflectionResidual A B) ↔
      Complex.normSq A ≠ Complex.normSq B := by
  constructor
  · intro hinj heq
    have hre : conj A + B = 0 := hinj (by
      rw [conjugateReflectionResidual_real_candidate, heq]
      simp [conjugateReflectionResidual])
    have him : I * (conj A - B) = 0 := hinj (by
      rw [conjugateReflectionResidual_imag_candidate, heq]
      simp [conjugateReflectionResidual])
    have hsub : conj A - B = 0 := (mul_eq_zero.mp him).resolve_left I_ne_zero
    have hAconj : conj A = 0 := by linear_combination (hre + hsub) / 2
    have hA : A = 0 := by simpa using congrArg conj hAconj
    have hB : B = 0 := by simpa [hA] using hre
    have hbad : (1 : ℂ) = 0 := hinj (by simp [conjugateReflectionResidual, hA, hB])
    exact one_ne_zero hbad
  · intro hnorm z w hzw
    have hdet : ((Complex.normSq A - Complex.normSq B : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hnorm)
    apply mul_left_cancel₀ hdet
    rw [← conjugateReflectionResidual_recovery A B z,
      ← conjugateReflectionResidual_recovery A B w, hzw]

/-- Modulus separation controls the residual only after multiplication by
the source norm.  A common zero remains a zero of every residual. -/
theorem conjugateReflectionResidual_norm_lower (A B z : ℂ) :
    |‖A‖ - ‖B‖| * ‖z‖ ≤ ‖conjugateReflectionResidual A B z‖ := by
  have h := abs_norm_sub_norm_le (A * z) (B * conj z)
  simpa only [conjugateReflectionResidual, norm_mul, Complex.norm_conj, ← sub_mul, abs_mul,
    abs_of_nonneg (norm_nonneg z)] using h

theorem conjugateReflectionResidual_norm_upper (A B z : ℂ) :
    ‖conjugateReflectionResidual A B z‖ ≤ (‖A‖ + ‖B‖) * ‖z‖ := by
  simpa only [conjugateReflectionResidual, norm_mul, Complex.norm_conj, add_mul]
    using norm_sub_le (A * z) (B * conj z)

/-- Complete cancellation classification: zero source, or exact phase
matching of the coefficients against that source. -/
theorem conjugateReflectionResidual_eq_zero_iff (A B z : ℂ) :
    conjugateReflectionResidual A B z = 0 ↔
      z = 0 ∨ (z ≠ 0 ∧ B = A * z / conj z) := by
  by_cases hz : z = 0
  · simp [hz, conjugateReflectionResidual]
  · have hc : conj z ≠ 0 := by simpa using hz
    unfold conjugateReflectionResidual
    constructor
    · intro h
      exact Or.inr ⟨hz, (eq_div_iff hc).mpr (sub_eq_zero.mp h).symm⟩
    · rintro (h | ⟨_, h⟩)
      · exact (hz h).elim
      · exact sub_eq_zero.mpr ((eq_div_iff hc).mp h).symm

end

end GaloisForLFunctions.HTGeometry
