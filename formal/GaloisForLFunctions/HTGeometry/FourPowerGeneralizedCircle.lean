import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Four powers on a generalized circle

A nonsingular Hermitian equation contains `1, a, a², a³` exactly when the nonzero
complex number `a` is real or has product one with its conjugate. The forward
implication is a four-node Vandermonde argument and includes repeated markings.
-/

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

/-- The four powers lie on one nonsingular generalized-circle equation. -/
def FourPowerGeneralizedCircle (a : ℂ) : Prop :=
  ∃ A D : ℝ, ∃ B : ℂ, B * conj B ≠ (A : ℂ) * (D : ℂ) ∧
    ∀ n : Fin 4, (A : ℂ) * a ^ (n : ℕ) * conj (a ^ (n : ℕ)) +
      B * a ^ (n : ℕ) + conj B * conj (a ^ (n : ℕ)) + (D : ℂ) = 0

private theorem fourPowerBases_injective {a : ℂ} (ha : a ≠ 0)
    (hr : a ≠ conj a) (hu : a * conj a ≠ 1) :
    Function.Injective (![a * conj a, a, conj a, 1] : Fin 4 → ℂ) := by
  have hc : conj a ≠ 0 := by simpa using ha
  have ha1 : a ≠ 1 := by intro h; apply hr; simp [h]
  have hc1 : conj a ≠ 1 := by
    intro h
    apply ha1
    simpa using congrArg conj h
  have hpa : a * conj a ≠ a := by
    intro h
    apply hc1
    exact mul_left_cancel₀ ha (by simpa using h)
  have hpc : a * conj a ≠ conj a := by
    intro h
    apply ha1
    exact mul_right_cancel₀ hc (by simpa using h)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Four consecutive powers lie on a circle or line precisely in the real or unit cases. -/
theorem fourPowerGeneralizedCircle_iff {a : ℂ} (ha : a ≠ 0) :
    FourPowerGeneralizedCircle a ↔ a = conj a ∨ a * conj a = 1 := by
  constructor
  · rintro ⟨A, D, B, hnonzero, hcircle⟩
    by_contra h
    push Not at h
    let f : Fin 4 → ℂ := ![a * conj a, a, conj a, 1]
    let v : Fin 4 → ℂ := ![(A : ℂ), B, conj B, (D : ℂ)]
    have hv : v = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (fourPowerBases_injective ha h.1 h.2) (by
        intro i
        have hi := hcircle i
        simpa [f, v, Fin.sum_univ_succ, mul_pow, map_pow, mul_assoc, add_assoc] using hi)
    have hA : A = 0 := by
      have := congrFun hv 0
      simpa [v] using this
    have hB : B = 0 := by
      have := congrFun hv 1
      simpa [v] using this
    have hD : D = 0 := by
      have := congrFun hv 3
      simpa [v] using this
    exact hnonzero (by simp [hA, hB, hD])
  · rintro (hr | hu)
    · refine ⟨0, 0, I, by simp, ?_⟩
      intro n
      simp only [Complex.ofReal_zero, zero_mul, zero_add, add_zero, map_pow, conj_I]
      rw [← hr]
      ring
    · refine ⟨1, -1, 0, by simp, ?_⟩
      intro n
      simp only [Complex.ofReal_one, Complex.ofReal_neg, map_zero, zero_mul,
        add_zero, one_mul, map_pow]
      rw [← mul_pow, hu]
      simp

end GaloisForLFunctions.HTGeometry
