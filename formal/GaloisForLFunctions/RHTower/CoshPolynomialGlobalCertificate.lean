import GaloisForLFunctions.RHTower.CoshPolynomialExactOrderOne

/-!
# Global certificate for polynomially weighted quartet envelopes

This module assembles the analytic, symmetry, positivity, period, and growth components of the
finite quartet-passport construction.  Once a polynomial is even, Schwarz-real, positive on the
imaginary axis, and nonconstant, multiplying it by a nontrivially displaced cosh quartet envelope
automatically gives an entire Xi-shaped function with trivial period group and exact order-one
growth.

The theorem is deliberately stated in terms of concrete polynomial identities rather than a bundled
property interface, so the equivariant CRT and positive-repair theorems can discharge its inputs
directly.
-/

open Complex Polynomial

namespace RHTower

/-- Polynomially weighted cosh quartet envelope. -/
noncomputable def polynomialXiEnvelope (a : ℝ) (P : Polynomial ℂ) (z : ℂ) : ℂ :=
  coshQuartetEnvelope a z * P.eval z

/-- **Global polynomial-envelope certificate.** Concrete polynomial symmetry and positivity data
produce one entire, real-even, Schwarz-real, imaginary-axis-positive, aperiodic exact-order-one
function. -/
theorem polynomialXiEnvelope_global_certificate
    (a : ℝ) (ha : a ≠ 0) (P : Polynomial ℂ) (hdegree : 0 < P.degree)
    (hPeven : ∀ z, P.eval (-z) = P.eval z)
    (hPconj : ∀ z, P.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.eval z))
    (hPpos : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ P.eval ((y : ℂ) * I) = (r : ℂ)) :
    (∀ z, AnalyticAt ℂ (polynomialXiEnvelope a P) z) ∧
    (∀ z, polynomialXiEnvelope a P (-z) = polynomialXiEnvelope a P z) ∧
    (∀ z, polynomialXiEnvelope a P ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (polynomialXiEnvelope a P z)) ∧
    (∀ y : ℝ, ∃ r : ℝ, 0 < r ∧
      polynomialXiEnvelope a P ((y : ℂ) * I) = (r : ℂ)) ∧
    (∀ h, Function.Periodic (polynomialXiEnvelope a P) h ↔ h = 0) ∧
    ∃ Kupper Klower R : ℝ,
      0 < Kupper ∧ 0 < Klower ∧
      (∀ z : ℂ, ‖polynomialXiEnvelope a P z‖ ≤
        Kupper * (1 + ‖z‖) ^ P.natDegree * Real.exp (2 * ‖z‖)) ∧
      ∀ x : ℝ, R ≤ x → Klower * Real.exp (2 * x) ≤
        ‖polynomialXiEnvelope a P (x : ℂ)‖ := by
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    simp at hdegree
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact (coshQuartetEnvelope_analyticAt a z).mul
      P.differentiable.contDiff.contDiffAt.analyticAt
  · intro z
    simp only [polynomialXiEnvelope, coshQuartetEnvelope_neg, hPeven]
  · intro z
    rw [polynomialXiEnvelope, polynomialXiEnvelope,
      coshQuartetEnvelope_conj, hPconj, map_mul]
  · intro y
    obtain ⟨rA, hrA, hA⟩ := coshQuartetEnvelope_mul_I_pos_real ha
    obtain ⟨rP, hrP, hP⟩ := hPpos y
    refine ⟨rA * rP, mul_pos hrA hrP, ?_⟩
    rw [polynomialXiEnvelope, hA, hP]
    norm_cast
  · intro h
    have hfun :
        polynomialXiEnvelope a P =
          (fun z => coshQuartetEnvelope a z * P.eval z) := by
      funext z
      rfl
    rw [hfun]
    exact coshQuartetEnvelope_mul_polynomial_periodic_iff a ha P hdegree h
  · simpa only [polynomialXiEnvelope] using
      coshQuartetEnvelope_mul_polynomial_exact_order_one_bounds a hPne

end RHTower
