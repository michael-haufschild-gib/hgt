import GaloisForLFunctions.HTGeometry.GomesFinitePolynomialTensorSector

/-!
# Polynomial amplitudes under exponential differentiation

A concrete real-polynomial specialization of exponential jet calculus. The logarithmic
connection acts by Q ↦ Q' + P' Q; iteration keeps every derivative of Q exp(P)
inside this polynomial-amplitude family. This supplies the missing derivative side of
the experimental tensor half-density construction inspired by the Gomes papers.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The polynomial amplitude after repeated differentiation of `Q exp(P)`. -/
def gomesPolynomialExpJet (P : ℝ[X]) : ℕ → ℝ[X] → ℝ[X]
  | 0, Q => Q
  | n + 1, Q => (gomesPolynomialExpJet P n Q).derivative +
      P.derivative * gomesPolynomialExpJet P n Q

/-- Exponential differentiation is the polynomial logarithmic connection. -/
theorem gomesPolynomialExp_hasDerivAt (P Q : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => Q.eval y * Real.exp (P.eval y))
      (((Q.derivative + P.derivative * Q).eval x) * Real.exp (P.eval x)) x := by
  have he : ((Q.derivative + P.derivative * Q).eval x) * Real.exp (P.eval x) =
      Q.derivative.eval x * Real.exp (P.eval x) +
        Q.eval x * (Real.exp (P.eval x) * P.derivative.eval x) := by
    simp only [eval_add, eval_mul]
    ring
  rw [he]
  exact (Q.hasDerivAt x).mul ((P.hasDerivAt x).exp)

/-- Every derivative has an exact polynomial amplitude, without regularity assumptions. -/
theorem gomesPolynomialExp_iteratedDeriv (P Q : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun x => Q.eval x * Real.exp (P.eval x)) =
      fun x => (gomesPolynomialExpJet P n Q).eval x * Real.exp (P.eval x) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, gomesPolynomialExpJet]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (gomesPolynomialExp_hasDerivAt P (gomesPolynomialExpJet P n Q) x).deriv

/-- The entire polynomial-amplitude family is smooth. -/
theorem gomesPolynomialExp_contDiff (P Q : ℝ[X]) :
    ContDiff ℝ ⊤ (fun x => Q.eval x * Real.exp (P.eval x)) := by
  have hP : ContDiff ℝ ⊤ (fun x : ℝ => P.eval x) := by
    simpa using (P.contDiff_aeval (𝕜 := ℝ) (n := ⊤))
  have hQ : ContDiff ℝ ⊤ (fun x : ℝ => Q.eval x) := by
    simpa using (Q.contDiff_aeval (𝕜 := ℝ) (n := ⊤))
  exact hQ.mul hP.exp

/-- Amplitude superposition commutes with every order of differentiation. -/
theorem gomesPolynomialExpJet_add (P Q R : ℝ[X]) (n : ℕ) :
    gomesPolynomialExpJet P n (Q + R) =
      gomesPolynomialExpJet P n Q + gomesPolynomialExpJet P n R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gomesPolynomialExpJet, ih, derivative_add, mul_add]; ring

/-- Constant amplitude rescaling commutes with every derivative. -/
theorem gomesPolynomialExpJet_scale (P Q : ℝ[X]) (c : ℝ) (n : ℕ) :
    gomesPolynomialExpJet P n (C c * Q) = C c * gomesPolynomialExpJet P n Q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [gomesPolynomialExpJet, ih, derivative_mul, derivative_C, zero_mul, zero_add]
    ring

/-- A constant log-density shift is invisible to the complete amplitude recurrence. -/
theorem gomesPolynomialExpJet_constant (P Q : ℝ[X]) (c : ℝ) (n : ℕ) :
    gomesPolynomialExpJet (P + C c) n Q = gomesPolynomialExpJet P n Q := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gomesPolynomialExpJet, ih, derivative_add, derivative_C, add_zero]

end GaloisForLFunctions.HTGeometry
