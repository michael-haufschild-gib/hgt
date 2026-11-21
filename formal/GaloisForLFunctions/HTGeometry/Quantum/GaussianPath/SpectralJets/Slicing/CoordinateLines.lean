import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.RealDerivatives
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Affine parameterization and differentiation of a single coupling line -/

open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {n : ℕ}

/-- Polynomial parameterization of the line that varies coupling i. -/
def coordinatePolynomials (x : Fin n → ℝ) (i : Fin n) : Fin n → Polynomial ℂ :=
  Function.update (fun j => Polynomial.C (x j : ℂ)) i Polynomial.X

theorem coordinatePolynomials_degree (x : Fin n → ℝ) (i j : Fin n) :
    (coordinatePolynomials x i j).natDegree ≤ 1 := by
  by_cases hj : j=i
  · subst j; simp [coordinatePolynomials]
  · simp [coordinatePolynomials,Function.update_of_ne hj]

theorem coordinatePolynomials_eval (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    (fun j => (coordinatePolynomials x i j).eval (t:ℂ)) = realEmbed (Function.update x i t) := by
  funext j
  by_cases hj : j=i
  · subst j; simp [coordinatePolynomials,realEmbed]
  · simp [coordinatePolynomials,realEmbed,Function.update_of_ne hj]

theorem differentiable_updateLine (x : Fin n → ℝ) (i : Fin n) :
    Differentiable ℝ (Function.update x i) := by
  intro t
  apply differentiableAt_pi.mpr
  intro j
  by_cases hj : j=i
  · subst j
    simp only [Function.update_self]
    fun_prop
  · simpa only [Function.update_of_ne hj] using (differentiableAt_const (c := x j))

private theorem realLine_update (x : Fin n → ℝ) (i : Fin n) (t u : ℝ) :
    realLine (Function.update x i t) i u = Function.update x i (t+u) := by
  funext j
  by_cases hj : j=i
  · subst j; simp [realLine]
  · simp [realLine,hj,Function.update_of_ne]

/-- Translating the line parameter identifies its ordinary derivative with
the next mixed derivative. -/
theorem deriv_realMixed_update (g : (Fin n → ℝ) → ℝ) (w : List (Fin n)) (x : Fin n → ℝ)
    (i : Fin n) (t : ℝ) : deriv (fun u => realMixed w g (Function.update x i u)) t =
      realMixed (i::w) g (Function.update x i t) := by
  change _ = deriv (fun u => realMixed w g (realLine (Function.update x i t) i u)) 0
  simp only [realLine_update]
  symm
  simpa only [add_zero] using deriv_comp_const_add (fun u => realMixed w g (Function.update x i u)) t 0

#print axioms deriv_realMixed_update
end
end GaloisForLFunctions.HTGeometry.SpectralJets
