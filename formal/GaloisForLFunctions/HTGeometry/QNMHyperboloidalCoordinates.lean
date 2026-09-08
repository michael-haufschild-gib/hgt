import GaloisForLFunctions.HTGeometry.QNMHyperboloidalPolynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# QNMHyperboloidalCoordinates

The Bizoń--Mach height log(2 cosh x) and compactification tanh x induce
the polynomial spatial operator of the optical QNM formulation. All derivative
identities are proved for the actual pulled-back profiles, with no regularity assumptions.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

theorem qnm_hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  convert! h using 1
  · funext y
    exact Real.tanh_eq_sinh_div_cosh y
  · rw [Real.tanh_eq_sinh_div_cosh]
    field_simp

def qnmHyperboloidalHeight (x : ℝ) : ℝ := Real.log (2 * Real.cosh x)

theorem hasDerivAt_qnmHyperboloidalHeight (x : ℝ) :
    HasDerivAt qnmHyperboloidalHeight (Real.tanh x) x := by
  have h := ((Real.hasDerivAt_cosh x).const_mul 2).log
    (mul_ne_zero two_ne_zero (Real.cosh_pos x).ne')
  apply h.congr_deriv
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

def qnmHyperboloidalProfile (z : ℝ) (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  Real.exp (-z * qnmHyperboloidalHeight x) * P.eval (Real.tanh x)

theorem hasDerivAt_qnmHyperboloidalProfile (z : ℝ) (P : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (qnmHyperboloidalProfile z P)
      (qnmHyperboloidalProfile z (qnmHyperboloidalDx z P) x) x := by
  have he := ((hasDerivAt_qnmHyperboloidalHeight x).const_mul (-z)).exp
  have hp := (P.hasDerivAt (Real.tanh x)).comp x (qnm_hasDerivAt_tanh x)
  apply (he.mul hp).congr_deriv
  simp [qnmHyperboloidalProfile, qnmHyperboloidalDx]
  ring

theorem deriv_qnmHyperboloidalProfile (z : ℝ) (P : Polynomial ℝ) :
    deriv (qnmHyperboloidalProfile z P) =
      qnmHyperboloidalProfile z (qnmHyperboloidalDx z P) := by
  funext x
  exact (hasDerivAt_qnmHyperboloidalProfile z P x).deriv

theorem deriv_two_qnmHyperboloidalProfile (z : ℝ) (P : Polynomial ℝ) :
    deriv (deriv (qnmHyperboloidalProfile z P)) =
      qnmHyperboloidalProfile z (qnmHyperboloidalDx z (qnmHyperboloidalDx z P)) := by
  rw [deriv_qnmHyperboloidalProfile, deriv_qnmHyperboloidalProfile]

end GaloisForLFunctions.HTGeometry
