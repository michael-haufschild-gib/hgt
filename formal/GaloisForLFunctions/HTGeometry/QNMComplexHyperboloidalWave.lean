import GaloisForLFunctions.HTGeometry.QNMHyperboloidalCoordinates
import GaloisForLFunctions.HTGeometry.QNMTimeConvention

/-!
# Complex-frequency hyperboloidal wave residuals

The Bizoń--Mach coordinates in Al Sheikh--Jaramillo, arXiv:2607.25133,
equations (11)--(13), transport complex-frequency wave profiles to the compact
polynomial operator already formalized in `QNMHyperboloidalPolynomial`.
This extends the real-profile derivative infrastructure to actual complex waves.
Both time and space derivatives are with respect to real variables. The complete
wave residual is the evaluation of an explicit polynomial residual.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

/-- Spatial profile of a separated complex-frequency hyperboloidal wave. -/
def qnmComplexHyperboloidalProfile (z : ℂ) (P : Polynomial ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-z * qnmHyperboloidalHeight x) * P.eval (Real.tanh x : ℂ)

theorem hasDerivAt_qnmComplexHyperboloidalProfile (z : ℂ) (P : Polynomial ℂ) (x : ℝ) :
    HasDerivAt (qnmComplexHyperboloidalProfile z P)
      (qnmComplexHyperboloidalProfile z (qnmHyperboloidalDx z P) x) x := by
  have he := ((hasDerivAt_qnmHyperboloidalHeight x).ofReal_comp.const_mul (-z)).cexp
  have hp := (P.hasDerivAt (Real.tanh x : ℂ)).scomp x (qnm_hasDerivAt_tanh x).ofReal_comp
  apply (he.mul hp).congr_deriv
  simp [qnmComplexHyperboloidalProfile, qnmHyperboloidalDx, smul_eq_mul]
  ring

theorem deriv_qnmComplexHyperboloidalProfile (z : ℂ) (P : Polynomial ℂ) :
    deriv (qnmComplexHyperboloidalProfile z P) =
      qnmComplexHyperboloidalProfile z (qnmHyperboloidalDx z P) := by
  funext x
  exact (hasDerivAt_qnmComplexHyperboloidalProfile z P x).deriv

/-- The pulled-back separated wave, with physical time restored. -/
def qnmComplexHyperboloidalWave (z : ℂ) (P : Polynomial ℂ) (t x : ℝ) : ℂ :=
  Complex.exp (z * t) * qnmComplexHyperboloidalProfile z P x

theorem qnmComplexHyperboloidalWave_time_deriv (z : ℂ) (P : Polynomial ℂ) (x : ℝ) :
    deriv (fun t => qnmComplexHyperboloidalWave z P t x) =
      fun t => z * qnmComplexHyperboloidalWave z P t x := by
  funext t
  have he := (((hasDerivAt_id t).ofReal_comp.const_mul z).cexp).mul_const
    (qnmComplexHyperboloidalProfile z P x)
  convert! he.deriv using 1
  simp [qnmComplexHyperboloidalWave]
  ring

theorem qnmComplexHyperboloidalWave_space_deriv (z : ℂ) (P : Polynomial ℂ) (t : ℝ) :
    deriv (qnmComplexHyperboloidalWave z P t) =
      qnmComplexHyperboloidalWave z (qnmHyperboloidalDx z P) t := by
  funext x
  exact ((hasDerivAt_qnmComplexHyperboloidalProfile z P x).const_mul
    (Complex.exp (z * t))).deriv

/-- Exact reduction of the full wave operator for any complex polynomial potential. -/
theorem qnmComplexHyperboloidalWave_wave_residual (z : ℂ) (P V : Polynomial ℂ) (t x : ℝ) :
    deriv (deriv (fun u => qnmComplexHyperboloidalWave z P u x)) t -
        deriv (deriv (qnmComplexHyperboloidalWave z P t)) x +
        V.eval (Real.tanh x : ℂ) * qnmComplexHyperboloidalWave z P t x =
      qnmComplexHyperboloidalWave z
        ((C (z ^ 2) + V) * P - qnmHyperboloidalDx z (qnmHyperboloidalDx z P)) t x := by
  rw [qnmComplexHyperboloidalWave_time_deriv]
  rw [deriv_const_mul_field, qnmComplexHyperboloidalWave_time_deriv]
  rw [qnmComplexHyperboloidalWave_space_deriv, qnmComplexHyperboloidalWave_space_deriv]
  simp [qnmComplexHyperboloidalWave, qnmComplexHyperboloidalProfile]
  ring

end GaloisForLFunctions.HTGeometry
