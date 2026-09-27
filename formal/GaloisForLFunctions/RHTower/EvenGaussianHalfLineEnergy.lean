import GaloisForLFunctions.RHTower.PolynomialGaussianLocalConcentration
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Half-line energy of even polynomial Gaussians

Reflection gives exactly half the full energy on the positive half-line.
The existing coefficient-uniform pointwise bound controls the mass removed
by excluding a finite initial interval, including every polynomial cross term.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory
open GaloisForLFunctions
noncomputable section

namespace RHTower

/-- An even polynomial Gaussian has exactly half its squared norm on the positive half-line. -/
theorem evenPolynomialGaussian_halfLine_energy (P : Polynomial ℝ) :
    (∫ x : ℝ in Set.Ioi 0, ‖polyGaussSchwartz (evenSquarePolynomial P) x‖ ^ 2) =
      ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 / 2 := by
  let f := polyGaussSchwartz (evenSquarePolynomial P)
  have he (x : ℝ) : ‖f |x|‖ ^ 2 = ‖f x‖ ^ 2 := by
    simp only [f, polyGaussSchwartz_apply, evenSquarePolynomial, Polynomial.eval_comp,
      Polynomial.eval_pow, Polynomial.eval_X, gaussReal, sq_abs]
  have hh := integral_comp_abs (f := fun x : ℝ => ‖f x‖ ^ (2 : ℕ))
  simp_rw [he] at hh
  rw [← norm_toLp_sq_eq_integral] at hh
  change (∫ x : ℝ in Set.Ioi 0, ‖f x‖ ^ 2) = ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 / 2
  linarith only [hh]

/-- Removing an initial interval costs at most its length times the uniform Gaussian point bound. -/
theorem evenPolynomialGaussian_tail_energy_lower (P : Polynomial ℝ) (R : ℝ≥0) :
    (1 / 2 - 9 * (R : ℝ) * Real.sqrt ((2 * P.natDegree : ℕ) + 1)) *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      ∫ x : ℝ in Set.Ioi (R : ℝ), ‖polyGaussSchwartz (evenSquarePolynomial P) x‖ ^ 2 := by
  let Q := evenSquarePolynomial P
  let f := polyGaussSchwartz Q
  have hint : Integrable (fun x : ℝ => ‖f x‖ ^ (2 : ℕ)) :=
    (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mp
      (f.memLp 2 (volume : Measure ℝ))
  have hlocal := intervalIntegral.integral_mono_on (μ := (volume : Measure ℝ)) R.coe_nonneg
    (f := fun x : ℝ => ‖f x‖ ^ (2 : ℕ))
    (g := fun _ : ℝ => 9 * Real.sqrt (Q.natDegree + 1) *
      ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2)
    ((by fun_prop : Continuous (fun x : ℝ => ‖f x‖ ^ (2 : ℕ))).intervalIntegrable 0 R)
    intervalIntegrable_const (fun x _ => norm_polyGaussSchwartz_sq_le Q x)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hlocal
  have hsplit := intervalIntegral.integral_interval_add_Ioi (a := (0 : ℝ)) (b := (R : ℝ))
    hint.integrableOn hint.integrableOn
  have hhalf := evenPolynomialGaussian_halfLine_energy P
  change (∫ x : ℝ in Set.Ioi 0, ‖f x‖ ^ 2) = ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 / 2 at hhalf
  rw [hhalf] at hsplit
  have hd : Q.natDegree = 2 * P.natDegree := natDegree_evenSquarePolynomial P
  rw [hd] at hlocal
  change (1 / 2 - 9 * (R : ℝ) * Real.sqrt ((2 * P.natDegree : ℕ) + 1)) *
    ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤ ∫ x : ℝ in Set.Ioi (R : ℝ), ‖f x‖ ^ 2
  nlinarith only [hlocal, hsplit]

end RHTower
