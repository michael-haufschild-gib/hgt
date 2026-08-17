import GaloisForLFunctions.HTGeometry.BivariateDiagonalSymbol
import GaloisForLFunctions.HTGeometry.ShellCarrierExpansion

/-!
# The carrier approximant as a bivariate series

Each truncating polynomial of the carrier assembly is the value at `s = x²` of a polynomial in the
reciprocal spectral parameter whose coefficients are polynomials in `s`.  Keeping that bivariate
form makes the shell variable visible as a separate grading, which is what the classification of
the Poincaré coefficients needs.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

/-- Dividing off the outer variable commutes with a coefficient ring map. -/
theorem map_divX {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : Polynomial R) :
    (p.divX).map f = (p.map f).divX := by
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_divX, Polynomial.coeff_divX, Polynomial.coeff_map]

section Series

/-- Substituting the square of the shell variable for the inner variable. -/
def shellEval (x : ℝ) : Polynomial (Polynomial ℂ) →+* Polynomial ℂ :=
  Polynomial.mapRingHom (Polynomial.evalRingHom (((x : ℝ) : ℂ) ^ 2))

theorem shellEval_apply (x : ℝ) (F : Polynomial (Polynomial ℂ)) :
    shellEval x F = F.map (Polynomial.evalRingHom (((x : ℝ) : ℂ) ^ 2)) := rfl

theorem coeff_shellEval (x : ℝ) (F : Polynomial (Polynomial ℂ)) (j : ℕ) :
    (shellEval x F).coeff j = (F.coeff j).eval (((x : ℝ) : ℂ) ^ 2) := by
  rw [shellEval_apply, Polynomial.coeff_map]
  rfl

theorem shellEval_CC (x : ℝ) (c : ℂ) :
    shellEval x (Polynomial.C (Polynomial.C c)) = Polynomial.C c := by
  rw [shellEval_apply, Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C]

theorem shellEval_X_pow (x : ℝ) (k : ℕ) :
    shellEval x ((Polynomial.X : Polynomial (Polynomial ℂ)) ^ k) = Polynomial.X ^ k := by
  rw [shellEval_apply, Polynomial.map_pow, Polynomial.map_X]

/-- The truncated shell binomial series, in the reciprocal parameter and the squared shell
variable. -/
def shellBinomSeries (α : ℝ) (m : ℕ) : Polynomial (Polynomial ℂ) :=
  ∑ k ∈ Finset.range m,
    Polynomial.C (Polynomial.C ((cbinomCoeff α k : ℝ) : ℂ) * Polynomial.X ^ k)
      * Polynomial.X ^ (2 * k)

theorem shellEval_shellBinomSeries (α : ℝ) (m : ℕ) (x : ℝ) :
    shellEval x (shellBinomSeries α m) = shellBinomPoly α m x := by
  rw [shellBinomSeries, shellBinomPoly, shellEval_apply, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, ← pow_mul]

/-- The truncated root-defect series. -/
def shellDefectSeries (m : ℕ) : Polynomial (Polynomial ℂ) :=
  (shellBinomSeries ((1 : ℝ) / 2) (m + 1) - 1).divX

theorem shellEval_shellDefectSeries (m : ℕ) (x : ℝ) :
    shellEval x (shellDefectSeries m) = shellDefectPoly m x := by
  rw [shellDefectSeries, shellDefectPoly, shellEval_apply, map_divX, Polynomial.map_sub,
    Polynomial.map_one, ← shellEval_apply, shellEval_shellBinomSeries]

/-- The truncated series of the exponential factor. -/
def defectExpSeries (a : ℝ) (m : ℕ) : Polynomial (Polynomial ℂ) :=
  ∑ j ∈ Finset.range m, Polynomial.C (Polynomial.C (((Nat.factorial j : ℕ) : ℂ)⁻¹))
    * (Polynomial.C (Polynomial.C (-(a : ℂ))) * shellDefectSeries m) ^ j

theorem shellEval_defectExpSeries (a : ℝ) (m : ℕ) (x : ℝ) :
    shellEval x (defectExpSeries a m) = defectExpPoly a x m := by
  rw [defectExpSeries, defectExpPoly, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, map_mul, shellEval_CC, shellEval_CC, shellEval_shellDefectSeries]

/-- The truncated series of the Poincaré factor. -/
def shellPoincareSeries (a : ℝ) (n m : ℕ) : Polynomial (Polynomial ℂ) :=
  ∑ k ∈ Finset.range n,
    Polynomial.C (Polynomial.C (((besselK1Coeff k : ℝ) : ℂ) * ((a : ℂ)⁻¹) ^ k))
      * Polynomial.X ^ k * shellBinomSeries (-(k : ℝ) / 2) m

theorem shellEval_shellPoincareSeries (a : ℝ) (n m : ℕ) (x : ℝ) :
    shellEval x (shellPoincareSeries a n m) = shellPoincarePoly a x n m := by
  rw [shellPoincareSeries, shellPoincarePoly, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, shellEval_shellBinomSeries, shellEval_CC, shellEval_X_pow]

/-- The assembled carrier approximant as a bivariate series. -/
def carrierProductSeries (a : ℝ) (n m : ℕ) : Polynomial (Polynomial ℂ) :=
  Polynomial.C (Polynomial.C ((Real.sqrt 2 : ℝ) : ℂ)) * shellBinomSeries (-1 / 2) m
    * shellBinomSeries (-1 / 4) m * defectExpSeries a m * shellPoincareSeries a n m

/-- **The assembled approximant is the value of the bivariate series at the squared shell
variable.** -/
theorem shellEval_carrierProductSeries (a : ℝ) (n m : ℕ) (x : ℝ) :
    shellEval x (carrierProductSeries a n m) = carrierProductPoly a x n m := by
  rw [carrierProductSeries, carrierProductPoly, map_mul, map_mul, map_mul, map_mul,
    shellEval_shellBinomSeries, shellEval_shellBinomSeries, shellEval_defectExpSeries,
    shellEval_shellPoincareSeries, shellEval_CC]

end Series

end

end GaloisForLFunctions.HTGeometry
