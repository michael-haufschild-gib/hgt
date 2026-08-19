/-
# The criticality expression as a polynomial in the auxiliary variable

The criticality criterion produces, for each coordinate direction, an expression polynomial in the
coordinates and in the unknown action value.  Squaring and summing over the directions gives a
single such polynomial which vanishes exactly where every direction is critical, and which is the
input the symmetrisation over labellings consumes.

Main results:
* `criticalityPoly`, `criticalitySquareSum` — the criticality polynomial and its square sum.
* `eval_map_criticalityPoly`, `eval_map_criticalitySquareSum` — their evaluations.
* `eval_map_criticalitySquareSum_eq_zero_of_forall` — **the square sum vanishes at a critical
  point**.
-/
import GaloisForLFunctions.HTGeometry.ShellActionRelation

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-- The criticality expression in one coordinate direction, as a polynomial in the auxiliary
variable over the coordinate ring. -/
def criticalityPoly (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (i : Fin N) :
    Polynomial (MvPolynomial (Fin N) ℝ) :=
  (∑ n ∈ Finset.range m, Polynomial.C (MvPolynomial.pderiv i (c n)) * Polynomial.X ^ n)
    + (∑ n ∈ Finset.range m,
        Polynomial.C ((n : MvPolynomial (Fin N) ℝ) * c n) * Polynomial.X ^ (n - 1))
      * (Polynomial.X * Polynomial.C (MvPolynomial.X i))

/-- The sum over all coordinate directions of the squared criticality expressions. -/
def criticalitySquareSum (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) :
    Polynomial (MvPolynomial (Fin N) ℝ) :=
  ∑ i : Fin N, (criticalityPoly m c i) ^ 2

theorem eval_map_criticalityPoly (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (i : Fin N)
    (θ : Fin N → ℝ) (y : ℝ) :
    Polynomial.eval y (Polynomial.map (MvPolynomial.eval θ) (criticalityPoly m c i))
      = (∑ n ∈ Finset.range m,
          MvPolynomial.eval θ (MvPolynomial.pderiv i (c n)) * y ^ n)
        + (∑ n ∈ Finset.range m, (n : ℝ) * MvPolynomial.eval θ (c n) * y ^ (n - 1))
          * (y * θ i) := by
  rw [criticalityPoly, ← Polynomial.coe_mapRingHom]
  simp only [map_add, map_mul, map_sum, map_pow, Polynomial.coe_mapRingHom, Polynomial.map_C,
    Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, MvPolynomial.eval_X, map_natCast, Polynomial.eval_natCast]

theorem eval_map_criticalitySquareSum (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (θ : Fin N → ℝ) (y : ℝ) :
    Polynomial.eval y (Polynomial.map (MvPolynomial.eval θ) (criticalitySquareSum m c))
      = ∑ i : Fin N,
        (Polynomial.eval y (Polynomial.map (MvPolynomial.eval θ) (criticalityPoly m c i))) ^ 2 := by
  rw [criticalitySquareSum, ← Polynomial.coe_mapRingHom]
  simp only [map_sum, map_pow, Polynomial.coe_mapRingHom, Polynomial.eval_finsetSum,
    Polynomial.eval_pow]

/-- **The square sum vanishes at a critical point.** -/
theorem eval_map_criticalitySquareSum_eq_zero_of_forall (m : ℕ)
    (c : ℕ → MvPolynomial (Fin N) ℝ) (θ : Fin N → ℝ) (y : ℝ)
    (h : ∀ i : Fin N,
      (∑ n ∈ Finset.range m, MvPolynomial.eval θ (MvPolynomial.pderiv i (c n)) * y ^ n)
        + (∑ n ∈ Finset.range m, (n : ℝ) * MvPolynomial.eval θ (c n) * y ^ (n - 1))
          * (y * θ i) = 0) :
    Polynomial.eval y (Polynomial.map (MvPolynomial.eval θ) (criticalitySquareSum m c)) = 0 := by
  rw [eval_map_criticalitySquareSum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [eval_map_criticalityPoly, h i]
  ring

end

end GaloisForLFunctions.HTGeometry
