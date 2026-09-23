import GaloisForLFunctions.HTGeometry.GramDiagonalAtomKernel

/-!
# The scaled Cauchy kernel has the atom kernel as its energy

The diagonal entry of the height-scaled Pick Gram matrix is the energy of the scaled Cauchy kernel
at the node, and that energy is pointwise the scaled Poisson kernel.

So the diagonal is an atom kernel integral, which vanishes at a node carrying no mass, and the
off-diagonal entries are then bounded by the geometric mean of two such diagonals through
Cauchy-Schwarz for the positive measure form.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- **The scaled Cauchy kernel has the atom kernel as its pointwise energy.** -/
theorem normSq_scaled_cauchy_eq_atomKernel (a y t : ℝ) :
    ‖(y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹‖ ^ (2 : ℕ) = atomKernel a y t := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Complex.sq_norm, normSq_inv_sub_upperNode, atomKernel, div_eq_mul_inv]

/-- The energy of the scaled Cauchy kernel is the atom kernel integral, so the scaled Gram diagonal
is exactly the quantity whose limit the atom law computes. -/
theorem integral_normSq_scaled_cauchy (ν : Measure ℝ) (a y : ℝ) :
    ∫ t, ‖(y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹‖ ^ (2 : ℕ) ∂ν
      = ∫ t, atomKernel a y t ∂ν := by
  congr 1
  funext t
  exact normSq_scaled_cauchy_eq_atomKernel a y t

/-- The scaled Cauchy kernel is square integrable exactly when the atom kernel is integrable, which
the Herglotz dominant supplies. -/
theorem integrable_normSq_scaled_cauchy_iff (ν : Measure ℝ) (a y : ℝ) :
    Integrable (fun t : ℝ => ‖(y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹‖ ^ (2 : ℕ)) ν ↔
      Integrable (fun t : ℝ => atomKernel a y t) ν := by
  constructor
  · intro h
    refine h.congr ?_
    filter_upwards with t
    exact normSq_scaled_cauchy_eq_atomKernel a y t
  · intro h
    refine h.congr ?_
    filter_upwards with t
    exact (normSq_scaled_cauchy_eq_atomKernel a y t).symm

end

end GaloisForLFunctions.HTGeometry
