import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The cubic-to-quartic projection identity

The five level-three invariant cubics satisfy a linear syzygy whose value
is the Burkhardt quartic at the even-coordinate projection. Consequently,
their common zero locus projects into the quartic, and the quartic
pullback belongs to the cubic ideal over every coefficient ring.

These are the explicit algebraic statements of the first two lemmas in
Section 3 of *A locally complete family of Kummer type hyperkähler
fourfolds*, https://arxiv.org/abs/2611.16593.
-/

namespace GaloisForLFunctions.HTGeometry.Burkhardt
open scoped BigOperators
open MvPolynomial
variable {R : Type*} [CommRing R]

/-- The four affine-line cubics and the diagonal cube sum. -/
def cubics (x : Fin 9 → R) : Fin 5 → R := ![
  3 * (x 0 * x 1 * x 2 + x 3 * x 4 * x 5 + x 6 * x 7 * x 8),
  3 * (x 0 * x 3 * x 6 + x 1 * x 4 * x 7 + x 2 * x 5 * x 8),
  3 * (x 0 * x 4 * x 8 + x 1 * x 5 * x 6 + x 2 * x 3 * x 7),
  3 * (x 0 * x 5 * x 7 + x 1 * x 3 * x 8 + x 2 * x 4 * x 6),
  x 0 ^ 3 + x 1 ^ 3 + x 2 ^ 3 + x 3 ^ 3 + x 4 ^ 3 +
    x 5 ^ 3 + x 6 ^ 3 + x 7 ^ 3 + x 8 ^ 3]

/-- Projection onto the five even coordinates of the coordinate inversion. -/
def evenProjection (x : Fin 9 → R) : Fin 5 → R :=
  ![x 1 + x 2, x 3 + x 6, x 4 + x 8, x 5 + x 7, x 0]

def quartic (y : Fin 5 → R) : R :=
  y 4 * (y 0 ^ 3 + y 1 ^ 3 + y 2 ^ 3 + y 3 ^ 3 + y 4 ^ 3) +
    3 * y 0 * y 1 * y 2 * y 3

/-- A universal syzygy identifies the quartic pullback with a combination of the five cubics. -/
theorem projection_identity (x : Fin 9 → R) :
    (∑ i, evenProjection x i * cubics x i) = quartic (evenProjection x) := by
  simp [Fin.sum_univ_succ, cubics, evenProjection, quartic]
  ring

/-- The affine cone over the cubic intersection maps into the quartic cone. -/
theorem projection_maps_zero_locus (x : Fin 9 → R) (hx : ∀ i, cubics x i = 0) :
    quartic (evenProjection x) = 0 := by
  rw [← projection_identity]
  exact Finset.sum_eq_zero fun i _ => by rw [hx i, mul_zero]

/-- The projection statement holds at ideal level, hence also with nilpotents. -/
theorem quartic_pullback_mem_cubic_ideal :
    quartic (evenProjection (X : Fin 9 → MvPolynomial (Fin 9) R)) ∈
      Ideal.span (Set.range (cubics (X : Fin 9 → MvPolynomial (Fin 9) R))) := by
  rw [← projection_identity]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The five polar cubics of the quartic. -/
def gradient (y : Fin 5 → R) : Fin 5 → R := ![
  3 * (y 4 * y 0 ^ 2 + y 1 * y 2 * y 3),
  3 * (y 4 * y 1 ^ 2 + y 0 * y 2 * y 3),
  3 * (y 4 * y 2 ^ 2 + y 0 * y 1 * y 3),
  3 * (y 4 * y 3 ^ 2 + y 0 * y 1 * y 2),
  y 0 ^ 3 + y 1 ^ 3 + y 2 ^ 3 + y 3 ^ 3 + 4 * y 4 ^ 3]

/-- The displayed polar cubics are the actual formal partial derivatives. -/
theorem pderiv_quartic (i : Fin 5) :
    pderiv i (quartic (X : Fin 5 → MvPolynomial (Fin 5) R)) =
      gradient (X : Fin 5 → MvPolynomial (Fin 5) R) i := by
  have hc (j : Fin 5) : pderiv j (3 : MvPolynomial (Fin 5) R) = 0 := by
    change pderiv j (C 3) = 0
    exact pderiv_C
  fin_cases i <;> simp [quartic, gradient, pderiv_X, hc] <;> ring

variable {K : Type*} [Field K] [CharZero K]

/-- Recover the inversion-fixed nine coordinates from their pairwise sums. -/
def evenEmbedding (y : Fin 5 → K) : Fin 9 → K :=
  ![y 4, y 0 / 2, y 0 / 2, y 1 / 2, y 2 / 2, y 3 / 2,
    y 1 / 2, y 3 / 2, y 2 / 2]

theorem evenProjection_evenEmbedding (y : Fin 5 → K) :
    evenProjection (evenEmbedding y) = y := by
  funext i
  fin_cases i <;> simp [evenProjection, evenEmbedding]

/-- Restricting the invariant cubics to the even subspace gives one quarter
of the polar gradient. The factor is the same for all five coordinates. -/
theorem four_mul_cubics_evenEmbedding (y : Fin 5 → K) (i : Fin 5) :
    4 * cubics (evenEmbedding y) i = gradient y i := by
  fin_cases i <;> simp [cubics, evenEmbedding, gradient] <;> ring

/-- The even slice of the cubic intersection is exactly the gradient-zero locus. -/
theorem even_slice_iff_gradient_zero (y : Fin 5 → K) :
    (∀ i, cubics (evenEmbedding y) i = 0) ↔ (∀ i, gradient y i = 0) := by
  simp_rw [← four_mul_cubics_evenEmbedding, mul_eq_zero,
    show (4 : K) ≠ 0 by norm_num, false_or]

#print axioms projection_identity
#print axioms quartic_pullback_mem_cubic_ideal
#print axioms pderiv_quartic
#print axioms even_slice_iff_gradient_zero
end GaloisForLFunctions.HTGeometry.Burkhardt
