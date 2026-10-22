/-
# Guinand--Weil reflection-odd finite rigidity

The source-reflection-even part of a Guinand--Weil event packet is diagonal.  This module asks
whether unequal weights on distinct reflection orbits can cancel the remaining odd incidence at a
finite stage.  They cannot.

For `N` event angles, the first `N` positive sine moments factor through evaluation of the first
`N` Chebyshev polynomials of the second kind.  Their evaluation determinant is a Vandermonde in the
cosine nodes, multiplied by nonzero sine and Chebyshev leading-coefficient factors.  Thus the sine
moment map is injective whenever the cosine nodes are distinct and the sine nodes are nonzero.

Applied to a literal `N`-orbit Guinand--Weil event packet on modes `0,...,N`, vanishing of every edge
from mode zero to modes `1,...,N` is equivalent to exact equality of the weights on each event and
its source reflection.  Representatives strictly between horizons zero and one half satisfy all
nondegeneracy conditions automatically.  Hence an at-most-`N`-orbit packet cannot erase its
codiagonal by cancellation among distinct nondegenerate events.  Overcomplete packets with more
than `N` orbits are intentionally excluded here and are classified by the observer-dimension
module.
-/
import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilSourceReflection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section

open scoped BigOperators

namespace RHTower

open Matrix Polynomial

/-- Matrix of the first `N` positive sine moments of `N` event angles.  Rows are moment orders
`1,...,N`; columns are event orbits. -/
def ccmGuinandWeilSineMomentMatrix {N : ℕ}
    (angle : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun k i => Real.sin (((k : ℕ) + 1 : ℝ) * angle i)

/-- Evaluation matrix of the first `N` Chebyshev polynomials of the second kind at the cosine
nodes of the event angles. -/
def ccmGuinandWeilChebyshevUEvaluationMatrix {N : ℕ}
    (angle : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i k =>
    (Polynomial.Chebyshev.U ℝ ((k : ℕ) : ℤ)).eval (Real.cos (angle i))

/-- Upper-triangular coefficient matrix of the first `N` Chebyshev polynomials of the second
kind. -/
def ccmGuinandWeilChebyshevUCoeffMatrix {N : ℕ} : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun degree k =>
    (Polynomial.Chebyshev.U ℝ ((k : ℕ) : ℤ)).coeff degree

/-- Chebyshev evaluation factors into the ordinary cosine-node Vandermonde and the triangular
Chebyshev coefficient matrix. -/
theorem ccmGuinandWeilChebyshevUEvaluationMatrix_factor {N : ℕ}
    (angle : Fin N → ℝ) :
    ccmGuinandWeilChebyshevUEvaluationMatrix angle =
      Matrix.vandermonde (fun i => Real.cos (angle i)) *
        ccmGuinandWeilChebyshevUCoeffMatrix := by
  let p : Fin N → ℝ[X] := fun k =>
    Polynomial.Chebyshev.U ℝ ((k : ℕ) : ℤ)
  have hdegree : ∀ k, (p k).natDegree ≤ k := by
    intro k
    simp [p]
  change (Matrix.of fun i k => (p k).eval (Real.cos (angle i))) = _
  exact Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
    (fun i => Real.cos (angle i)) p hdegree

/-- The Chebyshev coefficient determinant is the product of the successive leading coefficients
`2^k`. -/
theorem ccmGuinandWeilChebyshevUCoeffMatrix_det {N : ℕ} :
    (ccmGuinandWeilChebyshevUCoeffMatrix (N := N)).det =
      ∏ k : Fin N, (2 : ℝ) ^ (k : ℕ) := by
  let p : Fin N → ℝ[X] := fun k =>
    Polynomial.Chebyshev.U ℝ ((k : ℕ) : ℤ)
  have hdegree : ∀ k, (p k).natDegree ≤ k := by
    intro k
    simp [p]
  rw [ccmGuinandWeilChebyshevUCoeffMatrix,
    Matrix.det_of_upperTriangular
      (Matrix.matrixOfPolynomials_blockTriangular p hdegree)]
  apply Finset.prod_congr rfl
  intro k _
  change (Polynomial.Chebyshev.U ℝ ((k : ℕ) : ℤ)).coeff (k : ℕ) =
    (2 : ℝ) ^ (k : ℕ)
  simpa [Polynomial.leadingCoeff,
    Polynomial.Chebyshev.natDegree_U_natCast] using
      Polynomial.Chebyshev.leadingCoeff_U_natCast ℝ (k : ℕ)

/-- The sine-moment matrix is the transposed Chebyshev evaluation matrix followed by multiplication
by the event sine diagonal. -/
theorem ccmGuinandWeilSineMomentMatrix_factor {N : ℕ}
    (angle : Fin N → ℝ) :
    ccmGuinandWeilSineMomentMatrix angle =
      (ccmGuinandWeilChebyshevUEvaluationMatrix angle)ᵀ *
        Matrix.diagonal (fun i => Real.sin (angle i)) := by
  ext k i
  simp only [ccmGuinandWeilSineMomentMatrix, Matrix.transpose_apply,
    Matrix.mul_diagonal, ccmGuinandWeilChebyshevUEvaluationMatrix]
  simpa only [Int.cast_natCast, Int.cast_one, Int.cast_add, Nat.cast_add,
    Nat.cast_one] using
      (Polynomial.Chebyshev.U_real_cos (angle i) ((k : ℕ) : ℤ)).symm

/-- Exact sine--Chebyshev--Vandermonde determinant factorization. -/
theorem ccmGuinandWeilSineMomentMatrix_det {N : ℕ}
    (angle : Fin N → ℝ) :
    (ccmGuinandWeilSineMomentMatrix angle).det =
      ((Matrix.vandermonde (fun i => Real.cos (angle i))).det *
        ∏ k : Fin N, (2 : ℝ) ^ (k : ℕ)) *
          ∏ i : Fin N, Real.sin (angle i) := by
  rw [ccmGuinandWeilSineMomentMatrix_factor, Matrix.det_mul,
    Matrix.det_transpose, ccmGuinandWeilChebyshevUEvaluationMatrix_factor,
    Matrix.det_mul, ccmGuinandWeilChebyshevUCoeffMatrix_det,
    Matrix.det_diagonal]

/-- **Exact finite degeneracy classification.**  The sine-moment observer is singular exactly at a
sine-zero endpoint or a collision of two cosine nodes.  These are the only finite gates through
which reflection imbalance can become invisible. -/
theorem ccmGuinandWeilSineMomentMatrix_det_eq_zero_iff {N : ℕ}
    (angle : Fin N → ℝ) :
    (ccmGuinandWeilSineMomentMatrix angle).det = 0 ↔
      (∃ i, Real.sin (angle i) = 0) ∨
        ∃ i j, Real.cos (angle i) = Real.cos (angle j) ∧ i ≠ j := by
  rw [ccmGuinandWeilSineMomentMatrix_det]
  have hpowers : (∏ k : Fin N, (2 : ℝ) ^ (k : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (by norm_num)
  rw [mul_eq_zero, mul_eq_zero]
  simp only [hpowers, or_false, Matrix.det_vandermonde_eq_zero_iff,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  exact or_comm

/-- Distinct cosine nodes away from sine zeros make the first `N` sine moments nonsingular. -/
theorem ccmGuinandWeilSineMomentMatrix_det_ne_zero {N : ℕ}
    (angle : Fin N → ℝ)
    (hcos : Function.Injective (fun i => Real.cos (angle i)))
    (hsin : ∀ i, Real.sin (angle i) ≠ 0) :
    (ccmGuinandWeilSineMomentMatrix angle).det ≠ 0 := by
  rw [ccmGuinandWeilSineMomentMatrix_det]
  exact mul_ne_zero
    (mul_ne_zero
      (Matrix.det_vandermonde_ne_zero_iff.mpr hcos)
      (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (by norm_num)))
    (Finset.prod_ne_zero_iff.mpr fun i _ => hsin i)

/-- **Finite reflection-odd moment rigidity.**  The first `N` sine moments determine all `N`
reflection-imbalance coefficients. -/
theorem ccmGuinandWeilSineMoment_rigidity {N : ℕ}
    (angle : Fin N → ℝ)
    (hcos : Function.Injective (fun i => Real.cos (angle i)))
    (hsin : ∀ i, Real.sin (angle i) ≠ 0)
    (imbalance : Fin N → ℝ)
    (hmoment : ∀ k : Fin N,
      ∑ i, imbalance i * Real.sin (((k : ℕ) + 1 : ℝ) * angle i) = 0) :
    imbalance = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero
    (ccmGuinandWeilSineMomentMatrix_det_ne_zero angle hcos hsin)
  funext k
  simpa [ccmGuinandWeilSineMomentMatrix, Matrix.mulVec, dotProduct,
    mul_comm] using hmoment k

/-- Finite packet with independent weights on an event and its source reflection, carried by the
integral modes `0,...,N`. -/
def ccmGuinandWeilPairedEventPacketMatrix {N : ℕ}
    (forward reflected horizon : Fin N → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  ∑ r, (forward r •
      ccmGuinandWeilEventMatrix
        (fun j : Fin (N + 1) => (j : ℤ)) (horizon r) +
    reflected r •
      ccmGuinandWeilEventMatrix
        (fun j : Fin (N + 1) => (j : ℤ)) (1 - horizon r))

/-- The edge from mode zero to positive mode `k+1` reads exactly the `k+1` sine moment of the
reflection-imbalance weights, divided by its harmless Guinand--Weil normalization. -/
theorem ccmGuinandWeilPairedEventPacketMatrix_zero_edge {N : ℕ}
    (forward reflected horizon : Fin N → ℝ) (k : Fin N) :
    ccmGuinandWeilPairedEventPacketMatrix forward reflected horizon (Fin.succ k) 0 =
      (∑ r, (forward r - reflected r) *
        Real.sin (((k : ℕ) + 1 : ℝ) * (2 * Real.pi * horizon r))) /
          (Real.pi * ((k : ℕ) + 1 : ℝ)) := by
  rw [ccmGuinandWeilPairedEventPacketMatrix, Matrix.sum_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [ccmGuinandWeilEventMatrix, ccmDividedDifferenceMatrix,
    Fin.succ_ne_zero, if_false]
  simp_rw [ccmGuinandWeilEventSource_one_sub]
  simp [ccmGuinandWeilEventSource]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  rw [show 2 * Real.pi * horizon r * (((k : ℕ) : ℝ) + 1) =
    (((k : ℕ) : ℝ) + 1) * (2 * Real.pi * horizon r) by ring]
  have hkpos : (0 : ℝ) < ((k : ℕ) : ℝ) + 1 := by positivity
  field_simp [Real.pi_ne_zero, ne_of_gt hkpos]
  ring

/-- **Finite cross-event cancellation rigidity.**  Under the exact sine-moment nondegeneracy
conditions, all zero-to-positive off-diagonal entries vanish precisely when every event and its
source reflection have equal weights. -/
theorem ccmGuinandWeilPairedEventPacketMatrix_offDiagonal_zero_iff_reflection_balanced
    {N : ℕ} (forward reflected horizon : Fin N → ℝ)
    (hcos : Function.Injective (fun i => Real.cos (2 * Real.pi * horizon i)))
    (hsin : ∀ i, Real.sin (2 * Real.pi * horizon i) ≠ 0) :
    (∀ k : Fin N,
        ccmGuinandWeilPairedEventPacketMatrix forward reflected horizon (Fin.succ k) 0 = 0) ↔
      forward = reflected := by
  constructor
  · intro hedge
    have himbalance : forward - reflected = 0 := by
      refine ccmGuinandWeilSineMoment_rigidity (N := N)
        (fun i => 2 * Real.pi * horizon i) hcos hsin (forward - reflected) ?_
      intro k
      have hk := hedge k
      rw [ccmGuinandWeilPairedEventPacketMatrix_zero_edge] at hk
      have hdenom : Real.pi * ((k : ℕ) + 1 : ℝ) ≠ 0 :=
        mul_ne_zero Real.pi_ne_zero (by positivity)
      simpa only [Pi.sub_apply] using
        (div_eq_zero_iff.mp hk).resolve_right hdenom
    apply _root_.funext
    intro i
    exact sub_eq_zero.mp (congr_fun himbalance i)
  · rintro rfl
    intro k
    rw [ccmGuinandWeilPairedEventPacketMatrix_zero_edge]
    simp

/-- Distinct reflection-orbit representatives strictly between horizons zero and one half satisfy
the sine-moment nondegeneracy conditions automatically. -/
theorem
    ccmGuinandWeilPairedEventPacketMatrix_offDiagonal_zero_iff_reflection_balanced_of_open_half
    {N : ℕ} (forward reflected horizon : Fin N → ℝ)
    (hhorizon : ∀ i, 0 < horizon i ∧ horizon i < 1 / 2)
    (hinjective : Function.Injective horizon) :
    (∀ k : Fin N,
        ccmGuinandWeilPairedEventPacketMatrix forward reflected horizon (Fin.succ k) 0 = 0) ↔
      forward = reflected := by
  have hscale : 0 < (2 : ℝ) * Real.pi :=
    mul_pos (by norm_num) Real.pi_pos
  apply ccmGuinandWeilPairedEventPacketMatrix_offDiagonal_zero_iff_reflection_balanced
  · intro i j hij
    apply hinjective
    have hi0 : 0 < 2 * Real.pi * horizon i :=
      mul_pos hscale (hhorizon i).1
    have hj0 : 0 < 2 * Real.pi * horizon j :=
      mul_pos hscale (hhorizon j).1
    have hipi : 2 * Real.pi * horizon i < Real.pi := by
      have h := mul_lt_mul_of_pos_left (hhorizon i).2 hscale
      nlinarith [Real.pi_pos]
    have hjpi : 2 * Real.pi * horizon j < Real.pi := by
      have h := mul_lt_mul_of_pos_left (hhorizon j).2 hscale
      nlinarith [Real.pi_pos]
    have hangle : 2 * Real.pi * horizon i = 2 * Real.pi * horizon j :=
      Real.strictAntiOn_cos.injOn
        ⟨hi0.le, hipi.le⟩ ⟨hj0.le, hjpi.le⟩ hij
    nlinarith [Real.pi_pos]
  · intro i
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos hscale (hhorizon i).1
    · have h := mul_lt_mul_of_pos_left (hhorizon i).2 hscale
      nlinarith [Real.pi_pos]

end RHTower
