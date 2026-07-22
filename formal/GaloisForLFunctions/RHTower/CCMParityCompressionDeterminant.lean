import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Polynomial.Roots
import GaloisForLFunctions.HTGeometry.MomentHankelStrict

/-!
# CCM parity-compression determinant law

This module formalizes the determinant core of the CCM parity-compression law.  In coordinates
adapted to the central even direction, the odd block is intertwined with the central compression
of the even block.  An invertible intertwiner therefore identifies the odd characteristic
polynomial with the central adjugate cofactor of the even characteristic pencil.  Off the even
spectrum this is exactly the central resolvent entry.

The result is purely finite-dimensional and unconditional.  It assumes neither positivity of the
actual von Mangoldt--Gamma source nor RH.

The final section records the exact finite atomic Stieltjes law used by the same construction:
positive weights at distinct nodes make the corresponding full-size moment Hankel matrix strictly
positive.  Thus, after the parity determinant reduction, source positivity is the sole missing
analytic input rather than another determinant or interlacing problem.
-/

open Matrix

namespace RHTower

variable {K : Type*} [Field K]

/-- Delete the distinguished central row and column of a matrix.  The remaining coordinates are
the zero-boundary even hyperplane in an oblique CCM parity basis. -/
def ccmCentralCompression {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : Matrix (Fin n) (Fin n) K :=
  M.submatrix Fin.succ Fin.succ

/-- The determinant of the central compression is the distinguished adjugate cofactor. -/
theorem det_ccmCentralCompression_eq_adjugate_zero_zero {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (ccmCentralCompression M).det = M.adjugate 0 0 := by
  simpa [ccmCentralCompression, add_comm] using
    (Matrix.adjugate_fin_succ_eq_det_submatrix M
      (0 : Fin (n + 1)) (0 : Fin (n + 1))).symm

/-- Cramer's rule in the exact central-coordinate form used by the parity quotient. -/
theorem det_mul_nonsingInv_zero_zero_eq_ccmCentralCompression_det {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hM : M.det ≠ 0) :
    M.det * M⁻¹ 0 0 = (ccmCentralCompression M).det := by
  rw [Matrix.inv_def]
  simp [det_ccmCentralCompression_eq_adjugate_zero_zero, hM]

/-- Central compression commutes with a scalar characteristic shift. -/
theorem ccmCentralCompression_sub_smul_one {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (z : K) :
    ccmCentralCompression
        (M - z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) =
      ccmCentralCompression M - z • (1 : Matrix (Fin n) (Fin n) K) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ccmCentralCompression]
  · have hsij : i.succ ≠ j.succ := fun h => hij (Fin.succ_inj.mp h)
    simp [ccmCentralCompression, hij, hsij]

/-- Similarity through an arbitrary invertible intertwiner preserves every characteristic shift.
This formulation avoids choosing an inverse matrix explicitly. -/
theorem det_shift_eq_of_isUnit_intertwiner {n : ℕ}
    (A B J : Matrix (Fin n) (Fin n) K)
    (hJ : IsUnit J.det) (hinter : A * J = J * B) (z : K) :
    (A - z • (1 : Matrix (Fin n) (Fin n) K)).det =
      (B - z • (1 : Matrix (Fin n) (Fin n) K)).det := by
  have hmat :
      (A - z • (1 : Matrix (Fin n) (Fin n) K)) * J =
        J * (B - z • (1 : Matrix (Fin n) (Fin n) K)) := by
    calc
      (A - z • (1 : Matrix (Fin n) (Fin n) K)) * J
          = A * J - z • J := by noncomm_ring
      _ = J * B - z • J := by rw [hinter]
      _ = J * (B - z • (1 : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
  have hdet := congrArg Matrix.det hmat
  simp only [Matrix.det_mul] at hdet
  apply mul_left_cancel₀ hJ.ne_zero
  simpa [mul_comm] using hdet

/-- **Universal CCM parity determinant polynomial.**  If the odd block is intertwined with the
central compression of the even block, its characteristic determinant is exactly the central
adjugate cofactor of the even characteristic pencil. -/
theorem ccmParityCompression_shift_det_eq_adjugateCentral {n : ℕ}
    (Qplus : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (Qminus J : Matrix (Fin n) (Fin n) K)
    (hJ : IsUnit J.det)
    (hinter : Qminus * J = J * ccmCentralCompression Qplus)
    (z : K) :
    (Qminus - z • (1 : Matrix (Fin n) (Fin n) K)).det =
      (Qplus - z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)).adjugate 0 0 := by
  rw [det_shift_eq_of_isUnit_intertwiner Qminus (ccmCentralCompression Qplus) J hJ hinter z]
  rw [← det_ccmCentralCompression_eq_adjugate_zero_zero]
  rw [ccmCentralCompression_sub_smul_one]

/-- **Universal CCM parity resolvent quotient.**  Away from the even spectrum, the same odd
characteristic determinant is the even determinant multiplied by its central resolvent entry. -/
theorem ccmParityCompression_shift_det_eq_det_mul_resolventCentral {n : ℕ}
    (Qplus : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (Qminus J : Matrix (Fin n) (Fin n) K)
    (hJ : IsUnit J.det)
    (hinter : Qminus * J = J * ccmCentralCompression Qplus)
    (z : K)
    (hz : (Qplus - z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)).det ≠ 0) :
    (Qminus - z • (1 : Matrix (Fin n) (Fin n) K)).det =
      (Qplus - z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)).det *
        (Qplus - z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K))⁻¹ 0 0 := by
  rw [ccmParityCompression_shift_det_eq_adjugateCentral Qplus Qminus J hJ hinter z]
  rw [← det_ccmCentralCompression_eq_adjugate_zero_zero]
  rw [← det_mul_nonsingInv_zero_zero_eq_ccmCentralCompression_det _ hz]

/-! ## Exact positive atomic source law -/

open scoped BigOperators
open Polynomial HTGeometry

/-- Moments of a finite CCM source packet with weights `w` and source nodes `x`. -/
def ccmAtomicMixedMoment {n : ℕ} (w x : Fin n → ℝ) (m : ℕ) : ℝ :=
  ∑ i, w i * x i ^ m

/-- The atomic moment Hankel quadratic form is the weighted sum of squared polynomial values. -/
theorem ccmAtomicMixedMoment_quad_eq {n : ℕ} (w x a : Fin n → ℝ) :
    a ⬝ᵥ (momentHankelMatrix (ccmAtomicMixedMoment w x) n).mulVec a =
      ∑ k, w k * ((Polynomial.ofFn n a).eval (x k)) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, momentHankelMatrix, ccmAtomicMixedMoment,
    Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]
  classical
  calc
    (∑ i : Fin n, a i * ∑ j : Fin n,
      (∑ k : Fin n, w k * x k ^ ((i : ℕ) + (j : ℕ))) * a j) =
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          a i * (w k * x k ^ ((i : ℕ) + (j : ℕ)) * a j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
        a i * (w k * x k ^ ((i : ℕ) + (j : ℕ)) * a j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        a i * (w k * x k ^ ((i : ℕ) + (j : ℕ)) * a j) := by
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, w k * (∑ i : Fin n, a i * x k ^ (i : ℕ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      simp_rw [pow_add]
      simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- **Finite atomic strict-moment law.** Positive weights on `n` distinct real source nodes make
the order-`n` moment Hankel matrix positive definite.  The size bound is sharp: the proof is
Vandermonde injectivity, expressed without choosing or inverting a Vandermonde matrix. -/
theorem ccmAtomicMixedMomentHankel_posDef {n : ℕ} (hn : 0 < n)
    (w x : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hx : Function.Injective x) :
    (momentHankelMatrix (ccmAtomicMixedMoment w x) n).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨momentHankelMatrix_isHermitian _ _, ?_⟩
  intro a ha
  rw [star_trivial, ccmAtomicMixedMoment_quad_eq]
  have hp : Polynomial.ofFn n a ≠ 0 := by
    intro h
    apply ha
    apply Polynomial.injective_ofFn n
    rw [h, Polynomial.ofFn_zero]
  have hdeg : (Polynomial.ofFn n a).natDegree < Fintype.card (Fin n) := by
    simpa using Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr hn.ne') a
  have hnotall : ¬ ∀ i, (Polynomial.ofFn n a).eval (x i) = 0 := by
    intro hall
    exact hp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (Polynomial.ofFn n a) hx hall hdeg)
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  have hnonneg : ∀ k, 0 ≤ w k * ((Polynomial.ofFn n a).eval (x k)) ^ 2 := by
    intro k
    exact mul_nonneg (hw k).le (sq_nonneg _)
  have hpos : 0 < w i * ((Polynomial.ofFn n a).eval (x i)) ^ 2 := by
    exact mul_pos (hw i) (sq_pos_of_ne_zero hi)
  exact hpos.trans_le (Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i))

/-- Positive distinct atomic source data produce a strictly positive full-size Hankel determinant. -/
theorem det_ccmAtomicMixedMomentHankel_pos {n : ℕ} (hn : 0 < n)
    (w x : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hx : Function.Injective x) :
    0 < (momentHankelMatrix (ccmAtomicMixedMoment w x) n).det :=
  (ccmAtomicMixedMomentHankel_posDef hn w x hw hx).det_pos

end RHTower
