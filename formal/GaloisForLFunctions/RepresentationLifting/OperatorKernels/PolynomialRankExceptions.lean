import GaloisForLFunctions.HTGeometry.AnalyticMatrixRankStratification
import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CompositionCokernel
import Mathlib.Algebra.Polynomial.Roots

/-!
# Finite rank exceptions for polynomial operator families

Every polynomial matrix family admits a single nonzero polynomial whose
roots contain all departures from maximal rank. Hence the observation
quotient has its minimum dimension outside a finite exceptional set.
The certificate is obtained by evaluating a maximal-rank normal-form minor;
no generic-rank or nonvanishing assumption is imposed on the family.
This is the finite-exception mechanism of Zehavi, §3.2, arXiv:2611.18218.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

open GaloisForLFunctions.HTGeometry Polynomial

/-- Evaluate every entry of a polynomial matrix at the same real parameter. -/
def polynomialMatrixFamily {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ[X])
    (x : ℝ) : Matrix (Fin n) (Fin n) ℝ := P.map (Polynomial.evalRingHom x)

/-- A polynomial maximal-rank minor certifies every possible rank drop simultaneously. -/
theorem polynomialMatrix_rank_certificate {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ[X]) :
    ∃ q : ℝ[X], q ≠ 0 ∧ ∀ x,
      genericMatrixRankDefect (polynomialMatrixFamily P) <
        matrixRankDefect (polynomialMatrixFamily P) x → q.eval x = 0 := by
  classical
  let A := polynomialMatrixFamily P
  obtain ⟨x₀, hx₀⟩ := exists_matrixRankDefect_eq_generic A
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form (A x₀)
  let Q := ((V.map Polynomial.C) * P * (U.map Polynomial.C)).submatrix
    (fun i => e.symm (Sum.inl i)) (fun i => e.symm (Sum.inl i))
  have hev (x : ℝ) : Q.det.eval x = (normalFormPrincipalMinor V U e A x).det := by
    change (Polynomial.evalRingHom x) Q.det = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    change Polynomial.eval x (Q i j) = _
    simp [Q, normalFormPrincipalMinor, A, polynomialMatrixFamily, Matrix.mul_apply,
      Polynomial.eval_finsetSum, Polynomial.eval_mul]
  refine ⟨Q.det, ?_, ?_⟩
  · intro hq
    have hone := normalFormPrincipalMinor_det_eq_one A x₀ V U e hnormal
    rw [← hev, hq, Polynomial.eval_zero] at hone
    exact zero_ne_one hone
  · intro x hx
    rw [hev]
    exact matrixRankDefect_exceptional_subset_normalForm_zeroSet
      A x₀ hx₀ V U e rfl hV hU hx

/-- The entire exceptional locus is finite, not merely locally finite or null. -/
theorem polynomialMatrix_rank_exceptions_finite {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ[X]) :
    {x | genericMatrixRankDefect (polynomialMatrixFamily P) <
      matrixRankDefect (polynomialMatrixFamily P) x}.Finite := by
  obtain ⟨q, hq, h⟩ := polynomialMatrix_rank_certificate P
  exact (Polynomial.finite_setOf_isRoot hq).subset h

/-- Outside finitely many parameters the rank defect equals its attained minimum. -/
theorem polynomialMatrix_eventually_minimal_defect {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ[X]) :
    ∀ᶠ x in Filter.cofinite, matrixRankDefect (polynomialMatrixFamily P) x =
      genericMatrixRankDefect (polynomialMatrixFamily P) := by
  have h := polynomialMatrix_rank_exceptions_finite P
  filter_upwards [h.compl_mem_cofinite] with x hx
  exact le_antisymm (le_of_not_gt hx) (genericMatrixRankDefect_le _ x)

/-- Matrix rank defect is exactly the nullity of the associated linear operator. -/
theorem polynomialMatrix_nullity {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ[X]) (x : ℝ) :
    Module.finrank ℝ (polynomialMatrixFamily P x).toLin'.ker =
      matrixRankDefect (polynomialMatrixFamily P) x := by
  have hr := Matrix.rank_eq_finrank_range_toLin (polynomialMatrixFamily P x)
    (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
  rw [Matrix.toLin_eq_toLin'] at hr
  have hn := (polynomialMatrixFamily P x).toLin'.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin, ← hr] at hn
  unfold matrixRankDefect
  omega

/-- Every finite observation space sees a constant quotient dimension off a finite exceptional set. -/
theorem polynomialMatrix_observation_dimension {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ[X]) (W : Type*)
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W] :
    ∀ᶠ x in Filter.cofinite,
      Module.finrank ℝ (((Fin n → ℝ) →ₗ[ℝ] W) ⧸
        (precompose (W := W) (polynomialMatrixFamily P x).toLin').range) =
          Module.finrank ℝ W * genericMatrixRankDefect (polynomialMatrixFamily P) := by
  filter_upwards [polynomialMatrix_eventually_minimal_defect P] with x hx
  rw [finrank_compositionCokernel, polynomialMatrix_nullity, hx]

end GaloisForLFunctions.RepresentationLifting.OperatorKernels

#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.polynomialMatrix_rank_certificate
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.polynomialMatrix_rank_exceptions_finite

#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.polynomialMatrix_observation_dimension
