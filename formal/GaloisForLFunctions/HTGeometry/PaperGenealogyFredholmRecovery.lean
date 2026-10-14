import GaloisForLFunctions.HTGeometry.ScalarOperatorCertificateCoordinates
import GaloisForLFunctions.HTGeometry.FiniteGenealogyFredholm

/-! # Exact Fredholm recovery on the original scalar operator-certificate carrier

The literal native prefix has coefficient-blind ordinary determinants. Its actual
Gram determinants recover every certificate magnitude, although its compact-ideal
trace cost is zero at every depth.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt _root_.ContinuousLinearMap

theorem scalarCertificateCoordinates_prefix_operator (a : OpCertStream 1) (N : ℕ) :
    RHTower.unitaryPush scalarCertificateCoordinates (paperGenealogyPrefix a N) =
      finiteScalarGenealogy (scalarCertificateCoefficient a) N := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  rw [RHTower.unitaryPush_apply, scalarCertificateCoordinates_prefix,
    finiteScalarGenealogy_apply_coordinate]
  simp only [LinearIsometryEquiv.apply_symm_apply]

theorem paperGenealogyPrefix_eq_unitaryPush (a : OpCertStream 1) (N : ℕ) :
    paperGenealogyPrefix a N = RHTower.unitaryPush scalarCertificateCoordinates.symm
      (finiteScalarGenealogy (scalarCertificateCoefficient a) N) := by
  apply ContinuousLinearMap.ext
  intro f
  apply scalarCertificateCoordinates.injective
  have h := congrArg (fun T : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 =>
    T (scalarCertificateCoordinates f)) (scalarCertificateCoordinates_prefix_operator a N)
  simpa only [RHTower.unitaryPush_apply, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] using h

theorem paperGenealogyPrefix_traceClass (a : OpCertStream 1) (N : ℕ) :
    RHTower.MemSchattenClass 1 (paperGenealogyPrefix a N) := by
  rw [paperGenealogyPrefix_eq_unitaryPush, memSchattenClass_unitaryPush_iff]
  exact finiteScalarGenealogy_traceClass _ _

theorem paperGenealogyPrefix_gram_eq_unitaryPush (a : OpCertStream 1) (N : ℕ) :
    (paperGenealogyPrefix a N).adjoint ∘L paperGenealogyPrefix a N =
      RHTower.unitaryPush scalarCertificateCoordinates.symm
        ((finiteScalarGenealogy (scalarCertificateCoefficient a) N).adjoint ∘L
          finiteScalarGenealogy (scalarCertificateCoefficient a) N) := by
  rw [paperGenealogyPrefix_eq_unitaryPush, RHTower.adjoint_unitaryPush]
  exact (RHTower.unitaryPush_mul _ _ _).symm

theorem paperGenealogyPrefix_smul_fredholmDet (a : OpCertStream 1) (N : ℕ) (z : ℂ) :
    RHTower.fredholmDetOp scalarCertificateBasis (z • paperGenealogyPrefix a N) =
      (1 + z) ^ N := by
  rw [paperGenealogyPrefix_eq_unitaryPush, ← RHTower.unitaryPush_smul]
  rw [scalarCertificateBasis, fredholmDetOp_unitaryPush (lpBasis ℕ)
    scalarCertificateCoordinates.symm
    (RHTower.memSchattenClass_one_smul (finiteScalarGenealogy_traceClass _ _) z)]
  exact fredholmDetOp_smul_finiteScalarGenealogy _ _ _

def paperGenealogyGramDet (a : OpCertStream 1) (N : ℕ) : ℂ :=
  RHTower.fredholmDetOp scalarCertificateBasis
    ((paperGenealogyPrefix a N).adjoint ∘L paperGenealogyPrefix a N)

theorem paperGenealogyGramDet_eq (a : OpCertStream 1) (N : ℕ) :
    paperGenealogyGramDet a N =
      (finiteGenealogyGramValue (scalarCertificateCoefficient a) N : ℂ) := by
  rw [paperGenealogyGramDet, paperGenealogyPrefix_gram_eq_unitaryPush, scalarCertificateBasis,
    fredholmDetOp_unitaryPush (lpBasis ℕ) scalarCertificateCoordinates.symm
      (finiteScalarGenealogy_gram_traceClass _ _), fredholmDetOp_finiteScalarGenealogy_gram]

@[simp] theorem paperGenealogyGramDet_zero (a : OpCertStream 1) :
    paperGenealogyGramDet a 0 = 1 := by simp [paperGenealogyGramDet_eq]

@[simp] theorem paperGenealogyGramDet_one (a : OpCertStream 1) :
    paperGenealogyGramDet a 1 = 2 := by simp [paperGenealogyGramDet_eq]

theorem paperGenealogyGramDet_recurrence (a : OpCertStream 1) (N : ℕ) :
    paperGenealogyGramDet a (N + 2) = 2 * paperGenealogyGramDet a (N + 1) +
      (‖scalarCertificateCoefficient a N‖ ^ 2 : ℂ) *
        (paperGenealogyGramDet a (N + 1) - paperGenealogyGramDet a N) := by
  simp only [paperGenealogyGramDet_eq, finiteGenealogyGramValue_succ_succ]
  push_cast
  rfl

theorem paperGenealogyGramDet_increment_pos (a : OpCertStream 1) (N : ℕ) :
    0 < (paperGenealogyGramDet a (N + 1) - paperGenealogyGramDet a N).re := by
  simpa [paperGenealogyGramDet_eq] using
    finiteGenealogyGramValue_increment_pos (scalarCertificateCoefficient a) N

theorem paperGenealogyGramDet_two_pow_le (a : OpCertStream 1) (N : ℕ) :
    (2 : ℝ) ^ N ≤ (paperGenealogyGramDet a N).re := by
  simpa [paperGenealogyGramDet_eq] using
    two_pow_le_finiteGenealogyGramValue (scalarCertificateCoefficient a) N

theorem paperGenealogyGramDet_recovers_norm_sq (a : OpCertStream 1) (N : ℕ) :
    (‖scalarCertificateCoefficient a N‖ ^ 2 : ℂ) =
      (paperGenealogyGramDet a (N + 2) - 2 * paperGenealogyGramDet a (N + 1)) /
        (paperGenealogyGramDet a (N + 1) - paperGenealogyGramDet a N) := by
  simp only [paperGenealogyGramDet_eq]
  exact_mod_cast finiteGenealogyGramValue_recovers_norm_sq (scalarCertificateCoefficient a) N

theorem paperGenealogyGramDet_eq_iff (a b : OpCertStream 1) :
    (∀ N, paperGenealogyGramDet a N = paperGenealogyGramDet b N) ↔
      ∀ n, ‖scalarCertificateCoefficient a n‖ = ‖scalarCertificateCoefficient b n‖ := by
  simp only [paperGenealogyGramDet_eq, Complex.ofReal_inj]
  exact finiteGenealogyGramValue_eq_iff _ _

theorem paperGenealogyGramDet_zeroCost_recovery (a : OpCertStream 1) (N : ℕ) :
    compactOperatorTraceCost (FibSeq 1) (paperGenealogyPrefix a N) = 0 ∧
      (‖scalarCertificateCoefficient a N‖ ^ 2 : ℂ) =
        (paperGenealogyGramDet a (N + 2) - 2 * paperGenealogyGramDet a (N + 1)) /
          (paperGenealogyGramDet a (N + 1) - paperGenealogyGramDet a N) :=
  ⟨compactOperatorTraceCost_paperGenealogyPrefix a N, paperGenealogyGramDet_recovers_norm_sq a N⟩

end
end GaloisForLFunctions.HTGeometry
