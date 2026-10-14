import GaloisForLFunctions.HTGeometry.CertificateGenealogyTailRecovery

/-! # Positive scalar certificates on the original one-dimensional fibre

Scalar multiplication defines an invertible matrix certificate with the original
uniform bound. Its full genealogy, all infinite tails and their actual completed
determinants are transported by the fixed native coordinate unitary.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap

theorem matOp_algebraMap {d : ℕ} (z : ℂ) :
    matOp (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) z) = z • (1 : Fib d →L[ℂ] Fib d) := by
  rw [Algebra.algebraMap_eq_smul_one, matOp, map_smul, map_one]

theorem norm_matOp_algebraMap_le {d : ℕ} (z : ℂ) :
    ‖matOp (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) z)‖ ≤ ‖z‖ := by
  rw [matOp_algebraMap, norm_smul]
  calc
    ‖z‖ * ‖(1 : Fib d →L[ℂ] Fib d)‖ ≤ ‖z‖ * 1 :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (norm_nonneg z)
    _ = ‖z‖ := mul_one _

def scalarCertificateOperator (a : CertStream) : OpCertStream 1 where
  C n := algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) (a.c n : ℂ)
  unit n := (isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt (a.pos n)))).map
    (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ))
  bound := a.bound
  bound_nonneg := le_trans (a.pos 0).le (a.le_bound 0)
  le_bound n := (norm_matOp_algebraMap_le (a.c n : ℂ)).trans (a.norm_coe_le n)

@[simp] theorem scalarCertificateOperator_coefficient (a : CertStream) (n : ℕ) :
    scalarCertificateCoefficient (scalarCertificateOperator a) n = (a.c n : ℂ) := by
  change (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) (a.c n : ℂ)) 0 0 = _
  simp [Matrix.algebraMap_matrix_apply]

theorem scalarCertificateOperator_norm_coefficient (a : CertStream) (n : ℕ) :
    ‖scalarCertificateCoefficient (scalarCertificateOperator a) n‖ = a.c n := by
  rw [scalarCertificateOperator_coefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (a.pos n)]

theorem scalarCertificateOperator_coordinate_genealogy (a : CertStream) :
    scalarCoordinateGenealogy (scalarCertificateOperator a) = a.genealogy := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  rw [scalarCoordinateGenealogy_apply, CertStream.genealogy_apply,
    scalarCertificateOperator_coefficient]

theorem scalarCertificateOperator_genealogy (a : CertStream) :
    (scalarCertificateOperator a).genealogy =
      RHTower.unitaryPush scalarCertificateCoordinates.symm a.genealogy := by
  rw [paperGenealogy_eq_unitaryPush_scalarCoordinates, scalarCertificateOperator_coordinate_genealogy]

theorem scalarCertificateOperator_hilbertSchmidt_iff (a : CertStream) :
    IsHilbertSchmidt (1 - (scalarCertificateOperator a).genealogy) ↔ IsHilbertSchmidt a.weight := by
  rw [paperGenealogy_weight_isHilbertSchmidt_iff, scalarCertificate_weight_isHilbertSchmidt_iff]
  simp only [scalarCertificateOperator_norm_coefficient]

theorem scalarCertificateOperator_completion (a : CertStream) :
    paperGenealogyGramCompletion (scalarCertificateOperator a) = scalarCertificateGramCompletion a := by
  rw [paperGenealogyGramCompletion_eq_scalar, scalarCertificateOperator_coordinate_genealogy]
  change scalarGenealogyGramCompletion a.genealogy (scalarCertificateCoefficient (scalarCertificateOperator a)) =
    scalarGenealogyGramCompletion a.genealogy (fun n => (a.c n : ℂ))
  exact congrArg (scalarGenealogyGramCompletion a.genealogy)
    (funext (scalarCertificateOperator_coefficient a))

theorem scalarCertificateOperator_tail (a : CertStream) (k : ℕ) :
    paperCertificateTail (scalarCertificateOperator a) k =
      scalarCertificateOperator (scalarCertificateTail a k) := rfl

theorem scalarCertificateOperator_tailValue (a : CertStream) (k : ℕ) :
    paperCertificateTailValue (scalarCertificateOperator a) k = scalarCertificateTailValue a k := by
  rw [paperCertificateTailValue, scalarCertificateOperator_tail, scalarCertificateOperator_completion]
  rfl

end
end GaloisForLFunctions.HTGeometry
