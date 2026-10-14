import GaloisForLFunctions.HTGeometry.CriticalCertificatePerturbation
import GaloisForLFunctions.HTGeometry.UnitGramResolvent
import GaloisForLFunctions.HTGeometry.LpDiagonalSchattenEnergy
import GaloisForLFunctions.RHTower.ConnesConsaniTraceClassReduction
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-! # The actual critical-relative genealogy operator is trace class

The excess coefficient diagonal is absolutely summable for every HS input
certificate. Its composition with the original backward shift is exactly the
genealogy difference. The established modulus-square perturbation theorem then
places the actual Gram difference and its critical-relative operator in Schatten1.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap _root_.RHTower

private theorem excess_norm_bound (a : CertStream) (n : ℕ) :
    ‖(((criticalCertificatePerturbation a).c n - 1 : ℝ) : ℂ)‖ ≤
      (criticalCertificatePerturbation a).bound := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (criticalCertificatePerturbation_excess_le a n).1]
  linarith [(criticalCertificatePerturbation a).le_bound n]

def criticalCertificateExcessDiagonal (a : CertStream) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  lpDiagonalCLM (fun n => (((criticalCertificatePerturbation a).c n - 1 : ℝ) : ℂ))
    (criticalCertificatePerturbation a).bound_pos.le (excess_norm_bound a)

theorem criticalCertificateExcessDiagonal_schatten (a : CertStream)
    (ha : IsHilbertSchmidt a.weight) : MemSchattenClass 1 (criticalCertificateExcessDiagonal a) := by
  apply (memSchattenClass_lpDiagonalCLM_iff _ _ _ one_pos).mpr
  have hs := criticalCertificatePerturbation_summable_excess a
    ((scalarCertificate_weight_isHilbertSchmidt_iff a).mp ha)
  exact hs.congr fun n => by
    rw [Real.rpow_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (criticalCertificatePerturbation_excess_le a n).1]

theorem criticalCertificatePerturbation_genealogy_difference (a : CertStream) :
    (criticalCertificatePerturbation a).genealogy - CertStream.stationaryCritical.genealogy =
      -(criticalCertificateExcessDiagonal a ∘L backOp 1) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  simp only [sub_apply, neg_apply, ContinuousLinearMap.comp_apply, lp.coeFn_sub, Pi.sub_apply,
    lp.coeFn_neg, Pi.neg_apply, CertStream.genealogy_apply,
    criticalCertificateExcessDiagonal, lpDiagonalCLM_apply, backOp_apply]
  change f n - ((criticalCertificatePerturbation a).c n : ℂ) * f (n + 1) -
      (f n - 1 * f (n + 1)) =
    -((((criticalCertificatePerturbation a).c n - 1 : ℝ) : ℂ) * f (n + 1))
  push_cast
  ring

theorem criticalCertificatePerturbation_genealogy_difference_schatten (a : CertStream)
    (ha : IsHilbertSchmidt a.weight) :
    MemSchattenClass 1
      ((criticalCertificatePerturbation a).genealogy - CertStream.stationaryCritical.genealogy) := by
  rw [criticalCertificatePerturbation_genealogy_difference]
  exact (memSchattenClass_one_comp_right (criticalCertificateExcessDiagonal_schatten a ha) _).one_neg

def criticalGenealogyGramDifference (a : CertStream) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  unitGramOperator (criticalCertificatePerturbation a).genealogy -
    unitGramOperator CertStream.stationaryCritical.genealogy

theorem criticalGenealogyGramDifference_schatten (a : CertStream)
    (ha : IsHilbertSchmidt a.weight) : MemSchattenClass 1 (criticalGenealogyGramDifference a) := by
  have h := memSchattenClass_one_modulusSq_sub (E := CertStream.stationaryCritical.genealogy)
    (criticalCertificatePerturbation_genealogy_difference_schatten a ha).one_isTraceClass
  have he : CertStream.stationaryCritical.genealogy +
      ((criticalCertificatePerturbation a).genealogy - CertStream.stationaryCritical.genealogy) =
      (criticalCertificatePerturbation a).genealogy := by abel
  rw [he] at h
  have hg : criticalGenealogyGramDifference a =
      adjoint (criticalCertificatePerturbation a).genealogy ∘L (criticalCertificatePerturbation a).genealogy -
        adjoint CertStream.stationaryCritical.genealogy ∘L CertStream.stationaryCritical.genealogy := by
    change 1 + adjoint (criticalCertificatePerturbation a).genealogy *
        (criticalCertificatePerturbation a).genealogy -
        (1 + adjoint CertStream.stationaryCritical.genealogy * CertStream.stationaryCritical.genealogy) = _
    abel
  rw [hg]
  exact h

def criticalGenealogyRelativeOperator (a : CertStream) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  unitGramResolvent CertStream.stationaryCritical.genealogy ∘L criticalGenealogyGramDifference a

theorem criticalGenealogyRelativeOperator_schatten (a : CertStream)
    (ha : IsHilbertSchmidt a.weight) : MemSchattenClass 1 (criticalGenealogyRelativeOperator a) :=
  memSchattenClass_one_comp_left (criticalGenealogyGramDifference_schatten a ha) _

theorem criticalGenealogyRelativeOperator_traceClass (a : CertStream)
    (ha : IsHilbertSchmidt a.weight) : IsTraceClass (criticalGenealogyRelativeOperator a) :=
  (criticalGenealogyRelativeOperator_schatten a ha).one_isTraceClass

end
end GaloisForLFunctions.HTGeometry
