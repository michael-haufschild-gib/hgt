import GaloisForLFunctions.HTGeometry.CriticalGenealogyCompletion
import GaloisForLFunctions.HTGeometry.PositiveScalarCertificateOperator

/-! # Critical-relative completion on the original paper fibre

Canonical Gram inverses commute with the fixed native coordinate unitary.
The relative determinant therefore lands on the original `FibSeq 1` carrier,
whose full genealogy retains infinite compact-ideal cost.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap _root_.RHTower HilbertSchmidt Filter Topology
open scoped ENNReal

section Unitary
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem unitGramOperator_unitaryPush (u : H ≃ₗᵢ[ℂ] K) (G : H →L[ℂ] H) :
    unitGramOperator (unitaryPush u G) = unitaryPush u (unitGramOperator G) := by
  simp only [unitGramOperator, unitaryPush_add, unitaryPush_one, unitaryPush_mul, adjoint_unitaryPush]

theorem unitGramResolvent_unitaryPush (u : H ≃ₗᵢ[ℂ] K) (G : H →L[ℂ] H) :
    unitGramResolvent (unitaryPush u G) = unitaryPush u (unitGramResolvent G) := by
  have h : unitGramOperator (unitaryPush u G) * unitaryPush u (unitGramResolvent G) = 1 := by
    rw [unitGramOperator_unitaryPush, ← unitaryPush_mul,
      unitGramOperator_mul_resolvent, unitaryPush_one]
  calc
    unitGramResolvent (unitaryPush u G) = unitGramResolvent (unitaryPush u G) * 1 := (mul_one _).symm
    _ = unitGramResolvent (unitaryPush u G) *
        (unitGramOperator (unitaryPush u G) * unitaryPush u (unitGramResolvent G)) := by rw [h]
    _ = unitaryPush u (unitGramResolvent G) := by
      rw [← mul_assoc, unitGramResolvent_mul_operator, one_mul]

end Unitary

theorem scalarCertificateOperator_gramDet (a : CertStream) (N : ℕ) :
    paperGenealogyGramDet (scalarCertificateOperator a) N = scalarCertificateGramDet a N := by
  rw [paperGenealogyGramDet_eq, scalarCertificateGramDet_eq,
    show scalarCertificateCoefficient (scalarCertificateOperator a) = (fun n => (a.c n : ℂ)) from
      funext (scalarCertificateOperator_coefficient a)]

theorem scalarCertificate_genealogy_infiniteCost (a : CertStream) :
    compactOperatorTraceCost ToeplitzSpace a.genealogy = ∞ := by
  apply (compactOperatorTraceCost_eq_top_iff _).mpr
  intro hc
  apply not_isCompactOperator_genealogy 0 (scalarCertificateOperator a)
  rw [scalarCertificateOperator_genealogy]
  exact (hc.comp_clm (scalarCertificateCoordinates : FibSeq 1 →L[ℂ] ToeplitzSpace)).clm_comp
    (scalarCertificateCoordinates.symm : ToeplitzSpace →L[ℂ] FibSeq 1)

def paperCriticalGenealogyRelativeOperator (a : CertStream) : FibSeq 1 →L[ℂ] FibSeq 1 :=
  unitGramResolvent (scalarCertificateOperator CertStream.stationaryCritical).genealogy ∘L
    (unitGramOperator (scalarCertificateOperator (criticalCertificatePerturbation a)).genealogy -
      unitGramOperator (scalarCertificateOperator CertStream.stationaryCritical).genealogy)

theorem paperCriticalGenealogyRelativeOperator_eq_unitaryPush (a : CertStream) :
    paperCriticalGenealogyRelativeOperator a =
      unitaryPush scalarCertificateCoordinates.symm (criticalGenealogyRelativeOperator a) := by
  simp only [paperCriticalGenealogyRelativeOperator, scalarCertificateOperator_genealogy,
    unitGramResolvent_unitaryPush, unitGramOperator_unitaryPush,
    criticalGenealogyRelativeOperator, criticalGenealogyGramDifference]
  rw [← unitaryPush_sub]
  exact (unitaryPush_mul _ _ _).symm

theorem paperCriticalGenealogyRelativeOperator_schatten (a : CertStream)
    (ha : IsHilbertSchmidt a.weight) : MemSchattenClass 1 (paperCriticalGenealogyRelativeOperator a) := by
  rw [paperCriticalGenealogyRelativeOperator_eq_unitaryPush, memSchattenClass_unitaryPush_iff]
  exact criticalGenealogyRelativeOperator_schatten a ha

theorem fredholmDetOp_paperCriticalGenealogyRelativeOperator (a : CertStream)
    (ha : IsHilbertSchmidt a.weight) :
    fredholmDetOp scalarCertificateBasis (paperCriticalGenealogyRelativeOperator a) =
      fredholmDetOp (lpBasis ℕ) (criticalGenealogyRelativeOperator a) := by
  rw [paperCriticalGenealogyRelativeOperator_eq_unitaryPush, scalarCertificateBasis,
    fredholmDetOp_unitaryPush (lpBasis ℕ) scalarCertificateCoordinates.symm
      (criticalGenealogyRelativeOperator_schatten a ha)]

theorem paperCriticalGenealogyCompletion_iff (a : CertStream) :
    (compactOperatorTraceCost (FibSeq 1)
        (scalarCertificateOperator (criticalCertificatePerturbation a)).genealogy = ∞ ∧
      ¬ IsHilbertSchmidt (1 - (scalarCertificateOperator (criticalCertificatePerturbation a)).genealogy) ∧
      MemSchattenClass 1 (paperCriticalGenealogyRelativeOperator a) ∧
      (fredholmDetOp scalarCertificateBasis (paperCriticalGenealogyRelativeOperator a)).im = 0 ∧
      1 ≤ (fredholmDetOp scalarCertificateBasis (paperCriticalGenealogyRelativeOperator a)).re ∧
      Tendsto (fun N => paperGenealogyGramDet (scalarCertificateOperator (criticalCertificatePerturbation a)) N /
        paperGenealogyGramDet (scalarCertificateOperator CertStream.stationaryCritical) N) atTop
        (𝓝 (fredholmDetOp scalarCertificateBasis (paperCriticalGenealogyRelativeOperator a)))) ↔
      IsHilbertSchmidt a.weight := by
  constructor
  · rintro ⟨_, _, _, _, hpos, hlim⟩
    apply (criticalGenealogyGramRatio_finite_limit_iff a).mp
    refine ⟨_, hpos, ?_⟩
    have h := Complex.continuous_re.continuousAt.tendsto.comp hlim
    change Tendsto (fun N => (paperGenealogyGramDet (scalarCertificateOperator (criticalCertificatePerturbation a)) N /
      paperGenealogyGramDet (scalarCertificateOperator CertStream.stationaryCritical) N).re) atTop
      (𝓝 (fredholmDetOp scalarCertificateBasis (paperCriticalGenealogyRelativeOperator a)).re) at h
    simpa only [scalarCertificateOperator_gramDet, ← criticalGenealogyGramRatio_eq_actual,
      Complex.ofReal_re] using h
  · intro ha
    refine ⟨compactOperatorTraceCost_genealogy 0 _, ?_,
      paperCriticalGenealogyRelativeOperator_schatten a ha, ?_⟩
    · rw [scalarCertificateOperator_hilbertSchmidt_iff]
      exact criticalCertificatePerturbation_not_hilbertSchmidt a
    · rw [fredholmDetOp_paperCriticalGenealogyRelativeOperator a ha]
      simpa only [scalarCertificateOperator_gramDet] using (criticalGenealogyRelativeCompletion_iff a).mpr ha

end
end GaloisForLFunctions.HTGeometry
