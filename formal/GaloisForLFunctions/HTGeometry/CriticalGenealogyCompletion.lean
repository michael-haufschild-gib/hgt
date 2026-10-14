import GaloisForLFunctions.HTGeometry.CriticalGenealogyFiniteRelative
import GaloisForLFunctions.HTGeometry.CriticalGenealogyGramRatio
import GaloisForLFunctions.HTGeometry.FredholmTraceNormContinuity

/-! # Actual critical-reference completion, with an exact native threshold

The relative operator is the inverse of the actual stationary-critical Gram
operator times the actual Gram difference. Its Fredholm determinant is the
limit of the original finite determinant quotients exactly for HS input
weights. The resulting perturbed genealogy remains a critical mirage and its
own weight is never HS.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap _root_.RHTower HilbertSchmidt Filter Topology

theorem tendsto_traceNorm_criticalGenealogyPrefixRelative (a : CertStream)
    (ha : IsHilbertSchmidt a.weight) :
    Tendsto (fun N => traceNorm ToeplitzSpace
      (criticalGenealogyPrefixRelative a N - criticalGenealogyRelativeOperator a)) atTop (𝓝 0) :=
  tendsto_traceNorm_prefixGramRelativeOperator (criticalCertificatePerturbation a).genealogy
    CertStream.stationaryCritical.genealogy (criticalGenealogyGramDifference_schatten a ha)

theorem tendsto_criticalGenealogy_actual_relative_determinant (a : CertStream)
    (ha : IsHilbertSchmidt a.weight) :
    Tendsto (fun N => scalarCertificateGramDet (criticalCertificatePerturbation a) N /
      scalarCertificateGramDet CertStream.stationaryCritical N) atTop
      (𝓝 (fredholmDetOp (lpBasis ℕ) (criticalGenealogyRelativeOperator a))) := by
  have h := tendsto_fredholmDetOp_of_traceNorm_tendsto (lpBasis ℕ)
    (criticalGenealogyPrefixRelative a) (criticalGenealogyRelativeOperator a)
    (criticalGenealogyPrefixRelative_schatten a) (criticalGenealogyRelativeOperator_schatten a ha)
    (tendsto_traceNorm_criticalGenealogyPrefixRelative a ha)
  simpa only [fredholmDetOp_criticalGenealogyPrefixRelative] using h

theorem criticalGenealogyRelativeCompletion_iff (a : CertStream) :
    ((fredholmDetOp (lpBasis ℕ) (criticalGenealogyRelativeOperator a)).im = 0 ∧
      1 ≤ (fredholmDetOp (lpBasis ℕ) (criticalGenealogyRelativeOperator a)).re ∧
      Tendsto (fun N => scalarCertificateGramDet (criticalCertificatePerturbation a) N /
        scalarCertificateGramDet CertStream.stationaryCritical N) atTop
        (𝓝 (fredholmDetOp (lpBasis ℕ) (criticalGenealogyRelativeOperator a)))) ↔
      IsHilbertSchmidt a.weight := by
  constructor
  · rintro ⟨_, hpos, hlim⟩
    apply (criticalGenealogyGramRatio_finite_limit_iff a).mp
    refine ⟨_, hpos, ?_⟩
    have h := Complex.continuous_re.continuousAt.tendsto.comp hlim
    change Tendsto (fun N => (scalarCertificateGramDet (criticalCertificatePerturbation a) N /
      scalarCertificateGramDet CertStream.stationaryCritical N).re) atTop
      (𝓝 (fredholmDetOp (lpBasis ℕ) (criticalGenealogyRelativeOperator a)).re) at h
    simpa only [← criticalGenealogyGramRatio_eq_actual, Complex.ofReal_re] using h
  · intro ha
    obtain ⟨L, hL, hlim⟩ := (criticalGenealogyGramRatio_finite_limit_iff a).mpr ha
    have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp hlim
    change Tendsto (fun N => (criticalGenealogyGramRatio a N : ℂ)) atTop (𝓝 (L : ℂ)) at hcast
    have hactual := tendsto_criticalGenealogy_actual_relative_determinant a ha
    have he : (L : ℂ) = fredholmDetOp (lpBasis ℕ) (criticalGenealogyRelativeOperator a) := by
      apply tendsto_nhds_unique ?_ hactual
      simpa only [criticalGenealogyGramRatio_eq_actual] using hcast
    refine ⟨?_, ?_, hactual⟩
    · rw [← he, Complex.ofReal_im]
    · simpa only [← he, Complex.ofReal_re] using hL

theorem criticalGenealogyMirageCompletion_iff (a : CertStream) :
    ((criticalCertificatePerturbation a).IsCriticalMirage ∧
      ¬ IsHilbertSchmidt (criticalCertificatePerturbation a).weight ∧
      Function.Injective (criticalCertificatePerturbation a).genealogy ∧
      Dense (Set.range (criticalCertificatePerturbation a).genealogy) ∧
      Set.range (criticalCertificatePerturbation a).genealogy ≠ Set.univ ∧
      ¬ IsClosed (Set.range (criticalCertificatePerturbation a).genealogy) ∧
      MemSchattenClass 1 (criticalGenealogyRelativeOperator a) ∧
      (fredholmDetOp (lpBasis ℕ) (criticalGenealogyRelativeOperator a)).im = 0 ∧
      1 ≤ (fredholmDetOp (lpBasis ℕ) (criticalGenealogyRelativeOperator a)).re ∧
      Tendsto (fun N => scalarCertificateGramDet (criticalCertificatePerturbation a) N /
        scalarCertificateGramDet CertStream.stationaryCritical N) atTop
        (𝓝 (fredholmDetOp (lpBasis ℕ) (criticalGenealogyRelativeOperator a)))) ↔
      IsHilbertSchmidt a.weight := by
  constructor
  · intro h
    exact (criticalGenealogyRelativeCompletion_iff a).mp h.2.2.2.2.2.2.2
  · intro ha
    have hm := criticalCertificatePerturbation_mirage a ha
    obtain ⟨hi, hd, hp, hc⟩ := (criticalCertificatePerturbation a).mirage_range hm
    exact ⟨hm, criticalCertificatePerturbation_not_hilbertSchmidt a, hi, hd, hp, hc,
      criticalGenealogyRelativeOperator_schatten a ha,
      (criticalGenealogyRelativeCompletion_iff a).mpr ha⟩

end
end GaloisForLFunctions.HTGeometry
