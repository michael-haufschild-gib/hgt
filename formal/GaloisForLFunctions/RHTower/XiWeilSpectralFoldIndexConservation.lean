import GaloisForLFunctions.RHTower.XiWeilMultiOrbitSourceIndexConservation
import GaloisForLFunctions.RHTower.XiWeilDivisorHilbert
import GaloisForLFunctions.RHTower.XiReciprocalTranslationSeamNormLaw

/-!
# Spectral-fold conservation for analytic Xi Weil packets

The full Xi divisor Hilbert space sees multiplicity copies separately, but analytic evaluation
vectors are constant on every spectral fibre.  Consequently their negative index is controlled by
distinct off-real spectral locations modulo complex conjugation, not by raw multiplicity copies.

This file proves the sharp finite upper bound.  A nonsingular reflection-odd evaluation minor of
spectral-fibre-constant vectors can contain neither two equal spectral fibres nor two conjugate
spectral fibres.  Applied to explicit continued-Cauchy prime--Gamma packets, every negative
`k`-block therefore forces `k` distinct off-critical conjugation-fold orbits.
-/

namespace RHTower

open scoped BigOperators ComplexConjugate
open Complex Matrix

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Literal test-function evaluation is constant on multiplicity copies of one spectral point. -/
theorem factorsThroughSpectral_xiWeilEvaluationLp
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    FactorsThroughSpectral (xiWeilEvaluationLp F hF) := by
  intro q q' hqq
  rw [xiWeilEvaluationLp_apply, xiWeilEvaluationLp_apply, hqq]

/-- Continued-Cauchy packet evaluations are constant on multiplicity copies of one spectral
point. -/
theorem factorsThroughSpectral_xiWeilContinuedCauchyPacketLp
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (z : ι → XiContinuedCauchyPoint) :
    FactorsThroughSpectral (xiWeilContinuedCauchyPacketLp c z) := by
  rw [← xiWeilEvaluationLp_indexedCauchyPacket]
  exact factorsThroughSpectral_xiWeilEvaluationLp _ _

/-- Reflection-odd projection preserves spectral-fibre constancy. -/
theorem FactorsThroughSpectral.antiPart {v : XiWeilCarrier}
    (hv : FactorsThroughSpectral v) :
    FactorsThroughSpectral (xiWeilAntiPart v) := by
  intro q q' hqq
  have hline :
      xiSpectralPoint (xiZeroCopyLineConjEquiv q) =
        xiSpectralPoint (xiZeroCopyLineConjEquiv q') := by
    rw [xiSpectralPoint_lineConj, xiSpectralPoint_lineConj, hqq]
  simp only [xiWeilAntiPart, xiWeilLineConjLinearIsometry_apply,
    xiWeilLineConjLp_apply, lp.coeFn_sub, Pi.sub_apply]
  rw [hv q q' hqq, hv _ _ hline]

private theorem eq_of_matrix_rows_eq_of_isUnit_det
    {k : ℕ} {Q : Matrix (Fin k) (Fin k) ℂ} (hQdet : IsUnit Q.det)
    {r s : Fin k} (hrow : ∀ j, Q r j = Q s j) : r = s := by
  have hunit : Q * Q⁻¹ = 1 := Q.mul_nonsing_inv hQdet
  have hrr := congrArg (fun M : Matrix (Fin k) (Fin k) ℂ => M r r) hunit
  have hsr := congrArg (fun M : Matrix (Fin k) (Fin k) ℂ => M s r) hunit
  simp only [Matrix.mul_apply, Matrix.one_apply] at hrr hsr
  simp_rw [hrow] at hrr
  by_contra hrs
  have hsr' : s ≠ r := Ne.symm hrs
  simp only [if_neg hsr'] at hsr
  exact one_ne_zero (hrr.symm.trans hsr)

private theorem matrix_rows_ne_neg_of_isUnit_det
    {k : ℕ} {Q : Matrix (Fin k) (Fin k) ℂ} (hQdet : IsUnit Q.det)
    (r s : Fin k) : ¬ (∀ j, Q r j = -Q s j) := by
  intro hrow
  have hunit : Q * Q⁻¹ = 1 := Q.mul_nonsing_inv hQdet
  have hrr := congrArg (fun M : Matrix (Fin k) (Fin k) ℂ => M r r) hunit
  have hsr := congrArg (fun M : Matrix (Fin k) (Fin k) ℂ => M s r) hunit
  simp only [Matrix.mul_apply, Matrix.one_apply] at hrr hsr
  have hneg :
      (∑ j, Q r j * Q⁻¹ j r) = -(∑ j, Q s j * Q⁻¹ j r) := by
    simp_rw [hrow]
    calc
      (∑ j, -Q s j * Q⁻¹ j r) = ∑ j, -(Q s j * Q⁻¹ j r) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = -(∑ j, Q s j * Q⁻¹ j r) := by
        simp only [Finset.sum_neg_distrib]
  by_cases hsrIndex : s = r
  · subst s
    rw [hrr] at hneg
    norm_num at hneg
  · simp only [if_neg hsrIndex] at hsr
    rw [hrr, hsr] at hneg
    norm_num at hneg

/-- An invertible anti-part evaluation minor of spectral-fibre-constant vectors samples distinct
spectral locations modulo conjugation, and every sampled location is off the real axis. -/
theorem spectralFold_injective_and_offReal_of_antiPart_minor
    {k : ℕ} (v : Fin k → XiWeilCarrier)
    (hv : ∀ j, FactorsThroughSpectral (v j))
    (e : Fin k → XiZeroCopy) (Q : Matrix (Fin k) (Fin k) ℂ)
    (hQdet : IsUnit Q.det)
    (hQ : ∀ r s, Q r s = xiWeilAntiPart (v s) (e r)) :
    Function.Injective (fun r =>
        complexConjugationFold (xiSpectralPoint (e r))) ∧
      ∀ r, (xiSpectralPoint (e r)).im ≠ 0 := by
  have hantiFactor : ∀ j, FactorsThroughSpectral (xiWeilAntiPart (v j)) :=
    fun j => (hv j).antiPart
  have hnotConj : ∀ r s,
      xiSpectralPoint (e r) ≠ (starRingEnd ℂ) (xiSpectralPoint (e s)) := by
    intro r s hrs
    apply matrix_rows_ne_neg_of_isUnit_det hQdet r s
    intro j
    rw [hQ, hQ]
    have hfiber : xiWeilAntiPart (v j) (e r) =
        xiWeilAntiPart (v j) (xiZeroCopyLineConjEquiv (e s)) := by
      apply hantiFactor j
      rw [xiSpectralPoint_lineConj, hrs]
    rw [hfiber, xiWeilAntiPart_lineConj_apply]
  constructor
  · intro r s hrs
    rcases complexConjugationFold_eq_iff.mp hrs with hsame | hconj
    · apply eq_of_matrix_rows_eq_of_isUnit_det hQdet
      intro j
      rw [hQ, hQ]
      exact hantiFactor j _ _ hsame
    · exact False.elim ((hnotConj r s) hconj)
  · intro r him
    apply hnotConj r r
    apply Complex.ext
    · simp
    · simp [him]

/-- Every negative `k`-block of analytic Xi evaluation vectors forces `k` distinct off-real
spectral locations modulo complex conjugation. -/
theorem exists_xiSpectralFoldPacket_of_hilbertGram_negDef
    {k : ℕ} (v : Fin k → XiWeilCarrier)
    (hv : ∀ j, FactorsThroughSpectral (v j))
    (hneg : ∀ x : Fin k → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (xiWeilHilbertGram v).mulVec x).re < 0) :
    ∃ (e : Fin k → XiZeroCopy) (Q : Matrix (Fin k) (Fin k) ℂ),
      Function.Injective (fun r =>
        complexConjugationFold (xiSpectralPoint (e r))) ∧
      (∀ r, (xiSpectralPoint (e r)).im ≠ 0) ∧
      IsUnit Q.det ∧
      ∀ r s, Q r s = xiWeilAntiPart (v s) (e r) := by
  obtain ⟨e, Q, _he, _hsep, hQdet, hQ⟩ :=
    exists_xiZeroCopy_freeOrbitPacket_of_hilbertGram_negDef v hneg
  obtain ⟨hfold, him⟩ :=
    spectralFold_injective_and_offReal_of_antiPart_minor v hv e Q hQdet hQ
  exact ⟨e, Q, hfold, him, hQdet, hQ⟩

/-- Sharp source-side upper bound: every negative explicit separated continued-Cauchy
prime--Gamma block forces the same number of distinct off-critical conjugation-fold Xi spectral
orbits. -/
theorem exists_xiSpectralFoldPacket_of_xiSeparatedPacketWeilGram_negDef
    {k : ℕ} (P : Fin k → XiSeparatedContinuedCauchyPacket)
    (hneg : ∀ x : Fin k → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (xiSeparatedPacketWeilGram P).mulVec x).re < 0) :
    ∃ (e : Fin k → XiZeroCopy) (Q : Matrix (Fin k) (Fin k) ℂ),
      Function.Injective (fun r =>
        complexConjugationFold (xiSpectralPoint (e r))) ∧
      (∀ r, (xiSpectralPoint (e r)).im ≠ 0) ∧
      IsUnit Q.det ∧
      ∀ r s, Q r s = xiWeilAntiPart ((P s).evaluation) (e r) := by
  apply exists_xiSpectralFoldPacket_of_hilbertGram_negDef
    (fun j => (P j).evaluation)
  · intro j
    letI := (P j).fintypeIndex
    exact factorsThroughSpectral_xiWeilContinuedCauchyPacketLp
      (P j).coeff (P j).pole
  · simpa [xiSeparatedPacketWeilGram_eq_xiWeilHilbertGram] using hneg

/-- Exact finite source-index classification.  A negative-definite explicit continued-Cauchy
prime--Gamma block of dimension `k` exists if and only if the Xi divisor contains `k` distinct
off-real spectral locations modulo complex conjugation. -/
theorem exists_xiSeparatedPacketWeilGram_negDef_iff_exists_xiSpectralFoldPacket
    {k : ℕ} :
    (∃ P : Fin k → XiSeparatedContinuedCauchyPacket,
      ∀ x : Fin k → ℂ, x ≠ 0 →
        (star x ⬝ᵥ (xiSeparatedPacketWeilGram P).mulVec x).re < 0) ↔
    ∃ e : Fin k → XiZeroCopy,
      Function.Injective (fun r =>
        complexConjugationFold (xiSpectralPoint (e r))) ∧
      ∀ r, (xiSpectralPoint (e r)).im ≠ 0 := by
  constructor
  · rintro ⟨P, hneg⟩
    obtain ⟨e, _Q, hfold, him, _hQdet, _hQ⟩ :=
      exists_xiSpectralFoldPacket_of_xiSeparatedPacketWeilGram_negDef P hneg
    exact ⟨e, hfold, him⟩
  · rintro ⟨e, hfold, him⟩
    obtain ⟨P, _hP, hevent⟩ :=
      exists_xiSeparatedPacketWeilGram_eventually_negDef e hfold him
    obtain ⟨n, hn⟩ := hevent.exists
    exact ⟨fun j => P j n, hn⟩

/-- Fixed finite-source RH firewall.  RH is equivalent to absence of one strictly negative
explicit separated continued-Cauchy prime--Gamma Gram.  Off RH, one actual packet is a complete
finite witness; under RH, spectral reality excludes every such witness. -/
theorem riemannHypothesis_iff_no_negative_xiSeparatedPacketWeilGram :
    RiemannHypothesis ↔
      ¬ ∃ P : Fin 1 → XiSeparatedContinuedCauchyPacket,
        ∀ x : Fin 1 → ℂ, x ≠ 0 →
          (star x ⬝ᵥ (xiSeparatedPacketWeilGram P).mulVec x).re < 0 := by
  rw [xiSpectralPoint_im_eq_zero_iff_rh]
  constructor
  · intro hall hsource
    obtain ⟨e, _hfold, him⟩ :=
      exists_xiSeparatedPacketWeilGram_negDef_iff_exists_xiSpectralFoldPacket.mp hsource
    exact (him 0) (hall (e 0))
  · intro hsource q
    by_contra hq
    apply hsource
    apply exists_xiSeparatedPacketWeilGram_negDef_iff_exists_xiSpectralFoldPacket.mpr
    refine ⟨fun _ => q, ?_, ?_⟩
    · intro r s _hrs
      exact Subsingleton.elim r s
    · intro _r
      exact hq

/-- A one-dimensional reflected source Gram is negative definite exactly when its literal
prime--Gamma source energy is negative. -/
theorem xiSeparatedPacketWeilGram_single_negDef_iff_sourceEnergy_neg
    (P : XiSeparatedContinuedCauchyPacket) :
    (∀ x : Fin 1 → ℂ, x ≠ 0 →
      (star x ⬝ᵥ
        (xiSeparatedPacketWeilGram (fun _ => P)).mulVec x).re < 0) ↔
      P.sourceEnergy < 0 := by
  constructor
  · intro h
    have hx : (fun _ : Fin 1 => (1 : ℂ)) ≠ 0 := by
      intro hz
      have hz0 := congrFun hz 0
      norm_num at hz0
    have hn := h (fun _ => 1) hx
    simpa [dotProduct, Matrix.mulVec,
      xiSeparatedPacketWeilGram_diagonal_re] using hn
  · intro hP x hx
    have hx0 : x 0 ≠ 0 := by
      intro hx0
      apply hx
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      rw [hi, hx0]
      rfl
    have hnorm : 0 < Complex.normSq (x 0) :=
      Complex.normSq_pos.mpr hx0
    have hcalc :
        (star x ⬝ᵥ
          (xiSeparatedPacketWeilGram (fun _ => P)).mulVec x).re =
          Complex.normSq (x 0) * P.sourceEnergy := by
      simp [dotProduct, Matrix.mulVec,
        xiSeparatedPacketWeilGram_diagonal_re, Complex.normSq_apply]
      ring
    rw [hcalc]
    exact mul_neg_of_pos_of_neg hnorm hP

/-- Scalar finite-source falsification certificate.  Failure of RH is equivalent to existence of
one explicit pairwise-separated continued-Cauchy packet with strictly negative prime--Gamma source
energy. -/
theorem not_riemannHypothesis_iff_exists_xiSeparatedPacket_sourceEnergy_neg :
    ¬ RiemannHypothesis ↔
      ∃ P : XiSeparatedContinuedCauchyPacket, P.sourceEnergy < 0 := by
  constructor
  · intro hRH
    have hex : ∃ P : Fin 1 → XiSeparatedContinuedCauchyPacket,
        ∀ x : Fin 1 → ℂ, x ≠ 0 →
          (star x ⬝ᵥ (xiSeparatedPacketWeilGram P).mulVec x).re < 0 := by
      by_contra hno
      exact hRH (riemannHypothesis_iff_no_negative_xiSeparatedPacketWeilGram.mpr hno)
    obtain ⟨P, hP⟩ := hex
    have hPeq : P = fun _ => P 0 := by
      funext i
      exact congrArg P (Subsingleton.elim i 0)
    rw [hPeq] at hP
    exact ⟨P 0,
      xiSeparatedPacketWeilGram_single_negDef_iff_sourceEnergy_neg (P 0) |>.mp hP⟩
  · rintro ⟨P, hP⟩ hRH
    apply riemannHypothesis_iff_no_negative_xiSeparatedPacketWeilGram.mp hRH
    exact ⟨fun _ => P,
      xiSeparatedPacketWeilGram_single_negDef_iff_sourceEnergy_neg P |>.mpr hP⟩

/-- Universal scalar source criterion: RH holds exactly when every explicit pairwise-separated
continued-Cauchy prime--Gamma packet has nonnegative source energy. -/
theorem riemannHypothesis_iff_forall_xiSeparatedPacket_sourceEnergy_nonnegative :
    RiemannHypothesis ↔
      ∀ P : XiSeparatedContinuedCauchyPacket, 0 ≤ P.sourceEnergy := by
  constructor
  · intro hRH P
    by_contra hP
    have hneg : P.sourceEnergy < 0 := lt_of_not_ge hP
    exact (not_riemannHypothesis_iff_exists_xiSeparatedPacket_sourceEnergy_neg.mpr
      ⟨P, hneg⟩) hRH
  · intro hall
    by_contra hRH
    obtain ⟨P, hP⟩ :=
      not_riemannHypothesis_iff_exists_xiSeparatedPacket_sourceEnergy_neg.mp hRH
    exact (not_lt_of_ge (hall P)) hP

end

end RHTower
