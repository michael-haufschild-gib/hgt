import GaloisForLFunctions.HTGeometry.RegularizedDeterminantAlgebraicMultiplicity
import GaloisForLFunctions.RHTower.HedenmalmThetaActualFiniteDivisorRigidity
import GaloisForLFunctions.RHTower.HedenmalmThetaActualStageGreenBalance

/-!
# Explicit theta-source modewise Green flag

The former finite-stage specification records support, Hilbert--Schmidt accuracy, and trace zero,
but is spectrally nonselective.  This module isolates the exact source-coordinate replacement:
every nonzero eigenmode of every actual theta stage has zero complete Green charge.  No Xi zero,
divisor point, or spectral branch occurs in the definition.

The analytic completion is unconditional: actual kernels are Hilbert--Schmidt, converge in
Hilbert--Schmidt norm to the signed theta kernel, and their ordinary determinants converge
compact-open to normalized Xi.  The new arithmetic clause is exactly the unresolved part.  At
one finite stage it is equivalent to reality of that stage's divisor; globally it implies RH.
Thus installing the clause as a choice field would assume the desired theorem rather than prove it.
-/

open Complex Filter Metric

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmHilbertSchmidt

noncomputable section

/-- Source-only strengthened property at one actual theta stage.  It quantifies over all modes
rather than selecting a divisor point or an eigenbasis. -/
def ThetaSourceArithmeticGreenStageProperty (k : ℕ) : Prop :=
  ∀ {mu : ℂ} {f : H}, f ≠ 0 →
    thetaSourceSignedPulledOperator k f = mu • f →
    (inner ℂ (thetaSourceSignedStageGreenBoundary k f) f : ℂ) = 0

/-- Explicit cofinal theta-arithmetic flag: exact complete Green neutrality at every stage and on
every nonzero eigenmode. -/
def ThetaSourceArithmeticGreenFlag : Prop :=
  ∀ k : ℕ, ThetaSourceArithmeticGreenStageProperty k

/-- Exact Green neutrality at one stage forces every ordinary determinant zero to be real. -/
theorem thetaSourceArithmeticGreenStage_realDivisor
    (k : ℕ) (hgreen : ThetaSourceArithmeticGreenStageProperty k) :
    ThetaSourceSignedStageRealDivisor k := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp [thetaSourceSignedOrdinaryDet] at hz
  have hdet2 : entireDet2 (thetaSourceSignedKernel k) z = 0 := by
    rw [← thetaSourceSignedOrdinaryDet_eq_entireDet2 k z]
    exact hz
  obtain ⟨w, hw, heigen⟩ :=
    (entireDet2_eq_zero_iff_exists_eigenvector
      (isHS_thetaSourceSignedKernel k) hz0).mp hdet2
  let f : H := thetaCoord.symm w
  have hf : f ≠ 0 := by
    intro hfzero
    apply hw
    have h := congrArg thetaCoord hfzero
    simpa [f] using h
  have heigen' : thetaSourceSignedPulledOperator k f = z⁻¹ • f := by
    have h := congrArg thetaCoord.symm heigen
    simpa [thetaSourceSignedPulledOperator, thetaSourceSignedMatrixOperator, f] using h
  have himinv : z⁻¹.im = 0 :=
    (inner_thetaSourceSignedStageGreenBoundary_eigen_eq_zero_iff_im_eq_zero
      k hf heigen').mp (hgreen hf heigen')
  rw [Complex.inv_im] at himinv
  have hnorm : Complex.normSq z ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hz0
  have hneg : -z.im = 0 :=
    (div_eq_zero_iff).mp himinv |>.resolve_right hnorm
  linarith

/-- Conversely, real divisor at one stage gives exact Green neutrality on every mode. -/
theorem thetaSourceArithmeticGreenStage_of_realDivisor
    (k : ℕ) (hreal : ThetaSourceSignedStageRealDivisor k) :
    ThetaSourceArithmeticGreenStageProperty k := by
  intro mu f hf heigen
  apply (inner_thetaSourceSignedStageGreenBoundary_eigen_eq_zero_iff_im_eq_zero
    k hf heigen).mpr
  by_cases hmu : mu = 0
  · simp [hmu]
  · let w := thetaCoord f
    have hw : w ≠ 0 := by
      intro hwzero
      apply hf
      have h := congrArg thetaCoord.symm hwzero
      simpa [w] using h
    have heigen' : (HilbertSchmidt.toOperator (isHS_thetaSourceSignedKernel k)) w =
        mu • w := by
      have h := congrArg thetaCoord heigen
      simpa [thetaSourceSignedPulledOperator, thetaSourceSignedMatrixOperator, w] using h
    have hinv0 : mu⁻¹ ≠ 0 := inv_ne_zero hmu
    have hdet2 : entireDet2 (thetaSourceSignedKernel k) mu⁻¹ = 0 := by
      apply (entireDet2_eq_zero_iff_exists_eigenvector
        (isHS_thetaSourceSignedKernel k) hinv0).mpr
      refine ⟨w, hw, ?_⟩
      simpa [inv_inv] using heigen'
    have hdet : thetaSourceSignedOrdinaryDet k mu⁻¹ = 0 := by
      rw [thetaSourceSignedOrdinaryDet_eq_entireDet2]
      exact hdet2
    have himinv : mu⁻¹.im = 0 := hreal mu⁻¹ hdet
    rw [Complex.inv_im] at himinv
    have hnorm : Complex.normSq mu ≠ 0 := by
      simpa [Complex.normSq_eq_zero] using hmu
    have hneg : -mu.im = 0 :=
      (div_eq_zero_iff).mp himinv |>.resolve_right hnorm
    linarith

/-- At each finite stage, modewise rank-two Green neutrality is exactly real-divisor selection. -/
theorem thetaSourceArithmeticGreenStage_iff_realDivisor (k : ℕ) :
    ThetaSourceArithmeticGreenStageProperty k ↔
      ThetaSourceSignedStageRealDivisor k :=
  ⟨thetaSourceArithmeticGreenStage_realDivisor k,
    thetaSourceArithmeticGreenStage_of_realDivisor k⟩

/-- The cofinal source Green flag is exactly the all-stage real-divisor property. -/
theorem thetaSourceArithmeticGreenFlag_iff_allStagesRealDivisor :
    ThetaSourceArithmeticGreenFlag ↔ ThetaSourceSignedAllStagesRealDivisor := by
  constructor
  · intro hgreen k
    exact thetaSourceArithmeticGreenStage_realDivisor k (hgreen k)
  · intro hreal k
    exact thetaSourceArithmeticGreenStage_of_realDivisor k (hreal k)

/-- Unconditional finite-source completion.  Support, Hilbert--Schmidt membership, trace
cancellation, and Hilbert--Schmidt convergence hold before the new modal arithmetic clause. -/
theorem thetaSourceArithmeticStages_hilbertSchmidtCompletion :
    (∀ k p, p ∉ (thetaSourceSignedCutoff k) ×ˢ (thetaSourceSignedCutoff k) →
      thetaSourceSignedKernel k p = 0) ∧
    (∀ k, HilbertSchmidt.IsHS (thetaSourceSignedKernel k)) ∧
    (∀ k, HilbertSchmidt.hsTraceDiag (thetaSourceSignedKernel k) = 0) ∧
    Tendsto (fun k => HilbertSchmidt.hsNorm
      (thetaSourceSignedKernel k - (-thetaKernelMatrix))) atTop (nhds 0) := by
  exact ⟨thetaSourceSignedKernel_support, isHS_thetaSourceSignedKernel,
    hsTraceDiag_thetaSourceSignedKernel, thetaSourceSignedKernel_tendsto_source⟩

/-- Unconditional compact-open completion of the same source-defined stages. -/
theorem thetaSourceArithmeticStages_compactOpenCompletion :
    TendstoLocallyUniformly thetaSourceSignedOrdinaryDet
      (fun z => XiC z / XiC 0) atTop :=
  thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC

/-- Exact source-only Green flag, together with already-proved Hilbert--Schmidt and compact-open
completion, closes RH. -/
theorem riemannHypothesis_of_thetaSourceArithmeticGreenFlag
    (hgreen : ThetaSourceArithmeticGreenFlag) : RiemannHypothesis := by
  apply riemannHypothesis_of_thetaSourceSignedAllStagesRealDivisor
  exact thetaSourceArithmeticGreenFlag_iff_allStagesRealDivisor.mp hgreen

/-- Closed hostile audit: either RH holds or the explicit modal Green flag fails. -/
theorem riemannHypothesis_or_not_thetaSourceArithmeticGreenFlag :
    RiemannHypothesis ∨ ¬ ThetaSourceArithmeticGreenFlag := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr fun hgreen =>
      hRH (riemannHypothesis_of_thetaSourceArithmeticGreenFlag hgreen)

/-- Source-coordinate form of the failure branch: off RH, one actual stage has a nonzero
eigenmode carrying nonvanishing complete Green charge. -/
theorem riemannHypothesis_or_exists_thetaSourceArithmeticStage_nonNeutralMode :
    RiemannHypothesis ∨
      ∃ k : ℕ, ∃ mu : ℂ, ∃ f : H,
        f ≠ 0 ∧
        thetaSourceSignedPulledOperator k f = mu • f ∧
        (inner ℂ (thetaSourceSignedStageGreenBoundary k f) f : ℂ) ≠ 0 := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    by_contra hnone
    apply hRH
    apply riemannHypothesis_of_thetaSourceArithmeticGreenFlag
    intro k mu f hf heigen
    by_contra hcharge
    exact hnone ⟨k, mu, f, hf, heigen, hcharge⟩

/-- Closed frontier certificate.  Analytic completion is unconditional; exact modewise Green
neutrality is equivalent to real finite divisors and is sufficient for RH. -/
theorem thetaSourceArithmeticGreenFlag_certificate :
    ((∀ k, HilbertSchmidt.IsHS (thetaSourceSignedKernel k)) ∧
      Tendsto (fun k => HilbertSchmidt.hsNorm
        (thetaSourceSignedKernel k - (-thetaKernelMatrix))) atTop (nhds 0)) ∧
    TendstoLocallyUniformly thetaSourceSignedOrdinaryDet
      (fun z => XiC z / XiC 0) atTop ∧
    (ThetaSourceArithmeticGreenFlag ↔ ThetaSourceSignedAllStagesRealDivisor) ∧
    (ThetaSourceArithmeticGreenFlag → RiemannHypothesis) ∧
    (RiemannHypothesis ∨ ¬ ThetaSourceArithmeticGreenFlag) := by
  exact ⟨⟨isHS_thetaSourceSignedKernel, thetaSourceSignedKernel_tendsto_source⟩,
    thetaSourceArithmeticStages_compactOpenCompletion,
    thetaSourceArithmeticGreenFlag_iff_allStagesRealDivisor,
    riemannHypothesis_of_thetaSourceArithmeticGreenFlag,
    riemannHypothesis_or_not_thetaSourceArithmeticGreenFlag⟩

end

end RHTower.HedenmalmThetaSource
