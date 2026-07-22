import GaloisForLFunctions.RHTower.PrimeArchEuclideanSpectralRH
import GaloisForLFunctions.RHTower.PrimeArchKrylovResidualRH
import GaloisForLFunctions.RHTower.XiRadialJensenMassCentralCurvature
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniResolventSourceLaw
import GaloisForLFunctions.RHTower.XiThermalQuadraticReflectionDefectSpectrum

/-!
# Xi Euclidean--Krylov--Jensen reflection universality

Four terminal source modules describe one spectral-reflection boundary: Euclidean spectral
representability of the prime--Gamma moment tower, nontermination of its exact Krylov chain,
saturation of the centered radial Jensen mass, and vanishing of the Cassini/thermal/operator
anti-reflection defects.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- Simultaneous realization in ten Euclidean, Krylov, Jensen, Cassini, thermal, and operator
reflection charts. -/
def XiEuclideanKrylovJensenReflectionUniversalCertificate : Prop :=
  PrimeArchEuclideanSpectralRepresentation ∧
  PrimeArchInfiniteEuclideanSpectralRepresentation ∧
  (∃ v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
    (∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ)) ∧
    ComplexKrylovResidualsNonzero v) ∧
  xiCenteredRadialJensenMass = primeArchCentralCurvature ∧
  xiCenteredRadialJensenMass ≤ primeArchCentralCurvature ∧
  4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal +
      (iteratedDeriv 63 (logDeriv xiSquaredSeamCassiniSource) 0).re /
        ((63 : ℕ).factorial : ℝ) = 0 ∧
  xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy = 0 ∧
  ThetaCuspCassiniInwardBoundarySaturated ∧
  xiThermalSquareReflectionDefectEnergy = 0 ∧
  HilbertSchmidt.hsNormSq
      (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1 -
        HilbertSchmidt.hsAdjoint
          (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1)) = 0

/-- **Euclidean--Krylov--Jensen reflection universality law.**  RH is equivalent to simultaneous
realization of the ten terminal spectral-reflection charts. -/
theorem riemannHypothesis_iff_euclideanKrylovJensenReflectionUniversalCertificate :
    RiemannHypothesis ↔ XiEuclideanKrylovJensenReflectionUniversalCertificate := by
  constructor
  · intro hRH
    have hinfinite : PrimeArchInfiniteEuclideanSpectralRepresentation :=
      primeArchInfiniteEuclideanSpectralRepresentation_iff_riemannHypothesis.2 hRH
    have hjensen : xiCenteredRadialJensenMass = primeArchCentralCurvature :=
      xiCenteredRadialJensenMass_eq_centralCurvature_iff_rh.2 hRH
    have htheta : ThetaCuspCassiniInwardBoundarySaturated :=
      thetaCuspCassiniInwardBoundarySaturated_iff_riemannHypothesis.2 hRH
    have hthermal : xiThermalSquareReflectionDefectEnergy = 0 :=
      xiThermalSquareReflectionDefectEnergy_eq_zero_iff_rh.2 hRH
    have hkrylov :
        ∃ v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
          (∀ i j, inner ℂ (v i) (v j) =
            (normalizedPrimeArchMoment (i + j) : ℂ)) ∧
          ComplexKrylovResidualsNonzero v := by
      refine ⟨primeArchReflectionVector hRH,
        inner_primeArchReflectionVector_eq_normalizedMoment hRH, ?_⟩
      intro k
      let n := k + 1
      have hmatrix :
          Matrix.gram ℂ
              (fun i : Fin n => primeArchReflectionVector hRH (i : ℕ)) =
            (algebraMap ℝ ℂ).mapMatrix (primeArchSourceMomentHankelMatrix n) := by
        ext i j
        rw [Matrix.gram_apply, inner_primeArchReflectionVector_eq_normalizedMoment]
        rfl
      have hdetReal : 0 < (primeArchSourceMomentHankelMatrix n).det :=
        (primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mpr hRH) n
      have hdet :
          (Matrix.gram ℂ
            (fun i : Fin n => primeArchReflectionVector hRH (i : ℕ))).det ≠ 0 := by
        rw [hmatrix, ← RingHom.map_det]
        exact (map_ne_zero (algebraMap ℝ ℂ)).2 (ne_of_gt hdetReal)
      have hli : LinearIndependent ℂ
          (fun i : Fin n => primeArchReflectionVector hRH (i : ℕ)) :=
        Matrix.det_gram_ne_zero_iff_linearIndependent.mp hdet
      have hres := InnerProductSpace.gramSchmidt_ne_zero
        (⟨k, Nat.lt_succ_self k⟩ : Fin n) hli
      rw [GaloisForLFunctions.HTGeometry.gramSchmidt_fin_val] at hres
      exact hres
    exact ⟨
      primeArchEuclideanSpectralRepresentation_of_infinite hinfinite,
      hinfinite,
      hkrylov,
      hjensen,
      hjensen.le,
      intrinsicCassiniJetResidual_eq_zero_iff_riemannHypothesis.2 hRH,
      thetaCuspCassiniInwardBoundarySaturated_iff_reflectionDefect_zero.1 htheta,
      htheta,
      hthermal,
      by rw [xiReciprocalSquareKernel_adjointDefect_hsNormSq_eq_reflectionEnergy,
        hthermal]⟩
  · intro hcertificate
    exact primeArchEuclideanSpectralRepresentation_iff_riemannHypothesis.1 hcertificate.1

/-- Simultaneous failure of all ten terminal spectral-reflection charts. -/
def XiEuclideanKrylovJensenReflectionFailureUniversalCertificate : Prop :=
  (¬ PrimeArchEuclideanSpectralRepresentation) ∧
  (¬ PrimeArchInfiniteEuclideanSpectralRepresentation) ∧
  (¬ ∃ v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
    (∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ)) ∧
    ComplexKrylovResidualsNonzero v) ∧
  (¬ xiCenteredRadialJensenMass = primeArchCentralCurvature) ∧
  (¬ xiCenteredRadialJensenMass ≤ primeArchCentralCurvature) ∧
  (¬ 4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal +
      (iteratedDeriv 63 (logDeriv xiSquaredSeamCassiniSource) 0).re /
        ((63 : ℕ).factorial : ℝ) = 0) ∧
  (¬ xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy = 0) ∧
  (¬ ThetaCuspCassiniInwardBoundarySaturated) ∧
  (¬ xiThermalSquareReflectionDefectEnergy = 0) ∧
  (¬ HilbertSchmidt.hsNormSq
      (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1 -
        HilbertSchmidt.hsAdjoint
          (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1)) = 0)

/-- **Synchronized Euclidean--Krylov--Jensen reflection failure law.** -/
theorem not_riemannHypothesis_iff_euclideanKrylovJensenReflectionFailureUniversalCertificate :
    ¬ RiemannHypothesis ↔
      XiEuclideanKrylovJensenReflectionFailureUniversalCertificate := by
  constructor
  · intro hnotRH
    exact ⟨
      fun h => hnotRH (primeArchEuclideanSpectralRepresentation_iff_riemannHypothesis.1 h),
      fun h => hnotRH
        (primeArchInfiniteEuclideanSpectralRepresentation_iff_riemannHypothesis.1 h),
      fun h => by
        obtain ⟨v, hgram, hresidual⟩ := h
        exact hnotRH
          (riemannHypothesis_of_primeArchComplexKrylovResidualsNonzero v hgram hresidual),
      fun h => hnotRH (xiCenteredRadialJensenMass_eq_centralCurvature_iff_rh.1 h),
      fun h => hnotRH (xiCenteredRadialJensenMass_le_centralCurvature_iff_rh.1 h),
      fun h => hnotRH (intrinsicCassiniJetResidual_eq_zero_iff_riemannHypothesis.1 h),
      fun h => hnotRH (thetaCuspCassiniInwardBoundarySaturated_iff_riemannHypothesis.1
        (thetaCuspCassiniInwardBoundarySaturated_iff_reflectionDefect_zero.2 h)),
      fun h => hnotRH (thetaCuspCassiniInwardBoundarySaturated_iff_riemannHypothesis.1 h),
      fun h => hnotRH (xiThermalSquareReflectionDefectEnergy_eq_zero_iff_rh.1 h),
      fun h => hnotRH (xiThermalSquareReflectionDefectEnergy_eq_zero_iff_rh.1 (by
        rw [← xiReciprocalSquareKernel_adjointDefect_hsNormSq_eq_reflectionEnergy]
        exact h))⟩
  · intro hcertificate hRH
    exact hcertificate.1
      (primeArchEuclideanSpectralRepresentation_iff_riemannHypothesis.2 hRH)

end

end RHTower
