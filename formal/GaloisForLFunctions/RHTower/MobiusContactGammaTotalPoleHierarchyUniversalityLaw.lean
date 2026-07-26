import GaloisForLFunctions.RHTower.MobiusContactDigammaGammaAllJetPoleObstructionUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaAffineSecondSubprincipalPhaseUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaAllOrderParityResidueUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaBranchTransportedParityResidueUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaHarmonicTransverseResidueUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaHigherJetResidueHierarchyUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaIterateAllJetHypertranscendenceUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaIterateFirstJetMicroscopeUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaPunctureCapacityAtlasUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaScaleFreeJetRatioUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaThreeChartRelativeFormalHypertranscendenceAtlasUniversalityLaw

/-!
# Möbius-contact Gamma total pole-hierarchy universality

The oriented finite Möbius contact defect is one common coordinate for the complete proved Gamma
pole hierarchy: connection tensors, parity residues, branch transport, higher jets, puncture
geometry, iterate microscopes, differential obstruction, affine/nonlinear phase separation, and
the toric formal atlas.
-/

open Complex Filter Topology MvPolynomial

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Complete proved payload carried by the single Möbius-contact Gamma pole coordinate. -/
structure MobiusContactGammaTotalPoleHierarchyCertificate : Prop where
  connectionTensor :
    (∀ N : ℕ,
      ‖(-2 - mobiusGammaContactPartialCharge N) / 2‖ =
        GaloisForLFunctions.HTGeometry.gammaFactorialConnectionTransport N) ∧
    Tendsto (fun N : ℕ => ‖(-2 - mobiusGammaContactPartialCharge N) / 2‖)
      atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ‖(-2 - mobiusGammaContactPartialCharge N) / 2‖⁻¹)
      atTop atTop ∧
    ∀ branch n : ℕ, ∀ j : Fin (n + 1),
      ‖GaloisForLFunctions.gammaPoleCovariantTopResidueValue branch n j‖ =
        ‖(-2 - mobiusGammaContactPartialCharge branch) / 2‖⁻¹ ^ (j : ℕ) *
          ((j : ℕ).factorial : ℝ)
  allOrderParity :
    ∀ r : ℕ, ∀ x : ℂ, x ≠ 0 →
      Tendsto (fun n : ℕ =>
        (GaloisForLFunctions.gammaFactorialScaledPolygamma (2 * r + 1) n x -
            ((2 * r + 1).factorial : ℂ) / x ^ (2 * r + 2)) /
          mobiusContactGammaParityFactorialScale n ^ (2 * r + 2)) atTop
        (𝓝 (2 * (((2 * r + 1).factorial : ℂ) *
          riemannZeta ((2 * r + 2 : ℕ) : ℂ)))) ∧
      2 * (((2 * r + 1).factorial : ℂ) *
          riemannZeta ((2 * r + 2 : ℕ) : ℂ)) ≠ 0 ∧
      Tendsto (fun n : ℕ =>
        (GaloisForLFunctions.gammaFactorialScaledPolygamma (2 * r + 2) n x -
            (-(((2 * r + 2).factorial : ℂ) / x ^ (2 * r + 3)))) /
          mobiusContactGammaParityFactorialScale n ^ (2 * r + 3)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ((((n + 1 : ℕ) : ℂ) ^ (2 * r + 2)) *
        ((GaloisForLFunctions.gammaFactorialScaledPolygamma (2 * r + 2) n x -
            (-(((2 * r + 2).factorial : ℂ) / x ^ (2 * r + 3)))) /
          mobiusContactGammaParityFactorialScale n ^ (2 * r + 3)))) atTop
        (𝓝 (-(‖GaloisForLFunctions.gammaPoleCovariantTopResidueValue 0 (2 * r + 1)
          (Fin.last (2 * r + 1))‖ : ℂ)))
  branchParity :
    ∀ (r branch : ℕ) (x : ℂ), x ≠ 0 →
      Tendsto (fun n =>
        (mobiusContactGammaBranchParityTensorScale branch r : ℂ) *
          mobiusContactGammaOddCorrection r n x) atTop
        (𝓝 (2 *
          ((‖GaloisForLFunctions.gammaPoleCovariantTopResidueValue branch
            (2 * r + 1) (Fin.last (2 * r + 1))‖ : ℂ) *
            riemannZeta ((2 * r + 2 : ℕ) : ℂ)))) ∧
      Tendsto (fun n =>
        (mobiusContactGammaBranchParityTensorScale branch r : ℂ) *
          mobiusContactGammaEvenFiniteTail r n x) atTop
        (𝓝 (-(‖GaloisForLFunctions.gammaPoleCovariantTopResidueValue branch
          (2 * r + 1) (Fin.last (2 * r + 1))‖ : ℂ))) ∧
      Tendsto (fun n => mobiusContactGammaCrossParityRatio r n x) atTop
        (𝓝 (-2 * riemannZeta ((2 * r + 2 : ℕ) : ℂ))) ∧
      -2 * riemannZeta ((2 * r + 2 : ℕ) : ℂ) ≠ 0
  harmonicResidue :
    (∀ n : ℕ,
      Tendsto (fun x : ℂ =>
          x * GaloisForLFunctions.gammaFactorialFirstJetDefect n x)
        (𝓝[≠] 0)
        (𝓝 (-2 * ((-2 - mobiusGammaContactPartialCharge n) / 2) *
          Complex.digamma ((n : ℂ) + 1)))) ∧
    Tendsto (fun n : ℕ =>
      (-2 * ((-2 - mobiusGammaContactPartialCharge n) / 2) *
        Complex.digamma ((n : ℂ) + 1)) /
          mobiusContactGammaHarmonicMicroscopeScale n)
      atTop (𝓝 (-2)) ∧
    ∀ x : ℂ, x ≠ 0 →
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialFirstJetDefect n x /
          mobiusContactGammaHarmonicMicroscopeScale n)
        atTop (𝓝 (-2 / x))
  higherJetResidues :
    ∀ x : ℂ, x ≠ 0 →
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
          mobiusContactGammaHigherJetHarmonicScale n)
        atTop (𝓝 (6 / x ^ 2)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetProjectiveDefect n x /
          mobiusContactGammaHigherJetHarmonicScale n)
        atTop (𝓝 (2 / x ^ 3)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialThirdJetProjectiveDefect n x /
          mobiusContactGammaHigherJetHarmonicScale n ^ 2)
        atTop (𝓝 (-6 / x ^ 4)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
          mobiusContactGammaHigherJetFactorialScale n ^ 2)
        atTop (𝓝 (-4 * (Real.pi : ℂ) ^ 2 / x ^ 4)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x /
          mobiusContactGammaHigherJetFactorialScale n ^ 2)
        atTop (𝓝 (-4 * (Real.pi : ℂ) ^ 2 / x ^ 10))
  scaleFreeJetRatios :
    ∀ x : ℂ, x ≠ 0 →
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
          GaloisForLFunctions.gammaFactorialFirstJetDefect n x)
        atTop (𝓝 (-3 / x)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetProjectiveDefect n x /
          GaloisForLFunctions.gammaFactorialFirstJetDefect n x)
        atTop (𝓝 (-1 / x ^ 2)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialThirdJetProjectiveDefect n x /
          GaloisForLFunctions.gammaFactorialFirstJetDefect n x ^ 2)
        atTop (𝓝 (-3 / (2 * x ^ 2))) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
          GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x)
        atTop (𝓝 (x ^ 6))
  punctureAtlas :
    ∀ n : ℕ, ∀ z : ℂ,
      gammaPunctureMobiusContactNormalizedSheet n z =
          GaloisForLFunctions.gammaCommonInverseCollar.branch n
            (GaloisForLFunctions.HTGeometry.gammaPunctureCoordinate z) ∧
        GaloisForLFunctions.gammaMovingBaseTransition n
            (GaloisForLFunctions.HTGeometry.gammaPunctureCoordinate z) =
          GaloisForLFunctions.mobiusTangentGerm
            (GaloisForLFunctions.gammaMovingBaseShell n)
            (gammaPunctureMobiusContactNormalizedSheet n z) ∧
        gammaPunctureMobiusContactNormalizedSheet n
            (z + 2 * (Real.pi : ℂ) * Complex.I) =
          gammaPunctureMobiusContactNormalizedSheet n z
  punctureCapacity :
    ∀ {n : ℕ},
      GaloisForLFunctions.gammaCommonInverseCollar.threshold ≤ n →
      ∀ {z v : ℂ},
      GaloisForLFunctions.HTGeometry.gammaPunctureCoordinate z ∈
          Metric.closedBall (0 : ℂ) (1 / 4) →
      ‖GaloisForLFunctions.gammaMovingBaseShell n‖ < (1 / 2 : ℝ) →
      (16 / 81 : ℝ) * ‖v‖ ^ 2 ≤
          ‖(1 - GaloisForLFunctions.gammaMovingBaseShell n *
            gammaPunctureMobiusContactNormalizedSheet n z)⁻¹ ^ 2 * v‖ ^ 2 ∧
        ‖(1 - GaloisForLFunctions.gammaMovingBaseShell n *
            gammaPunctureMobiusContactNormalizedSheet n z)⁻¹ ^ 2 * v‖ ^ 2 ≤
          16 * ‖v‖ ^ 2
  punctureTangent :
    ∀ {z : ℂ},
      GaloisForLFunctions.HTGeometry.gammaPunctureCoordinate z ∈
          Metric.closedBall (0 : ℂ) (1 / 4) →
      Tendsto
        (fun n : ℕ =>
          (1 - GaloisForLFunctions.gammaMovingBaseShell n *
            gammaPunctureMobiusContactNormalizedSheet n z)⁻¹ ^ 2)
        atTop (nhds 1)
  iterateFirstJet :
    (∀ (k : ℕ) (x : ℂ),
      1 ≤ k →
      x ∈ GaloisForLFunctions.localGammaMicroscopeDomain
        (GaloisForLFunctions.gammaIterateRegularSet k) →
      x ∈ GaloisForLFunctions.gammaFactorialMicroscopeDomain →
      ∀ i : Fin (k + 1) × Fin 2,
        Tendsto (fun n =>
            mobiusContactGammaIterateScaledFirstJetTail (k + 1) n x i)
          atTop (𝓝 (GaloisForLFunctions.gammaFirstJetBoundaryTail
            k ((-x)⁻¹) i))) ∧
      AlgebraicIndependent ℂ
        GaloisForLFunctions.gammaIterateInfiniteFirstJetFamily
  iterateAllJets :
    (∀ (k : ℕ) (x : ℂ),
      x ∈ GaloisForLFunctions.localGammaMicroscopeDomain
        (GaloisForLFunctions.gammaIterateRegularSet k) →
      ∀ j : ℕ,
        Tendsto
          (fun n => iteratedDeriv j
            (mobiusContactGammaAllJetZoom
              (fun z => GaloisForLFunctions.gammaIterate k (Complex.Gamma z)) n) x)
          atTop
          (𝓝 (iteratedDeriv j
            (GaloisForLFunctions.outerReciprocalLimit
              (GaloisForLFunctions.gammaIterate k)) x))) ∧
    (∀ k : ℕ, 1 ≤ k →
      GaloisForLFunctions.Hypertranscendental
        (GaloisForLFunctions.gammaIterate k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∀ V : Set ℂ, IsOpen V → V.Nonempty →
        V ⊆ GaloisForLFunctions.gammaIterateRegularSet k →
        ¬ GaloisForLFunctions.DifferentiallyAlgebraicOn
          (GaloisForLFunctions.gammaIterate k) V)
  digammaGammaAllJets :
    (∀ (x : ℂ), x ∈ GaloisForLFunctions.reciprocalGammaBlowUpDisk →
      ∀ j : ℕ,
        Tendsto
          (fun n => iteratedDeriv j
            (mobiusContactDigammaGammaZoom
              (fun z => Complex.digamma (Complex.Gamma z)) n) x)
          atTop
          (𝓝 (iteratedDeriv j GaloisForLFunctions.digammaReciprocalLimit x))) ∧
    GaloisForLFunctions.Hypertranscendental
      (fun z => Complex.digamma (Complex.Gamma z)) ∧
    (∀ V : Set ℂ, IsOpen V → V.Nonempty →
      V ⊆ GaloisForLFunctions.digammaGammaRegularSet →
      ¬GaloisForLFunctions.DifferentiallyAlgebraicOn
        (fun z => Complex.digamma (Complex.Gamma z)) V) ∧
    (∀ n : ℕ,
      ¬GaloisForLFunctions.LocallyMeromorphicallyAlgebraicAt
        (fun z : ℂ => Complex.digamma (Complex.Gamma z)) (-(n : ℂ)))
  affineSecondSubprincipal :
    ∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) (W : ℕ),
      P.IsWeightedHomogeneous
          (GaloisForLFunctions.bellJetWeight (n + 2)) W →
      2 ≤ W →
      GaloisForLFunctions.gammaPolePrincipalReflectionSymbol (n + 1) P = 0 →
      GaloisForLFunctions.gammaPolePrincipalReflectionSymbol (n + 1)
          (MvPolynomial.pderiv (0 : Fin (n + 2)) P) = 0 →
      GammaMobiusContactAffineSecondSubprincipalPhaseSeparationCertificate n P W
  toricFormalAtlas :
    MobiusContactGammaToricFormalAtlasMasterCertificate

/--
**Möbius-contact Gamma total pole-hierarchy universality.**

One arithmetic contact defect carries every proved analytic, geometric, differential, algebraic,
and formal Gamma pole layer.
-/
theorem mobiusContactGamma_totalPoleHierarchyUniversality :
    MobiusContactGammaTotalPoleHierarchyCertificate := by
  exact {
    connectionTensor := mobiusContactGamma_completeConnectionTensorUniversality
    allOrderParity := mobiusContactGammaAllOrder_completeParityResidueUniversality
    branchParity := mobiusContactGamma_branchTransportedParityResidueUniversality
    harmonicResidue := mobiusContactGammaHarmonic_completeTransverseResidueUniversality
    higherJetResidues := mobiusContactGammaHigherJet_completeResidueHierarchyUniversality
    scaleFreeJetRatios := mobiusContactGamma_scaleFreeJetRatioUniversality
    punctureAtlas := gammaPunctureMobiusContact_completeAtlasUniversality
    punctureCapacity :=
      gammaPunctureMobiusContactNormalizedSheet_capacity_congruent
    punctureTangent :=
      tendsto_gammaPunctureMobiusContactNormalizedSheet_tangentFactor_one
    iterateFirstJet := mobiusContactGammaIteration_completeFirstJetMicroscopeUniversality
    iterateAllJets := mobiusContactGammaIteration_completeAllJetHypertranscendenceUniversality
    digammaGammaAllJets := mobiusContactDigammaGamma_completeAllJetPoleObstructionUniversality
    affineSecondSubprincipal := fun n P W hP hW hcancel hpartial =>
      gammaMobiusContactAffineSecondSubprincipal_phaseSeparationUniversality
        n P hP hW hcancel hpartial
    toricFormalAtlas := mobiusContactGamma_toricFormalAtlasMasterUniversality }

end

end GaloisForLFunctions.RHTower
