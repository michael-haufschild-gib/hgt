import GaloisForLFunctions.HTGeometry.GammaMovingCenterScaleClockRelativeFormalHypertranscendenceUniversalityLaw
import GaloisForLFunctions.RHTower.GammaFactorialCompleteToricJetClosureUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaHigherJetResidueHierarchyUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaMovingCenterThreeChartAtlasUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusContactGammaScaleCovariantResidueJointFreenessUniversalityLaw

/-!
# Möbius-contact Gamma three-chart relative formal hypertranscendence

The contact-headed finite-part, covariant-residue, and inverse-branch Gamma charts are each
algebraically independent over the moving-center field. Injectively enumerating their common
scale head and countable tails turns all three into formally hypertranscendental power-series
germs over that same field. Their polynomial coordinate atlas remains exact, and the
inverse-branch presentation is the previously constructed Gamma scale-clock germ.
-/

open Filter MvPolynomial Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance mobiusContactGammaFormalNatGermAlgebra :
    Algebra GammaPoleRationalBase NatGerm :=
  ratNatEval.toAlgebra

local instance mobiusContactGammaMasterComplexNatGermAlgebra :
    Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

/-- Enumerate a contact-headed chart by its common scale head followed by every tail
coordinate. -/
def mobiusContactGammaScaleHeadedChartIndex : ℕ → Option ℕ :=
  gammaPoleScaleHeadedInverseClockIndex

theorem mobiusContactGammaScaleHeadedChartIndex_injective :
    Function.Injective mobiusContactGammaScaleHeadedChartIndex :=
  gammaPoleScaleHeadedInverseClockIndex_injective

def mobiusContactGammaScaleHeadedFinitePartCoefficientGerm : ℕ → NatGerm :=
  mobiusContactGammaFinitePartJetFamily ∘ mobiusContactGammaScaleHeadedChartIndex

def mobiusContactGammaScaleHeadedCovariantResidueCoefficientGerm : ℕ → NatGerm :=
  mobiusContactGammaCovariantResidueFamily ∘ mobiusContactGammaScaleHeadedChartIndex

def mobiusContactGammaScaleHeadedInverseBranchCoefficientGerm : ℕ → NatGerm :=
  mobiusContactGammaInverseBranchCoefficientFamily ∘ mobiusContactGammaScaleHeadedChartIndex

theorem
    algebraicIndependent_mobiusContactGammaScaleHeadedFinitePartCoefficientGerm_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      mobiusContactGammaScaleHeadedFinitePartCoefficientGerm := by
  exact mobiusContactGamma_allMovingCenterCharts_algebraicIndependent.1.comp
    mobiusContactGammaScaleHeadedChartIndex
    mobiusContactGammaScaleHeadedChartIndex_injective

theorem
    algebraicIndependent_mobiusContactGammaScaleHeadedCovariantResidueCoefficientGerm_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      mobiusContactGammaScaleHeadedCovariantResidueCoefficientGerm := by
  exact mobiusContactGamma_allMovingCenterCharts_algebraicIndependent.2.1.comp
    mobiusContactGammaScaleHeadedChartIndex
    mobiusContactGammaScaleHeadedChartIndex_injective

theorem
    algebraicIndependent_mobiusContactGammaScaleHeadedInverseBranchCoefficientGerm_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      mobiusContactGammaScaleHeadedInverseBranchCoefficientGerm := by
  exact mobiusContactGamma_allMovingCenterCharts_algebraicIndependent.2.2.comp
    mobiusContactGammaScaleHeadedChartIndex
    mobiusContactGammaScaleHeadedChartIndex_injective

/-- Contact-headed finite-part formal germ. -/
def mobiusContactGammaScaleHeadedFinitePartFormalGerm : PowerSeries NatGerm :=
  PowerSeries.mk mobiusContactGammaScaleHeadedFinitePartCoefficientGerm

/-- Contact-headed covariant-residue formal germ. -/
def mobiusContactGammaScaleHeadedCovariantResidueFormalGerm : PowerSeries NatGerm :=
  PowerSeries.mk mobiusContactGammaScaleHeadedCovariantResidueCoefficientGerm

/-- Contact-headed inverse-branch formal germ. -/
def mobiusContactGammaScaleHeadedInverseBranchFormalGerm : PowerSeries NatGerm :=
  PowerSeries.mk mobiusContactGammaScaleHeadedInverseBranchCoefficientGerm

theorem mobiusContactGammaScaleHeadedFinitePartFormalGerm_formallyHypertranscendental_over_ratFunc
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) GammaPoleRationalBase} (hP : P ≠ 0) :
    MvPolynomial.aeval
      (formalJetsOver n mobiusContactGammaScaleHeadedFinitePartFormalGerm) P ≠ 0 := by
  exact aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent_over
    mobiusContactGammaScaleHeadedFinitePartCoefficientGerm
    algebraicIndependent_mobiusContactGammaScaleHeadedFinitePartCoefficientGerm_over_ratFunc hP

theorem
    mobiusContactGammaScaleHeadedCovariantResidueFormalGerm_formallyHypertranscendental_over_ratFunc
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) GammaPoleRationalBase} (hP : P ≠ 0) :
    MvPolynomial.aeval
      (formalJetsOver n mobiusContactGammaScaleHeadedCovariantResidueFormalGerm) P ≠ 0 := by
  exact aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent_over
    mobiusContactGammaScaleHeadedCovariantResidueCoefficientGerm
    algebraicIndependent_mobiusContactGammaScaleHeadedCovariantResidueCoefficientGerm_over_ratFunc
    hP

theorem
    mobiusContactGammaScaleHeadedInverseBranchFormalGerm_formallyHypertranscendental_over_ratFunc
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) GammaPoleRationalBase} (hP : P ≠ 0) :
    MvPolynomial.aeval
      (formalJetsOver n mobiusContactGammaScaleHeadedInverseBranchFormalGerm) P ≠ 0 := by
  exact aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent_over
    mobiusContactGammaScaleHeadedInverseBranchCoefficientGerm
    algebraicIndependent_mobiusContactGammaScaleHeadedInverseBranchCoefficientGerm_over_ratFunc
    hP

/-- The contact-headed inverse-branch presentation is exactly the Gamma moving-center scale
clock. -/
theorem mobiusContactGammaScaleHeadedInverseBranchFormalGerm_eq :
    mobiusContactGammaScaleHeadedInverseBranchFormalGerm =
      gammaPoleScaleHeadedInverseClockFormalGerm := by
  rw [mobiusContactGammaScaleHeadedInverseBranchFormalGerm,
    mobiusContactGammaScaleHeadedInverseBranchCoefficientGerm,
    mobiusContactGammaScaleHeadedChartIndex,
    mobiusContactGammaInverseBranchCoefficientFamily_eq]
  rfl

/-- The pairwise unique polynomial-coordinate interchange property of the three contact-headed
moving-center charts. -/
def MobiusContactGammaMovingCenterThreeChartPolynomialAtlas : Prop :=
  ((∀ P, ∃! Q, mobiusContactGammaFinitePartJetRationalEval Q =
      mobiusContactGammaCovariantResidueRationalEval P) ∧
    (∀ Q, ∃! P, mobiusContactGammaCovariantResidueRationalEval P =
      mobiusContactGammaFinitePartJetRationalEval Q)) ∧
  ((∀ P, ∃! Q, mobiusContactGammaFinitePartJetRationalEval Q =
      mobiusContactGammaInverseBranchCoefficientRationalEval P) ∧
    (∀ Q, ∃! P, mobiusContactGammaInverseBranchCoefficientRationalEval P =
      mobiusContactGammaFinitePartJetRationalEval Q)) ∧
  ((∀ P, ∃! Q, mobiusContactGammaInverseBranchCoefficientRationalEval Q =
      mobiusContactGammaCovariantResidueRationalEval P) ∧
    (∀ Q, ∃! P, mobiusContactGammaCovariantResidueRationalEval P =
      mobiusContactGammaInverseBranchCoefficientRationalEval Q))

/-- **Möbius-contact Gamma three-chart relative formal-hypertranscendence atlas universality
law.** All three contact-headed moving-center charts are formally hypertranscendental over
`ℂ(N)` at every finite jet order, are pairwise unique polynomial coordinates for one evaluated
algebra, and the inverse chart is the exact Gamma scale clock. -/
theorem mobiusContactGamma_threeChartRelativeFormalHypertranscendenceAtlasUniversality :
    (∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) GammaPoleRationalBase), P ≠ 0 →
      MvPolynomial.aeval
        (formalJetsOver n mobiusContactGammaScaleHeadedFinitePartFormalGerm) P ≠ 0) ∧
    (∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) GammaPoleRationalBase), P ≠ 0 →
      MvPolynomial.aeval
        (formalJetsOver n mobiusContactGammaScaleHeadedCovariantResidueFormalGerm) P ≠ 0) ∧
    (∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) GammaPoleRationalBase), P ≠ 0 →
      MvPolynomial.aeval
        (formalJetsOver n mobiusContactGammaScaleHeadedInverseBranchFormalGerm) P ≠ 0) ∧
    MobiusContactGammaMovingCenterThreeChartPolynomialAtlas ∧
    mobiusContactGammaScaleHeadedInverseBranchFormalGerm =
      gammaPoleScaleHeadedInverseClockFormalGerm := by
  refine ⟨fun _ _ hP =>
      mobiusContactGammaScaleHeadedFinitePartFormalGerm_formallyHypertranscendental_over_ratFunc
        hP,
    fun _ _ hP =>
      mobiusContactGammaScaleHeadedCovariantResidueFormalGerm_formallyHypertranscendental_over_ratFunc
        hP,
    fun _ _ hP =>
      mobiusContactGammaScaleHeadedInverseBranchFormalGerm_formallyHypertranscendental_over_ratFunc
        hP,
    ?_, mobiusContactGammaScaleHeadedInverseBranchFormalGerm_eq⟩
  exact mobiusContactGamma_completeMovingCenterThreeChartAtlasUniversality

/-- The Gamma moving-center three-chart polynomial-atlas interface is unconditional. -/
theorem mobiusContactGammaMovingCenterThreeChartPolynomialAtlas :
    MobiusContactGammaMovingCenterThreeChartPolynomialAtlas :=
  mobiusContactGamma_threeChartRelativeFormalHypertranscendenceAtlasUniversality.2.2.2.1

/-- The complete analytic, algebraic, and formal payload carried by the single Möbius-contact
Gamma pole-scale coordinate. -/
structure MobiusContactGammaToricFormalAtlasMasterCertificate : Prop where
  contactScale :
    ∀ n : ℕ,
      mobiusContactGammaHigherJetFactorialScale n =
        GaloisForLFunctions.reciprocalGammaFactorialScale n
  jointAlgebraicFreeness :
    AlgebraicIndependent ℂ mobiusContactGammaScaleAndCovariantResidueFamily
  finitePartFormalFreeness :
    ∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) GammaPoleRationalBase), P ≠ 0 →
      MvPolynomial.aeval
        (formalJetsOver n mobiusContactGammaScaleHeadedFinitePartFormalGerm) P ≠ 0
  covariantResidueFormalFreeness :
    ∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) GammaPoleRationalBase), P ≠ 0 →
      MvPolynomial.aeval
        (formalJetsOver n mobiusContactGammaScaleHeadedCovariantResidueFormalGerm) P ≠ 0
  inverseBranchFormalFreeness :
    ∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) GammaPoleRationalBase), P ≠ 0 →
      MvPolynomial.aeval
        (formalJetsOver n mobiusContactGammaScaleHeadedInverseBranchFormalGerm) P ≠ 0
  polynomialAtlas :
    MobiusContactGammaMovingCenterThreeChartPolynomialAtlas
  inverseClock :
    mobiusContactGammaScaleHeadedInverseBranchFormalGerm =
      gammaPoleScaleHeadedInverseClockFormalGerm
  toricClosure :
    (∀ x : ℂ, x ≠ 0 →
      Tendsto (fun n => gammaFactorialProjectiveSecondFirstClosureRatio n x)
        atTop (𝓝 (-1 / 9)) ∧
      Tendsto (fun n => gammaFactorialProjectiveThirdSecondClosureRatio n x)
        atTop (𝓝 (-1 / 6)) ∧
      Tendsto (fun n => gammaFactorialLogSecondHarmonicClosureRatio n x)
        atTop (𝓝 (-((Real.pi : ℂ) ^ 2) / 9)) ∧
      Tendsto (fun n => gammaFactorialLogEnvelopeSixthJetClosureRatio n x)
        atTop (𝓝 729)) ∧
    ∀ aF aS aP aT aL aE aH : ℤ,
      GammaFactorialToricBalanced aF aS aP aT aL aE aH ↔
        ∃ u v w q : ℤ,
          aF = u - 6 * q ∧
          aS = -2 * u - 2 * v - 2 * w + 6 * q ∧
          aP = u ∧
          aT = v ∧
          aL = w + q ∧
          aE = -q ∧
          aH = 2 * w

/-- **Möbius-contact Gamma toric formal-atlas master universality law.**  The observable
contact defect is the common Gamma pole scale supporting joint residue freeness, three
formally hypertranscendental polynomial-coordinate charts over `ℂ(N)`, and the complete
rank-four toric lattice of scale-free analytic jet closures. -/
theorem mobiusContactGamma_toricFormalAtlasMasterUniversality :
    MobiusContactGammaToricFormalAtlasMasterCertificate := by
  have hcharts :=
    mobiusContactGamma_threeChartRelativeFormalHypertranscendenceAtlasUniversality
  exact
    ⟨mobiusContactGammaHigherJetFactorialScale_eq,
      algebraicIndependent_mobiusContactGammaScaleAndCovariantResidueFamily,
      hcharts.1,
      hcharts.2.1,
      hcharts.2.2.1,
      mobiusContactGammaMovingCenterThreeChartPolynomialAtlas,
      hcharts.2.2.2.2,
      gammaFactorial_completeToricJetClosureUniversality⟩

end

end GaloisForLFunctions.RHTower
