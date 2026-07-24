import GaloisForLFunctions.HTGeometry.GammaPoleScalePrincipalRemainderUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma moving-center three-chart atlas universality

The shifted negative Möbius contact defect is the common head of the finite-part,
covariant-residue, and normalized inverse-branch Gamma pole charts. All three remain countably
free over the moving-center field and are pairwise uniquely interchangeable by polynomial maps.
-/

open Filter MvPolynomial

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance mobiusContactGammaMovingCenterNatGermAlgebra :
    Algebra GaloisForLFunctions.GammaPoleRationalBase GaloisForLFunctions.NatGerm :=
  GaloisForLFunctions.ratNatEval.toAlgebra

/-- Shifted negative contact defect used as the distinguished moving-center chart coordinate. -/
def mobiusContactGammaMovingCenterScaleGerm : GaloisForLFunctions.NatGerm :=
  fun N : ℕ => -((-2 - mobiusGammaContactPartialCharge (N - 1)) / 2)

theorem mobiusContactGammaMovingCenterScaleGerm_eq :
    mobiusContactGammaMovingCenterScaleGerm =
      GaloisForLFunctions.reciprocalSignedFactorialGerm := by
  change
    (↑(fun N : ℕ => -((-2 - mobiusGammaContactPartialCharge (N - 1)) / 2)) :
      GaloisForLFunctions.NatGerm) =
    (↑GaloisForLFunctions.reciprocalSignedFactorialSequence :
      GaloisForLFunctions.NatGerm)
  rw [Filter.Germ.coe_eq]
  exact Filter.eventually_atTop.2 ⟨1, fun N hN => by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
    have hscale :
        (-2 - mobiusGammaContactPartialCharge n) / 2 =
          GaloisForLFunctions.reciprocalGammaFactorialScale n := by
      rw [mobiusGammaContactPartialCharge_eq]
      simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
      ring
    change -((-2 - mobiusGammaContactPartialCharge ((1 + n) - 1)) / 2) =
      GaloisForLFunctions.reciprocalSignedFactorialSequence (1 + n)
    rw [Nat.add_sub_cancel_left, hscale]
    simpa [Nat.add_comm] using
      (GaloisForLFunctions.reciprocalSignedFactorialSequence_succ_eq_neg_scale n).symm⟩

/-- Replace the factorial head of a countable Gamma pole chart by the equal contact germ. -/
def mobiusContactGammaMovingCenterChartFamily
    (tail : ℕ → GaloisForLFunctions.NatGerm) :
    Option ℕ → GaloisForLFunctions.NatGerm
  | none => mobiusContactGammaMovingCenterScaleGerm
  | some j => tail j

def mobiusContactGammaFinitePartJetFamily :
    Option ℕ → GaloisForLFunctions.NatGerm :=
  mobiusContactGammaMovingCenterChartFamily
    GaloisForLFunctions.gammaPoleFinitePartJetGerm

def mobiusContactGammaCovariantResidueFamily :
    Option ℕ → GaloisForLFunctions.NatGerm :=
  mobiusContactGammaMovingCenterChartFamily
    GaloisForLFunctions.gammaSimpleZeroCovariantResidueGerm

def mobiusContactGammaInverseBranchCoefficientFamily :
    Option ℕ → GaloisForLFunctions.NatGerm :=
  mobiusContactGammaMovingCenterChartFamily
    GaloisForLFunctions.gammaInversePoleBranchCoefficientGerm

theorem mobiusContactGammaFinitePartJetFamily_eq :
    mobiusContactGammaFinitePartJetFamily =
      GaloisForLFunctions.gammaPoleScaleAndFinitePartJetFamily := by
  funext o
  rcases o with (_ | j)
  · exact mobiusContactGammaMovingCenterScaleGerm_eq
  · rfl

theorem mobiusContactGammaCovariantResidueFamily_eq :
    mobiusContactGammaCovariantResidueFamily =
      GaloisForLFunctions.gammaPoleScaleAndCovariantResidueFamily := by
  funext o
  rcases o with (_ | j)
  · exact mobiusContactGammaMovingCenterScaleGerm_eq
  · rfl

theorem mobiusContactGammaInverseBranchCoefficientFamily_eq :
    mobiusContactGammaInverseBranchCoefficientFamily =
      GaloisForLFunctions.gammaPoleScaleAndInverseBranchCoefficientFamily := by
  funext o
  rcases o with (_ | j)
  · exact mobiusContactGammaMovingCenterScaleGerm_eq
  · rfl

def mobiusContactGammaFinitePartJetRationalEval :
    MvPolynomial (Option ℕ) GaloisForLFunctions.GammaPoleRationalBase →+*
      GaloisForLFunctions.NatGerm :=
  MvPolynomial.eval₂Hom GaloisForLFunctions.ratNatEval
    mobiusContactGammaFinitePartJetFamily

def mobiusContactGammaCovariantResidueRationalEval :
    MvPolynomial (Option ℕ) GaloisForLFunctions.GammaPoleRationalBase →+*
      GaloisForLFunctions.NatGerm :=
  MvPolynomial.eval₂Hom GaloisForLFunctions.ratNatEval
    mobiusContactGammaCovariantResidueFamily

def mobiusContactGammaInverseBranchCoefficientRationalEval :
    MvPolynomial (Option ℕ) GaloisForLFunctions.GammaPoleRationalBase →+*
      GaloisForLFunctions.NatGerm :=
  MvPolynomial.eval₂Hom GaloisForLFunctions.ratNatEval
    mobiusContactGammaInverseBranchCoefficientFamily

theorem mobiusContactGammaFinitePartJetRationalEval_eq :
    mobiusContactGammaFinitePartJetRationalEval =
      GaloisForLFunctions.gammaPoleScaleAndFinitePartJetRationalEval := by
  rw [mobiusContactGammaFinitePartJetRationalEval,
    mobiusContactGammaFinitePartJetFamily_eq]
  rfl

theorem mobiusContactGammaCovariantResidueRationalEval_eq :
    mobiusContactGammaCovariantResidueRationalEval =
      GaloisForLFunctions.gammaPoleScaleAndCovariantResidueRationalEval := by
  rw [mobiusContactGammaCovariantResidueRationalEval,
    mobiusContactGammaCovariantResidueFamily_eq]
  rfl

theorem mobiusContactGammaInverseBranchCoefficientRationalEval_eq :
    mobiusContactGammaInverseBranchCoefficientRationalEval =
      GaloisForLFunctions.gammaPoleScaleAndInverseBranchCoefficientRationalEval := by
  rw [mobiusContactGammaInverseBranchCoefficientRationalEval,
    mobiusContactGammaInverseBranchCoefficientFamily_eq]
  rfl

/-- Every contact-headed chart remains countably algebraically independent over `ℂ(N)`. -/
theorem mobiusContactGamma_allMovingCenterCharts_algebraicIndependent :
    AlgebraicIndependent GaloisForLFunctions.GammaPoleRationalBase
        mobiusContactGammaFinitePartJetFamily ∧
      AlgebraicIndependent GaloisForLFunctions.GammaPoleRationalBase
        mobiusContactGammaCovariantResidueFamily ∧
      AlgebraicIndependent GaloisForLFunctions.GammaPoleRationalBase
        mobiusContactGammaInverseBranchCoefficientFamily := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mobiusContactGammaFinitePartJetFamily_eq]
    exact GaloisForLFunctions.algebraicIndependent_gammaPoleScaleAndFinitePartJet_over_ratFunc
  · rw [mobiusContactGammaCovariantResidueFamily_eq]
    exact GaloisForLFunctions.algebraicIndependent_gammaPoleScaleAndCovariantResidue_over_ratFunc
  · rw [mobiusContactGammaInverseBranchCoefficientFamily_eq,
      algebraicIndependent_iff_injective_aeval]
    simpa [GaloisForLFunctions.gammaPoleScaleAndInverseBranchCoefficientRationalEval,
      MvPolynomial.aeval_def] using
      GaloisForLFunctions.gammaPoleScaleAndInverseBranchCoefficientRationalEval_injective

/-- **Möbius-contact Gamma moving-center three-chart atlas universality law.** Finite parts,
covariant residues, and inverse-branch coefficients are pairwise unique polynomial coordinate
systems for one contact-headed evaluated algebra. -/
theorem mobiusContactGamma_completeMovingCenterThreeChartAtlasUniversality :
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
        mobiusContactGammaInverseBranchCoefficientRationalEval Q)) := by
  simpa only [mobiusContactGammaFinitePartJetRationalEval_eq,
    mobiusContactGammaCovariantResidueRationalEval_eq,
    mobiusContactGammaInverseBranchCoefficientRationalEval_eq] using
    GaloisForLFunctions.gammaPole_finitePart_covariantResidue_inverseBranch_coordinateAtlasUniversality

end

end GaloisForLFunctions.RHTower
