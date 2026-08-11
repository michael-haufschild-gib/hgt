import GaloisForLFunctions.HTGeometry.EllipticGammaDefectFieldEscape
import GaloisForLFunctions.HTGeometry.DifferentialOperatorRowHypertranscendence

/-!
# Freeness of the differential translation orbit of the elliptic gamma source

A finite family of translates of the elliptic gamma logarithmic derivative, taken at nonresonant and
pairwise separated shifts, is differentially independent over the constants.  Hence any nonzero
constant-coefficient differential-operator row applied to it is hypertranscendental: no nonzero
combination of jets of distinct translates satisfies an algebraic differential equation.

This is the freeness that identifies the kernel of the triptic orbit-residue divisor.

* `differentialIndependent_ellipticGammaTranslateFamily`;
* `hypertranscendentalOver_ellipticGammaTranslateRow`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {sigma tau : ℂ}

/-- **A separated finite family of translates of the elliptic gamma source is differentially
independent over the constants.** -/
theorem differentialIndependent_ellipticGammaTranslateFamily (hsigma : 0 < sigma.im)
    (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (A : Finset ℂ)
    (hnonres : ∀ a ∈ A, ThetaTranslationNonresonant tau sigma a)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ThetaTranslationNonresonant tau sigma (a - b)) :
    DifferentialIndependent ℂ
      (ellipticGammaTranslateFamily (fun a : {x // x ∈ A} ↦ (a : ℂ)) sigma tau hsigma htau) := by
  classical
  set d := ellipticGammaExternalDefectFamily (fun a : {x // x ∈ A} ↦ (a : ℂ)) sigma tau hsigma htau
    with hd
  have hdefC : DifferentialIndependent ℂ d :=
    (differentialIndependent_meromorphicRationalCoordinateField_iff d).mp
      (ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase
        (fun a : {x // x ∈ A} ↦ (a : ℂ)) sigma tau hsigma htau hindependent
        (fun j ↦ hnonres (j : ℂ) j.2)
        (fun i j hji ↦ hsep (j : ℂ) j.2 (i : ℂ) i.2 (fun hh ↦ hji (Subtype.ext hh))))
  have hpacket := ellipticGammaTranslatePacket_diffIndepOn_of_separated hsigma htau hindependent
    A hnonres hsep
  set t := ellipticGammaTranslateFamily (fun a : {x // x ∈ A} ↦ (a : ℂ)) sigma tau hsigma htau
    with ht
  have hinj : Function.Injective t := by
    intro i j hij
    refine hdefC.injective ?_
    have h1 := ellipticGammaTranslateFamily_eq_add_defect
      (fun a : {x // x ∈ A} ↦ (a : ℂ)) sigma tau hsigma htau i
    have h2 := ellipticGammaTranslateFamily_eq_add_defect
      (fun a : {x // x ∈ A} ↦ (a : ℂ)) sigma tau hsigma htau j
    rw [← ht, ← hd] at h1 h2
    rw [h1, h2] at hij
    exact add_left_cancel hij
  have hmem : ∀ i, t i ∈ insert (ellipticGammaLogDerivMero sigma tau hsigma htau)
      (Set.range t) := fun i ↦ Set.mem_insert_of_mem _ ⟨i, rfl⟩
  have hcomp : DifferentialIndependent ℂ
      (fun i ↦ (⟨t i, hmem i⟩ :
        ↥(insert (ellipticGammaLogDerivMero sigma tau hsigma htau) (Set.range t))).val) :=
    DifferentialIndependent.comp hpacket (fun i ↦ ⟨t i, hmem i⟩)
      (fun i j hij ↦ hinj (congrArg Subtype.val hij))
  exact hcomp

/-- **A nonzero jet row on a separated family of gamma translates is hypertranscendental.** -/
theorem hypertranscendentalOver_ellipticGammaTranslateRow (hsigma : 0 < sigma.im)
    (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (A : Finset ℂ)
    (hnonres : ∀ a ∈ A, ThetaTranslationNonresonant tau sigma a)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ThetaTranslationNonresonant tau sigma (a - b))
    (v : {x // x ∈ A} → Polynomial ℂ) (hv : v ≠ 0) :
    HypertranscendentalOver ℂ
      (∑ a : {x // x ∈ A}, differentialOperatorApply (v a)
        (ellipticGammaTranslateFamily (fun a : {x // x ∈ A} ↦ (a : ℂ)) sigma tau hsigma htau a)) :=
  hypertranscendentalOver_differentialOperatorRow_of_ne_zero
    (fun c ↦ deriv_algebraMap_complex c) v hv _
    (differentialIndependent_ellipticGammaTranslateFamily hsigma htau hindependent A hnonres hsep)

end

end GaloisForLFunctions.HTGeometry
