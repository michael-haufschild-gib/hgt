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

/-- **A separated family of translates of the elliptic gamma source is differentially independent
over the constants.** -/
theorem differentialIndependent_ellipticGammaTranslateFamily {ι : Type*} [Fintype ι]
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hs : ι → ℂ) (hnonres : ∀ i, ThetaTranslationNonresonant tau sigma (hs i))
    (hsep : ∀ i j, i ≠ j → ThetaTranslationNonresonant tau sigma (hs j - hs i)) :
    DifferentialIndependent ℂ (ellipticGammaTranslateFamily hs sigma tau hsigma htau) := by
  classical
  set d := ellipticGammaExternalDefectFamily hs sigma tau hsigma htau with hd
  have hdefC : DifferentialIndependent ℂ d :=
    (differentialIndependent_meromorphicRationalCoordinateField_iff d).mp
      (ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase
        hs sigma tau hsigma htau hindependent hnonres (fun i j hji ↦ hsep i j (fun hh ↦ hji hh.symm)))
  set A : Finset ℂ := Finset.image hs Finset.univ with hA
  have hmemA : ∀ a ∈ A, ThetaTranslationNonresonant tau sigma a := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hnonres i
  have hsepA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ThetaTranslationNonresonant tau sigma (a - b) := by
    intro a ha b hb hab
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact hsep j i (fun hh ↦ hab (by rw [hh]))
  have hpacket := ellipticGammaTranslatePacket_diffIndepOn_of_separated hsigma htau hindependent
    A hmemA hsepA
  set t := ellipticGammaTranslateFamily hs sigma tau hsigma htau with ht
  have hinj : Function.Injective t := by
    intro i j hij
    refine hdefC.injective ?_
    have h1 := ellipticGammaTranslateFamily_eq_add_defect hs sigma tau hsigma htau i
    have h2 := ellipticGammaTranslateFamily_eq_add_defect hs sigma tau hsigma htau j
    rw [← ht, ← hd] at h1 h2
    rw [h1, h2] at hij
    exact add_left_cancel hij
  have hmem : ∀ i, t i ∈ insert (ellipticGammaLogDerivMero sigma tau hsigma htau)
      (Set.range (ellipticGammaTranslateFamily (fun a : {x // x ∈ A} ↦ (a : ℂ))
        sigma tau hsigma htau)) := by
    intro i
    refine Set.mem_insert_of_mem _ ⟨⟨hs i, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · rfl
  exact DifferentialIndependent.comp hpacket (fun i ↦ ⟨t i, hmem i⟩)
    (fun i j hij ↦ hinj (congrArg Subtype.val hij))

/-- **A nonzero jet row on a separated family of gamma translates is hypertranscendental.** -/
theorem hypertranscendentalOver_ellipticGammaTranslateRow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hs : ι → ℂ) (hnonres : ∀ i, ThetaTranslationNonresonant tau sigma (hs i))
    (hsep : ∀ i j, i ≠ j → ThetaTranslationNonresonant tau sigma (hs j - hs i))
    (v : ι → Polynomial ℂ) (hv : v ≠ 0) :
    HypertranscendentalOver ℂ
      (∑ i, differentialOperatorApply (v i)
        (ellipticGammaTranslateFamily hs sigma tau hsigma htau i)) :=
  hypertranscendentalOver_differentialOperatorRow_of_ne_zero
    (fun c ↦ deriv_algebraMap_complex c) v hv _
    (differentialIndependent_ellipticGammaTranslateFamily hsigma htau hindependent hs hnonres hsep)


/-- A member of a differentially independent family is nonzero: otherwise two distinct jets of it
would coincide. -/
theorem ne_zero_of_differentialIndependent {ι : Type*} {x : ι → meroField (Set.univ : Set ℂ)}
    (hx : DifferentialIndependent ℂ x) (i : ι) : x i ≠ 0 := by
  intro hzero
  have hinj := hx.injective
  have h01 : (fun p : ι × ℕ ↦ differentialJet p.2 (x p.1)) (i, 0)
      = (fun p : ι × ℕ ↦ differentialJet p.2 (x p.1)) (i, 1) := by
    simp only [hzero]
    rw [differentialJet_zero, differentialJet_succ, differentialJet_zero]
    simp
  have := hinj h01
  simp at this

/-- The shift family of a translation packet, with the base source adjoined at the index `none`. -/
def optionShift {ι : Type*} (hs : ι → ℂ) : Option ι → ℂ := fun i ↦ i.elim 0 hs

@[simp] theorem optionShift_none {ι : Type*} (hs : ι → ℂ) : optionShift hs none = 0 := rfl

@[simp] theorem optionShift_some {ι : Type*} (hs : ι → ℂ) (i : ι) :
    optionShift hs (some i) = hs i := rfl

/-- **The translation packet, base source included, is differentially independent.** -/
theorem differentialIndependent_ellipticGammaTranslateFamily_option {ι : Type*} [Fintype ι]
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hs : ι → ℂ) (hnonres : ∀ i, ThetaTranslationNonresonant tau sigma (hs i))
    (hsep : ∀ i j, i ≠ j → ThetaTranslationNonresonant tau sigma (hs j - hs i)) :
    DifferentialIndependent ℂ
      (ellipticGammaTranslateFamily (optionShift hs) sigma tau hsigma htau) := by
  classical
  set d := ellipticGammaExternalDefectFamily hs sigma tau hsigma htau with hd
  have hdefC : DifferentialIndependent ℂ d :=
    (differentialIndependent_meromorphicRationalCoordinateField_iff d).mp
      (ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase
        hs sigma tau hsigma htau hindependent hnonres
        (fun i j hji ↦ hsep i j (fun hh ↦ hji hh.symm)))
  set A : Finset ℂ := Finset.image hs Finset.univ with hA
  have hmemA : ∀ a ∈ A, ThetaTranslationNonresonant tau sigma a := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hnonres i
  have hsepA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ThetaTranslationNonresonant tau sigma (a - b) := by
    intro a ha b hb hab
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact hsep j i (fun hh ↦ hab (by rw [hh]))
  have hpacket := ellipticGammaTranslatePacket_diffIndepOn_of_separated hsigma htau hindependent
    A hmemA hsepA
  set F := ellipticGammaLogDerivMero sigma tau hsigma htau with hF
  set t := ellipticGammaTranslateFamily (optionShift hs) sigma tau hsigma htau with ht
  have hnone : t none = F := by
    rw [ht, ellipticGammaTranslateFamily, optionShift_none]
    exact addTranslationMeroEquiv_zero_apply _
  have hsome : ∀ i, t (some i) = F + d i := by
    intro i
    have h := ellipticGammaTranslateFamily_eq_add_defect (optionShift hs) sigma tau hsigma htau
      (some i)
    rw [ht, h, ← hF, ← hd, ellipticGammaExternalDefectFamily, ellipticGammaExternalDefectFamily,
      optionShift_some]
  have hinj : Function.Injective t := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some j =>
            exfalso
            rw [hnone, hsome j] at hij
            exact ne_zero_of_differentialIndependent hdefC j (by linear_combination -hij)
    | some i =>
        cases j with
        | none =>
            exfalso
            rw [hnone, hsome i] at hij
            exact ne_zero_of_differentialIndependent hdefC i (by linear_combination hij)
        | some j =>
            rw [hsome i, hsome j] at hij
            exact congrArg some (hdefC.injective (add_left_cancel hij))
  have hmem : ∀ i, t i ∈ insert F
      (Set.range (ellipticGammaTranslateFamily (fun a : {x // x ∈ A} ↦ (a : ℂ))
        sigma tau hsigma htau)) := by
    intro i
    cases i with
    | none =>
        rw [hnone]
        exact Set.mem_insert _ _
    | some i =>
        refine Set.mem_insert_of_mem _ ⟨⟨hs i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩, ?_⟩
        rw [hsome i, ellipticGammaTranslateFamily,
          ellipticGammaTranslateFamily_eq_add_defect hs sigma tau hsigma htau i] at *
        rfl
  exact DifferentialIndependent.comp hpacket (fun i ↦ ⟨t i, hmem i⟩)
    (fun i j hij ↦ hinj (congrArg Subtype.val hij))

/-- **A nonzero jet row on the packet, base source included, is hypertranscendental.** -/
theorem hypertranscendentalOver_ellipticGammaTranslateRow_option {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hs : ι → ℂ) (hnonres : ∀ i, ThetaTranslationNonresonant tau sigma (hs i))
    (hsep : ∀ i j, i ≠ j → ThetaTranslationNonresonant tau sigma (hs j - hs i))
    (v : Option ι → Polynomial ℂ) (hv : v ≠ 0) :
    HypertranscendentalOver ℂ
      (∑ i, differentialOperatorApply (v i)
        (ellipticGammaTranslateFamily (optionShift hs) sigma tau hsigma htau i)) :=
  hypertranscendentalOver_differentialOperatorRow_of_ne_zero
    (fun c ↦ deriv_algebraMap_complex c) v hv _
    (differentialIndependent_ellipticGammaTranslateFamily_option hsigma htau hindependent hs
      hnonres hsep)

end

end GaloisForLFunctions.HTGeometry
