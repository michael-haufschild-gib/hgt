import GaloisForLFunctions.HTGeometry.TranslationDefectDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.EllipticGammaRationalBaseMatroid

/-!
# Structural-generator DA spectrum of the genuine elliptic gamma defect

The hard off-spectrum theorem already proves differential independence for separated nonzero
rank-three cosets.  This module closes the complementary structural-generator interface.  The
direct elliptic-gamma source faces identify the two nontrivial generator defects with theta
logarithmic derivatives modulo normalization constants.  Their derivatives are elliptic, so the
general affine first-order law makes the source faces differentially algebraic over the paired
elliptic compositum.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher
open HTGeometry

noncomputable section

local instance ellipticGammaStructuralGeneratorDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaStructuralGeneratorComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticGammaStructuralGeneratorComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero

local instance ellipticGammaStructuralGeneratorAmbientDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaStructuralGeneratorMeroCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField Set.univ)).injective

local instance ellipticGammaStructuralGeneratorRestrictedDifferential
    (sigma tau : ℂ) :
    Differential (meromorphicEllipticCompositum sigma tau) :=
  meromorphicEllipticCompositumDifferential sigma tau

local instance ellipticGammaStructuralGeneratorDifferentialAlgebra
    (sigma tau : ℂ) :
    DifferentialAlgebra (meromorphicEllipticCompositum sigma tau)
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    (meromorphicEllipticCompositum sigma tau)
    (meromorphicEllipticCompositum_derivationClosed sigma tau) x⟩

private theorem meroField_deriv_algebraMap_complex_structuralGenerator (c : ℂ) :
    (algebraMap ℂ (meroField Set.univ) c)′ = 0 := by
  change
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (constToAnalytic Set.univ c))′ = 0
  rw [meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ
    Set.univ_nonempty]
  have hconst : analyticSubringDeriv isOpen_univ
      (constToAnalytic Set.univ c) = 0 := by
    apply Subtype.ext
    rw [analyticSubringDeriv_coe]
    let f : ℂ → ℂ := fun _ ↦ c
    calc
      Germ.coeRingHom (Filter.principal Set.univ) (deriv f) =
          Germ.coeRingHom (Filter.principal Set.univ) (0 : ℂ → ℂ) := by
        congr 1
        funext z
        simp [f]
      _ = 0 := (Germ.coeRingHom (Filter.principal Set.univ)).map_zero
  rw [hconst, map_zero]

/-- The derivative of the genuine theta logarithmic derivative is elliptic: the additive
quasiperiod constant disappears under differentiation. -/
theorem thetaLogDerivMero_deriv_mem_ellipticMeroField
    (tau : ℂ) (htau : 0 < tau.im) :
    (thetaLogDerivMero tau htau)′ ∈ ellipticMeroField tau := by
  rw [mem_ellipticMeroField_iff]
  constructor
  · rw [addTranslationMeroEquiv_deriv,
      addTranslationMeroEquiv_thetaLogDeriv_one]
  · rw [addTranslationMeroEquiv_deriv,
      addTranslationMeroEquiv_thetaLogDeriv_tau]
    rw [map_sub]
    change (thetaLogDerivMero tau htau)′ -
      (algebraMap ℂ (meroField Set.univ) (2 * Real.pi * I))′ = _
    rw [meroField_deriv_algebraMap_complex_structuralGenerator, sub_zero]

/-- Every translate of a theta logarithmic derivative is DA over any translation-stable paired
elliptic compositum containing its elliptic derivative field. -/
theorem differentialAlgebraicOver_addTranslationMeroEquiv_thetaLogDerivMero
    (q omega sigma tau : ℂ) (homega : 0 < omega.im)
    (hsub : ellipticMeroField omega ≤ meromorphicEllipticCompositum sigma tau) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (addTranslationMeroEquiv q (thetaLogDerivMero omega homega)) := by
  have hderiv : (thetaLogDerivMero omega homega)′ ∈
      meromorphicEllipticCompositum sigma tau :=
    hsub (thetaLogDerivMero_deriv_mem_ellipticMeroField omega homega)
  have htranslated : addTranslationMeroEquiv q
      (thetaLogDerivMero omega homega)′ ∈
        meromorphicEllipticCompositum sigma tau :=
    addTranslationMeroAlgEquiv_mem_ellipticCompositum sigma tau q hderiv
  let b : meromorphicEllipticCompositum sigma tau :=
    ⟨addTranslationMeroEquiv q (thetaLogDerivMero omega homega)′, htranslated⟩
  apply differentialAlgebraicOver_of_deriv_eq_base b
  simpa [b] using (addTranslationMeroEquiv_deriv q
    (thetaLogDerivMero omega homega)).symm

/-- Embedded complex constants are DA over every paired elliptic compositum. -/
theorem differentialAlgebraicOver_meromorphicConstant_ellipticCompositum
    (sigma tau c : ℂ) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c)) := by
  change DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
    (algebraMap ℂ (meroField Set.univ) c)
  simpa using differentialAlgebraicOver_algebraMap
    (F := meromorphicEllipticCompositum sigma tau)
    (E := meroField Set.univ)
    (algebraMap ℂ (meromorphicEllipticCompositum sigma tau) c)

/-- The first nontrivial structural generator defect is DA over the paired elliptic compositum. -/
theorem differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_sigma
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalLogDerivDefectMero sigma sigma tau hsigma htau) := by
  obtain ⟨c, hface⟩ :=
    ellipticGammaExternalLogDerivDefectMero_sigma sigma tau hsigma htau
  rw [hface]
  apply differentialAlgebraicOver_add
  · simpa only [addTranslationMeroEquiv_zero_apply] using
    differentialAlgebraicOver_addTranslationMeroEquiv_thetaLogDerivMero
      0 tau sigma tau htau (by
        rw [meromorphicEllipticCompositum]
        exact le_sup_right)
  · exact differentialAlgebraicOver_meromorphicConstant_ellipticCompositum
      sigma tau c

/-- The second nontrivial structural generator defect is DA over the paired elliptic compositum. -/
theorem differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_tau
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalLogDerivDefectMero tau sigma tau hsigma htau) := by
  obtain ⟨d, hface⟩ :=
    ellipticGammaExternalLogDerivDefectMero_tau sigma tau hsigma htau
  rw [hface]
  apply differentialAlgebraicOver_add
  · exact differentialAlgebraicOver_addTranslationMeroEquiv_thetaLogDerivMero
      ((tau - sigma) / 2) sigma sigma tau hsigma (by
        rw [meromorphicEllipticCompositum]
        exact le_sup_left)
  · exact differentialAlgebraicOver_meromorphicConstant_ellipticCompositum
      sigma tau d

/-! ## Exact rank-three spectrum over the paired elliptic base -/

/-- Every translate of a defect whose shift belongs to the rank-three integer period group is DA
over the paired elliptic compositum.  The translation-uniform conclusion avoids any hidden
coefficient-fixing assumption. -/
theorem differentialAlgebraicOver_addTranslationMeroEquiv_ellipticGammaExternalDefect_of_resonant
    (q sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (a b n : ℤ) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (addTranslationMeroEquiv q
        (ellipticGammaExternalLogDerivDefectMero
          ((a : ℂ) + (b : ℂ) * tau + (n : ℂ) * sigma)
          sigma tau hsigma htau)) := by
  let x := ellipticGammaLogDerivMero sigma tau hsigma htau
  have hone : ∀ q : ℂ, DifferentialAlgebraicOver
      (meromorphicEllipticCompositum sigma tau)
      (addTranslationMeroEquiv q (addTranslationMeroEquiv 1 x - x)) := by
    intro q
    rw [addTranslationMeroEquiv_ellipticGammaLogDerivMero_one, sub_self, map_zero]
    exact differentialAlgebraicOver_algebraMap 0
  have hsigmaGen : ∀ q : ℂ, DifferentialAlgebraicOver
      (meromorphicEllipticCompositum sigma tau)
      (addTranslationMeroEquiv q (addTranslationMeroEquiv sigma x - x)) := by
    intro q
    obtain ⟨c, hface⟩ := ellipticGammaLogDerivMero_source_face_sigma hsigma htau
    rw [hface, (addTranslationMeroEquiv q).map_add,
      addTranslationMeroEquiv_const]
    exact differentialAlgebraicOver_add
      (differentialAlgebraicOver_addTranslationMeroEquiv_thetaLogDerivMero
        q tau sigma tau htau (by
          rw [meromorphicEllipticCompositum]
          exact le_sup_right))
      (differentialAlgebraicOver_meromorphicConstant_ellipticCompositum
        sigma tau c)
  have htauGen : ∀ q : ℂ, DifferentialAlgebraicOver
      (meromorphicEllipticCompositum sigma tau)
      (addTranslationMeroEquiv q (addTranslationMeroEquiv tau x - x)) := by
    intro q
    obtain ⟨d, hface⟩ := ellipticGammaLogDerivMero_source_face_tau hsigma htau
    rw [hface, (addTranslationMeroEquiv q).map_add,
      addTranslationMeroEquiv_const, addTranslationMeroEquiv_add]
    exact differentialAlgebraicOver_add
      (differentialAlgebraicOver_addTranslationMeroEquiv_thetaLogDerivMero
        (q + (tau - sigma) / 2) sigma sigma tau hsigma (by
          rw [meromorphicEllipticCompositum]
          exact le_sup_left))
      (differentialAlgebraicOver_meromorphicConstant_ellipticCompositum
        sigma tau d)
  have ha := fun q ↦ differentialAlgebraicOver_addTranslationMeroEquiv_defect_zsmul
    sigma tau x 1 hone q a
  have hb := fun q ↦ differentialAlgebraicOver_addTranslationMeroEquiv_defect_zsmul
    sigma tau x tau htauGen q b
  have hn := fun q ↦ differentialAlgebraicOver_addTranslationMeroEquiv_defect_zsmul
    sigma tau x sigma hsigmaGen q n
  have hab := fun q ↦ differentialAlgebraicOver_addTranslationMeroEquiv_defect_add
    sigma tau x (a • (1 : ℂ)) (b • tau) ha hb q
  have hall := differentialAlgebraicOver_addTranslationMeroEquiv_defect_add
    sigma tau x (a • (1 : ℂ) + b • tau) (n • sigma) hab hn q
  simpa [ellipticGammaExternalLogDerivDefectMero] using hall

/-- Every rank-three resonant elliptic-gamma defect is DA over the paired elliptic base. -/
theorem differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_of_resonant
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (a b n : ℤ) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalLogDerivDefectMero
        ((a : ℂ) + (b : ℂ) * tau + (n : ℂ) * sigma)
        sigma tau hsigma htau) := by
  simpa only [addTranslationMeroEquiv_zero_apply] using
    differentialAlgebraicOver_addTranslationMeroEquiv_ellipticGammaExternalDefect_of_resonant
      0 sigma tau hsigma htau a b n

/-- **Same-coset rank neutrality.**  External defects whose shift parameters differ by a
rank-three period have a DA difference over the paired elliptic compositum. -/
theorem differentialAlgebraicOver_ellipticGammaExternalDefect_sub_of_sameCoset
    (h k sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hcoset : ∃ a b n : ℤ,
      h - k = a + b * tau + n * sigma) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau -
        ellipticGammaExternalLogDerivDefectMero k sigma tau hsigma htau) := by
  rcases hcoset with ⟨a, b, n, hab⟩
  change DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
    ((addTranslationMeroEquiv h
          (ellipticGammaLogDerivMero sigma tau hsigma htau) -
        ellipticGammaLogDerivMero sigma tau hsigma htau) -
      (addTranslationMeroEquiv k
          (ellipticGammaLogDerivMero sigma tau hsigma htau) -
        ellipticGammaLogDerivMero sigma tau hsigma htau))
  rw [addTranslationMeroEquiv_defect_sub, hab]
  exact
    differentialAlgebraicOver_addTranslationMeroEquiv_ellipticGammaExternalDefect_of_resonant
      k sigma tau hsigma htau a b n

/-- **Exact natural-base DA spectrum.**  Under rational independence of `1`, `sigma`, and `tau`,
the genuine elliptic-gamma logarithmic-derivative defect is DA over the paired elliptic compositum
exactly on the rank-three integer period group.  The reverse implication is the existing
finite-family Ostrowski theorem specialized to one defect; the forward implication is the new
structural integer-span law above. -/
theorem differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_iff_resonant
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) ↔
      ∃ a b n : ℤ, h = a + b * tau + n * sigma := by
  constructor
  · intro hDA
    by_contra hres
    have hnonres : ThetaTranslationNonresonant tau sigma h := hres
    have hDI := ellipticGammaExternalDefectFamily_differentialIndependent
      (fun _ : Unit ↦ h) sigma tau hsigma htau hindependent
      (fun _ ↦ hnonres) (by simp)
    have hHT : HypertranscendentalOver
        (meromorphicEllipticCompositum sigma tau)
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) := by
      rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
      simpa [ellipticGammaExternalDefectFamily] using hDI
    exact hHT hDA
  · rintro ⟨a, b, n, rfl⟩
    exact differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_of_resonant
      sigma tau hsigma htau a b n

end


end GaloisForLFunctions
