import GaloisForLFunctions.HTGeometry.FaceShiftLatticeNonresonance

/-!
# Distinct bottom faces have no common translate

Two bottom faces with different surviving pairs cannot have translates of their coordinates agree.
Applying the structural difference operator of a parameter that survives on one face and is deleted
on the other produces, on one side, a *resonant* defect — differentially algebraic — and on the
other an *external* nonresonant defect — hypertranscendental.

* **`multipleEllipticGammaFace_translate_ne_bottom`** — the separation.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A translate of a resonant defect is differentially algebraic over the constants. -/
theorem differentialAlgebraicOver_translate_resonant_defect
    {h sigma tau w : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hres : ∃ p q r : ℤ, h = p + q * tau + r * sigma) :
    DifferentialAlgebraicOver ℂ
      (addTranslationMeroEquiv w
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau)) := by
  have hbase : DifferentialAlgebraicOver ℂ
      (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) :=
    differentialAlgebraicOver_meromorphicRationalCoordinateField_iff.mp
      (differentialAlgebraicOver_rationalCoordinateField_of_ratFunc
        (differentialAlgebraicOver_ratFunc_ellipticGammaExternalLogDerivDefectMero_of_resonant
          h sigma tau hsigma htau hperiods hres))
  exact (HTGeometry.DifferentialAlgEquiv.differentialAlgebraicOver_map_iff
    (addTranslationMeroDifferentialAlgEquiv w) _).mpr hbase

/-- A translate of a nonresonant defect is hypertranscendental over the constants. -/
theorem hypertranscendentalOver_translate_nonresonant_defect
    {h sigma tau w : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnr : ThetaTranslationNonresonant tau sigma h) :
    HypertranscendentalOver ℂ
      (addTranslationMeroEquiv w
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau)) := by
  have hcomp := (hypertranscendentalOver_ellipticGammaExternalLogDerivDefectMero_iff_nonresonant
    h sigma tau hsigma htau hperiods).mpr hnr
  have hbase : HypertranscendentalOver ℂ
      (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) := by
    intro hda
    exact hcomp fun hind =>
      hda (HTGeometry.DifferentialIndependent.restrictScalarsTower hind)
  exact fun hda => hbase ((HTGeometry.DifferentialAlgEquiv.differentialAlgebraicOver_map_iff
    (addTranslationMeroDifferentialAlgEquiv w) _).mp hda)

set_option maxHeartbeats 1000000 in
/-- **Distinct bottom faces have no common translate.** -/
theorem multipleEllipticGammaFace_translate_ne_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J J' : Finset ι) {a b a' b' : ι}
    (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b) (hJ : ∀ i, i ∉ J → i = a ∨ i = b)
    (haJ' : a' ∉ J') (hbJ' : b' ∉ J') (hab' : a' ≠ b') (hJ' : ∀ i, i ∉ J' → i = a' ∨ i = b')
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    (hperiods' : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a') (τ b')))
    (haa' : a ≠ a') (hab'' : a ≠ b') (u v : ℂ) :
    addTranslationMeroEquiv u (multipleEllipticGammaLogDerivFaceMero τ hτ J) ≠
      addTranslationMeroEquiv v (multipleEllipticGammaLogDerivFaceMero τ hτ J') := by
  classical
  intro heq
  rw [multipleEllipticGammaLogDerivFaceMero_two_surviving τ hτ J haJ hbJ hab hJ,
    multipleEllipticGammaLogDerivFaceMero_two_surviving τ hτ J' haJ' hbJ' hab' hJ',
    addTranslationMeroEquiv_add, addTranslationMeroEquiv_add] at heq
  set w : ℂ := u + -(1 + τ b) / 2 with hwdef
  set w' : ℂ := v + -(1 + τ b') / 2 with hw'def
  have hform : ∀ (s : ℂ) (Ψ : meroField (Set.univ : Set ℂ)) (t : ℂ),
      addTranslationMeroEquiv s (addTranslationMeroEquiv t Ψ - Ψ) =
        addTranslationMeroEquiv t (addTranslationMeroEquiv s Ψ) -
          addTranslationMeroEquiv s Ψ := by
    intro s Ψ t
    rw [map_sub, addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm s t]
  have hkey :
      addTranslationMeroEquiv w
          (ellipticGammaExternalLogDerivDefectMero (τ a) (τ a) (τ b) (hτ a) (hτ b)) =
        addTranslationMeroEquiv w'
          (ellipticGammaExternalLogDerivDefectMero (τ a) (τ a') (τ b') (hτ a') (hτ b')) := by
    rw [ellipticGammaExternalLogDerivDefectMero, ellipticGammaExternalLogDerivDefectMero,
      hform, hform, heq]
  have hDA := differentialAlgebraicOver_translate_resonant_defect
    (h := τ a) (sigma := τ a) (tau := τ b) (w := w) (hτ a) (hτ b) hperiods
    ⟨0, 0, 1, by push_cast; ring⟩
  have hnr : ThetaTranslationNonresonant (τ b') (τ a') (τ a) :=
    thetaTranslationNonresonant_period_of_ne τ hQ haa' hab''
  have hHT := hypertranscendentalOver_translate_nonresonant_defect
    (h := τ a) (sigma := τ a') (tau := τ b') (w := w') (hτ a') (hτ b') hperiods' hnr
  rw [hkey] at hDA
  exact hHT hDA

set_option maxHeartbeats 1000000 in
/-- **Cross-face star exponents.**  Slice points of two bottom faces separated by a parameter that
survives on the first and is deleted on the second never have equal translates, so the star exponent
statement holds vacuously. -/
theorem multipleEllipticGammaFacePacketSlice_exponent_eq_bottom_cross
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J J' : Finset ι) {a b a' b' : ι}
    (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b) (hJ : ∀ i, i ∉ J → i = a ∨ i = b)
    (haJ' : a' ∉ J') (hbJ' : b' ∉ J') (hab' : a' ≠ b') (hJ' : ∀ i, i ∉ J' → i = a' ∨ i = b')
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    (hperiods' : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a') (τ b')))
    (hsepa : a ∈ J') {q : ι} {m n : ℤ} {y z : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ multipleEllipticGammaFacePacketSlice τ hτ J q)
    (hz : z ∈ multipleEllipticGammaFacePacketSlice τ hτ J' q)
    (heq : addTranslationMeroEquiv ((m : ℂ) * τ q) y =
      addTranslationMeroEquiv ((n : ℂ) * τ q) z) :
    m = n := by
  classical
  exfalso
  obtain ⟨g, -, rfl⟩ := hy
  obtain ⟨g', -, rfl⟩ := hz
  rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add] at heq
  have haa' : a ≠ a' := fun h => haJ' (h ▸ hsepa)
  have hab'' : a ≠ b' := fun h => hbJ' (h ▸ hsepa)
  exact multipleEllipticGammaFace_translate_ne_bottom τ hτ hQ J J' haJ hbJ hab hJ
    haJ' hbJ' hab' hJ' hperiods hperiods' haa' hab'' _ _ heq

set_option maxHeartbeats 1000000 in
/-- **Off-star displacements at the bottom layer are differentially algebraic.**  If the star
direction `q` survives on the face `J`, translation by `n tau_q` is a structural translation there,
so it moves every packet element by a translate of a *resonant* defect. -/
theorem differentialAlgebraicOver_offStar_displacement_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {a b : ι}
    (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b) (hJ : ∀ i, i ∉ J → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    {q : ι} (hq : q ∉ J) (n : ℤ) {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ multipleEllipticGammaFacePacket τ hτ J) :
    DifferentialAlgebraicOver ℂ
      (addTranslationMeroEquiv ((n : ℂ) * τ q) y - y) := by
  classical
  obtain ⟨g, -, rfl⟩ := hy
  show DifferentialAlgebraicOver ℂ
    (addTranslationMeroEquiv ((n : ℂ) * τ q)
        (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) -
      addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J))
  have hform : ∀ (s : ℂ) (Ψ : meroField (Set.univ : Set ℂ)) (t : ℂ),
      addTranslationMeroEquiv t (addTranslationMeroEquiv s Ψ) -
          addTranslationMeroEquiv s Ψ =
        addTranslationMeroEquiv s (addTranslationMeroEquiv t Ψ - Ψ) := by
    intro s Ψ t
    rw [map_sub, addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm s t]
  rw [hform, multipleEllipticGammaLogDerivFaceMero_two_surviving τ hτ J haJ hbJ hab hJ,
    hform, addTranslationMeroEquiv_add]
  have hres : ∃ p r' r : ℤ, (n : ℂ) * τ q = p + r' * τ b + r * τ a := by
    rcases hJ q hq with rfl | rfl
    · exact ⟨0, 0, n, by push_cast; ring⟩
    · exact ⟨0, n, 0, by push_cast; ring⟩
  exact differentialAlgebraicOver_translate_resonant_defect (hτ a) (hτ b) hperiods hres

omit [Fintype ι] [DecidableEq ι] in
/-- Distinct faces admit a parameter surviving on one and deleted on the other. -/
theorem exists_separating_parameter_of_ne {J J' : Finset ι} (h : J ≠ J') :
    (∃ x, x ∉ J ∧ x ∈ J') ∨ (∃ x, x ∉ J' ∧ x ∈ J) := by
  classical
  rw [Ne, Finset.ext_iff] at h
  push Not at h
  obtain ⟨x, hx⟩ := h
  rcases hx with ⟨hxJ, hxJ'⟩ | ⟨hxJ, hxJ'⟩
  · exact Or.inr ⟨x, hxJ', hxJ⟩
  · exact Or.inl ⟨x, hxJ, hxJ'⟩

end

end GaloisForLFunctions
