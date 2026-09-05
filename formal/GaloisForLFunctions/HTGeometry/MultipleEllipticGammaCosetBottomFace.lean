import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCosetFacePacket
import GaloisForLFunctions.HTGeometry.FaceShiftLatticeNonresonance
import GaloisForLFunctions.HTGeometry.EllipticGammaTranslateOrbitSeparated

/-!
# The labelled bottom layer

A face retaining exactly two parameters `τ a, τ b` has, after the fixed half-period normalization,
the order-one elliptic-gamma logarithmic derivative as its coordinate.  Its labelled packet is
therefore a translation orbit of that logarithmic derivative along the shifted labelled shift set.

Under coset separation of the labels and integral independence of the periods, *differences* of
distinct labelled shifts are nonresonant.  That is exactly the hypothesis of the base-point-free
order-one orbit theorem, so the labelled bottom packet is atomic.  No individual shift has to be
nonresonant, which matters because one label class is the class of the half period itself.

* **`thetaTranslationNonresonant_cosetFaceShiftSet_sub`** — the arithmetic input;
* **`cosetFacePacket_diffIndepOn_bottom`** — labelled bottom atomicity;
* **`cosetFaceShiftSet_translate_injective_bottom`** — faithful labelling of the bottom packet.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

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

omit [DecidableEq ι] in
/-- Every rank-three resonance vector of a pair of parameters is a period of the hierarchy. -/
theorem mem_fullPeriodLattice_pair (τ : ι → ℂ) (a b : ι) (p q r : ℤ) :
    ((p : ℂ) + (q : ℂ) * τ b + (r : ℂ) * τ a) ∈ fullPeriodLattice τ := by
  classical
  refine ⟨p, fun i => (if i = b then q else 0) + (if i = a then r else 0), ?_⟩
  have hterm : ∀ i : ι,
      ((((if i = b then q else 0) + (if i = a then r else 0) : ℤ)) : ℂ) * τ i =
        (if i = b then (q : ℂ) * τ i else 0) + (if i = a then (r : ℂ) * τ i else 0) := by
    intro i
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ b fun i => (q : ℂ) * τ i,
    Finset.sum_ite_eq' Finset.univ a fun i => (r : ℂ) * τ i]
  simp
  ring

/-- **Distinct labelled shifts are separated.**  Either the labels agree, and the lattice parts
are separated by integral independence of the periods, or the labels differ, and their difference
is not a period at all. -/
theorem thetaTranslationNonresonant_cosetFaceShiftSet_sub
    (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A) (J : Finset ι) {a b : ι}
    (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b)
    {g g' : ℂ} (hg : g ∈ cosetFaceShiftSet τ A J) (hg' : g' ∈ cosetFaceShiftSet τ A J)
    (hne : g ≠ g') :
    ThetaTranslationNonresonant (τ b) (τ a) (g - g') := by
  classical
  obtain ⟨α, hα, h, hh, rfl⟩ := hg
  obtain ⟨α', hα', h', hh', rfl⟩ := hg'
  by_cases hαα : α = α'
  · subst hαα
    have hhne : h ≠ h' := fun hc => hne (by rw [hc])
    have hdiff : α + h - (α + h') = h - h' := by ring
    rw [hdiff]
    exact thetaTranslationNonresonant_faceShiftLattice_sub τ hQ J haJ hbJ hh hh' hhne
  · rintro ⟨p, q, r, hpqr⟩
    refine hA α hα α' hα' hαα ?_
    have hval : α - α' = ((p : ℂ) + (q : ℂ) * τ b + (r : ℂ) * τ a) - (h - h') := by
      linear_combination hpqr
    rw [hval]
    exact sub_mem_fullPeriodLattice τ (mem_fullPeriodLattice_pair τ a b p q r)
      (sub_mem_fullPeriodLattice τ (faceShiftLattice_subset_fullPeriodLattice τ J hh)
        (faceShiftLattice_subset_fullPeriodLattice τ J hh'))

/-- The labelled bottom packet is a translation orbit of the order-one logarithmic derivative. -/
theorem cosetFacePacket_eq_translateOrbit_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ) (J : Finset ι) {a b : ι}
    (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b)
    (hJ : ∀ i, i ∉ J → i = a ∨ i = b) :
    cosetFacePacket τ hτ A J =
      ellipticGammaTranslateOrbit
        ((fun g => g + -(1 + τ b) / 2) '' cosetFaceShiftSet τ A J)
        (τ a) (τ b) (hτ a) (hτ b) := by
  classical
  have hbridge : ∀ g : ℂ,
      addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
        addTranslationMeroEquiv (g + -(1 + τ b) / 2)
          (ellipticGammaLogDerivMero (τ a) (τ b) (hτ a) (hτ b)) := by
    intro g
    rw [multipleEllipticGammaLogDerivFaceMero_two_surviving τ hτ J haJ hbJ hab hJ,
      addTranslationMeroEquiv_add]
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g + -(1 + τ b) / 2, ⟨g, hg, rfl⟩, (hbridge g).symm⟩
  · rintro ⟨s, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, hbridge g⟩

set_option synthInstance.maxHeartbeats 800000 in
/-- **Labelled bottom atomicity.**  The labelled packet of a face with exactly two surviving
parameters is differentially independent over every differentially algebraic extension of the
constants. -/
theorem cosetFacePacket_diffIndepOn_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (J : Finset ι) {a b : ι} (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b)
    (hJ : ∀ i, i ∉ J → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    {G : Set (meroField (Set.univ : Set ℂ))}
    (hG : ∀ g ∈ G, DifferentialAlgebraicOver ℂ g) :
    DiffIndepOn ↥(differentialAdjoin ℂ G) (cosetFacePacket τ hτ A J) := by
  classical
  rw [cosetFacePacket_eq_translateOrbit_bottom τ hτ A J haJ hbJ hab hJ]
  refine ellipticGammaTranslateOrbit_diffIndepOn_daExtension_of_pairwiseSeparated
    (hτ a) (hτ b) hperiods _ ?_ hG
  rintro s ⟨g, hg, rfl⟩ s' ⟨g', hg', rfl⟩ hss
  have hgne : g ≠ g' := fun hc => hss (by rw [hc])
  have hdiff : g + -(1 + τ b) / 2 - (g' + -(1 + τ b) / 2) = g - g' := by ring
  rw [hdiff]
  exact thetaTranslationNonresonant_cosetFaceShiftSet_sub τ hQ hA J haJ hbJ hab hg hg' hgne

/-- **Faithful labelling of the bottom packet.**  Distinct labelled shifts give distinct
translates: a coincidence would make a nonresonant order-one defect vanish. -/
theorem cosetFaceShiftSet_translate_injective_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (J : Finset ι) {a b : ι} (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b)
    (hJ : ∀ i, i ∉ J → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    {g g' : ℂ} (hg : g ∈ cosetFaceShiftSet τ A J) (hg' : g' ∈ cosetFaceShiftSet τ A J)
    (heq : addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
      addTranslationMeroEquiv g' (multipleEllipticGammaLogDerivFaceMero τ hτ J)) :
    g = g' := by
  classical
  by_contra hne
  have hnr := thetaTranslationNonresonant_cosetFaceShiftSet_sub τ hQ hA J haJ hbJ hab hg hg' hne
  set Ψ := ellipticGammaLogDerivMero (τ a) (τ b) (hτ a) (hτ b) with hΨdef
  set c : ℂ := -(1 + τ b) / 2 with hcdef
  have hbridge : ∀ u : ℂ,
      addTranslationMeroEquiv u (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
        addTranslationMeroEquiv (u + c) Ψ := by
    intro u
    rw [multipleEllipticGammaLogDerivFaceMero_two_surviving τ hτ J haJ hbJ hab hJ,
      addTranslationMeroEquiv_add]
  rw [hbridge g, hbridge g'] at heq
  have hshift := congrArg (addTranslationMeroEquiv (-(g' + c))) heq
  rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add] at hshift
  have harg1 : -(g' + c) + (g + c) = g - g' := by ring
  have harg2 : -(g' + c) + (g' + c) = 0 := by ring
  rw [harg1, harg2, addTranslationMeroEquiv_zero_apply] at hshift
  have hzero : ellipticGammaExternalLogDerivDefectMero (g - g') (τ a) (τ b) (hτ a) (hτ b) = 0 := by
    rw [ellipticGammaExternalLogDerivDefectMero, hshift, sub_self]
  have hHT := (hypertranscendentalOver_ellipticGammaExternalLogDerivDefectMero_iff_nonresonant
    (g - g') (τ a) (τ b) (hτ a) (hτ b) hperiods).mpr hnr
  rw [hzero] at hHT
  exact hHT (by
    simpa using
      HTGeometry.differentialAlgebraicOver_algebraMap
        (F := ↥(meromorphicEllipticCompositum (τ a) (τ b)))
        (E := meroField (Set.univ : Set ℂ)) 0)

end

end GaloisForLFunctions
