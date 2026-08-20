import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCosetLayerGluing
import GaloisForLFunctions.HTGeometry.FaceTranslateInjective

/-!
# Faithful labelling of the labelled packets

The labelled analogue of `FaceTranslateInjective`.  For a face with at least two surviving
parameters, distinct labelled shifts give distinct translates of the face coordinate; hence the
labelled palette and the labelled displacement labelling are injective.

* **`cosetFaceShiftSet_translate_injective`**;
* **`cosetFacePalette_injective`**;
* **`cosetFacePacketDisplacementSlice_injective`**.
-/

open Filter Topology Set Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry
open MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000 in
/-- Faithful labelling for a labelled face whose complement has a prescribed size. -/
theorem cosetFaceShiftSet_translate_injective_aux
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A) :
    ∀ (k : ℕ) (L : Finset ι), (Lᶜ).card = k + 2 →
      ∀ g g' : ℂ, g ∈ cosetFaceShiftSet τ A L → g' ∈ cosetFaceShiftSet τ A L →
        addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L) =
            addTranslationMeroEquiv g' (multipleEllipticGammaLogDerivFaceMero τ hτ L) →
          g = g' := by
  classical
  intro k
  induction k with
  | zero =>
      intro L hcard g g' hg hg' heq
      obtain ⟨a, b, hab, hLc⟩ := Finset.card_eq_two.mp hcard
      have hmem : ∀ i : ι, i ∉ L ↔ i = a ∨ i = b := by
        intro i
        rw [← Finset.mem_compl, hLc, Finset.mem_insert, Finset.mem_singleton]
      have haL : a ∉ L := (hmem a).mpr (Or.inl rfl)
      have hbL : b ∉ L := (hmem b).mpr (Or.inr rfl)
      exact cosetFaceShiftSet_translate_injective_bottom τ hτ hQ hA L haL hbL hab
        (fun i hi => (hmem i).mp hi)
        (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab)
        hg hg' heq
  | succ k ih =>
      intro L hcard g g' hg hg' heq
      have hne : (Lᶜ).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨q, hqc⟩ := hne
      have hq : q ∉ L := Finset.mem_compl.mp hqc
      have hcard' : ((insert q L)ᶜ).card = k + 2 := by
        rw [Finset.compl_insert, Finset.card_erase_of_mem hqc, hcard]
        omega
      have hstep : addTranslationMeroEquiv (τ q)
            (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L)) -
              addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L) =
          addTranslationMeroEquiv (τ q)
            (addTranslationMeroEquiv g' (multipleEllipticGammaLogDerivFaceMero τ hτ L)) -
              addTranslationMeroEquiv g' (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
        rw [heq]
      rw [facePacket_coface τ hτ L hq g, facePacket_coface τ hτ L hq g'] at hstep
      exact ih (insert q L) hcard' g g'
        (cosetFaceShiftSet_mono τ A (Finset.subset_insert q L) hg)
        (cosetFaceShiftSet_mono τ A (Finset.subset_insert q L) hg')
        hstep

/-- **Faithful labelling of a labelled face packet.** -/
theorem cosetFaceShiftSet_translate_injective
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (L : Finset ι) (hL : 2 ≤ (Lᶜ).card)
    {g g' : ℂ} (hg : g ∈ cosetFaceShiftSet τ A L) (hg' : g' ∈ cosetFaceShiftSet τ A L)
    (heq : addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L) =
      addTranslationMeroEquiv g' (multipleEllipticGammaLogDerivFaceMero τ hτ L)) :
    g = g' := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hL
  exact cosetFaceShiftSet_translate_injective_aux τ hτ hQ hA k L (by omega) g g' hg hg' heq

/-- **The labelled palette is a faithful parametrization of the labelled packet.** -/
theorem cosetFacePalette_injective
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (L : Finset ι) (hL : 2 ≤ (Lᶜ).card) {q : ι} (hq : q ∈ L) :
    Function.Injective (cosetFacePalette τ hτ A L q) := by
  classical
  rintro ⟨a, m⟩ ⟨a', m'⟩ hpal
  obtain ⟨h, hh, hha₀⟩ := a.2
  obtain ⟨h', hh', hha'₀⟩ := a'.2
  have hha : addTranslationMeroEquiv h (multipleEllipticGammaLogDerivFaceMero τ hτ L) =
      (a : meroField (Set.univ : Set ℂ)) := hha₀
  have hha' : addTranslationMeroEquiv h' (multipleEllipticGammaLogDerivFaceMero τ hτ L) =
      (a' : meroField (Set.univ : Set ℂ)) := hha'₀
  have hval : addTranslationMeroEquiv ((m : ℂ) * τ q + h)
        (multipleEllipticGammaLogDerivFaceMero τ hτ L) =
      addTranslationMeroEquiv ((m' : ℂ) * τ q + h')
        (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
    rw [← addTranslationMeroEquiv_add, ← addTranslationMeroEquiv_add, hha, hha']
    exact hpal
  have hshift := cosetFaceShiftSet_translate_injective τ hτ hQ hA L hL
    (cosetFaceShiftSet_add_zsmul τ A L hq (cosetFaceShiftSetSlice_subset τ A L q hh) m)
    (cosetFaceShiftSet_add_zsmul τ A L hq (cosetFaceShiftSetSlice_subset τ A L q hh') m')
    hval
  have hm : m = m' := cosetFaceShiftSetSlice_zsmul_eq τ hQ hA L hq hh hh' hshift
  subst hm
  have hhh : h = h' := add_left_cancel hshift
  subst hhh
  have haa : a = a' := Subtype.ext (by rw [← hha, ← hha'])
  rw [haa]

/-- **The labelled displacement labelling is injective.** -/
theorem cosetFacePacketDisplacementSlice_injective
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {A : Set ℂ} (hA : CosetSeparated τ A)
    (J : Finset ι) {q : ι} (hq : q ∉ J) (hcard : 2 ≤ (((insert q J))ᶜ).card) :
    Function.Injective (cosetFacePacketDisplacementSlice τ hτ A J hq) := by
  classical
  rintro y y' hdisp
  obtain ⟨g, hg, hgy⟩ := y.2
  obtain ⟨g', hg', hgy'⟩ := y'.2
  have hval : addTranslationMeroEquiv (τ q) (y : meroField (Set.univ : Set ℂ)) -
      (y : meroField (Set.univ : Set ℂ)) =
    addTranslationMeroEquiv (τ q) (y' : meroField (Set.univ : Set ℂ)) -
      (y' : meroField (Set.univ : Set ℂ)) :=
    congrArg (fun w : ↥(cosetFacePacketSlice τ hτ A (insert q J) q) =>
      (w : meroField (Set.univ : Set ℂ))) hdisp
  rw [← hgy, ← hgy', facePacket_coface τ hτ J hq g, facePacket_coface τ hτ J hq g'] at hval
  have hgg' : g = g' := cosetFaceShiftSet_translate_injective τ hτ hQ hA (insert q J) hcard
    (cosetFaceShiftSet_mono τ A (Finset.subset_insert q J) hg)
    (cosetFaceShiftSet_mono τ A (Finset.subset_insert q J) hg') hval
  subst hgg'
  exact Subtype.ext (by rw [← hgy, ← hgy'])

end

end GaloisForLFunctions
