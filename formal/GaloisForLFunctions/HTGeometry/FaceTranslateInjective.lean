import GaloisForLFunctions.HTGeometry.BottomFaceStarIndependence

/-!
# Faithful labelling of every face packet

Distinct external lattice shifts give distinct translates of a face coordinate, for every face with
at least two surviving parameters — not only for the bottom faces.  Adding a surviving direction to
the face turns the coincidence into a coincidence one level deeper, so the statement descends to a
face with exactly two surviving parameters, where it is the nonvanishing of a nonresonant defect of
the order-one elliptic gamma.

* **`faceShiftLattice_translate_injective`** — faithful labelling of a face packet;
* **`facePalette_injective`** — hence the palette is a faithful parametrization;
* **`facePacketDisplacementSlice_injective`** — and the displacement labelling is injective, which
  is the freeness input of the descending face-lifting lemma.
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

set_option maxHeartbeats 1000000 in
/-- Faithful labelling for a face whose complement has a prescribed size, by induction on the
number of surviving parameters beyond the second. -/
theorem faceShiftLattice_translate_injective_aux
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ) :
    ∀ (k : ℕ) (L : Finset ι), (Lᶜ).card = k + 2 →
      ∀ g g' : ℂ, g ∈ faceShiftLattice τ L → g' ∈ faceShiftLattice τ L →
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
      exact faceShiftLattice_translate_injective_bottom τ hτ hQ L haL hbL hab
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
        (faceShiftLattice_mono τ (Finset.subset_insert q L) hg)
        (faceShiftLattice_mono τ (Finset.subset_insert q L) hg')
        hstep

/-- **Faithful labelling of a face packet.**  For a face with at least two surviving parameters,
distinct external lattice shifts give distinct translates of the face coordinate. -/
theorem faceShiftLattice_translate_injective
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (L : Finset ι) (hL : 2 ≤ (Lᶜ).card)
    {g g' : ℂ} (hg : g ∈ faceShiftLattice τ L) (hg' : g' ∈ faceShiftLattice τ L)
    (heq : addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L) =
      addTranslationMeroEquiv g' (multipleEllipticGammaLogDerivFaceMero τ hτ L)) :
    g = g' := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hL
  exact faceShiftLattice_translate_injective_aux τ hτ hQ k L (by omega) g g' hg hg' heq

/-- **The palette is a faithful parametrization of the packet.**  Distinct pairs of a slice point
and an exponent give distinct germs. -/
theorem facePalette_injective
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (L : Finset ι) (hL : 2 ≤ (Lᶜ).card) {q : ι} (hq : q ∈ L) :
    Function.Injective (facePalette τ hτ L q) := by
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
  have hshift := faceShiftLattice_translate_injective τ hτ hQ L hL
    (faceShiftLattice_add_zsmul τ L hq (faceShiftLatticeSlice_subset τ L q hh) m)
    (faceShiftLattice_add_zsmul τ L hq (faceShiftLatticeSlice_subset τ L q hh') m')
    hval
  have hm : m = m' := faceShiftLatticeSlice_zsmul_eq τ hQ L q hh hh' hshift
  subst hm
  have hhh : h = h' := add_left_cancel hshift
  subst hhh
  have haa : a = a' := Subtype.ext (by rw [← hha, ← hha'])
  rw [haa]

/-- **The displacement labelling is injective.**  Two packet elements with the same displacement in
a surviving direction have the same lattice shift, because the displacement is the corresponding
translate of the coface coordinate. -/
theorem facePacketDisplacementSlice_injective
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J : Finset ι) {q : ι} (hq : q ∉ J) (hcard : 2 ≤ (((insert q J))ᶜ).card) :
    Function.Injective (facePacketDisplacementSlice τ hτ J hq) := by
  classical
  rintro y y' hdisp
  obtain ⟨g, hg, hgy⟩ := y.2
  obtain ⟨g', hg', hgy'⟩ := y'.2
  have hval : addTranslationMeroEquiv (τ q) (y : meroField (Set.univ : Set ℂ)) -
      (y : meroField (Set.univ : Set ℂ)) =
    addTranslationMeroEquiv (τ q) (y' : meroField (Set.univ : Set ℂ)) -
      (y' : meroField (Set.univ : Set ℂ)) :=
    congrArg (fun w : ↥(multipleEllipticGammaFacePacketSlice τ hτ (insert q J) q) =>
      (w : meroField (Set.univ : Set ℂ))) hdisp
  rw [← hgy, ← hgy', facePacket_coface τ hτ J hq g, facePacket_coface τ hτ J hq g'] at hval
  have hgg' : g = g' := faceShiftLattice_translate_injective τ hτ hQ (insert q J) hcard
    (faceShiftLattice_mono τ (Finset.subset_insert q J) hg)
    (faceShiftLattice_mono τ (Finset.subset_insert q J) hg') hval
  subst hgg'
  exact Subtype.ext (by rw [← hgy, ← hgy'])

end

end GaloisForLFunctions
