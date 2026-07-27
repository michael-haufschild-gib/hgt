import GaloisForLFunctions.HTGeometry.FaceDepthRigidity
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaReflectionHypertranscendenceUniversalityLaw

/-!
# Generic structural universality for multiple elliptic gamma functions

Integral independence of `1` and a finite upper-half-plane period family forces a rank-three minor
as soon as two parameters are present.  It therefore supplies the hypertranscendence/reflection law,
joint differential independence of every uniform bottom-face family, and strict rigidity along all
proper deletion chains.
-/

open Filter Set Topology Complex
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

/-- Integral independence supplies a rationally independent unit-period triple whenever the family
contains at least two parameters. -/
theorem multipleEllipticGammaHasRankThreeMinor_of_periodsIntegrallyIndependent
    (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ)
    (hcard : 2 ≤ Fintype.card ι) :
    MultipleEllipticGammaHasRankThreeMinor τ := by
  classical
  have huniv : 2 ≤ (Finset.univ : Finset ι).card := by simpa using hcard
  obtain ⟨A, -, hAcard⟩ := Finset.exists_subset_card_eq huniv
  obtain ⟨q, r, hqr, -⟩ := Finset.card_eq_two.mp hAcard
  exact ⟨q, r, hqr,
    linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hqr⟩

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Joint differential independence for an arbitrary finite family of bottom faces, without asking
the caller to supply the redundant uniform-cardinality witness. -/
theorem multipleEllipticGammaFaceStar_diffIndepOn_bottom_family
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ)
    (faces : Finset (Finset ι))
    (hbottom : ∀ J ∈ faces, ∃ a b : ι, a ∉ J ∧ b ∉ J ∧ a ≠ b ∧
      ∀ i, i ∉ J → i = a ∨ i = b) :
    DiffIndepOn ℂ
      (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅) := by
  classical
  apply multipleEllipticGammaFaceStar_diffIndepOn_bottom
    τ hτ hQ faces (Fintype.card ι - 2) _ hbottom
  intro J hJfaces
  obtain ⟨a, b, haJ, hbJ, hab, hJ⟩ := hbottom J hJfaces
  have hcomp : Jᶜ = {a, b} := by
    ext i
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact hJ i
    · rintro (rfl | rfl)
      · exact haJ
      · exact hbJ
  have hcardcomp : (Jᶜ).card = 2 := by
    rw [hcomp, Finset.card_pair hab]
  have htotal := Finset.card_add_card_compl J
  omega

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Generic structural universality law.**  Under integral independence and the presence of at
least two periods:

1. a rank-three minor exists, activating the top-level reflection--hypertranscendence law;
2. every uniform finite family of bottom-face packets is jointly differentially independent;
3. external-lattice packets of comparable distinct faces are disjoint while the deeper face retains
   at least two periods.
-/
theorem multipleEllipticGamma_integrallyIndependent_structuralUniversality
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hcard : 2 ≤ Fintype.card ι) :
    MultipleEllipticGammaHasRankThreeMinor τ ∧
      (∀ (faces : Finset (Finset ι)) (s : ℕ),
        (∀ J ∈ faces, J.card = s) →
        (∀ J ∈ faces, ∃ a b : ι, a ∉ J ∧ b ∉ J ∧ a ≠ b ∧
          ∀ i, i ∉ J → i = a ∨ i = b) →
        DiffIndepOn ℂ
          (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅)) ∧
      (∀ (J L : Finset ι), J ⊆ L → J ≠ L → 2 ≤ (Lᶜ).card →
        ∀ (g h : ℂ), g ∈ faceShiftLattice τ J → h ∈ faceShiftLattice τ L →
          addTranslationMeroEquiv g
              (multipleEllipticGammaLogDerivFaceMero τ hτ J) ≠
            addTranslationMeroEquiv h
              (multipleEllipticGammaLogDerivFaceMero τ hτ L)) := by
  refine ⟨
    multipleEllipticGammaHasRankThreeMinor_of_periodsIntegrallyIndependent τ hQ hcard,
    ?_, ?_⟩
  · intro faces s huniform hbottom
    exact multipleEllipticGammaFaceStar_diffIndepOn_bottom
      τ hτ hQ faces s huniform hbottom
  · intro J L hJL hJLne hL g h hg hh
    exact multipleEllipticGammaFace_translate_ne_of_ssubset
      τ hτ hQ J L hJL hJLne hL hg hh

end

end GaloisForLFunctions
