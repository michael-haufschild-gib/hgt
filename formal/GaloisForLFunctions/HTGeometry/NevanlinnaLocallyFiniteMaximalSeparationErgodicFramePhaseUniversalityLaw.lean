import GaloisForLFunctions.HTGeometry.NevLeafLocalFiniteExtremeUniversalityLaw
import GaloisForLFunctions.HTGeometry.MomentIndeterminacyMaximalTotalVariationUniversalityLaw
import GaloisForLFunctions.HTGeometry.NevanlinnaErgodicExtremeFrameUniversalityLaw

/-!
# Nevanlinna locally-finite/maximal-separation ergodic-frame phase

Canonical real Nevanlinna leaves are locally finite on every compact, globally ergodic and extreme,
and pairwise maximally separated in total variation.  Infinite-support projective mixtures occupy
the complementary nonergodic/nonextreme phase while retaining infinite carrier support and
complete-frame identifiability.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint Set
open scoped OnePoint

noncomputable section

/-- **Nevanlinna locally-finite/maximal-separation ergodic-frame phase universality law.**  Pure
real leaves form a locally finite, ergodic/extreme, pairwise maximally separated phase.  Every
infinite-support projective mixture is nonergodic and nonextreme, has infinite real support, and is
still uniquely determined by its complete canonical frame tower. -/
theorem nevanlinna_locallyFiniteMaximalSeparation_ergodicFramePhaseUniversality
    {s : ℕ → ℝ} (h : _root_.HTGeometry.PositiveMomentForm s)
    (h0b : _root_.HTGeometry.BoundedKernel s 0)
    (h0 : s 0 = 1) :
    let F := _root_.HTGeometry.nevBoundaryFamily h h0b h0
    ((∀ t : ℝ,
        F.barycenter
            (⟨Measure.dirac (t : OnePoint ℝ), Measure.dirac.isProbabilityMeasure⟩ :
              ProbabilityMeasure (OnePoint ℝ)) =
              _root_.HTGeometry.nevLeaf h h0b h0 (t : OnePoint ℝ) ∧
          F.IsErgodicConstraintStationaryLaw
            (F.barycenter
              (⟨Measure.dirac (t : OnePoint ℝ), Measure.dirac.isProbabilityMeasure⟩ :
                ProbabilityMeasure (OnePoint ℝ))) ∧
          IsExtremeProbabilityLaw (Set.range F.barycenter)
            (F.barycenter
              (⟨Measure.dirac (t : OnePoint ℝ), Measure.dirac.isProbabilityMeasure⟩ :
                ProbabilityMeasure (OnePoint ℝ)))) ∧
      (∀ (t : ℝ) {K : Set ℝ}, IsCompact K →
        ∃ A : Set ℝ, A.Finite ∧ A ⊆ K ∧
          (_root_.HTGeometry.nevLeaf h h0b h0
              (t : OnePoint ℝ) : Measure ℝ).restrict K =
            (_root_.HTGeometry.nevLeaf h h0b h0
              (t : OnePoint ℝ) : Measure ℝ).restrict A) ∧
      (∀ t u : ℝ, t ≠ u →
        (_root_.HTGeometry.nevLeaf h h0b h0
            (t : OnePoint ℝ) : Measure ℝ) ⟂ₘ
          (_root_.HTGeometry.nevLeaf h h0b h0
            (u : OnePoint ℝ) : Measure ℝ) ∧
        (((_root_.HTGeometry.nevLeaf h h0b h0
              (t : OnePoint ℝ) : Measure ℝ).toSignedMeasure -
            (_root_.HTGeometry.nevLeaf h h0b h0
              (u : OnePoint ℝ) : Measure ℝ).toSignedMeasure).totalVariation
              Set.univ = 2))) ∧
    ∀ eta : InfiniteSupportProjectiveProbability,
      ((F.barycenter eta.1 : ProbabilityMeasure ℝ) : Measure ℝ).support.Infinite ∧
      ¬ F.IsErgodicConstraintStationaryLaw (F.barycenter eta.1) ∧
      ¬ IsExtremeProbabilityLaw (Set.range F.barycenter) (F.barycenter eta.1) ∧
      ∀ theta : InfiniteSupportProjectiveProbability,
        F.completeBoundaryCanonicalFrameTower theta =
            F.completeBoundaryCanonicalFrameTower eta →
          theta = eta := by
  dsimp only
  let F := _root_.HTGeometry.nevBoundaryFamily h h0b h0
  have hphase :=
    nevBauer_ergodicExtreme_infiniteSupportFrame_phase h h0b h0
  refine ⟨⟨?_, ?_, ?_⟩, hphase.2⟩
  · intro t
    let eta : ProbabilityMeasure (OnePoint ℝ) :=
      ⟨Measure.dirac (t : OnePoint ℝ), Measure.dirac.isProbabilityMeasure⟩
    have hbary : F.barycenter eta =
        _root_.HTGeometry.nevLeaf h h0b h0 (t : OnePoint ℝ) := by
      rw [F.barycenter_dirac]
      rfl
    have hergodic : F.IsErgodicConstraintStationaryLaw (F.barycenter eta) := by
      apply (F.barycenter_isErgodicConstraintStationaryLaw_iff_dirac eta).2
      exact ⟨(t : OnePoint ℝ), rfl⟩
    have hextreme :
        IsExtremeProbabilityLaw (Set.range F.barycenter) (F.barycenter eta) :=
      (hphase.1 eta).mp hergodic
    exact ⟨hbary, hergodic, hextreme⟩
  · intro t K hK
    exact _root_.HTGeometry.nevLeaf_compactRestriction_eq_finiteDenominatorSection
      h h0b h0 t hK
  · intro t u htu
    let E := _root_.HTGeometry.nevExtremalFamily h h0b h0
    have hsing :
        (E.leaf (t : OnePoint ℝ) : Measure ℝ) ⟂ₘ
          (E.leaf (u : OnePoint ℝ) : Measure ℝ) :=
      _root_.HTGeometry.mutuallySingular_leaf E htu
    have htv :
        (((E.leaf (t : OnePoint ℝ) : Measure ℝ).toSignedMeasure -
            (E.leaf (u : OnePoint ℝ) : Measure ℝ).toSignedMeasure).totalVariation
              Set.univ = 2) :=
      _root_.HTGeometry.totalVariation_univ_eq_of_isProbability
        (E.leaf (t : OnePoint ℝ) : Measure ℝ)
        (E.leaf (u : OnePoint ℝ) : Measure ℝ) hsing
    simpa [E] using And.intro hsing htv

end

end GaloisForLFunctions.HTGeometry
