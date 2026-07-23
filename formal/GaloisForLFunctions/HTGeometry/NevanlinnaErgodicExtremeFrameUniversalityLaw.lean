import GaloisForLFunctions.HTGeometry.NevBauerUnconditional
import GaloisForLFunctions.HTGeometry.NevanlinnaKernelErgodicity
import GaloisForLFunctions.HTGeometry.InfiniteSupportBoundaryCarrier

/-!
# Nevanlinna ergodic/extreme/frame universality

For the canonical boundary family of every normalized indeterminate Hamburger sequence, convex
extremality and invariant-set ergodicity select the same Dirac leaves.  Infinite-support parameter
laws lie in the complementary mixed phase, but their carriers retain infinite support and their
complete inverse-Cholesky frame towers remain faithful.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint Set
open scoped OnePoint

noncomputable section

/-- **Nevanlinna ergodic/extreme/frame universality law.**  The canonical Bauer boundary has one
ergodic/extreme phase.  Every infinite-support mixture is nonergodic and nonextreme, while its
carrier support is infinite and its complete canonical frame tower uniquely determines the
projective parameter law. -/
theorem nevBauer_ergodicExtreme_infiniteSupportFrame_phase
    {s : ℕ → ℝ} (h : _root_.HTGeometry.PositiveMomentForm s)
    (h0b : _root_.HTGeometry.BoundedKernel s 0)
    (h0 : s 0 = 1) :
    let F := _root_.HTGeometry.nevBoundaryFamily h h0b h0
    (∀ eta : ProbabilityMeasure (OnePoint ℝ),
      F.IsErgodicConstraintStationaryLaw (F.barycenter eta) ↔
        IsExtremeProbabilityLaw (Set.range F.barycenter) (F.barycenter eta)) ∧
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
  constructor
  · intro eta
    have hergodic := F.barycenter_isErgodicConstraintStationaryLaw_iff_dirac eta
    have hextreme := _root_.HTGeometry.nevBauer_extreme_iff h h0b h0 eta
    exact hergodic.trans hextreme.symm
  · intro eta
    have hsupport := F.barycenter_support_infinite eta.1 eta.2
    have hnotDirac : ¬ ∃ t : OnePoint ℝ,
        eta.1 = (⟨Measure.dirac t, Measure.dirac.isProbabilityMeasure⟩ :
          ProbabilityMeasure (OnePoint ℝ)) := by
      rintro ⟨t, ht⟩
      apply eta.2
      rw [ht]
      exact Set.finite_singleton t |>.subset
        (Measure.support_subset_of_isClosed isClosed_singleton (by simp))
    have hergodic := F.barycenter_isErgodicConstraintStationaryLaw_iff_dirac eta.1
    have hextreme := _root_.HTGeometry.nevBauer_extreme_iff h h0b h0 eta.1
    refine ⟨hsupport, ?_, ?_, ?_⟩
    · exact fun hE => hnotDirac (hergodic.mp hE)
    · exact fun hE => hnotDirac (hextreme.mp hE)
    · intro theta htower
      exact F.injective_completeBoundaryCanonicalFrameTower htower

end

end GaloisForLFunctions.HTGeometry
