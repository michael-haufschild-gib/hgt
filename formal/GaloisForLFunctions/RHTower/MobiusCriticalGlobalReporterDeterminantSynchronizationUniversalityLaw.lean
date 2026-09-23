import GaloisForLFunctions.RHTower.MobiusCriticalFisherReporterEscapeUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusCriticalSoftHardReporterEscapeUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusFisherSoftHardDeterminantSynchronizationUniversalityLaw

/-!
# Möbius critical global reporter/determinant synchronization

The determinant synchronization law retains reporter blindness only on a punctured neighborhood of
zero aperture.  The pointwise Fisher escape theorem upgrades its soft branch to every positive
aperture while preserving the exact hard/soft ratio and both determinant obstructions.
-/

open Complex Filter MeasureTheory
open scoped Topology

namespace RHTower

noncomputable section

/-- **Möbius critical global reporter/determinant synchronization universality law.**  The
hard/soft ratio and determinant coordinates synchronize, the soft Fisher coefficient escapes every
fixed bounded reporter at every positive aperture, the hard profile does so eventually, and no
quadratic reporter can track either synchronized determinant signal. -/
theorem mobiusCriticalGlobalReporterDeterminantSynchronizationUniversality
    {α : Type*} {l : Filter α} [l.NeBot] (sigma u : α → ℝ)
    (hsigma : Tendsto sigma l (nhdsWithin 1 (Set.Ioi 1)))
    (hu : Tendsto u l (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto
        (fun v : ℝ => squarefreeMobiusCriticalFisherCutoffWardLimit v /
          (2 * v / (1 + v) ^ (2 : ℕ)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 4) ∧
      Tendsto
        (fun a =>
          mobiusCriticalPointedFisherDeterminantBoundarySignal (sigma a) -
            mobiusCriticalSoftHardDeterminantBoundarySignal (u a))
        l (nhds 0) ∧
      (∀ (f : Lp ℂ 2 (volume : Measure ℝ))
          (ell : InfiniteMobiusShiftChannel →L[ℂ] ℂ)
          (v : ℝ), 0 < v →
        ¬ Tendsto
          (fun s : ℝ =>
            ell (mobiusCriticalShiftChannel s f) -
              infiniteMobiusCriticalFisherTangentDampedCoefficient s v)
          (nhdsWithin 1 (Set.Ioi 1)) (nhds 0)) ∧
      (∀ (f : Lp ℂ 2 (volume : Measure ℝ))
          (ell : InfiniteMobiusShiftChannel →L[ℂ] ℂ),
        ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ¬ Tendsto
            (fun s : ℝ =>
              ell (mobiusCriticalShiftChannel s f) -
                ((squarefreeMobiusCriticalFisherCutoffWardLimit v / 4 : ℝ) : ℂ))
            (nhdsWithin 1 (Set.Ioi 1)) (nhds 0)) ∧
      ∀ (f : Lp ℂ 2 (volume : Measure ℝ))
          (ell : InfiniteMobiusShiftChannel →L[ℂ] ℂ),
        (¬ Tendsto
          (fun a =>
            (ell (mobiusCriticalShiftChannel (sigma a) f)) ^ (2 : ℕ) -
              mobiusCriticalPointedFisherDeterminantBoundarySignal (sigma a))
          l (nhds 0)) ∧
        (¬ Tendsto
          (fun a =>
            (ell (mobiusCriticalShiftChannel (sigma a) f)) ^ (2 : ℕ) -
              mobiusCriticalSoftHardDeterminantBoundarySignal (u a))
          l (nhds 0)) := by
  have hsoftHard := mobiusCriticalSoftHardReporterEscapeUniversality
  refine ⟨hsoftHard.1,
    mobiusFisherQFIDeterminant_softHardBoundarySynchronization sigma u hsigma hu,
    ?_, ?_, ?_⟩
  · intro f ell v hv
    exact no_fixedReporter_tracks_infiniteMobiusCriticalFisherTangentDampedCoefficient
      hv f ell
  · intro f ell
    filter_upwards [hsoftHard.2 f ell] with v hv
    exact hv.2
  · intro f ell
    have hweak :
        Tendsto (fun a => ell (mobiusCriticalShiftChannel (sigma a) f)) l (nhds 0) :=
      (mobiusCriticalShiftChannel_weakly_tendsto_zero f ell).comp hsigma
    have hsq :
        Tendsto (fun a => (ell (mobiusCriticalShiftChannel (sigma a) f)) ^ (2 : ℕ))
          l (nhds 0) := by
      simpa using hweak.pow 2
    have hpointed :
        Tendsto
          (fun a => mobiusCriticalPointedFisherDeterminantBoundarySignal (sigma a))
          l (nhds (-8 : ℂ)) := by
      have hboundary :
          Tendsto mobiusCriticalPointedFisherDeterminantBoundarySignal
            (nhdsWithin 1 (Set.Ioi 1)) (nhds (-8 : ℂ)) := by
        simpa only [mobiusCriticalPointedFisherDeterminantBoundarySignal] using!
          squarefreeMobiusCritical_fisherQFIDeterminantUniversality.1
      exact hboundary.comp hsigma
    have hsoftHardPath :
        Tendsto
          (fun a => mobiusCriticalSoftHardDeterminantBoundarySignal (u a))
          l (nhds (-8 : ℂ)) :=
      tendsto_mobiusCriticalSoftHardDeterminantBoundarySignal.comp hu
    constructor
    · intro hzero
      have height :
          Tendsto
            (fun a =>
              (ell (mobiusCriticalShiftChannel (sigma a) f)) ^ (2 : ℕ) -
                mobiusCriticalPointedFisherDeterminantBoundarySignal (sigma a))
            l (nhds (8 : ℂ)) := by
        simpa using hsq.sub hpointed
      have heq : (8 : ℂ) = 0 := tendsto_nhds_unique height hzero
      norm_num at heq
    · intro hzero
      have height :
          Tendsto
            (fun a =>
              (ell (mobiusCriticalShiftChannel (sigma a) f)) ^ (2 : ℕ) -
                mobiusCriticalSoftHardDeterminantBoundarySignal (u a))
            l (nhds (8 : ℂ)) := by
        simpa using hsq.sub hsoftHardPath
      have heq : (8 : ℂ) = 0 := tendsto_nhds_unique height hzero
      norm_num at heq

end

end RHTower
