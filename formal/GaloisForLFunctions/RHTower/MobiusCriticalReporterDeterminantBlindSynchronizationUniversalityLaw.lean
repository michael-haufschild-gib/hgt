import GaloisForLFunctions.RHTower.MobiusCriticalSoftHardReporterEscapeUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusFisherSoftHardDeterminantSynchronizationUniversalityLaw

/-!
# Möbius critical reporter/determinant blind synchronization

The soft--hard Fisher boundary and completed pointed-Fisher determinant synchronize along every
coupled approach path.  At the same time, every fixed bounded reporter of the critical Möbius shift
channel vanishes weakly.  Hence even the square of such a reporter cannot track either synchronized
nonlinear determinant signal.
-/

open Complex Filter MeasureTheory
open scoped Topology

namespace RHTower

noncomputable section

/-- **Möbius reporter/determinant blind synchronization universality law.**  Along every coupled
Euler-boundary/vanishing-aperture path, the completed pointed-Fisher determinant and transformed
hard/soft signal synchronize.  The parent first-order soft/hard reporter obstructions persist, and
the square of every fixed bounded reporter fails to track either synchronized determinant
coordinate. -/
theorem mobiusCriticalReporterDeterminantBlindSynchronizationUniversality
    {α : Type*} {l : Filter α} [l.NeBot] (sigma u : α → ℝ)
    (hsigma : Tendsto sigma l (nhdsWithin 1 (Set.Ioi 1)))
    (hu : Tendsto u l (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto
        (fun a =>
          mobiusCriticalPointedFisherDeterminantBoundarySignal (sigma a) -
            mobiusCriticalSoftHardDeterminantBoundarySignal (u a))
        l (nhds 0) ∧
      (∀ (f : Lp ℂ 2 (volume : Measure ℝ))
          (ell : InfiniteMobiusShiftChannel →L[ℂ] ℂ),
        ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0),
          (¬ Tendsto
            (fun s : ℝ =>
              ell (mobiusCriticalShiftChannel s f) -
                infiniteMobiusCriticalFisherTangentDampedCoefficient s v)
            (nhdsWithin 1 (Set.Ioi 1)) (nhds 0)) ∧
          (¬ Tendsto
            (fun s : ℝ =>
              ell (mobiusCriticalShiftChannel s f) -
                ((squarefreeMobiusCriticalFisherCutoffWardLimit v / 4 : ℝ) : ℂ))
            (nhdsWithin 1 (Set.Ioi 1)) (nhds 0))) ∧
      ∀ (f : Lp ℂ 2 (volume : Measure ℝ))
          (ell : InfiniteMobiusShiftChannel →L[ℂ] ℂ),
        (¬ Tendsto
          (fun a =>
            (ell (mobiusCriticalShiftChannel (sigma a) f)) ^ 2 -
              mobiusCriticalPointedFisherDeterminantBoundarySignal (sigma a))
          l (nhds 0)) ∧
        (¬ Tendsto
          (fun a =>
            (ell (mobiusCriticalShiftChannel (sigma a) f)) ^ 2 -
              mobiusCriticalSoftHardDeterminantBoundarySignal (u a))
          l (nhds 0)) := by
  refine ⟨mobiusFisherQFIDeterminant_softHardBoundarySynchronization sigma u hsigma hu,
    mobiusCriticalSoftHardReporterEscapeUniversality.2, ?_⟩
  intro f ell
  have hweak :
      Tendsto (fun a => ell (mobiusCriticalShiftChannel (sigma a) f)) l (nhds 0) :=
    (mobiusCriticalShiftChannel_weakly_tendsto_zero f ell).comp hsigma
  have hsq :
      Tendsto (fun a => (ell (mobiusCriticalShiftChannel (sigma a) f)) ^ 2)
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
  have hsoftHard :
      Tendsto
        (fun a => mobiusCriticalSoftHardDeterminantBoundarySignal (u a))
        l (nhds (-8 : ℂ)) :=
    tendsto_mobiusCriticalSoftHardDeterminantBoundarySignal.comp hu
  constructor
  · intro hzero
    have height :
        Tendsto
          (fun a =>
            (ell (mobiusCriticalShiftChannel (sigma a) f)) ^ 2 -
              mobiusCriticalPointedFisherDeterminantBoundarySignal (sigma a))
          l (nhds (8 : ℂ)) := by
      simpa using hsq.sub hpointed
    have heq : (8 : ℂ) = 0 := tendsto_nhds_unique height hzero
    norm_num at heq
  · intro hzero
    have height :
        Tendsto
          (fun a =>
            (ell (mobiusCriticalShiftChannel (sigma a) f)) ^ 2 -
              mobiusCriticalSoftHardDeterminantBoundarySignal (u a))
          l (nhds (8 : ℂ)) := by
      simpa using hsq.sub hsoftHard
    have heq : (8 : ℂ) = 0 := tendsto_nhds_unique height hzero
    norm_num at heq

end

end RHTower
