import GaloisForLFunctions.RHTower.MobiusCriticalGlobalReporterDeterminantSynchronizationUniversalityLaw

/-!
# Möbius critical continuous-calibration determinant-blind synchronization

Every fixed bounded reporter of the critical Möbius shift channel collapses weakly at the Euler
boundary.  The completed pointed-Fisher and transformed soft--hard determinant channels instead
converge to the same nonzero value.  Consequently no origin-preserving continuous calibration of
such a reporter can track either determinant channel.  This upgrades the previous quadratic
obstruction to its full topological form.
-/

open Complex Filter MeasureTheory
open scoped Topology

namespace RHTower

noncomputable section

/-- **Möbius critical continuous-calibration determinant-blind synchronization universality
law.**  The hard/soft ratio, determinant synchronization, global soft escape, and eventual hard
escape persist.  After any continuous calibration germ fixing zero, every fixed bounded reporter
remains unable to track either synchronized determinant signal. -/
theorem mobiusCriticalContinuousCalibrationDeterminantBlindSynchronizationUniversality
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
          (ell : InfiniteMobiusShiftChannel →L[ℂ] ℂ)
          (phi : ℂ → ℂ), ContinuousAt phi 0 → phi 0 = 0 →
        (¬ Tendsto
          (fun a =>
            phi (ell (mobiusCriticalShiftChannel (sigma a) f)) -
              mobiusCriticalPointedFisherDeterminantBoundarySignal (sigma a))
          l (nhds 0)) ∧
        (¬ Tendsto
          (fun a =>
            phi (ell (mobiusCriticalShiftChannel (sigma a) f)) -
              mobiusCriticalSoftHardDeterminantBoundarySignal (u a))
          l (nhds 0)) := by
  have hglobal :=
    mobiusCriticalGlobalReporterDeterminantSynchronizationUniversality sigma u hsigma hu
  refine ⟨hglobal.1, hglobal.2.1, hglobal.2.2.1, hglobal.2.2.2.1, ?_⟩
  intro f ell phi hphi hphi0
  have hweak :
      Tendsto (fun a => ell (mobiusCriticalShiftChannel (sigma a) f)) l (nhds 0) :=
    (mobiusCriticalShiftChannel_weakly_tendsto_zero f ell).comp hsigma
  have hcalibrated :
      Tendsto (fun a => phi (ell (mobiusCriticalShiftChannel (sigma a) f)))
        l (nhds 0) := by
    simpa [hphi0] using! hphi.tendsto.comp hweak
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
            phi (ell (mobiusCriticalShiftChannel (sigma a) f)) -
              mobiusCriticalPointedFisherDeterminantBoundarySignal (sigma a))
          l (nhds (8 : ℂ)) := by
      simpa using hcalibrated.sub hpointed
    have heq : (8 : ℂ) = 0 := tendsto_nhds_unique height hzero
    norm_num at heq
  · intro hzero
    have height :
        Tendsto
          (fun a =>
            phi (ell (mobiusCriticalShiftChannel (sigma a) f)) -
              mobiusCriticalSoftHardDeterminantBoundarySignal (u a))
          l (nhds (8 : ℂ)) := by
      simpa using hcalibrated.sub hsoftHard
    have heq : (8 : ℂ) = 0 := tendsto_nhds_unique height hzero
    norm_num at heq

/-- The previous quadratic reporter obstruction is the specialization `phi(z) = z²` of the
continuous-calibration law. -/
theorem mobiusCriticalContinuousCalibration_recoversQuadraticReporterBlindness
    {α : Type*} {l : Filter α} [l.NeBot] (sigma u : α → ℝ)
    (hsigma : Tendsto sigma l (nhdsWithin 1 (Set.Ioi 1)))
    (hu : Tendsto u l (nhdsWithin 0 (Set.Ioi 0))) :
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
  intro f ell
  simpa only [id_eq] using
    (mobiusCriticalContinuousCalibrationDeterminantBlindSynchronizationUniversality
      sigma u hsigma hu).2.2.2.2 f ell (fun z : ℂ => z ^ (2 : ℕ))
      (continuousAt_id.pow 2) (by norm_num)

end

end RHTower
