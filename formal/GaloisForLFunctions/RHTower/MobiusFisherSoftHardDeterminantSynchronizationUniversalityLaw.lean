import GaloisForLFunctions.RHTower.MobiusCriticalSoftHardFisherBoundaryUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusFisherQFIDeterminantUniversalityLaw

/-!
# Möbius Fisher soft--hard/determinant synchronization universality

The hard/soft Fisher ratio and the completed pointed-Fisher determinant arise from separate
regularizations.  The corpus limits and the negative half-square determinant transform force
their critical boundaries to synchronize along every coupled approach path.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- Completed pointed-Fisher determinant, extended by zero outside the Euler half-plane. -/
def mobiusCriticalPointedFisherDeterminantBoundarySignal (sigma : ℝ) : ℂ :=
  if hsigma : 1 < sigma then
    (GaloisForLFunctions.HTGeometry.pointedFisherConnectionCompression
      (infiniteMobiusSignedWeightLp sigma hsigma)
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma)).det
  else 0

/-- Negative half-square transform of the hard/soft Fisher boundary ratio. -/
def mobiusCriticalSoftHardDeterminantBoundarySignal (u : ℝ) : ℂ :=
  -(1 / 2 : ℂ) *
    ((squarefreeMobiusCriticalFisherCutoffWardLimit u /
      mobiusCriticalSoftFisherCoefficientLimit u : ℝ) : ℂ) ^ (2 : ℕ)

/-- The transformed hard/soft boundary ratio has the same universal `-8` limit as the completed
pointed-Fisher determinant. -/
theorem tendsto_mobiusCriticalSoftHardDeterminantBoundarySignal :
    Tendsto mobiusCriticalSoftHardDeterminantBoundarySignal
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-8 : ℂ)) := by
  have hratioReal :=
    tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_softFisherCoefficientLimit
  have hratio :
      Tendsto
        (fun u : ℝ =>
          ((squarefreeMobiusCriticalFisherCutoffWardLimit u /
            mobiusCriticalSoftFisherCoefficientLimit u : ℝ) : ℂ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (4 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hratioReal
  change Tendsto
    (fun u : ℝ => -(1 / 2 : ℂ) *
      ((squarefreeMobiusCriticalFisherCutoffWardLimit u /
        mobiusCriticalSoftFisherCoefficientLimit u : ℝ) : ℂ) ^ (2 : ℕ))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (-8 : ℂ))
  convert tendsto_const_nhds.mul (hratio.pow 2) using 1
  norm_num

/-- **Möbius Fisher boundary synchronization universality law.** Along every coupled path and
every source filter approaching the Euler critical boundary and the vanishing hard-clock window,
the completed pointed-Fisher determinant and the negative half-square hard/soft ratio become
indistinguishable. -/
theorem mobiusFisherQFIDeterminant_softHardBoundarySynchronization
    {α : Type*} {l : Filter α} (sigma u : α → ℝ)
    (hsigma : Tendsto sigma l (nhdsWithin 1 (Set.Ioi 1)))
    (hu : Tendsto u l (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto
      (fun a =>
        mobiusCriticalPointedFisherDeterminantBoundarySignal (sigma a) -
          mobiusCriticalSoftHardDeterminantBoundarySignal (u a))
      l (nhds 0) := by
  have hdet :
      Tendsto mobiusCriticalPointedFisherDeterminantBoundarySignal
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (-8 : ℂ)) := by
    simpa only [mobiusCriticalPointedFisherDeterminantBoundarySignal] using!
      squarefreeMobiusCritical_fisherQFIDeterminantUniversality.1
  have hdetPath := hdet.comp hsigma
  have hsoftHardPath :=
    tendsto_mobiusCriticalSoftHardDeterminantBoundarySignal.comp hu
  simpa using hdetPath.sub hsoftHardPath

end

end RHTower
