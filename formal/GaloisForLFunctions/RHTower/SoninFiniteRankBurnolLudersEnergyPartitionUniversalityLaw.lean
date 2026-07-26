import GaloisForLFunctions.RHTower.SoninFiniteRankWardBoundaryEnergy

/-!
# Sonin finite-rank Burnol--Lüders energy-partition universality

The reflected diagonal Ward form of a finite Sonin packet has two independently proved
representations.  Equating its physical two-corner Hilbert--Schmidt energy representation with its
Burnol-conductor/Lüders representation gives an exact three-channel conservation law.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι]

/-- **Finite-rank Burnol--Lüders energy-partition universality law.**  Total physical Sonin
boundary energy equals the Burnol-conductor trace of the cutoff-commuting Lüders block plus the
reflected Ward trace of the two discarded boundary blocks. -/
theorem soninFiniteRank_burnolLudersBoundaryEnergyPartition
    (a : ℝ) (c : ι → ℂ) (x y : ι → evenSubspace) :
    ((hsNormSq
          (crossBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y)) +
        hsNormSq
          (upperBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y)) : ℝ) : ℂ) =
      finiteRankCutoffWardTrace (evenIndicatorCutoff a)
          (burnolConductor
            (ludersPinching (evenIndicatorCutoff a)
              (finiteRankProbe c
                (fun i ↦ evenFourierTransform (x i))
                (fun i ↦ evenFourierTransform (y i))))
            evenFourierTransform)
          c x y +
        finiteRankCutoffWardTrace (evenFourierCutoff a)
          (crossBoundary (evenIndicatorCutoff a)
              (finiteRankProbe c
                (fun i ↦ evenFourierTransform (x i))
                (fun i ↦ evenFourierTransform (y i))) +
            upperBoundary (evenIndicatorCutoff a)
              (finiteRankProbe c
                (fun i ↦ evenFourierTransform (x i))
                (fun i ↦ evenFourierTransform (y i))))
          c
          (fun i ↦ evenFourierTransform (x i))
          (fun i ↦ evenFourierTransform (y i)) := by
  calc
    ((hsNormSq
          (crossBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y)) +
        hsNormSq
          (upperBoundary (evenIndicatorCutoff a) (finiteRankProbe c x y)) : ℝ) : ℂ) =
        finiteRankCutoffWardForm (evenFourierCutoff a) c
          (fun i ↦ evenFourierTransform (x i))
          (fun i ↦ evenFourierTransform (y i)) c
          (fun i ↦ evenFourierTransform (x i))
          (fun i ↦ evenFourierTransform (y i)) :=
      (finiteRankCutoffWardForm_evenFourier_reflected_self_eq_physicalBoundaryEnergySum
        a c x y).symm
    _ = finiteRankCutoffWardTrace (evenFourierCutoff a)
          (finiteRankProbe c
            (fun i ↦ evenFourierTransform (x i))
            (fun i ↦ evenFourierTransform (y i))) c
          (fun i ↦ evenFourierTransform (x i))
          (fun i ↦ evenFourierTransform (y i)) := rfl
    _ = _ :=
      finiteRankCutoffWardTrace_evenFourierPosition_ludersBoundarySplit
        a
          (finiteRankProbe c
            (fun i ↦ evenFourierTransform (x i))
            (fun i ↦ evenFourierTransform (y i)))
          c x y

end RHTower
