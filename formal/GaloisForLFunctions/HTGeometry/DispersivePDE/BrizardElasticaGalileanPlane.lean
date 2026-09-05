import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaGalileanAction
import Mathlib.Tactic

/-!
# Explicit plane waves inhabit the compatible Galilean solution space

This module proves the affine transport chain rule for every plane wave in paper equation (27).
The general certified Galilean action is therefore non-vacuous, and its orbit through each plane
wave is exactly the paper's wave-number translation `k ↦ k+v`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Every explicit paper plane wave has the transport compatibility needed by repeated boosts. -/
noncomputable def planeWaveCompatibleJet (D a k : ℝ) : TransportCompatibleJet2 where
  toComplexEvolutionJet2 := planeWaveJet D a k
  hasDerivAt_transport := by
    intro c t x
    have h := (hasDerivAt_linearPhase_time
      (D * (a ^ 2 / 2 - k ^ 2) - k * c) k t x).const_mul (a : ℂ)
    apply (h.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards with s
      simp only [planeWaveJet, planeWave]
      rw [linearPhase_shift]
    · simp only [planeWaveJet]
      rw [linearPhase_shift]
      push_cast
      ring

noncomputable def planeWaveCompatibleSolution (D a k : ℝ) :
    TransportCompatibleBrizardSolution D :=
  ⟨planeWaveCompatibleJet D a k, planeWave_solves D a k⟩

theorem planeWaveCompatibleSolution_solves (D a k : ℝ) :
    SolvesNLS D (planeWaveCompatibleSolution D a k).val.toComplexEvolutionJet2 :=
  (planeWaveCompatibleSolution D a k).property

/-- Applying the certified action produces the exact translated plane-wave field. -/
theorem galileanCompatible_planeWave_field (D a k v t x : ℝ) :
    (galileanCompatibleBrizardSolution D v
        (planeWaveCompatibleSolution D a k)).val.u t x =
      planeWave D a (k + v) t x := by
  rw [galileanCompatibleBrizardSolution_field]
  exact galileanField_planeWave D a k v t x

/-- Every certified translated plane wave remains an exact solution. -/
theorem galileanCompatible_planeWave_solves (D a k v : ℝ) :
    SolvesNLS D
      (galileanCompatibleBrizardSolution D v
        (planeWaveCompatibleSolution D a k)).val.toComplexEvolutionJet2 :=
  (galileanCompatibleBrizardSolution D v
    (planeWaveCompatibleSolution D a k)).property

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
