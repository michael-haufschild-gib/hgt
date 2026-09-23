import GaloisForLFunctions.RHTower.PrimeMellinInverseGapEnergy
import GaloisForLFunctions.RHTower.CriticalMellinFourCoordinateCollapseUniversalityLaw

/-!
# Regularized critical-Mellin inverse-gap incidence universality

The finite inverse-gap commutator incidence originally used the Laplace critical-Mellin
coordinate.  Four-coordinate collapse identifies its Gram with the pole-filled globally continued
germ whose half-plane analyticity classifies RH.  Hence both the signed commutator incidence and
its squared entry energy admit an exact expression in that RH-classifying coordinate.
-/

open Complex Matrix

noncomputable section

namespace RHTower

/-- Boundary inverse-gap commutator incidence in the RH-classifying regularized coordinate. -/
theorem cauchyBoundaryValueCommutator_eq_prime_sub_shiftedPolar_add_regularizedCriticalMellin
    {N : ℕ} (ε : ℝ) (hε : 0 < ε) (x : Fin N → ℝ) (v : Fin N → ℂ) :
    HTGeometry.gramValueCommutator
        (cauchyRightHalfPlaneGram (HTGeometry.cauchyBoundaryNode ε x)) v =
      HTGeometry.gramValueCommutator
          (vonMangoldtPrimeRightHalfPlaneGram (HTGeometry.cauchyBoundaryNode ε x)) v -
        HTGeometry.gramValueCommutator
          (shiftedPolarRightHalfPlaneGram (HTGeometry.cauchyBoundaryNode ε x)) v +
        HTGeometry.gramValueCommutator
          (regularizedCriticalMellinRightHalfPlaneGram
            (HTGeometry.cauchyBoundaryNode ε x)) v := by
  have hw : ∀ i, 0 < (HTGeometry.cauchyBoundaryNode ε x i).re := by
    intro i
    simp [HTGeometry.cauchyBoundaryNode, hε]
  rw [← criticalMellinDefectRightHalfPlaneGram_eq_regularized
    (HTGeometry.cauchyBoundaryNode ε x) hw]
  exact cauchyBoundaryValueCommutator_eq_prime_sub_shiftedPolar_add_mellinDefect
    ε hε x v

/-- Inverse-gap energy is the signed prime--polar--regularized-critical-Mellin packet energy. -/
theorem regularizedInverseGapCommutatorEnergy_eq_primePolarRegularizedCriticalMellinIncidence
    {N : ℕ} (ε : ℝ) (hε : 0 < ε) (x : Fin N → ℝ) (v : Fin N → ℂ) :
    HTGeometry.regularizedInverseGapCommutatorEnergy ε x v =
      ∑ i, ∑ j,
        ‖HTGeometry.gramValueCommutator
              (vonMangoldtPrimeRightHalfPlaneGram
                (HTGeometry.cauchyBoundaryNode ε x)) v i j -
            HTGeometry.gramValueCommutator
              (shiftedPolarRightHalfPlaneGram
                (HTGeometry.cauchyBoundaryNode ε x)) v i j +
            HTGeometry.gramValueCommutator
              (regularizedCriticalMellinRightHalfPlaneGram
                (HTGeometry.cauchyBoundaryNode ε x)) v i j‖ ^ (2 : ℕ) := by
  have hw : ∀ i, 0 < (HTGeometry.cauchyBoundaryNode ε x i).re := by
    intro i
    simp [HTGeometry.cauchyBoundaryNode, hε]
  rw [← criticalMellinDefectRightHalfPlaneGram_eq_regularized
    (HTGeometry.cauchyBoundaryNode ε x) hw]
  exact regularizedInverseGapCommutatorEnergy_eq_primePolarMellinIncidence
    ε hε x v

end RHTower

end
