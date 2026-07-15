/-
# Prime--Mellin source incidence for the inverse-gap boundary commutator

The source-free Cauchy-commutator construction is in
`HTGeometry.InverseGapCauchyCommutator`.  The live CCM Mellin colligation identifies its Cauchy
Gram, at every positive regularization scale, with the resolved von-Mangoldt Gram minus the
shifted polar Gram plus the critical Mellin-defect Gram.  This is an arbitrary-node source
identity: no Xi zero list enters the construction.
-/
import GaloisForLFunctions.HTGeometry.InverseGapCauchyCommutator
import GaloisForLFunctions.RHTower.CCMComplexMellinColligation

open Complex Matrix

noncomputable section

namespace RHTower

/-- The CCM Cauchy Gram is the source-free universal Cauchy Gram. -/
theorem cauchyRightHalfPlaneGram_eq_universal {N : ℕ} (w : Fin N → ℂ) :
    cauchyRightHalfPlaneGram w = HTGeometry.rightHalfPlaneCauchyGram w :=
  rfl

/-- **Prime--polar--Mellin incidence for inverse-gap regularization.**  Before any zero set is
chosen, the regularized Cauchy value commutator is the exact signed sum of the resolved prime,
shifted-polar, and critical Mellin-defect commutators. -/
theorem cauchyBoundaryValueCommutator_eq_prime_sub_shiftedPolar_add_mellinDefect
    {N : ℕ} (ε : ℝ) (hε : 0 < ε) (x : Fin N → ℝ) (v : Fin N → ℂ) :
    HTGeometry.gramValueCommutator
        (cauchyRightHalfPlaneGram (HTGeometry.cauchyBoundaryNode ε x)) v =
      HTGeometry.gramValueCommutator
          (vonMangoldtPrimeRightHalfPlaneGram (HTGeometry.cauchyBoundaryNode ε x)) v -
        HTGeometry.gramValueCommutator
          (shiftedPolarRightHalfPlaneGram (HTGeometry.cauchyBoundaryNode ε x)) v +
        HTGeometry.gramValueCommutator
          (criticalMellinDefectRightHalfPlaneGram (HTGeometry.cauchyBoundaryNode ε x)) v := by
  rw [cauchyRightHalfPlaneGram_eq_prime_sub_shiftedPolar_add_criticalMellinDefect,
    HTGeometry.gramValueCommutator_sub_add]
  intro i
  simp [HTGeometry.cauchyBoundaryNode]
  exact hε

end RHTower
