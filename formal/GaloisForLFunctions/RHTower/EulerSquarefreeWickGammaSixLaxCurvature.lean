import GaloisForLFunctions.RHTower.EulerSquarefreeWickGammaSixCurvatureBridge
import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Noncommutative Lax realization of the EWQ--Gamma-six curvature

The scalar opposite-character orbit is multiplicatively rank one, so its determinant flatness
cannot see the anchored EWQ interaction.  A dimension-preserving noncommutative lift does see it:
place the forward and reflected Gamma-six boundary defects on the two opposite nilpotent roots of
`sl₂`.  Their matrix commutator is exactly the Gamma-six curvature times the Cartan signature.

Equivalently, the two unipotent transports around the common-refinement square commute exactly at
the neutral physical character.  At every literal prime clock and Xi divisor copy this is exactly
critical-line placement.  The canonical BZ construction uses only one nilpotent root and therefore
commutes identically; it cannot supply the opposite-root condition by itself.  This module proves
the exact fixed-rank receiver and the sharp same-root no-go, not a source theorem forcing the two
physical transports to commute.
-/

open scoped Matrix

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Forward Gamma-six boundary defect placed on the upper BZ nilpotent root. -/
def gammaSixForwardNilpotentResidue (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  belinskiZakharovNilpotentResidue (Real.exp a - 1)

/-- Reflected Gamma-six boundary defect placed on the opposite lower nilpotent root. -/
def gammaSixReflectedNilpotentResidue (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; Real.exp (-a) - 1, 0]

/-- Cartan signature carrying the opposite-root commutator. -/
def gammaSixOppositeRootSignature : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- Noncommutative curvature of the two opposite physical-character roots. -/
def gammaSixOppositeRootCommutator (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  gammaSixForwardNilpotentResidue a * gammaSixReflectedNilpotentResidue a -
    gammaSixReflectedNilpotentResidue a * gammaSixForwardNilpotentResidue a

/-- Exact matrix landing of Gamma-six curvature, hence of the EWQ interaction class. -/
theorem gammaSixOppositeRootCommutator_eq_curvature (a : ℝ) :
    gammaSixOppositeRootCommutator a =
      (-_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a) •
        gammaSixOppositeRootSignature := by
  rw [_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects,
    _root_.RHTower.sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
    _root_.RHTower.sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaSixOppositeRootCommutator, gammaSixForwardNilpotentResidue,
      gammaSixReflectedNilpotentResidue, gammaSixOppositeRootSignature,
      belinskiZakharovNilpotentResidue] <;>
    ring

/-- Opposite-root zero curvature has the exact neutral radical. -/
theorem gammaSixOppositeRootCommutator_eq_zero_iff (a : ℝ) :
    gammaSixOppositeRootCommutator a = 0 ↔ a = 0 := by
  rw [gammaSixOppositeRootCommutator_eq_curvature]
  constructor
  · intro h
    have h00 := congr_fun₂ h (0 : Fin 2) (0 : Fin 2)
    simp [gammaSixOppositeRootSignature] at h00
    exact (_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff a).mp
      h00
  · intro ha
    subst a
    simp [_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]

/-- Forward unipotent transport on the fixed two-dimensional carrier. -/
def gammaSixForwardUnipotentTransport (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  1 + gammaSixForwardNilpotentResidue a

/-- Reflected unipotent transport on the same fixed carrier. -/
def gammaSixReflectedUnipotentTransport (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  1 + gammaSixReflectedNilpotentResidue a

/-- The two paths around the binary common-refinement square differ by the EWQ--Gamma-six
curvature, without any growing auxiliary gauge cube. -/
theorem gammaSixUnipotentTransport_pathDifference_eq_curvature (a : ℝ) :
    gammaSixForwardUnipotentTransport a * gammaSixReflectedUnipotentTransport a -
        gammaSixReflectedUnipotentTransport a * gammaSixForwardUnipotentTransport a =
      (-_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a) •
        gammaSixOppositeRootSignature := by
  rw [← gammaSixOppositeRootCommutator_eq_curvature]
  simp [gammaSixForwardUnipotentTransport, gammaSixReflectedUnipotentTransport,
    gammaSixOppositeRootCommutator]
  noncomm_ring

/-- Dimension-preserving Beck--Chevalley law: the opposite unipotent paths commute exactly at the
neutral character. -/
theorem gammaSixUnipotentTransport_commute_iff (a : ℝ) :
    Commute (gammaSixForwardUnipotentTransport a)
      (gammaSixReflectedUnipotentTransport a) ↔ a = 0 := by
  constructor
  · intro h
    have hpath :
        gammaSixForwardUnipotentTransport a * gammaSixReflectedUnipotentTransport a -
          gammaSixReflectedUnipotentTransport a * gammaSixForwardUnipotentTransport a = 0 :=
      sub_eq_zero.mpr h.eq
    rw [gammaSixUnipotentTransport_pathDifference_eq_curvature] at hpath
    have h00 := congr_fun₂ hpath (0 : Fin 2) (0 : Fin 2)
    simp [gammaSixOppositeRootSignature] at h00
    exact (_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff a).mp
      h00
  · intro ha
    subst a
    simp [gammaSixForwardUnipotentTransport, gammaSixReflectedUnipotentTransport,
      gammaSixForwardNilpotentResidue, gammaSixReflectedNilpotentResidue,
      belinskiZakharovNilpotentResidue]

/-- At every prime clock, path independence of the fixed-rank EWQ/Gamma-six transports is exactly
critical-line placement of the chosen Xi divisor copy. -/
theorem gammaSixPrimePhysicalUnipotentTransport_commute_iff
    (q : _root_.RHTower.XiZeroCopy) (p : Nat.Primes) :
    Commute
        (gammaSixForwardUnipotentTransport
          (Real.log (p : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1))
        (gammaSixReflectedUnipotentTransport
          (Real.log (p : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [gammaSixUnipotentTransport_commute_iff]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  rw [mul_eq_zero]
  simp only [hlog, false_or]
  exact _root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1

/-- Sharp BZ no-go: two residues in the canonical single nilpotent root commute for all
coefficients, so its existing zero-curvature law cannot detect the EWQ interaction. -/
theorem belinskiZakharovSameRootCommutator_eq_zero (u v : ℝ) :
    belinskiZakharovNilpotentResidue u * belinskiZakharovNilpotentResidue v -
        belinskiZakharovNilpotentResidue v * belinskiZakharovNilpotentResidue u = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [belinskiZakharovNilpotentResidue]

end

end GaloisForLFunctions.RHTower
