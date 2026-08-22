import GaloisForLFunctions.RHTower.EulerSquarefreeWickReplicaDensityOrientation
import GaloisForLFunctions.RHTower.EulerSquarefreeWickHolonomyRecurrence
import GaloisForLFunctions.RHTower.FESemilinearTwoTorsionExtension

/-!
# EWQ replica interaction as a genuine Krein extension

The positive two-replica EWQ density contains identical Euler-log marginals on its diagonal and
the unsquared joint quadratic character off diagonal.  Removing the two marginals does not leave
another positive density.  It leaves exactly the functional-equation hyperbolic weld block, with
rate `chi(p)^k / k`.  That rate is nonzero at every prime depth, so the interaction quotient is a
genuine split-signature Krein direction.

This identifies the higher principle behind several earlier obstructions.  The completed Xi
landing is carried by the positive diagonal marginal; the coefficient-faithful EWQ orientation is
the nonsplit extension between the two lanes.  Hilbert positivity cannot descend to the quotient
unchanged.  A viable completed mechanism must instead pair its negative Krein direction with an
independently positive completed capacity through a Schur or boundary incidence law.

The normalized anchored interaction extracts residue one.  This is precisely the constant residue
of the corpus's genuine FE-semilinear two-torsion extension.  Thus the extension is now sourced by
the literal EWQ packet rather than inserted as an unrelated unit, although its later completed
divisor activation remains open.
-/

open Complex Matrix Polynomial

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Common Euler-log diagonal marginal weight at one prime depth. -/
def eulerWickReplicaMarginalWeight (x : PrimePowerClockIndex) : ℝ :=
  (((x.2 + 1 : ℕ) : ℝ))⁻¹

/-- Interaction quotient obtained by removing the two one-lane diagonal marginals. -/
def eulerWickReplicaCenteredInteraction
    (x : PrimePowerClockIndex) : Matrix (Fin 2) (Fin 2) ℂ :=
  eulerWickReplicaDensity x - (eulerWickReplicaMarginalWeight x : ℂ) • 1

/-- Signed real activation of the EWQ interaction quotient. -/
def eulerWickReplicaKreinRate (x : PrimePowerClockIndex) : ℝ :=
  eulerWickReplicaMarginalWeight x * (eulerWickQuadraticDepthCharacter x).re

/-- **Replica-to-Krein identification.**  Removing both Euler-log marginals from the positive EWQ
density leaves exactly the FE hyperbolic weld block carrying the unsquared interaction character. -/
theorem eulerWickReplicaCenteredInteraction_eq_weldFEKreinGram
    (x : PrimePowerClockIndex) :
    eulerWickReplicaCenteredInteraction x = weldFEKreinGram (eulerWickReplicaKreinRate x) := by
  rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [eulerWickReplicaCenteredInteraction, eulerWickReplicaMarginalWeight,
      eulerWickReplicaKreinRate, eulerWickReplicaDensity, eulerWickReplicaVector,
      GaloisForLFunctions.HTGeometry.finiteBuresTargetRay, Matrix.vecMulVec,
      weldFEKreinGram, h]

/-- The literal quadratic character activates the Krein extension at every prime depth. -/
theorem eulerWickReplicaKreinRate_ne_zero (x : PrimePowerClockIndex) :
    eulerWickReplicaKreinRate x ≠ 0 := by
  have hdepth : ((x.2 : ℝ) + 1) ≠ 0 := by positivity
  rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h <;>
    simp [eulerWickReplicaKreinRate, eulerWickReplicaMarginalWeight, h, hdepth]

/-- The marginal quotient of the positive replica is unconditionally indefinite.  Positivity of
the original density therefore cannot be inherited by interaction cohomology. -/
theorem eulerWickReplicaCenteredInteraction_not_kreinNonneg
    (x : PrimePowerClockIndex) :
    ¬_root_.RHTower.KreinNonneg (eulerWickReplicaCenteredInteraction x) := by
  rw [eulerWickReplicaCenteredInteraction_eq_weldFEKreinGram,
    weldFEKreinGram_kreinNonneg_iff]
  exact eulerWickReplicaKreinRate_ne_zero x

/-- The normalized anchored EWQ packet extracts the canonical unit extension residue. -/
theorem eulerWickNormalizedInteraction_extracts_unitExtensionResidue :
    (-1 / 8 : ℂ) *
      (eulerWickQuadraticParityCompression eulerWickNormalizedInteractionCarrier) 0 = 1 := by
  rw [eulerWickQuadraticParityCompression_normalizedInteraction]
  norm_num

/-- At every positive torsion length the EWQ-normalized unit residue realizes the corpus's genuine
FE-semilinear nonsplit two-torsion extension. -/
theorem eulerWickUnitTwoTorsionExtension_equivariant_and_nonsplit (m : ℕ) :
    _root_.RHTower.FESemilinearIntertwines _root_.RHTower.feCoefficientParity
        (_root_.RHTower.twoTorsionSourceFEParity (m + 1) 1)
        (_root_.RHTower.feUnitTwoTorsionExtension (m + 1)) ∧
      ¬ ∃ U V : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        _root_.RHTower.feUnitTwoTorsionExtension (m + 1) =
          U * _root_.RHTower.twoTorsionSplitPresentation (m + 1) 1 * V := by
  exact _root_.RHTower.feUnitTwoTorsionExtension_equivariant_and_nonsplit (by omega)

end


end GaloisForLFunctions.RHTower
