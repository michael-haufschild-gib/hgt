import GaloisForLFunctions.RHTower.XiFormationEscapePrincipalClassLaw
import GaloisForLFunctions.RHTower.XiWardCubicReflectionLoewnerCodiagonalIncidence
import GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionSubquantum

/-!
# Direct subunit fusion of escape multiplicity and cubic capacity

The corpus has both halves of a Ferrero--Washington-shaped direct anchor.  Every strict-right Xi
copy carries one integer Kakutani escape unit, while its cubic Loewner landing costs at least
`115 / 108`.  The complete primitive Euler collision budget is strictly smaller than that same
quantum.

This module proves the exact three-organ fusion

`Euler budget < (115 / 108) * escape multiplicity <= cubic Loewner landing`.

No amplification occurs.  Exact signed source-to-completion transport, arithmetic-current to
reflection--Loewner identification, opposite-radial residue landing, and shorting already exist
elsewhere in the corpus.  The open theorem is formation strictness: after the common non-trace-class
metric is removed, the finite source cancellations must assemble into one coherent prime-mixed
primitive whose exactness witness survives completion.  Such a theorem must be proved before
divisor specialization.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Every actual strict-right Xi copy carries exactly one unsigned integer escape unit. -/
theorem xiRight_thetaKakutaniEscapeMultiplicity_eq_one
    (q : XiRightZeroCopy) :
    thetaKakutaniEscapeMultiplicity q.1 = 1 := by
  apply thetaKakutaniEscapeMultiplicity_eq_one_of_boundaryFlux_ne_zero
  intro hflux
  have hrate :=
    (thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero q.1).1 hflux
  have hline := (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1.1).1 hrate
  have hright := q.2
  rw [I_mul_xiSpectralPoint] at hright
  norm_num at hright hline
  linarith

/-- **Direct subunit escape-capacity fusion.**  For every actual strict-right Xi copy, the complete
primitive Euler capacity is smaller than one quantized escape unit, and that unit is bounded by
the copy's exact cubic Loewner landing. -/
theorem xiRight_directSubunitEscapeCapacityGap
    (q : XiRightZeroCopy) :
    routePPrimitiveCollisionCubicTraceBudget <
        (115 / 108 : ℝ) * thetaKakutaniEscapeMultiplicity q.1 ∧
      (115 / 108 : ℝ) * thetaKakutaniEscapeMultiplicity q.1 ≤
        ∫ r : ℝ in Set.Ioi 0,
          xiWardCubicReflectionLoewnerCodiagonalLanding q.1.1 r := by
  have hindex := xiRight_thetaKakutaniEscapeMultiplicity_eq_one q
  constructor
  · simpa [hindex] using routePPrimitiveCollisionCubicTraceBudget_lt_quantum
  · have hright := q.2
    rw [I_mul_xiSpectralPoint] at hright
    have hcharge :=
      xiWardCubicReflectionLoewnerCodiagonalLanding_charge_ge_quantum q.1.1 (by
        norm_num at hright ⊢
        linarith)
    simpa [hindex] using hcharge

end

end RHTower
