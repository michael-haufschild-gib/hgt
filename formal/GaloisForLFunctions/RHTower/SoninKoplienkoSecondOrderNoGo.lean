import GaloisForLFunctions.HTGeometry.KoplienkoSecondOrderGram
import GaloisForLFunctions.RHTower.HilbertSchmidtTraceObstruction
import GaloisForLFunctions.RHTower.SoninRelativeGramDefect

/-!
# Koplienko second-order regularization erases the linear Sonin Euler channel

The principal/residual Sonin Gram defect is Hilbert--Schmidt but its linear cross term is not known
to be trace class.  Koplienko's second-order trace regularization is the canonical tempting
replacement for an ordinary trace of a Hilbert--Schmidt perturbation.  Its defining subtraction,
however, removes the first variation before taking a trace.

For the Sonin perturbation `P + c R`, that first variation is exactly

```text
c P†R + conj(c) R†P,
```

the only part retaining the unsquared logarithmic Euler coefficient.  The second-order remainder
is exactly `|c|² R†R`.  Therefore a Koplienko-regularized scalar can see only the already available
quadratic residual energy and cannot close the open linear relative-trace interface.
-/

namespace RHTower

noncomputable section

/-- The second-order Gram remainder of the principal/residual Sonin perturbation. -/
def centralSoninKoplienkoSecondOrderGram
    (a p : ℝ) (hp : 1 < p) (c : ℂ) : SoninL2 →L[ℂ] SoninL2 :=
  HTGeometry.gramSecondOrderRemainder
    (centralSoninPrincipalDilationCorner a p hp)
    (centralSoninDilationCornerResidual a p hp) c

/-- Expanded form: the Koplienko remainder is the relative Gram defect after subtracting exactly
the principal/residual first variation. -/
theorem centralSoninKoplienkoSecondOrderGram_eq_relativeDefect_sub_firstVariation
    (a p : ℝ) (hp : 1 < p) (c : ℂ) :
    centralSoninKoplienkoSecondOrderGram a p hp c =
      centralSoninWeightedRelativeGramDefect a p hp c -
        (c • (ContinuousLinearMap.adjoint
            (centralSoninPrincipalDilationCorner a p hp) *
              centralSoninDilationCornerResidual a p hp) +
          star c • (ContinuousLinearMap.adjoint
            (centralSoninDilationCornerResidual a p hp) *
              centralSoninPrincipalDilationCorner a p hp)) := by
  rfl

/-- **Koplienko collapse at one scale.**  The second-order subtraction leaves only the quadratic
residual energy. -/
theorem centralSoninKoplienkoSecondOrderGram_eq_residualEnergy
    (a p : ℝ) (hp : 1 < p) (c : ℂ) :
    centralSoninKoplienkoSecondOrderGram a p hp c =
      (star c * c) • centralSoninDilationCornerResidualEnergy a p hp := by
  rw [centralSoninKoplienkoSecondOrderGram,
    HTGeometry.gramSecondOrderRemainder_eq_residualEnergy]
  rfl

/-- Prime-power specialization with the exact logarithmic Euler coefficient. -/
def centralSoninPrimePowerKoplienkoSecondOrderGram
    (a : ℝ) (pk : Nat.Primes × ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  centralSoninKoplienkoSecondOrderGram a (soninPrimePowerScale pk)
    (one_lt_soninPrimePowerScale pk) (soninLogPrimePowerCoefficient pk)

/-- **Prime-power second-order no-go.**  Koplienko regularization squares the logarithmic Euler
coefficient and discards both unsquared principal/residual cross terms. -/
theorem centralSoninPrimePowerKoplienkoSecondOrderGram_eq_squaredResidualEnergy
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    centralSoninPrimePowerKoplienkoSecondOrderGram a pk =
      (star (soninLogPrimePowerCoefficient pk) *
          soninLogPrimePowerCoefficient pk) •
        centralSoninDilationCornerResidualEnergy a (soninPrimePowerScale pk)
          (one_lt_soninPrimePowerScale pk) := by
  exact centralSoninKoplienkoSecondOrderGram_eq_residualEnergy a
    (soninPrimePowerScale pk) (one_lt_soninPrimePowerScale pk)
    (soninLogPrimePowerCoefficient pk)

/-- The second-order regularized prime-power Gram is already trace-ideal because it is merely a
scalar multiple of the known residual energy.  This confirms that regularization repairs the
trace class only by deleting the linear data sought by the route. -/
theorem centralSoninPrimePowerKoplienkoSecondOrderGram_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt
      (centralSoninPrimePowerKoplienkoSecondOrderGram a pk) := by
  rw [centralSoninPrimePowerKoplienkoSecondOrderGram_eq_squaredResidualEnergy]
  have hR := centralSoninDilationCornerResidual_isHilbertSchmidt a
    (soninPrimePowerScale pk) ha (one_lt_soninPrimePowerScale pk)
  exact (hR.adjoint.comp_right
    (centralSoninDilationCornerResidual a (soninPrimePowerScale pk)
      (one_lt_soninPrimePowerScale pk))).smul _

end

end RHTower
