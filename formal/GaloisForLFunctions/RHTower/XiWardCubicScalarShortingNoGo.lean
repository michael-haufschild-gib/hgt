import GaloisForLFunctions.RHTower.XiWardCubicOppositeRadialBoundarySignature

/-!
# Scalar-shortening no-go for the signed opposite-radial source current

The literal signed completed Xi conormal column is anti-Hermitian under
functional-equation reflection plus radial reversal.  This module proves that
the signature survives every *scalar* multiplier with the corresponding
reflection covariance.  Hence a scalar polar--Gamma shortening cannot turn
the continuation-boundary product into a positive source form.

This does not rule out the remaining source mechanism: a coefficient-faithful
nonlocal or matrix-valued oriented contraction may act before continuation.
The result isolates that as a necessary structural feature of any surviving
global shorting law.
-/

open Complex

namespace RHTower

noncomputable section

/-- A scalar source multiplier compatible with functional-equation reflection
and opposite-radial orientation. -/
structure XiWardCubicReflectionCompatibleScalarMultiplier where
  value : ℂ → ℝ → ℂ
  reflection : ∀ (s : ℂ) (r : ℝ),
    value (1 - star s) (-r) = star (value s r)

/-- The scalar-shortened signed completed conormal column. -/
def xiWardCubicScalarShortedConormalColumn
    (m : XiWardCubicReflectionCompatibleScalarMultiplier) (s : ℂ) (r : ℝ) : ℂ :=
  m.value s r * xiWardCubicSignedCompletedConormalColumn s r

/-- Reflection covariance of a scalar multiplier preserves the anti-Hermitian
law of the literal signed completed column. -/
theorem xiWardCubicScalarShortedConormalColumn_reflection
    (m : XiWardCubicReflectionCompatibleScalarMultiplier) (s : ℂ) (r : ℝ) :
    xiWardCubicScalarShortedConormalColumn m (1 - star s) (-r) =
      -star (xiWardCubicScalarShortedConormalColumn m s r) := by
  unfold xiWardCubicScalarShortedConormalColumn
  rw [m.reflection s r, xiWardCubicSignedCompletedConormalColumn_reflection]
  rw [Complex.star_def]
  rw [map_mul]
  ring

/-- The reflected opposite-radial product of every reflection-compatible
scalar shortening remains the negative of its own norm square. -/
theorem xiWardCubicScalarShortedConormalColumn_reflection_pair
    (m : XiWardCubicReflectionCompatibleScalarMultiplier) (s : ℂ) (r : ℝ) :
    xiWardCubicScalarShortedConormalColumn m (1 - star s) (-r) *
        xiWardCubicScalarShortedConormalColumn m s r =
      -((Complex.normSq
        (xiWardCubicScalarShortedConormalColumn m s r) : ℝ) : ℂ) := by
  rw [xiWardCubicScalarShortedConormalColumn_reflection]
  calc
    -star (xiWardCubicScalarShortedConormalColumn m s r) *
        xiWardCubicScalarShortedConormalColumn m s r =
      -(star (xiWardCubicScalarShortedConormalColumn m s r) *
        xiWardCubicScalarShortedConormalColumn m s r) := by ring
    _ = -((Complex.normSq
        (xiWardCubicScalarShortedConormalColumn m s r) : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      rfl

/-- Consequently, a reflection-compatible scalar shortening has nonpositive
real boundary product everywhere. -/
theorem xiWardCubicScalarShortedConormalColumn_reflection_pair_re_nonpos
    (m : XiWardCubicReflectionCompatibleScalarMultiplier) (s : ℂ) (r : ℝ) :
    (xiWardCubicScalarShortedConormalColumn m (1 - star s) (-r) *
        xiWardCubicScalarShortedConormalColumn m s r).re ≤ 0 := by
  rw [xiWardCubicScalarShortedConormalColumn_reflection_pair]
  simp only [Complex.neg_re, Complex.ofReal_re]
  exact neg_nonpos.mpr (Complex.normSq_nonneg _)

end

end RHTower
