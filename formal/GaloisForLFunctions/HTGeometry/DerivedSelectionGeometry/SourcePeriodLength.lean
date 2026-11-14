import GaloisForLFunctions.EisensteinDegeneration.PeriodImage
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.SourceScalarBoundary

/-!
# Period orders in the cyclic-source boundary quotient

The cyclic-source quotient has elementary factors `(c)` and `(c q(q-1))`.
For `c = X^m u` and a rotation approaching either singular value to order
`n+1`, its total length is `2m+n+1`. Its annihilator at the zero rotation
has order `m+n+1`. The period-map length formula thus distinguishes total
boundary length from the longer elementary divisor.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection.NonunitSource
open PowerSeries EisensteinDegeneration
noncomputable section
variable {K : Type*} [Field K]

private theorem rotation_boundary_unit (n : ℕ) (v : (PowerSeries K)ˣ) :
    IsUnit ((X : PowerSeries K) ^ (n + 1) * v - 1) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- At the zero rotation, source vanishing contributes twice its order, while rotation
vanishing contributes once. Both orders retain their full scheme-theoretic length. -/
theorem sourcePeriodQuotient_length_zero (m n : ℕ) (u v : (PowerSeries K)ˣ) :
    Module.length (PowerSeries K)
      (SourceQuotient (X ^ (n + 1) * (v : PowerSeries K))
        (X ^ m * (u : PowerSeries K))) = (2 * m + n + 1 : ℕ) := by
  let q : PowerSeries K := X ^ (n + 1) * (v : PowerSeries K)
  obtain ⟨w, hw⟩ := rotation_boundary_unit n v
  have hfactor : X ^ m * (u : PowerSeries K) * q * (q - 1) =
      X ^ (m + n + 1) * ((u * v * w : (PowerSeries K)ˣ) : PowerSeries K) := by
    rw [← hw]
    dsimp only [q]
    simp only [Units.val_mul, pow_add]
    ring
  rw [(quotientEquiv q (X ^ m * (u : PowerSeries K))).length_eq,
    Module.length_prod, hfactor, periodQuotient_length, periodQuotient_length]
  push_cast
  ring

/-- The annihilator records the longer elementary divisor, not the sum of the two lengths. -/
theorem sourcePeriodQuotient_annihilator_zero (m n : ℕ) (u v : (PowerSeries K)ˣ) :
    Module.annihilator (PowerSeries K)
      (SourceQuotient (X ^ (n + 1) * (v : PowerSeries K))
        (X ^ m * (u : PowerSeries K))) =
      IsLocalRing.maximalIdeal (PowerSeries K) ^ (m + n + 1) := by
  rw [annihilator]
  obtain ⟨w, hw⟩ := rotation_boundary_unit n v
  have hfactor : X ^ m * (u : PowerSeries K) * (X ^ (n + 1) * (v : PowerSeries K)) *
      (X ^ (n + 1) * (v : PowerSeries K) - 1) =
      X ^ (m + n + 1) * ((u * v * w : (PowerSeries K)ˣ) : PowerSeries K) := by
    rw [← hw]
    simp only [Units.val_mul, pow_add]
    ring
  rw [hfactor, periodIdeal_eq]

/-- The second singular rotation has the same length law. -/
theorem sourcePeriodQuotient_length_one (m n : ℕ) (u v : (PowerSeries K)ˣ) :
    Module.length (PowerSeries K)
      (SourceQuotient (1 + X ^ (n + 1) * (v : PowerSeries K))
        (X ^ m * (u : PowerSeries K))) = (2 * m + n + 1 : ℕ) := by
  let q : PowerSeries K := 1 + X ^ (n + 1) * (v : PowerSeries K)
  have hq : IsUnit q := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [q]
  obtain ⟨w, hw⟩ := hq
  have hfactor : X ^ m * (u : PowerSeries K) * q * (q - 1) =
      X ^ (m + n + 1) * ((u * v * w : (PowerSeries K)ˣ) : PowerSeries K) := by
    have hqm : q - 1 = X ^ (n + 1) * (v : PowerSeries K) := by simp [q]
    rw [hqm, ← hw]
    simp only [Units.val_mul, pow_add]
    ring
  rw [(quotientEquiv q (X ^ m * (u : PowerSeries K))).length_eq,
    Module.length_prod, hfactor, periodQuotient_length, periodQuotient_length]
  push_cast
  ring

end
end GaloisForLFunctions.HTGeometry.DerivedSelection.NonunitSource
