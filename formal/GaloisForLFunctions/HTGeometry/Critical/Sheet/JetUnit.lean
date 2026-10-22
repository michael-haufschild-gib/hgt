import GaloisForLFunctions.HTGeometry.MonomialTailFibreCount
import GaloisForLFunctions.HTGeometry.Critical.Schur.SheetLift

/-!
# The jet of a sheet is invertible at the origin, in the valuation ring

The corpus proves `(A + U).coeff 0 ≠ 0` for a point of the critical fibre over a *field*.  The
underlying identity is stronger and needs no field:

```text
criticalLowProduct_coeff_zero_mul     A.coeff 0 * B.coeff 0 = 1, over any commutative ring
isUnit_criticalLowProduct_coeff_zero  hence the constant term is a UNIT
isUnit_criticalSheetJetCoeffZero      ** for every geometric sheet, in the upper Schur valuation
                                         ring **
```

That is exactly what the Schur normalisation needs.  The Schur coordinates divide the raw
coefficients by the zeroth one, and for the argument that two colliding sheets cut out the same
place one has to know that this division stays inside the valuation ring — for *every* sheet, not
only for the canonical one.  Integrality over the observation DVR is not available and is not the
right tool: the fibre equation itself makes the divisor a unit, because the observed tails vanish at
the origin and the compatibility equation reads `A(0)·B(0) = 1` in whatever ring the fibre point
lives.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **The jet and its reciprocal have inverse constant terms**, over any commutative ring. -/
theorem criticalLowProduct_coeff_zero_mul {R : Type*} [CommRing R] {L : ℕ} (hL : 0 < L)
    {U V A B : R[X]} (hU : U.coeff 0 = 0) (hV : V.coeff 0 = 0)
    (h : (X : R[X]) ^ L ∣ (criticalLowProduct U V A B - 1)) :
    A.coeff 0 * B.coeff 0 = 1 := by
  obtain ⟨r, hr⟩ := h
  have hzero : (criticalLowProduct U V A B - 1).coeff 0 = 0 := by
    rw [hr, Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow,
      if_neg (by omega : ¬ ((0 : ℕ) = L)), zero_mul]
  have hcoeff : (criticalLowProduct U V A B - 1).coeff 0
      = A.coeff 0 * B.coeff 0 + A.coeff 0 * V.coeff 0 + U.coeff 0 * B.coeff 0 - 1 := by
    simp only [criticalLowProduct, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.mul_coeff_zero, Polynomial.coeff_one_zero]
  rw [hcoeff, hU, hV] at hzero
  linear_combination hzero

/-- **The constant term of a compatible jet is a unit**, over any commutative ring. -/
theorem isUnit_criticalLowProduct_coeff_zero {R : Type*} [CommRing R] {L : ℕ} (hL : 0 < L)
    {U V A B : R[X]} (hU : U.coeff 0 = 0) (hV : V.coeff 0 = 0)
    (h : (X : R[X]) ^ L ∣ (criticalLowProduct U V A B - 1)) :
    IsUnit (A.coeff 0) :=
  isUnit_iff_exists_inv.mpr ⟨B.coeff 0, criticalLowProduct_coeff_zero_mul hL hU hV h⟩

section Horizon

set_option synthInstance.maxHeartbeats 3000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ}

/-- **The constant term of a sheet's jet is a unit of the upper Schur valuation ring.**  This is
what makes the Schur normalisation legitimate for every sheet, with no integrality input. -/
theorem isUnit_criticalSheetJetCoeffZero (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) :
    IsUnit ((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff 0) := by
  have hU : (criticalNormalClosureSchurRawTailIntegral K
      (by omega : 0 < m) (by omega : 0 < n)).coeff 0 = 0 := by
    refine Polynomial.X_dvd_iff.mp (dvd_trans ?_
      (X_pow_dvd_criticalNormalClosureSchurRawTailIntegral K (by omega) (by omega)))
    exact dvd_pow_self _ (by omega)
  have hV : (criticalNormalClosureSchurReciprocalTailIntegral K
      (by omega : 0 < m) (by omega : 0 < n)).coeff 0 = 0 := by
    refine Polynomial.X_dvd_iff.mp (dvd_trans ?_
      (X_pow_dvd_criticalNormalClosureSchurReciprocalTailIntegral K (by omega) (by omega)))
    exact dvd_pow_self _ (by omega)
  exact isUnit_criticalLowProduct_coeff_zero (L := m + n) (by omega) hU hV
    (criticalGeometricSheetToSchurFibre K hm hn σ).2.2.2

end Horizon

end GaloisForLFunctions.HTGeometry
