import GaloisForLFunctions.HTGeometry.CenteredFullMonodromyIn
import GaloisForLFunctions.HTGeometry.CenteredFreeParameter
import GaloisForLFunctions.HTGeometry.FreeParameterBaseChange
import GaloisForLFunctions.HTGeometry.SplittingFieldOverRootField

/-!
# The centered equation over the parameter field

An ambient splitting field of the centered polynomial together with the radical is a splitting field
of the centered polynomial alone over the root field of the radical, so the base change statement
can be read there.

Adjoining a free parameter to that base leaves the Galois group unchanged.  So over the coefficient
field extended by a radical of the constant coefficient and by one independent transcendental — the
field the rank-one fiber equation is written over — the Galois group is the full symmetric group.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}
variable {L : Type*} [Field L] [Algebra (centeredCoeffField K d) L]

/-- **Full symmetric monodromy over the parameter field, at an even exponent.**  Over the
rational functions in one free variable above the root field of the radical, the centered equation
of degree `d` has the full symmetric group on `d` letters. -/
noncomputable def centeredParameterMonodromy (hd : 3 ≤ d) {m : ℕ} (hm : 0 < m)
    [Polynomial.IsSplittingField (centeredCoeffField K d) L
      (centeredMonicE K d *
        (Polynomial.X ^ (2 * m) -
          Polynomial.C (centeredConstant K d (show 0 < d by omega))))] :
    (FractionRing (Polynomial L) ≃ₐ[
        fracSub
          (rootField (centeredCoeffField K d) (L := L)
            (Polynomial.X ^ (2 * m) -
              Polynomial.C (centeredConstant K d (show 0 < d by omega))))
          L]
      FractionRing (Polynomial L)) ≃* Equiv.Perm (Fin d) := by
  have hq : (Polynomial.X ^ (2 * m) -
      Polynomial.C (centeredConstant K d (show 0 < d by omega)) :
      Polynomial (centeredCoeffField K d)) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C _ (by omega)).ne_zero
  haveI := isSplittingField_over_rootField (L := L) centeredMonicE_ne_zero hq
  have hsplit := Polynomial.IsSplittingField.splits'
    (K := rootField (centeredCoeffField K d) (L := L)
      (Polynomial.X ^ (2 * m) -
        Polynomial.C (centeredConstant K d (show 0 < d by omega))))
    (L := L)
    (f := (centeredMonicE K d).map
      (algebraMap (centeredCoeffField K d)
        (rootField (centeredCoeffField K d) (L := L)
          (Polynomial.X ^ (2 * m) -
            Polynomial.C (centeredConstant K d (show 0 < d by omega))))))
  exact freeParameterPermEquiv
    (map_rootField_ne_zero (centeredMonicE_ne_zero (K := K) (d := d)) _)
    (separable_map_rootField (separable_centeredMonicE (K := K) (d := d)) _)
    hsplit
    (adjoin_rootSet_eq_top _)
    (centeredFullMonodromyIn hd hm)

/-- **Full symmetric monodromy over the parameter field, at an odd exponent.**  Over the
rational functions in one free variable above the root field of the radical, the centered equation
of degree `d` has the full symmetric group on `d` letters. -/
noncomputable def centeredParameterMonodromyOdd (hd : 3 ≤ d) {n : ℕ} (hn : 0 < n) (hodd : ¬ 2 ∣ n)
    [Polynomial.IsSplittingField (centeredCoeffField K d) L
      (centeredMonicE K d *
        (Polynomial.X ^ n -
          Polynomial.C (centeredConstant K d (show 0 < d by omega))))] :
    (FractionRing (Polynomial L) ≃ₐ[
        fracSub
          (rootField (centeredCoeffField K d) (L := L)
            (Polynomial.X ^ n -
              Polynomial.C (centeredConstant K d (show 0 < d by omega))))
          L]
      FractionRing (Polynomial L)) ≃* Equiv.Perm (Fin d) := by
  have hq : (Polynomial.X ^ n -
      Polynomial.C (centeredConstant K d (show 0 < d by omega)) :
      Polynomial (centeredCoeffField K d)) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C _ (by omega)).ne_zero
  haveI := isSplittingField_over_rootField (L := L) centeredMonicE_ne_zero hq
  have hsplit := Polynomial.IsSplittingField.splits'
    (K := rootField (centeredCoeffField K d) (L := L)
      (Polynomial.X ^ n -
        Polynomial.C (centeredConstant K d (show 0 < d by omega))))
    (L := L)
    (f := (centeredMonicE K d).map
      (algebraMap (centeredCoeffField K d)
        (rootField (centeredCoeffField K d) (L := L)
          (Polynomial.X ^ n -
            Polynomial.C (centeredConstant K d (show 0 < d by omega))))))
  exact freeParameterPermEquiv
    (map_rootField_ne_zero (centeredMonicE_ne_zero (K := K) (d := d)) _)
    (separable_map_rootField (separable_centeredMonicE (K := K) (d := d)) _)
    hsplit
    (adjoin_rootSet_eq_top _)
    (centeredFullMonodromyOddIn hd hn hodd)

end GaloisForLFunctions.HTGeometry
