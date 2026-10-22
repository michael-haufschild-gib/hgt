import GaloisForLFunctions.HTGeometry.AverageProductNonSquare
import GaloisForLFunctions.HTGeometry.CenteredGenericPolynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The discriminant and the centered constant coefficient are in different square classes

The scaled centered coordinate maps to `d` times the centered root, so the product of all of them
maps to `d ^ d` times the product of the centered roots, which is the constant coefficient of the
centered polynomial up to the sign `(-1) ^ d`.

Over an algebraically closed field of constants that scalar is a square, so the nonsquare statement
for the product of the linear forms transfers to the product of the discriminant with the constant
coefficient of the centered polynomial.  This is the square-class input of the even Kummer case, on
the field of rational functions in the roots and hence on every subfield of it.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

set_option maxRecDepth 8000

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

omit [CharZero K] in
theorem algebraMap_X_eq_genericRoot (i : Fin d) :
    algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) (MvPolynomial.X i) =
      genericRoot K d i := rfl

theorem algebraMap_avgForm (hd : 0 < d) (i : Fin d) :
    algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) (avgForm K d i) =
      (d : SymmetricRationalField K d) * centeredRoot K d i := by
  have hd0 : (d : SymmetricRationalField K d) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [avgForm, map_sub, map_mul, map_sum, map_natCast]
  simp only [algebraMap_X_eq_genericRoot]
  rw [centeredRoot, genericAverage]
  field_simp

theorem algebraMap_prod_avgForm (hd : 0 < d) :
    algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)
        (∏ i : Fin d, avgForm K d i) =
      (d : SymmetricRationalField K d) ^ d * ∏ i : Fin d, centeredRoot K d i := by
  rw [map_prod, Finset.prod_congr rfl (fun i _ => algebraMap_avgForm hd i),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

omit [CharZero K] in
/-- **The constant coefficient of the centered polynomial.** -/
theorem coeff_zero_centeredMonicF :
    (centeredMonicF K d).coeff 0 = (-1 : SymmetricRationalField K d) ^ d *
      ∏ i : Fin d, centeredRoot K d i := by
  rw [Polynomial.coeff_zero_eq_eval_zero, centeredMonicF, Polynomial.eval_prod]
  have hterm : ∀ i : Fin d,
      Polynomial.eval 0 (Polynomial.X - Polynomial.C (centeredRoot K d i)) =
        (-1 : SymmetricRationalField K d) * centeredRoot K d i := by
    intro i
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

omit [CharZero K] in
theorem prod_centeredRoot_eq :
    ∏ i : Fin d, centeredRoot K d i =
      (-1 : SymmetricRationalField K d) ^ d * (centeredMonicF K d).coeff 0 := by
  rw [coeff_zero_centeredMonicF, ← mul_assoc, ← pow_add]
  rw [show d + d = 2 * d from by ring, pow_mul]
  norm_num

/-- **The discriminant times the constant coefficient of the centered polynomial is not a square.**
Over an algebraically closed field of constants, the scalar relating the constant coefficient to
the product of the scaled centered coordinates is a square, so the statement descends from the
product of the linear forms. -/
theorem not_exists_sq_disc_mul_centeredConstant [IsAlgClosed K] (hd : 3 ≤ d) :
    ¬ ∃ t : SymmetricRationalField K d,
      algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)
          (vandermondePoly K d * vandermondePoly K d) * (centeredMonicF K d).coeff 0 = t * t := by
  haveI : NeZero d := ⟨by omega⟩
  rintro ⟨t, ht⟩
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq ((d : K) ^ d * (-1 : K) ^ d) (n := 2) (by norm_num)
  refine not_isSquare_vandermondeSq_mul_avgProduct (K := K) (d := d) hd
    ⟨algebraMap K (SymmetricRationalField K d) u * t, ?_⟩
  have hscalar : algebraMap K (SymmetricRationalField K d) ((d : K) ^ d * (-1 : K) ^ d) =
      (d : SymmetricRationalField K d) ^ d * (-1 : SymmetricRationalField K d) ^ d := by
    rw [map_mul, map_pow, map_pow, map_natCast, map_neg, map_one]
  have hu' : algebraMap K (SymmetricRationalField K d) u *
      algebraMap K (SymmetricRationalField K d) u =
      (d : SymmetricRationalField K d) ^ d * (-1 : SymmetricRationalField K d) ^ d := by
    rw [← map_mul, ← sq, hu, hscalar]
  rw [map_mul, algebraMap_prod_avgForm (by omega), prod_centeredRoot_eq]
  calc algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)
        (vandermondePoly K d * vandermondePoly K d) *
      ((d : SymmetricRationalField K d) ^ d *
        ((-1 : SymmetricRationalField K d) ^ d * (centeredMonicF K d).coeff 0))
      = ((d : SymmetricRationalField K d) ^ d * (-1 : SymmetricRationalField K d) ^ d) *
        (algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)
          (vandermondePoly K d * vandermondePoly K d) * (centeredMonicF K d).coeff 0) := by ring
    _ = (algebraMap K (SymmetricRationalField K d) u *
        algebraMap K (SymmetricRationalField K d) u) * (t * t) := by rw [hu', ht]
    _ = algebraMap K (SymmetricRationalField K d) u * t *
        (algebraMap K (SymmetricRationalField K d) u * t) := by ring

end GaloisForLFunctions.HTGeometry
