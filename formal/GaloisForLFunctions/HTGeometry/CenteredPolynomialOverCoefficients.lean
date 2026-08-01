import GaloisForLFunctions.HTGeometry.CenteredGenericGalois

/-!
# The centered polynomial over its own coefficient field

Every coefficient of the centered generic polynomial generates the coefficient field, so the
polynomial is defined over that field: writing it as the leading power plus the sum of its lower
coefficients gives a polynomial whose image in the root field is the centered polynomial.

This is what lets the base change step be applied to it, since that step takes a polynomial over the
base field rather than over the field its roots generate.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- The centered coefficients, inside the field they generate. -/
noncomputable def centeredCoeffIn (K : Type*) [Field K] [CharZero K] (d : ℕ) (k : Fin d) :
    centeredCoeffField K d :=
  ⟨centeredCoeff K d k, IntermediateField.subset_adjoin _ _ ⟨k, rfl⟩⟩

/-- The centered generic polynomial, over its own coefficient field. -/
noncomputable def centeredMonicE (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    Polynomial (centeredCoeffField K d) :=
  Polynomial.X ^ d + ∑ k : Fin d, Polynomial.C (centeredCoeffIn K d k) * Polynomial.X ^ (k : ℕ)

/-- **Its image in the root field is the centered polynomial.** -/
theorem map_centeredMonicE :
    Polynomial.map (algebraMap (centeredCoeffField K d) (centeredField K d))
      (centeredMonicE K d) = centeredMonicL K d := by
  have hterm : ∀ k : Fin d,
      Polynomial.map (algebraMap (centeredCoeffField K d) (centeredField K d))
        (Polynomial.C (centeredCoeffIn K d k) * Polynomial.X ^ (k : ℕ)) =
      Polynomial.C ((centeredMonicL K d).coeff (k : ℕ)) * Polynomial.X ^ (k : ℕ) := by
    intro k
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      coeff_centeredMonicL_lt k.2]
    rfl
  rw [centeredMonicE, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Finset.sum_congr rfl (fun k _ => hterm k),
    Fin.sum_univ_eq_sum_range
      (fun k => Polynomial.C ((centeredMonicL K d).coeff k) * Polynomial.X ^ k) d]
  conv_rhs => rw [(monic_centeredMonicL (K := K) (d := d)).as_sum]
  rw [natDegree_centeredMonicL]

theorem natDegree_centeredMonicE : (centeredMonicE K d).natDegree = d := by
  have hinj := (algebraMap (centeredCoeffField K d) (centeredField K d)).injective
  rw [← Polynomial.natDegree_map_eq_of_injective hinj, map_centeredMonicE,
    natDegree_centeredMonicL]

theorem monic_centeredMonicE : (centeredMonicE K d).Monic := by
  have hinj := (algebraMap (centeredCoeffField K d) (centeredField K d)).injective
  have hL : (centeredMonicL K d).coeff d = 1 := by
    have h := (monic_centeredMonicL (K := K) (d := d)).leadingCoeff
    rwa [Polynomial.leadingCoeff, natDegree_centeredMonicL] at h
  refine hinj ?_
  rw [map_one]
  show (algebraMap (centeredCoeffField K d) (centeredField K d))
    ((centeredMonicE K d).coeff (centeredMonicE K d).natDegree) = 1
  rw [← Polynomial.coeff_map, map_centeredMonicE, natDegree_centeredMonicE, hL]

theorem centeredMonicE_ne_zero : centeredMonicE K d ≠ 0 :=
  monic_centeredMonicE.ne_zero

end GaloisForLFunctions.HTGeometry
