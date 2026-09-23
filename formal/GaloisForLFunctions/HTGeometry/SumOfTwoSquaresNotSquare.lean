import GaloisForLFunctions.HTGeometry.SquarefreeNotSquareInFractionField
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable

/-!
# A product of distinct "sum of two squares" factors is not a square

The Kummer independence needed by the generic two-local Galois computation is, after the block
decomposition, the statement that for every nonempty set `S` of environments

  `∏_{z ∈ S} ((X + c_z)² + w²)`

is not a square in `K(X)`, where the `c_z` are pairwise distinct and `w ≠ 0`.  Over a field
containing a square root `I` of `-1` each factor splits as `(X − (−c_z + Iw))(X − (−c_z − Iw))`,
so the product has `2|S|` **distinct** roots, hence is separable, hence squarefree — and a
squarefree non-unit is not a square in the fraction field.

No multivariate irreducibility is needed: the whole independence statement is a one-variable
separability computation.

## Main results

* `not_isSquare_ratFunc_prod_X_sub_C` — a product of distinct monic linear factors is not a square
  in `K(X)`.
* `sq_add_sq_eq_prod_linear` — `(X + c)² + w² = (X − (−c + Iw))(X − (−c − Iw))`.
* `not_isSquare_prod_sq_add_sq` — the independence statement itself.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- A product of distinct monic linear factors is squarefree and not a unit, hence not a square in
the rational function field. -/
theorem not_isSquare_ratFunc_prod_X_sub_C {ι : Type*} [Fintype ι] [Nonempty ι]
    {f : ι → K} (hf : Function.Injective f) :
    ¬ IsSquare (algebraMap K[X] (RatFunc K) (∏ i, (X - C (f i)))) := by
  refine not_isSquare_algebraMap_of_squarefree ?_ ?_
  · exact (Polynomial.separable_prod_X_sub_C_iff.mpr hf).squarefree
  · intro hu
    have hmonic : (∏ i, (X - C (f i))).Monic :=
      monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (f i)
    have hdeg : (∏ i, (X - C (f i))).natDegree = Fintype.card ι := by
      rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (f i)]
      simp
    have hz := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [hdeg] at hz
    exact Fintype.card_ne_zero hz

/-- `(X + c)² + w²` splits over a field containing `√(-1)`. -/
theorem sq_add_sq_eq_prod_linear {I : K} (hI : I * I = -1) (c w : K) :
    (X + C c) ^ (2 : ℕ) + C (w * w) = (X - C (-c + I * w)) * (X - C (-c - I * w)) := by
  have hIC : (C I : K[X]) * C I = -1 := by
    rw [← map_mul, hI, map_neg, map_one]
  simp only [map_add, map_sub, map_neg, map_mul]
  linear_combination (C w * C w) * hIC

/-- **The independence statement.**  With pairwise distinct `c_z` and the separation
`c_z − c_{z'} ≠ 2Iw` (which at `z = z'` is exactly `Iw ≠ 0`), the product of the
`(X + c_z)² + w²` is not a square in `K(X)`. -/
theorem not_isSquare_prod_sq_add_sq {ι : Type*} [Fintype ι] [Nonempty ι] {I : K}
    (hI : I * I = -1) {c : ι → K} (hc : Function.Injective c) {w : K}
    (hsep : ∀ z z' : ι, c z - c z' ≠ 2 * (I * w)) :
    ¬ IsSquare (algebraMap K[X] (RatFunc K)
      (∏ z, ((X + C (c z)) ^ (2 : ℕ) + C (w * w)))) := by
  classical
  set root : ι × Bool → K :=
    fun p => if p.2 then -c p.1 + I * w else -c p.1 - I * w with hroot
  have hinj : Function.Injective root := by
    rintro ⟨z, a⟩ ⟨z', a'⟩ h
    simp only [hroot] at h
    rcases a with _ | _ <;> rcases a' with _ | _ <;> simp only [Bool.false_eq_true,
      if_false, if_true] at h
    · have hcc : c z = c z' := by linear_combination -h
      rw [hc hcc]
    · exact absurd (by linear_combination h : c z' - c z = 2 * (I * w)) (hsep z' z)
    · exact absurd (by linear_combination -h : c z - c z' = 2 * (I * w)) (hsep z z')
    · have hcc : c z = c z' := by linear_combination -h
      rw [hc hcc]
  have hprod : (∏ z, ((X + C (c z)) ^ (2 : ℕ) + C (w * w)))
      = ∏ p : ι × Bool, (X - C (root p)) := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [sq_add_sq_eq_prod_linear hI, Fintype.prod_bool]
    simp only [hroot, if_false, Bool.false_eq_true, if_pos]
  rw [hprod]
  exact not_isSquare_ratFunc_prod_X_sub_C hinj

end GaloisForLFunctions.HTGeometry
