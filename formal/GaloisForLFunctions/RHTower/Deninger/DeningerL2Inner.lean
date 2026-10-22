import GaloisForLFunctions.RHTower.Deninger.DeningerL2Norm

/-!
# The `L²` inner product on the place space

The `L²` place norm is a weighted sum of squares, so it is the diagonal of the weighted sum of
products.  That form is symmetric, additive in each argument under multiplication of algebraic
numbers — because the logarithm of a place is additive — and multiplies by `[L : K]` on each fibre
under base change, by the same computation as for the norm.

* `deningerL2Inner` : the weighted sum of products.
* `deningerL2Inner_self` : its diagonal is `deningerL2NormSq`.
* `deningerL2Inner_comm` : symmetry.
* `deningerL2FibreSumProd` : the fibre law for the product.
-/

namespace RHTower

open NumberField Module

section Inner

variable {K : Type*} [Field K] [NumberField K]

/-- The `L²` inner product of two algebraic numbers on the place space. -/
noncomputable def deningerL2Inner (x y : K) : ℝ :=
  (∑ v : InfinitePlace K, (v.mult : ℝ) * (Real.log (v x) * Real.log (v y)))
    + ∑ᶠ w : FinitePlace K, (Real.log (w x) * Real.log (w y)) / (deningerPlaceDegree w : ℝ)

/-- **The diagonal of the inner product is the `L²` norm.** -/
theorem deningerL2Inner_self (x : K) : deningerL2Inner x x = deningerL2NormSq x := by
  rw [deningerL2Inner, deningerL2NormSq]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [← pow_two]
  · refine finsum_congr fun w => ?_
    rw [← pow_two]

/-- **The inner product is symmetric.** -/
theorem deningerL2Inner_comm (x y : K) : deningerL2Inner x y = deningerL2Inner y x := by
  rw [deningerL2Inner, deningerL2Inner]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_comm (Real.log (v x))]
  · refine finsum_congr fun w => ?_
    rw [mul_comm (Real.log (w x))]

end Inner

section FibreProd

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The weighted fibre sum law for products.**  Summing `(log ‖x‖_w)(log ‖y‖_w)/d_w` over the
places above `v` multiplies the corresponding quantity at `v` by `[L : K]`. -/
theorem deningerL2FibreSumProd (v : FinitePlace K) (x y : K) :
    ∑ w ∈ deningerPlacesOver (L := L) v,
        (Real.log (w (algebraMap K L x)) * Real.log (w (algebraMap K L y)))
          / (deningerPlaceDegree w : ℝ)
      = (finrank K L : ℝ)
          * ((Real.log (v x) * Real.log (v y)) / (deningerPlaceDegree v : ℝ)) := by
  have hdv : (0 : ℝ) < (deningerPlaceDegree v : ℝ) := by
    exact_mod_cast deningerPlaceDegree_pos v
  have hterm : ∀ w ∈ deningerPlacesOver (L := L) v,
      (Real.log (w (algebraMap K L x)) * Real.log (w (algebraMap K L y)))
          / (deningerPlaceDegree w : ℝ)
        = (deningerRelDegree (K := K) w : ℝ)
            * ((Real.log (v x) * Real.log (v y)) / (deningerPlaceDegree v : ℝ)) := by
    intro w hw
    have hres : deningerRestrictPlace (K := K) w = v := (deningerMem_placesOver v w).mp hw
    have hvalx := deningerFinitePlace_apply_relDegree (K := K) w x
    have hvaly := deningerFinitePlace_apply_relDegree (K := K) w y
    rw [hres] at hvalx hvaly
    have hrpos : 0 < deningerRelDegree (K := K) w := by
      haveI : (Ideal.under (𝓞 K) w.maximalIdeal.asIdeal).IsMaximal :=
        Ring.DimensionLEOne.maximalOfPrime (Ideal.under_ne_bot (𝓞 K) w.maximalIdeal.ne_bot)
          (Ideal.IsPrime.under (𝓞 K) w.maximalIdeal.asIdeal)
      refine Nat.pos_of_ne_zero (Nat.mul_ne_zero ?_ (Ideal.inertiaDeg'_ne_zero _ _))
      exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.maximalIdeal.asIdeal
        (Ideal.under_ne_bot (𝓞 K) w.maximalIdeal.ne_bot)
    have hdeg : (deningerPlaceDegree w : ℝ)
        = (deningerPlaceDegree v : ℝ) * (deningerRelDegree (K := K) w : ℝ) := by
      have h := deningerPlaceDegree_tower (K := K) w
      rw [hres] at h
      rw [h, deningerRelDegree]
      push_cast
      ring
    have hrne : ((deningerRelDegree (K := K) w : ℝ)) ≠ 0 := by
      exact_mod_cast hrpos.ne'
    rw [hvalx, hvaly, Real.log_pow, Real.log_pow, hdeg]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  congr 1
  rw [← Nat.cast_sum, deningerRelDegree_sum v]

end FibreProd

end RHTower
