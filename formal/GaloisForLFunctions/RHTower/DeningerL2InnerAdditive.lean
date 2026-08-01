import GaloisForLFunctions.RHTower.DeningerAbsL2Inner

/-!
# Additivity of the `L²` inner product

The logarithm of a place is additive under multiplication of algebraic numbers, so the `L²` inner
product is additive in each argument.  Together with symmetry and vanishing on torsion this is
what lets the form descend to the Kummer group.

* `deningerL2Inner_mul_left` : additivity in the first argument.
* `deningerL2Inner_mul_right` : additivity in the second argument.
-/

namespace RHTower

open NumberField Module

section Additive

variable {K : Type*} [Field K] [NumberField K]

/-- The summand of the finite part has finite support. -/
private theorem deningerInnerSupportFinite {x : K} (hx : x ≠ 0) (z : K) :
    (Function.support fun w : FinitePlace K =>
      Real.log (w x) * Real.log (w z) / (deningerPlaceDegree w : ℝ)).Finite := by
  refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport hx) ?_
  intro w hw
  by_contra hwS
  refine hw ?_
  show Real.log (w x) * Real.log (w z) / (deningerPlaceDegree w : ℝ) = 0
  have hone : w x = 1 := by
    by_contra hne
    exact hwS hne
  rw [hone, Real.log_one, zero_mul, zero_div]

omit [NumberField K] in
/-- The logarithm of an infinite place is additive. -/
theorem deningerInfinitePlace_log_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (v : InfinitePlace K) : Real.log (v (x * y)) = Real.log (v x) + Real.log (v y) := by
  rw [map_mul, Real.log_mul (InfinitePlace.pos_iff.mpr hx).ne'
    (InfinitePlace.pos_iff.mpr hy).ne']

/-- The logarithm of a finite place is additive. -/
theorem deningerFinitePlace_log_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (w : FinitePlace K) : Real.log (w (x * y)) = Real.log (w x) + Real.log (w y) := by
  rw [map_mul, Real.log_mul (FinitePlace.pos_iff.mpr hx).ne'
    (FinitePlace.pos_iff.mpr hy).ne']

/-- **The `L²` inner product is additive in the first argument.** -/
theorem deningerL2Inner_mul_left {x y z : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    deningerL2Inner (x * y) z = deningerL2Inner x z + deningerL2Inner y z := by
  have harchsum :
      (∑ v : InfinitePlace K, (v.mult : ℝ) * (Real.log (v (x * y)) * Real.log (v z)))
        = (∑ v : InfinitePlace K, (v.mult : ℝ) * (Real.log (v x) * Real.log (v z)))
          + ∑ v : InfinitePlace K, (v.mult : ℝ) * (Real.log (v y) * Real.log (v z)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [deningerInfinitePlace_log_mul hx hy v]
    ring
  have hfinsum :
      (∑ᶠ w : FinitePlace K,
          Real.log (w (x * y)) * Real.log (w z) / (deningerPlaceDegree w : ℝ))
        = (∑ᶠ w : FinitePlace K,
            Real.log (w x) * Real.log (w z) / (deningerPlaceDegree w : ℝ))
          + ∑ᶠ w : FinitePlace K,
            Real.log (w y) * Real.log (w z) / (deningerPlaceDegree w : ℝ) := by
    rw [← finsum_add_distrib (deningerInnerSupportFinite hx z) (deningerInnerSupportFinite hy z)]
    refine finsum_congr fun w => ?_
    rw [deningerFinitePlace_log_mul hx hy w]
    ring
  rw [deningerL2Inner, deningerL2Inner, deningerL2Inner, harchsum, hfinsum]
  ring

/-- **The `L²` inner product is additive in the second argument.** -/
theorem deningerL2Inner_mul_right {x y z : K} (hy : y ≠ 0) (hz : z ≠ 0) :
    deningerL2Inner x (y * z) = deningerL2Inner x y + deningerL2Inner x z := by
  rw [deningerL2Inner_comm, deningerL2Inner_mul_left hy hz, deningerL2Inner_comm x y,
    deningerL2Inner_comm x z]

end Additive

end RHTower
