import GaloisForLFunctions.HTGeometry.MultipleSineOrderOneSourceDA
import GaloisForLFunctions.HTGeometry.MultipleSineLadderRationalDefect

/-!
# The order-one source, exactly, and the periodicity of the period cotangent

Two exact identities the multiple-sine normalization needs.

* The order-one frame source **is** the period cotangent plus an explicit rational function:

  ```text
  L_{i} = (π/ω_i) cot(π z/ω_i) + (2z - ω_i)/(z (ω_i - z)).
  ```

* The period cotangent is invariant under its own period, because both the sine and the scaled
  cosine of the period change sign under it.  This is the order-one case `(T_i - 1) L_{i} = 0` of
  the multiple-sine difference equation, and it is what makes the two-direction cocycle identity
  collapse to a rational one.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-! ### The order-one source, exactly -/

/-- The rational correction between the order-one source and the period cotangent. -/
def orderOneCorrection (w : ℂ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (orderOneNumerator w) /
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (orderOneDenominator w)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **The order-one frame source is the period cotangent plus an explicit rational function.** -/
theorem frameSourceMero_singleton_eq (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (i : ι)
    (hS : ({i} : Finset ι).Nonempty) :
    frameSourceMero ω hω ({i} : Finset ι) hS
      = periodCotMero (ω i) + ratMero (orderOneCorrection (ω i)) := by
  have hwim : 0 < (ω i).im := hω i
  have hw0 : ω i ≠ 0 := by
    intro h
    rw [h] at hwim
    simp at hwim
  have hsub := eq_ratfuncToMero_of_hasPuncturedMeromorphicRep_ratio
    (orderOneDenominator_ne_zero hw0)
    (hasPuncturedMeromorphicRep_frameSourceMero_singleton_sub ω hω i hS)
  rw [orderOneCorrection]
  linear_combination hsub

/-! ### The period cotangent is invariant under its period -/

theorem cot_add_pi' (u : ℂ) : Complex.cot (u + (Real.pi : ℂ)) = Complex.cot u := by
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, Complex.cos_add_pi,
    Complex.sin_add_pi, neg_div_neg_eq]

/-- **The period cotangent is invariant under its period.**  This is `(T_i - 1) L_{i} = 0`. -/
theorem addTranslationMeroEquiv_periodCotMero {w : ℂ} (hw : w ≠ 0) :
    addTranslationMeroEquiv w (periodCotMero w) = periodCotMero w := by
  have hrep := hasPuncturedMeromorphicRep_periodCotMero hw
  have hdiff := (hrep.translate w).sub hrep
  have hzero : HasPuncturedMeromorphicRep
      (addTranslationMeroEquiv w (periodCotMero w) - periodCotMero w)
      (fun z => (0 : Polynomial ℂ).eval z / (1 : Polynomial ℂ).eval z) := by
    refine hdiff.congr_fun fun z₀ => Filter.Eventually.of_forall fun z => ?_
    have harg : (Real.pi : ℂ) * (z + w) / w = (Real.pi : ℂ) * z / w + (Real.pi : ℂ) := by
      field_simp
    show ((Real.pi : ℂ) / w) * Complex.cot ((Real.pi : ℂ) * (z + w) / w)
        - ((Real.pi : ℂ) / w) * Complex.cot ((Real.pi : ℂ) * z / w)
      = (0 : Polynomial ℂ).eval z / (1 : Polynomial ℂ).eval z
    rw [harg, cot_add_pi']
    simp
  have heq := eq_ratfuncToMero_of_hasPuncturedMeromorphicRep_ratio one_ne_zero hzero
  rw [map_zero, map_one, zero_div, map_zero] at heq
  exact sub_eq_zero.mp heq

end

end GaloisForLFunctions.HTGeometry
