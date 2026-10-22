import GaloisForLFunctions.RHTower.Deninger.DeningerHigherMassBound
import GaloisForLFunctions.RHTower.Deninger.DeningerHigherMoment
import GaloisForLFunctions.RHTower.Deninger.DeningerHigherCoefficient
import GaloisForLFunctions.RHTower.Deninger.DeningerAbelMajorant

/-!
# The order-`r` majorant has finite mass

Weighting the Abel majorant by `x^r` and integrating over the ray produces, after the monotone
exchange of sum and integral, the series `∑_i |M(i)| (i^{-(r+1)} - (i+1)^{-(r+1)})/(r+1)` times the
`(r+1)`-st weighted moment of the pullback derivative.  Both factors are finite: the series by the
unconditional Möbius saving, the moment by the two-sided decay of the source.

* `deningerHigherMomentMass` : the `(r+1)`-st weighted moment as an `ℝ≥0∞` integral.
* `deningerHigherMajorant` : the `x^r`-weighted majorant.
* `deningerHigherMajorant_mass_lt_top` : **its total mass over the ray is finite for `r ≥ 1`.**
-/

namespace RHTower

open MeasureTheory SchwartzMap ENNReal

noncomputable section

/-- The `(r+1)`-st weighted moment, as an `ℝ≥0∞`-valued integral. -/
def deningerHigherMomentMass (h : 𝓢(ℝ, ℂ)) (r : ℕ) : ℝ≥0∞ :=
  ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (r + 1) * ‖deningerLogPullDeriv h u‖)

theorem deningerHigherMomentMass_lt_top {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (r : ℕ) :
    deningerHigherMomentMass h r < ⊤ := by
  have hint := deningerHigherMoment_integrable hh r
  have hfin := hint.2
  rw [hasFiniteIntegral_iff_enorm] at hfin
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hu
  rw [deningerHigherMomentFun, ← ofReal_norm,
    Real.norm_of_nonneg (mul_nonneg (pow_nonneg hu0.le _) (norm_nonneg _))]

/-- The `x^r`-weighted majorant of the Abel series. -/
def deningerHigherMajorant (h : 𝓢(ℝ, ℂ)) (r : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (x ^ r) * deningerAbelMajorant h x

/-- The weighted Abel difference is a measurable function of the dilation. -/
theorem deningerAbelDifferencePow_measurable (h : 𝓢(ℝ, ℂ)) (i r : ℕ) :
    Measurable fun x : ℝ => ENNReal.ofReal (x ^ r) *
      ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ := by
  have h1 : Measurable fun x : ℝ => ENNReal.ofReal (x ^ r) :=
    (measurable_id.pow_const r).ennreal_ofReal
  exact h1.mul (deningerAbelDifference_measurable h i)

/-- The order-`r` Abel coefficients, in the normalisation the mass bound produces. -/
theorem deningerHigherCoefficientScaled_summable {r : ℕ} (hr : 1 ≤ r) :
    Summable fun i : ℕ => |Sieve.mertensM i| *
      ((1 / ((r : ℝ) + 1)) *
        (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))) := by
  have hsum := (deningerHigherCoefficient_summable hr).mul_left (1 / ((r : ℝ) + 1))
  refine hsum.congr fun i => ?_
  ring

/-- **The order-`r` majorant has finite total mass over the ray**, for every `r ≥ 1`. -/
theorem deningerHigherMajorant_mass_lt_top {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    {r : ℕ} (hr : 1 ≤ r) :
    (∫⁻ x in Set.Ioi (0 : ℝ), deningerHigherMajorant h r x) < ⊤ := by
  have hswap : (∫⁻ x in Set.Ioi (0 : ℝ), deningerHigherMajorant h r x)
      = ∑' i : ℕ, ENNReal.ofReal |Sieve.mertensM i| *
        ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) *
          ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ := by
    have hpt : ∀ x : ℝ, deningerHigherMajorant h r x
        = ∑' i : ℕ, ENNReal.ofReal |Sieve.mertensM i| *
          (ENNReal.ofReal (x ^ r) *
            ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ) := by
      intro x
      rw [deningerHigherMajorant, deningerAbelMajorant, ← ENNReal.tsum_mul_left]
      exact tsum_congr fun i => by ring
    rw [lintegral_congr hpt,
      lintegral_tsum fun i =>
        ((deningerAbelDifferencePow_measurable h i r).const_mul _).aemeasurable]
    exact tsum_congr fun i => lintegral_const_mul' _ _ ofReal_ne_top
  rw [hswap]
  have hterm : ∀ i : ℕ, ENNReal.ofReal |Sieve.mertensM i| *
      (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) *
        ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ)
        ≤ ENNReal.ofReal (|Sieve.mertensM i| *
            ((1 / ((r : ℝ) + 1)) *
              (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1)))) *
          deningerHigherMomentMass h r := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have hzero : Sieve.mertensM 0 = 0 := by
        rw [Sieve.mertensM]
        simp
      rw [hzero]
      simp
    · have hstep : ENNReal.ofReal |Sieve.mertensM i| *
          (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) *
            ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ)
          ≤ ENNReal.ofReal |Sieve.mertensM i| *
            (ENNReal.ofReal ((1 / ((r : ℝ) + 1)) *
                (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))) *
              deningerHigherMomentMass h r) := by
        rw [deningerHigherMomentMass]
        gcongr
        exact deningerAbelDifferencePow_mass_le h hi r
      refine le_trans hstep (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_lt_top ?_ (deningerHigherMomentMass_lt_top hh r)
  have hnn : ∀ i : ℕ, 0 ≤ |Sieve.mertensM i| *
      ((1 / ((r : ℝ) + 1)) *
        (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))) := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have hz : Sieve.mertensM 0 = 0 := by
        rw [Sieve.mertensM]
        simp
      simp [hz]
    · exact mul_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (deningerHigherBracket_le hi hr).1)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn (deningerHigherCoefficientScaled_summable hr)]
  exact ofReal_lt_top

end

end RHTower
