import GaloisForLFunctions.RHTower.Deninger.DeningerAbelMassBound
import GaloisForLFunctions.RHTower.Deninger.DeningerAbelCoefficient

/-!
# The majorant of the Abel series has finite mass

Summing the per-difference mass bound against the summatory function gives a majorant for the
canonical Möbius preimage whose total mass over the ray is finite: the coefficients are
`|M(i)|/(i(i+1))`, which the unconditional saving already makes summable, and the common factor is
the first weighted moment of the pullback derivative.

Monotone convergence exchanges the sum with the integral, with no integrability side condition —
everything happens in `ℝ≥0∞`.

* `deningerAbelMajorant` : the majorant series.
* `deningerAbelMajorant_mass_lt_top` : **its total mass over the ray is finite.**
-/

namespace RHTower

open MeasureTheory SchwartzMap ENNReal

noncomputable section

/-- The first weighted moment, as an `ℝ≥0∞`-valued integral. -/
def deningerWeightedMomentMass (h : 𝓢(ℝ, ℂ)) : ℝ≥0∞ :=
  ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u * ‖deningerLogPullDeriv h u‖)

theorem deningerWeightedMomentMass_lt_top {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    deningerWeightedMomentMass h < ⊤ := by
  have hint := deningerWeightedMoment_integrable hh
  have hfin := hint.2
  rw [hasFiniteIntegral_iff_enorm] at hfin
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hu
  rw [deningerWeightedMomentFun, ← ofReal_norm,
    Real.norm_of_nonneg (mul_nonneg hu0.le (norm_nonneg _))]

/-- The majorant of the Abel series. -/
def deningerAbelMajorant (h : 𝓢(ℝ, ℂ)) (x : ℝ) : ℝ≥0∞ :=
  ∑' i : ℕ, ENNReal.ofReal |Sieve.mertensM i| *
    ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ

/-- The Abel difference is a measurable function of the dilation. -/
theorem deningerAbelDifference_measurable (h : 𝓢(ℝ, ℂ)) (i : ℕ) :
    Measurable fun x : ℝ =>
      ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ := by
  have hpull : Measurable (deningerLogPull h) :=
    (h.continuous.measurable).comp Real.measurable_log
  exact ((hpull.comp (measurable_id.const_mul _)).sub
    (hpull.comp (measurable_id.const_mul _))).enorm

/-- **The majorant has finite total mass over the ray.** -/
theorem deningerAbelMajorant_mass_lt_top {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    (∫⁻ x in Set.Ioi (0 : ℝ), deningerAbelMajorant h x) < ⊤ := by
  have hswap : (∫⁻ x in Set.Ioi (0 : ℝ), deningerAbelMajorant h x)
      = ∑' i : ℕ, ENNReal.ofReal |Sieve.mertensM i| *
        ∫⁻ x in Set.Ioi (0 : ℝ),
          ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ := by
    simp only [deningerAbelMajorant]
    rw [lintegral_tsum fun i => ((deningerAbelDifference_measurable h i).const_mul _).aemeasurable]
    exact tsum_congr fun i => lintegral_const_mul' _ _ ofReal_ne_top
  rw [hswap]
  have hterm : ∀ i : ℕ, ENNReal.ofReal |Sieve.mertensM i| *
      (∫⁻ x in Set.Ioi (0 : ℝ),
        ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ)
        ≤ ENNReal.ofReal (|Sieve.mertensM i| / ((i : ℝ) * ((i : ℝ) + 1))) *
          deningerWeightedMomentMass h := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have hzero : Sieve.mertensM 0 = 0 := by
        rw [Sieve.mertensM]
        simp
      rw [hzero]
      simp
    · have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
      have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
      have hstep : ENNReal.ofReal |Sieve.mertensM i| *
          (∫⁻ x in Set.Ioi (0 : ℝ),
            ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ)
          ≤ ENNReal.ofReal |Sieve.mertensM i| *
            (ENNReal.ofReal (1 / ((i : ℝ) * ((i : ℝ) + 1))) *
              deningerWeightedMomentMass h) := by
        rw [deningerWeightedMomentMass]
        gcongr
        exact deningerAbelDifference_mass_le h hi
      refine le_trans hstep (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
      have harg : |Sieve.mertensM i| * (1 / ((i : ℝ) * ((i : ℝ) + 1)))
          = |Sieve.mertensM i| / ((i : ℝ) * ((i : ℝ) + 1)) := by ring
      rw [harg]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_lt_top ?_ (deningerWeightedMomentMass_lt_top hh)
  have hsum := deningerAbelCoefficient_summable
  have hnn : ∀ i : ℕ, 0 ≤ |Sieve.mertensM i| / ((i : ℝ) * ((i : ℝ) + 1)) := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
      positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  exact ofReal_lt_top

end

end RHTower
