import GaloisForLFunctions.RHTower.RoutePLatePrimeIncrementLimits
import GaloisForLFunctions.RHTower.RoutePLatePrimeIncrementVariation

/-!
# Admission of the literal reciprocal's continuous and jump coefficients

The actual inverse-square asymptotic separates both one-sided values
from zero. The reciprocal jump is identified from the proved left limit,
and every positively damped continuous and atomic coefficient is admitted.
The finite-window reciprocal FTC remains a separate identity.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower

/-- The actual reciprocal change at a removal, once both values are nonzero. -/
def routePLatePrimeReciprocalJump (p : ℕ) : ℝ :=
  (criticalAbelLogProfile (Real.log p) / p) /
    (routePLatePrimeIncrement (2 * Real.log p) *
      (routePLatePrimeIncrement (2 * Real.log p) + criticalAbelLogProfile (Real.log p) / p))

private theorem eventually_scaled_negative_both :
    ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
      (∀ t, T < t → t ^ 2 * routePLatePrimeIncrement t ≤ -c) ∧
      (∀ p : ℕ, p.Prime → T < 2 * Real.log p →
        (2 * Real.log p) ^ 2 * (routePLatePrimeIncrement (2 * Real.log p) +
          criticalAbelLogProfile (Real.log p) / p) ≤ -c) := by
  have hD := divisorHarmonicBoundary_pos
  have hgap : -(divisorHarmonicBoundary / 3) < -(divisorHarmonicBoundary / 6) := by
    linarith
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    (tendsto_routePLatePrimeIncrement_scaled.eventually (eventually_lt_nhds hgap))
  refine ⟨max S 1, divisorHarmonicBoundary / 6, by positivity, by positivity, ?_, ?_⟩
  · intro t ht
    exact (hS t ((le_max_left S 1).trans ht.le)).le
  · intro p hp ht
    have hlim : Tendsto (fun t : ℝ => t ^ 2 * routePLatePrimeIncrement t)
        (𝓝[Iio (2 * Real.log p)] (2 * Real.log p))
        (𝓝 ((2 * Real.log p) ^ 2 * (routePLatePrimeIncrement (2 * Real.log p) +
          criticalAbelLogProfile (Real.log p) / p))) :=
      (((continuous_id.pow 2).tendsto _).mono_left nhdsWithin_le_nhds).mul
        (tendsto_routePLatePrimeIncrement_left_prime hp)
    apply le_of_tendsto hlim
    filter_upwards [(eventually_gt_nhds ((le_max_left S 1).trans_lt ht)).filter_mono
      nhdsWithin_le_nhds] with t ht'
    exact (hS t ht'.le).le

private theorem reciprocal_bound {c t y : ℝ} (hc : 0 < c)
    (h : t ^ 2 * y ≤ -c) : y ≠ 0 ∧ |1 / y| ≤ t ^ 2 / c := by
  have hy : y < 0 := by
    by_contra hn
    have hprod := mul_nonneg (sq_nonneg t) (le_of_not_gt hn)
    linarith
  refine ⟨hy.ne, ?_⟩
  rw [abs_div, abs_one, abs_of_neg hy, div_le_iff₀ (neg_pos.mpr hy),
    div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith only [h]

/-- One common late ray controls both values at every removal; no denominator
condition is assumed for the native increment. -/
theorem exists_routePLatePrimeReciprocalBounds :
    ∃ T C : ℝ, 0 < T ∧ 0 < C ∧
      (∀ t, T < t → routePLatePrimeIncrement t ≠ 0 ∧
        |1 / routePLatePrimeIncrement t| ≤ C * t ^ 2) ∧
      (∀ p : ℕ, p.Prime → T < 2 * Real.log p →
        routePLatePrimeIncrement (2 * Real.log p) + criticalAbelLogProfile (Real.log p) / p ≠ 0 ∧
        |1 / (routePLatePrimeIncrement (2 * Real.log p) +
          criticalAbelLogProfile (Real.log p) / p)| ≤ C * (2 * Real.log p) ^ 2) := by
  obtain ⟨T, c, hT, hc, hr, hl⟩ := eventually_scaled_negative_both
  refine ⟨T, 1 / c, hT, by positivity, ?_, ?_⟩
  · intro t ht
    simpa only [one_div_mul_eq_div] using reciprocal_bound hc (hr t ht)
  · intro p hp ht
    simpa only [one_div_mul_eq_div] using reciprocal_bound hc (hl p hp ht)

/-- The stated atom is the actual change of the reciprocal across each late
physical removal, including the literal left limit. -/
theorem exists_routePLatePrimeReciprocalJumpLaw :
    ∃ T : ℝ, 0 < T ∧ ∀ p : ℕ, p.Prime → T < 2 * Real.log p →
      1 / routePLatePrimeIncrement (2 * Real.log p) -
        Function.leftLim (fun t => 1 / routePLatePrimeIncrement t) (2 * Real.log p) =
        routePLatePrimeReciprocalJump p := by
  obtain ⟨T, C, hT, _, hr, hl⟩ := exists_routePLatePrimeReciprocalBounds
  refine ⟨T, hT, ?_⟩
  intro p hp ht
  have hleft : Tendsto (fun t => 1 / routePLatePrimeIncrement t)
      (𝓝[Iio (2 * Real.log p)] (2 * Real.log p))
      (𝓝 (1 / (routePLatePrimeIncrement (2 * Real.log p) +
        criticalAbelLogProfile (Real.log p) / p))) := by
    simpa only [one_div] using
      (tendsto_routePLatePrimeIncrement_left_prime hp).inv₀ (hl p hp ht).1
  rw [leftLim_eq_of_tendsto hleft, routePLatePrimeReciprocalJump]
  field_simp [(hr _ ht).1, (hl p hp ht).1]
  ring

private theorem reciprocal_jump_norm_le {T C : ℝ} (hC : 0 < C)
    (hr : ∀ t, T < t → routePLatePrimeIncrement t ≠ 0 ∧
      |1 / routePLatePrimeIncrement t| ≤ C * t ^ 2)
    (hl : ∀ p : ℕ, p.Prime → T < 2 * Real.log p →
      routePLatePrimeIncrement (2 * Real.log p) + criticalAbelLogProfile (Real.log p) / p ≠ 0 ∧
      |1 / (routePLatePrimeIncrement (2 * Real.log p) +
        criticalAbelLogProfile (Real.log p) / p)| ≤ C * (2 * Real.log p) ^ 2)
    {p : ℕ} (hp : p.Prime) (ht : T < 2 * Real.log p) :
    |routePLatePrimeReciprocalJump p| ≤
      C ^ 2 * (2 * Real.log p) ^ 4 * (|criticalAbelLogProfile (Real.log p)| / p) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  calc
    _ = (|criticalAbelLogProfile (Real.log p)| / p) *
        |1 / routePLatePrimeIncrement (2 * Real.log p)| *
        |1 / (routePLatePrimeIncrement (2 * Real.log p) +
          criticalAbelLogProfile (Real.log p) / p)| := by
      rw [routePLatePrimeReciprocalJump, abs_div, abs_mul, abs_div,
        abs_of_pos hp0, abs_div, abs_one, abs_div, abs_one]
      ring
    _ ≤ (|criticalAbelLogProfile (Real.log p)| / p) *
        (C * (2 * Real.log p) ^ 2) * (C * (2 * Real.log p) ^ 2) := by
      gcongr
      · exact (hr _ ht).2
      · exact (hl p hp ht).2
    _ = _ := by ring

/-- Both reciprocal coefficients are admitted on one native late ray for
every positive damping. This discharges measure admission, not the FTC. -/
theorem exists_routePLatePrimeReciprocalAdmission :
    ∃ T : ℝ, 0 < T ∧ ∀ η : ℝ, 0 < η →
      IntegrableOn (fun t => Real.exp (-η * t) * routePLatePrimeVelocity t /
        routePLatePrimeIncrement t ^ 2) (Ioi T) ∧
      Summable (fun p : Nat.Primes => if T < 2 * Real.log (p : ℕ) then
        Real.exp (-η * (2 * Real.log (p : ℕ))) * |routePLatePrimeReciprocalJump p| else 0) := by
  obtain ⟨T, C, hT, hC, hr, hl⟩ := exists_routePLatePrimeReciprocalBounds
  refine ⟨T, hT, ?_⟩
  intro η hη
  constructor
  · have hi := ((integrableOn_exp_mul_pow_mul_routePLatePrimeVelocity 4 hη).mono_set
      (Ioi_subset_Ioi hT.le)).norm.const_mul (C ^ 2)
    apply hi.mono'
    · exact ((((show Measurable (fun t : ℝ => Real.exp (-η * t)) by fun_prop).mul
        measurable_routePLatePrimeVelocity).div
          (measurable_routePLatePrimeIncrement.pow_const 2)).aestronglyMeasurable).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := hT.le.trans ht.le
      have hb : |1 / routePLatePrimeIncrement t| ^ 2 ≤ (C * t ^ 2) ^ 2 := by
        gcongr
        exact (hr t ht).2
      calc
        _ = Real.exp (-η * t) * |routePLatePrimeVelocity t| *
            |1 / routePLatePrimeIncrement t| ^ 2 := by
          rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
            abs_pow, abs_div, abs_one]
          ring
        _ ≤ Real.exp (-η * t) * |routePLatePrimeVelocity t| * (C * t ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = C ^ 2 * ‖Real.exp (-η * t) * t ^ 4 * routePLatePrimeVelocity t‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht0 4), Real.norm_eq_abs]
          ring
  · apply ((summable_exp_mul_pow_mul_routePLatePrimeRemovalMass 4 hη).mul_left
      (C ^ 2)).of_norm_bounded
    intro p
    have hp0 : 0 < ((p : ℕ) : ℝ) := by exact_mod_cast p.property.pos
    have hl0 : 0 ≤ Real.log ((p : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)
    by_cases ht : T < 2 * Real.log (p : ℕ)
    · rw [if_pos ht, Real.norm_of_nonneg (by positivity)]
      have hb := mul_le_mul_of_nonneg_left
        (reciprocal_jump_norm_le hC hr hl p.property ht)
        (Real.exp_pos (-η * (2 * Real.log (p : ℕ)))).le
      calc
        _ ≤ Real.exp (-η * (2 * Real.log (p : ℕ))) *
            (C ^ 2 * (2 * Real.log (p : ℕ)) ^ 4 *
              (|criticalAbelLogProfile (Real.log (p : ℕ))| / (p : ℕ))) := hb
        _ = _ := by ring
    · rw [if_neg ht, norm_zero]
      positivity

end RHTower
