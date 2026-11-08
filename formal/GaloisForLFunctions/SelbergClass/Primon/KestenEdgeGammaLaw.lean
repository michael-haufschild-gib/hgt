import GaloisForLFunctions.SelbergClass.Primon.KestenPowerConcentration
import GaloisForLFunctions.HTGeometry.BetaGammaFactorization
import GaloisForLFunctions.HTGeometry.MethodOfMomentsReal

/-!
# A universal gamma law at the prime spectral edges

Under normalized `x^(2n)` weighting of any prime Hecke law, the rescaled gap
`(n+2)(4-x²)` converges in distribution to `Gamma(3/2, 1/4)`, with rate
parameter `1/4`. Its moments are the exact edge coefficients. Uniform
factorial bounds allow the method of moments on the real line to identify
the limit, despite the expanding support of the rescaled variables.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The rescaled squared-edge gap on the compact Hecke interval. -/
def kestenScaledGap (n : ℕ) (x : Icc (-2 : ℝ) 2) : ℝ := ((n : ℝ) + 2) * (4 - (x : ℝ) ^ 2)

/-- The rescaled gap is a continuous coordinate. -/
theorem continuous_kestenScaledGap (n : ℕ) : Continuous (kestenScaledGap n) := by
  unfold kestenScaledGap
  fun_prop

/-- The rescaled gap takes values on the nonnegative half-line. -/
theorem kestenScaledGap_nonneg (n : ℕ) (x : Icc (-2 : ℝ) 2) : 0 ≤ kestenScaledGap n x :=
  mul_nonneg (by positivity) (kestenInterval_gap_nonneg x)

/-- Distribution of the rescaled gap under the normalized prime power tilt. -/
def kestenScaledGapLaw (p : Nat.Primes) (n : ℕ) : ProbabilityMeasure ℝ :=
  (kestenPowerTilt p n).map (continuous_kestenScaledGap n).measurable.aemeasurable

/-- Every rescaled-gap power is integrable. -/
theorem integrable_kestenScaledGapLaw_pow (p : Nat.Primes) (n k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (kestenScaledGapLaw p n : Measure ℝ) := by
  rw [kestenScaledGapLaw, ProbabilityMeasure.toMeasure_map,
    integrable_map_measure (by fun_prop) (continuous_kestenScaledGap n).measurable.aemeasurable]
  exact ((continuous_kestenScaledGap n).pow k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The rescaled-gap law realizes the rescaled tilted gap moments. -/
theorem integral_kestenScaledGapLaw_pow (p : Nat.Primes) (n k : ℕ) :
    (∫ x : ℝ, x ^ k ∂(kestenScaledGapLaw p n : Measure ℝ)) =
      ((n : ℝ) + 2) ^ k * kestenTiltedGapMoment p n k := by
  rw [kestenScaledGapLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_kestenScaledGap n).measurable.aemeasurable (by fun_prop)]
  simp_rw [kestenScaledGap, mul_pow]
  exact integral_const_mul _ _

private theorem integral_abs_pow_kestenScaledGapLaw (p : Nat.Primes) (n k : ℕ) :
    (∫ x : ℝ, |x| ^ k ∂(kestenScaledGapLaw p n : Measure ℝ)) =
      ∫ x : ℝ, x ^ k ∂(kestenScaledGapLaw p n : Measure ℝ) := by
  rw [kestenScaledGapLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_kestenScaledGap n).measurable.aemeasurable (by fun_prop),
    integral_map (continuous_kestenScaledGap n).measurable.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change |kestenScaledGap n x| ^ k = kestenScaledGap n x ^ k
    rw [abs_of_nonneg (kestenScaledGap_nonneg n x)]

/-- The limiting edge coefficients satisfy a factorial bound. -/
theorem semicircleEdgeCoefficient_le_factorial (k : ℕ) :
    semicircleEdgeCoefficient k ≤ (6 : ℝ) ^ k * (Nat.factorial k : ℝ) := by
  induction k with
  | zero => norm_num [semicircleEdgeCoefficient]
  | succ k ih =>
    have hc : 2 * (2 * (k : ℝ) + 3) ≤ 6 * ((k : ℝ) + 1) := by
      have hk := Nat.cast_nonneg (α := ℝ) k
      linarith only [hk]
    calc
      _ = semicircleEdgeCoefficient k * (2 * (2 * (k : ℝ) + 3)) := by
        unfold semicircleEdgeCoefficient
        rw [Finset.prod_range_succ]
      _ ≤ ((6 : ℝ) ^ k * (Nat.factorial k : ℝ)) * (6 * ((k : ℝ) + 1)) :=
        mul_le_mul ih hc (by positivity) (by positivity)
      _ = _ := by rw [pow_succ, Nat.factorial_succ]; push_cast; ring

/-- The endpoint density ratio is at most six over all primes. -/
theorem kestenEdgeScale_le_six (p : Nat.Primes) : kestenEdgeScale p ≤ 6 := by
  have hp : 2 ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
  have hd : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith only [hp])
  have h := mul_nonneg (show 0 ≤ (p : ℝ) - 2 by linarith only [hp])
    (show 0 ≤ 5 * (p : ℝ) - 3 by linarith only [hp])
  unfold kestenEdgeScale
  apply (div_le_iff₀ hd).mpr
  nlinarith only [h]

private theorem six_mul_edgeCoefficient_le (k : ℕ) :
    6 * semicircleEdgeCoefficient (k + 1) ≤
      (Nat.factorial (k + 1) : ℝ) * (36 : ℝ) ^ (k + 1) := by
  have h6 : (6 : ℝ) ≤ 6 ^ (k + 1) := by
    have h := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 6) (n := k)
    rw [pow_succ]
    nlinarith only [h]
  calc
    _ ≤ 6 * ((6 : ℝ) ^ (k + 1) * (Nat.factorial (k + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (semicircleEdgeCoefficient_le_factorial (k + 1)) (by norm_num)
    _ ≤ (6 : ℝ) ^ (k + 1) * ((6 : ℝ) ^ (k + 1) * (Nat.factorial (k + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = _ := by rw [show (36 : ℝ) = 6 * 6 by norm_num, mul_pow]; ring

/-- All prime rescaled-gap laws obey one factorial moment bound, uniform in both parameters. -/
theorem kestenScaledGapLaw_factorial_bound (p : Nat.Primes) (n : ℕ) :
    HasFactorialMomentBound (kestenScaledGapLaw p n : Measure ℝ) 36 := by
  intro k
  have hi : Integrable (fun x : ℝ => |x| ^ k) (kestenScaledGapLaw p n : Measure ℝ) := by
    simpa only [abs_pow] using (integrable_kestenScaledGapLaw_pow p n k).abs
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_abs_pow_kestenScaledGapLaw, integral_kestenScaledGapLaw_pow]
  cases k with
  | zero => simp [kestenTiltedGapMoment]
  | succ k =>
    calc
      _ ≤ kestenEdgeScale p * semicircleEdgeCoefficient (k + 1) :=
        scaled_kestenTiltedGapMoment_le p n (k + 1)
      _ ≤ 6 * semicircleEdgeCoefficient (k + 1) :=
        mul_le_mul_of_nonneg_right (kestenEdgeScale_le_six p) (semicircleEdgeCoefficient_pos _).le
      _ ≤ _ := six_mul_edgeCoefficient_le k

/-- The universal edge law has gamma shape `3/2` and rate `1/4`. -/
def primonEdgeGammaLaw : ProbabilityMeasure ℝ :=
  ⟨gammaMeasure (3 / 2) (1 / 4), gammaMeasure_isProbability (by norm_num) (by norm_num)⟩

/-- Gamma moments agree exactly with the coefficients exposed by the edge expansion. -/
theorem integral_primonEdgeGammaLaw_pow (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂(primonEdgeGammaLaw : Measure ℝ)) = semicircleEdgeCoefficient k := by
  have hg (j : ℕ) : (∫ x : ℝ, x ^ j ∂(primonEdgeGammaLaw : Measure ℝ)) =
      Real.Gamma ((3 : ℝ) / 2 + j) / (Real.Gamma (3 / 2) * (1 / 4 : ℝ) ^ j) :=
    integral_pow_gammaMeasure (by norm_num) (by norm_num) j
  have hG : Real.Gamma (3 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)).ne'
  induction k with
  | zero => rw [hg]; norm_num [semicircleEdgeCoefficient, hG]
  | succ k ih =>
    have hs : Real.Gamma ((3 : ℝ) / 2 + (k + 1 : ℕ)) =
        ((3 : ℝ) / 2 + k) * Real.Gamma ((3 : ℝ) / 2 + k) := by
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Real.Gamma_add_one (by positivity)]
    rw [hg] at ih ⊢
    have hd : semicircleEdgeCoefficient (k + 1) =
        semicircleEdgeCoefficient k * (2 * (2 * (k : ℝ) + 3)) := by
      unfold semicircleEdgeCoefficient
      rw [Finset.prod_range_succ]
    rw [hs, hd, ← ih, pow_succ]
    field_simp [hG]
    ring

/-- Every power is integrable under the limiting gamma law. -/
theorem integrable_primonEdgeGammaLaw_pow (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (primonEdgeGammaLaw : Measure ℝ) := by
  by_contra h
  have hz := integral_undef h
  rw [integral_primonEdgeGammaLaw_pow] at hz
  exact (semicircleEdgeCoefficient_pos k).ne' hz

/-- The gamma limit obeys the same factorial bound as the rescaled prime laws. -/
theorem primonEdgeGammaLaw_factorial_bound :
    HasFactorialMomentBound (primonEdgeGammaLaw : Measure ℝ) 36 := by
  intro k
  have hi : Integrable (fun x : ℝ => |x| ^ k) (primonEdgeGammaLaw : Measure ℝ) := by
    simpa only [abs_pow] using (integrable_primonEdgeGammaLaw_pow k).abs
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : (∫ x : ℝ, |x| ^ k ∂(primonEdgeGammaLaw : Measure ℝ)) =
      ∫ x : ℝ, x ^ k ∂(primonEdgeGammaLaw : Measure ℝ) := by
    apply integral_congr_ae
    filter_upwards [ae_pos_gammaMeasure (3 / 2) (1 / 4)] with x hx
    rw [abs_of_pos hx]
  rw [he, integral_primonEdgeGammaLaw_pow]
  calc
    _ ≤ (6 : ℝ) ^ k * (Nat.factorial k : ℝ) := semicircleEdgeCoefficient_le_factorial k
    _ ≤ (36 : ℝ) ^ k * (Nat.factorial k : ℝ) := by
      gcongr
      norm_num
    _ = _ := by ring

/-- Every rescaled-gap moment converges to the corresponding gamma moment. -/
theorem tendsto_integral_kestenScaledGapLaw_pow (p : Nat.Primes) (k : ℕ) :
    Tendsto (fun n => ∫ x : ℝ, x ^ k ∂(kestenScaledGapLaw p n : Measure ℝ)) atTop
      (𝓝 (∫ x : ℝ, x ^ k ∂(primonEdgeGammaLaw : Measure ℝ))) := by
  simp_rw [integral_kestenScaledGapLaw_pow, integral_primonEdgeGammaLaw_pow]
  exact tendsto_scaled_kestenTiltedGapMoment p k

/-- The full rescaled spectral-gap distribution converges to `Gamma(3/2, 1/4)`. -/
theorem tendsto_kestenScaledGapLaw (p : Nat.Primes) :
    Tendsto (kestenScaledGapLaw p) atTop (𝓝 primonEdgeGammaLaw) :=
  tendsto_of_tendsto_moments (by norm_num : (0 : ℝ) < 36)
    (kestenScaledGapLaw_factorial_bound p) primonEdgeGammaLaw_factorial_bound
    (tendsto_integral_kestenScaledGapLaw_pow p)

end
end GaloisForLFunctions.SelbergClass.Primon
