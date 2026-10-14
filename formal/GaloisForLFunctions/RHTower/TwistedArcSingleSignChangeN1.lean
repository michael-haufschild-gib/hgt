import GaloisForLFunctions.RHTower.TwistedArcMomentN1Reduction

/-!
# (N1) line witnesses from a twisted arc density with one sign change

Let `g ν` be a signed twisted-blind density on the arc `u ∈ [−½, ½]` which is nonpositive on a
central band `|u| < u₀` and nonnegative on `|u| ≥ u₀`.  Then every weighted even moment dominates a
positive multiple of the weighted mass:

  `∫ g √(y/2) u^{2j} dν ≥ u₀^{2j} ∫ g √(y/2) dν`,

because `(u^{2j} − u₀^{2j}) g(u) ≥ 0` pointwise.  Hence positivity of the single number
`∫ g √(y/2) dν` already gives all the moment inequalities of
`exists_decayClass_fullLineWitness_of_momentPositive`, and the decay-class (N1) line witness follows.

For the unique twisted-blind arc density this means: if it changes sign at most once on `[0, ½]`
(negative toward the top of the arc, positive toward the corners), (N1) is equivalent to the sign of
its weighted mass.
-/

open MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-- **Moment domination under one sign change.** -/
theorem moment_ge_of_singleSignChange {ν : Measure ArcParam} [IsFiniteMeasure ν]
    {g : ArcParam → ℝ} (hg : Measurable g) {B : ℝ} (hgB : ∀ u, |g u| ≤ B) {u₀ : ℝ} (hu₀ : 0 ≤ u₀)
    (hneg : ∀ u : ArcParam, |(u : ℝ)| < u₀ → g u ≤ 0)
    (hpos : ∀ u : ArcParam, u₀ ≤ |(u : ℝ)| → 0 ≤ g u) (j : ℕ) :
    u₀ ^ (2 * j) * ∫ u, g u * Real.sqrt (modularArcHeight u / 2) ∂ν ≤
      ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν := by
  have hcs : Continuous fun u : ArcParam => Real.sqrt (modularArcHeight u / 2) :=
    Real.continuous_sqrt.comp (continuous_modularArcHeight_param.div_const 2)
  have hs1 : ∀ u : ArcParam, |Real.sqrt (modularArcHeight u / 2)| ≤ 1 := fun u => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
    have : modularArcHeight u ≤ 1 := by
      unfold modularArcHeight; rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (u : ℝ)]
    linarith
  have hI1 : Integrable (fun u => g u * Real.sqrt (modularArcHeight u / 2)) ν :=
    integrable_g_mul_of_bound hg hgB hcs hs1
  have hI2 : Integrable (fun u => g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)))
      ν := by
    refine integrable_g_mul_of_bound hg hgB (hcs.mul (by fun_prop)) (C := 1) fun u => ?_
    rw [abs_mul]
    have hp : |(u : ℝ) ^ (2 * j)| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_arcParam_lt u).le
    calc |Real.sqrt (modularArcHeight u / 2)| * |(u : ℝ) ^ (2 * j)| ≤ 1 * 1 :=
          mul_le_mul (hs1 u) hp (abs_nonneg _) zero_le_one
      _ = 1 := one_mul _
  rw [← integral_const_mul]
  refine integral_mono (hI1.const_mul _) hI2 fun u => ?_
  have hpow : (u : ℝ) ^ (2 * j) = |(u : ℝ)| ^ (2 * j) := by
    rw [pow_mul, pow_mul, sq_abs]
  have hsq := Real.sqrt_nonneg (modularArcHeight u / 2)
  show u₀ ^ (2 * j) * (g u * Real.sqrt (modularArcHeight u / 2)) ≤
    g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j))
  rw [hpow]
  rcases lt_or_ge |(u : ℝ)| u₀ with h | h
  · have hle : |(u : ℝ)| ^ (2 * j) ≤ u₀ ^ (2 * j) := pow_le_pow_left₀ (abs_nonneg _) h.le _
    have := hneg u h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg this hsq]
  · have hle : u₀ ^ (2 * j) ≤ |(u : ℝ)| ^ (2 * j) := pow_le_pow_left₀ hu₀ h _
    have := hpos u h
    nlinarith [mul_nonneg this hsq]

/-- **Decay-class (N1) line witnesses from a twisted-blind arc density with one sign change and
positive weighted mass.** -/
theorem exists_decayClass_fullLineWitness_of_singleSignChange
    {ν : Measure ArcParam} [IsFiniteMeasure ν] {g : ArcParam → ℝ} (hg : Measurable g) {B : ℝ}
    (hgB : ∀ u, |g u| ≤ B) (hblind : ∀ n : ℕ, ∫ u, g u * twArcMoment n u ∂ν = 0)
    {u₀ : ℝ} (hu₀ : 0 ≤ u₀) (hneg : ∀ u : ArcParam, |(u : ℝ)| < u₀ → g u ≤ 0)
    (hpos : ∀ u : ArcParam, u₀ ≤ |(u : ℝ)| → 0 ≤ g u)
    (hmass : 0 < ∫ u, g u * Real.sqrt (modularArcHeight u / 2) ∂ν) :
    ∃ h h' : ℝ → ℝ, (∀ x, HasDerivAt h (h' x) x) ∧ Integrable h ∧ Integrable h' ∧
      (∀ x, h (-x) = h x) ∧ (∀ x, x ≠ 0 → h (1 / x) = |x| * h x) ∧ ∫ x, h x = 0 ∧
      (∃ C, ∀ v, |Real.exp (v / 2) * h (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2))) ∧
      (∀ n : ℕ, ∫ x, h' x * Real.sin (arcFreq (n + 1) * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * h (Real.exp v)) :=
  exists_decayClass_fullLineWitness_of_momentPositive hg hgB hblind
    (fun j => (mul_nonneg (pow_nonneg hu₀ _) hmass.le).trans
      (moment_ge_of_singleSignChange hg hgB hu₀ hneg hpos j)) hmass

end

end RHTower
