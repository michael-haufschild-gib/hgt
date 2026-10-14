import GaloisForLFunctions.RHTower.TwistedArcSingleSignChangeN1

/-!
# (N1) line witnesses from corner positivity and finitely many moment inequalities

Let `g ν` be a signed twisted-blind density on the arc `u ∈ [−½, ½]` which is nonnegative near the
corners, `g ≥ 0` on `|u| ≥ u₁`.  Put `w(u) = √(y_u/2)`, `μ_j = ∫ g w u^{2j} dν`,
`P = ∫_{|u| ≥ u₂} g w dν` for some `u₂ > u₁`, and `Q = B ν(arc)` with `|g| ≤ B`.  Pointwise

  `g w u^{2j} ≥ u₂^{2j} 1_{|u|≥u₂} g w − u₁^{2j} 1_{|u|<u₁} |g|`,

so `μ_j ≥ u₂^{2j} P − u₁^{2j} Q`.  Hence every moment beyond an explicit index `J` with
`u₁^{2J} Q ≤ u₂^{2J} P` is nonnegative, the high moments being controlled by the corners.  Together with
`μ_0 > 0` and the finitely many inequalities `μ_j ≥ 0`, `1 ≤ j < J`, this gives all the hypotheses of
`exists_decayClass_fullLineWitness_of_momentPositive`.
-/

open MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-- The weighted arc density `g(u) √(y_u/2)`. -/
def arcWeightedDensity (g : ArcParam → ℝ) (u : ArcParam) : ℝ :=
  g u * Real.sqrt (modularArcHeight u / 2)

theorem abs_sqrt_arcHeight_half_le_one (u : ArcParam) :
    |Real.sqrt (modularArcHeight u / 2)| ≤ 1 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
  have : modularArcHeight u ≤ 1 := by
    unfold modularArcHeight; rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (u : ℝ)]
  linarith

/-- **Moment lower bound from corner positivity.** -/
theorem moment_ge_corner_sub {ν : Measure ArcParam} [IsFiniteMeasure ν]
    {g : ArcParam → ℝ} (hg : Measurable g) {B : ℝ} (hgB : ∀ u, |g u| ≤ B)
    {u₁ u₂ : ℝ} (hu₁ : 0 ≤ u₁) (hu12 : u₁ ≤ u₂)
    (hcorner : ∀ u : ArcParam, u₁ ≤ |(u : ℝ)| → 0 ≤ g u) (j : ℕ) :
    u₂ ^ (2 * j) * (∫ u, {u : ArcParam | u₂ ≤ |(u : ℝ)|}.indicator (arcWeightedDensity g) u ∂ν) -
        u₁ ^ (2 * j) * (B * ν.real univ) ≤
      ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have hcs : Continuous fun u : ArcParam => Real.sqrt (modularArcHeight u / 2) :=
    Real.continuous_sqrt.comp (continuous_modularArcHeight_param.div_const 2)
  have hmeasS : MeasurableSet {u : ArcParam | u₂ ≤ |(u : ℝ)|} :=
    measurableSet_le measurable_const (continuous_subtype_val.abs.measurable)
  have hIw : Integrable (arcWeightedDensity g) ν :=
    integrable_g_mul_of_bound hg hgB hcs abs_sqrt_arcHeight_half_le_one
  have hI2 : Integrable (fun u => g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)))
      ν := by
    refine integrable_g_mul_of_bound hg hgB (hcs.mul (by fun_prop)) (C := 1) fun u => ?_
    rw [abs_mul]
    have hp : |(u : ℝ) ^ (2 * j)| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_arcParam_lt u).le
    calc |Real.sqrt (modularArcHeight u / 2)| * |(u : ℝ) ^ (2 * j)| ≤ 1 * 1 :=
          mul_le_mul (abs_sqrt_arcHeight_half_le_one u) hp (abs_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hIind : Integrable ({u : ArcParam | u₂ ≤ |(u : ℝ)|}.indicator (arcWeightedDensity g)) ν :=
    hIw.indicator hmeasS
  have hlhs : u₂ ^ (2 * j) * (∫ u, {u : ArcParam | u₂ ≤ |(u : ℝ)|}.indicator
        (arcWeightedDensity g) u ∂ν) - u₁ ^ (2 * j) * (B * ν.real univ) =
      ∫ u, (u₂ ^ (2 * j) * {u : ArcParam | u₂ ≤ |(u : ℝ)|}.indicator (arcWeightedDensity g) u -
        u₁ ^ (2 * j) * B) ∂ν := by
    rw [integral_sub (hIind.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, smul_eq_mul]
    ring
  rw [hlhs]
  refine integral_mono ((hIind.const_mul _).sub (integrable_const _)) hI2 fun u => ?_
  have hsq := Real.sqrt_nonneg (modularArcHeight u / 2)
  have hs1 : Real.sqrt (modularArcHeight u / 2) ≤ 1 :=
    (le_abs_self _).trans (abs_sqrt_arcHeight_half_le_one u)
  have hpow : (u : ℝ) ^ (2 * j) = |(u : ℝ)| ^ (2 * j) := by
    rw [pow_mul, pow_mul, sq_abs]
  show u₂ ^ (2 * j) * {u : ArcParam | u₂ ≤ |(u : ℝ)|}.indicator (arcWeightedDensity g) u -
      u₁ ^ (2 * j) * B ≤ g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j))
  rw [hpow]
  have hu1p : 0 ≤ u₁ ^ (2 * j) * B := mul_nonneg (pow_nonneg hu₁ _) hB0
  by_cases h2 : u₂ ≤ |(u : ℝ)|
  · rw [indicator_of_mem (show u ∈ {u : ArcParam | u₂ ≤ |(u : ℝ)|} from h2)]
    have hg0 : 0 ≤ g u := hcorner u (hu12.trans h2)
    have hle : u₂ ^ (2 * j) ≤ |(u : ℝ)| ^ (2 * j) :=
      pow_le_pow_left₀ (hu₁.trans hu12) h2 _
    unfold arcWeightedDensity
    nlinarith [mul_nonneg hg0 hsq]
  · rw [indicator_of_notMem (show u ∉ {u : ArcParam | u₂ ≤ |(u : ℝ)|} from h2), mul_zero,
      zero_sub]
    by_cases h1 : u₁ ≤ |(u : ℝ)|
    · have hg0 : 0 ≤ g u := hcorner u h1
      have : 0 ≤ g u * (Real.sqrt (modularArcHeight u / 2) * |(u : ℝ)| ^ (2 * j)) :=
        mul_nonneg hg0 (mul_nonneg hsq (pow_nonneg (abs_nonneg _) _))
      linarith
    · rw [not_le] at h1
      have hle : |(u : ℝ)| ^ (2 * j) ≤ u₁ ^ (2 * j) := pow_le_pow_left₀ (abs_nonneg _) h1.le _
      have habs : |g u * (Real.sqrt (modularArcHeight u / 2) * |(u : ℝ)| ^ (2 * j))| ≤
          B * u₁ ^ (2 * j) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hsq,
          abs_of_nonneg (pow_nonneg (abs_nonneg (u : ℝ)) (2 * j))]
        calc |g u| * (Real.sqrt (modularArcHeight u / 2) * |(u : ℝ)| ^ (2 * j))
            ≤ B * (1 * u₁ ^ (2 * j)) :=
              mul_le_mul (hgB u) (mul_le_mul hs1 hle (pow_nonneg (abs_nonneg _) _) zero_le_one)
                (mul_nonneg hsq (pow_nonneg (abs_nonneg _) _)) hB0
          _ = B * u₁ ^ (2 * j) := by ring
      have := neg_abs_le (g u * (Real.sqrt (modularArcHeight u / 2) * |(u : ℝ)| ^ (2 * j)))
      linarith

/-- **Decay-class (N1) line witnesses from corner positivity, positive mass and finitely many moment
inequalities.**  If the twisted-blind density `g ν` is nonnegative on `|u| ≥ u₁`, its weighted mass
is positive, `u₁^{2J} B ν(arc) ≤ u₂^{2J} P` for the corner mass `P` on `|u| ≥ u₂ > u₁`, and the
moments `μ_j` are nonnegative for `1 ≤ j < J`, then a decay-class line witness exists. -/
theorem exists_decayClass_fullLineWitness_of_cornerPositive_finiteMoments
    {ν : Measure ArcParam} [IsFiniteMeasure ν] {g : ArcParam → ℝ} (hg : Measurable g) {B : ℝ}
    (hgB : ∀ u, |g u| ≤ B) (hblind : ∀ n : ℕ, ∫ u, g u * twArcMoment n u ∂ν = 0)
    {u₁ u₂ : ℝ} (hu₁ : 0 ≤ u₁) (hu12 : u₁ < u₂)
    (hcorner : ∀ u : ArcParam, u₁ ≤ |(u : ℝ)| → 0 ≤ g u) {J : ℕ}
    (hJ : u₁ ^ (2 * J) * (B * ν.real univ) ≤
      u₂ ^ (2 * J) * ∫ u, {u : ArcParam | u₂ ≤ |(u : ℝ)|}.indicator (arcWeightedDensity g) u ∂ν)
    (hfin : ∀ j : ℕ, j < J →
      0 ≤ ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν)
    (hmass : 0 < ∫ u, g u * Real.sqrt (modularArcHeight u / 2) ∂ν) :
    ∃ h h' : ℝ → ℝ, (∀ x, HasDerivAt h (h' x) x) ∧ Integrable h ∧ Integrable h' ∧
      (∀ x, h (-x) = h x) ∧ (∀ x, x ≠ 0 → h (1 / x) = |x| * h x) ∧ ∫ x, h x = 0 ∧
      (∃ C, ∀ v, |Real.exp (v / 2) * h (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2))) ∧
      (∀ n : ℕ, ∫ x, h' x * Real.sin (arcFreq (n + 1) * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * h (Real.exp v)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  set P := ∫ u, {u : ArcParam | u₂ ≤ |(u : ℝ)|}.indicator (arcWeightedDensity g) u ∂ν with hP
  have hP0 : 0 ≤ P := by
    refine integral_nonneg fun u => ?_
    by_cases h2 : u₂ ≤ |(u : ℝ)|
    · rw [indicator_of_mem (show u ∈ {u : ArcParam | u₂ ≤ |(u : ℝ)|} from h2)]
      exact mul_nonneg (hcorner u (hu12.le.trans h2)) (Real.sqrt_nonneg _)
    · rw [indicator_of_notMem (show u ∉ {u : ArcParam | u₂ ≤ |(u : ℝ)|} from h2)]
      simp
  have hu2 : 0 < u₂ := lt_of_le_of_lt hu₁ hu12
  refine exists_decayClass_fullLineWitness_of_momentPositive hg hgB hblind (fun j => ?_) hmass
  rcases lt_or_ge j J with hj | hj
  · exact hfin j hj
  · have hlow := moment_ge_corner_sub (ν := ν) hg hgB hu₁ hu12.le hcorner j
    -- `u₁^{2j} Q ≤ u₂^{2j} P` for `j ≥ J`, since the ratio `(u₁/u₂)^{2j}` decreases
    have hratio : u₁ ^ (2 * j) * (B * ν.real univ) ≤ u₂ ^ (2 * j) * P := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
      have hQ0 : 0 ≤ B * ν.real univ := mul_nonneg hB0 measureReal_nonneg
      have e1 : u₁ ^ (2 * (J + k)) = u₁ ^ (2 * J) * u₁ ^ (2 * k) := by rw [mul_add, pow_add]
      have e2 : u₂ ^ (2 * (J + k)) = u₂ ^ (2 * J) * u₂ ^ (2 * k) := by rw [mul_add, pow_add]
      have hk : u₁ ^ (2 * k) ≤ u₂ ^ (2 * k) := pow_le_pow_left₀ hu₁ hu12.le _
      rw [e1, e2]
      calc u₁ ^ (2 * J) * u₁ ^ (2 * k) * (B * ν.real univ)
          = u₁ ^ (2 * k) * (u₁ ^ (2 * J) * (B * ν.real univ)) := by ring
        _ ≤ u₂ ^ (2 * k) * (u₂ ^ (2 * J) * P) :=
            mul_le_mul hk hJ (mul_nonneg (pow_nonneg hu₁ _) hQ0) (pow_nonneg hu2.le _)
        _ = u₂ ^ (2 * J) * u₂ ^ (2 * k) * P := by ring
    linarith

end

end RHTower
