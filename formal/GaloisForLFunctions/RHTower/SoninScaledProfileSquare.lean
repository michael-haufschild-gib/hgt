import GaloisForLFunctions.RHTower.SoninScaledPacketBandEnergy

/-!
# The squared profile

The packet's energy is an integral against the *square* of the annulus profile, so the estimates
that governed the profile have to be repeated for its square.  They can be: once the half-width is
smaller than the annulus radius the two lobes are disjoint, so the squared profile is again a sum of
two translated dilates of one fixed reference — the square of the reference bump.

That reference square is smooth with compact support and has positive mass, so it carries the same
decay and mass statements the reference bump did, and the squared profile's mass is again the
half-width times a constant, free of the annulus centre.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform ContDiff

/-- The square of the reference profile. -/
def soninUnitBumpSq : ℝ → ℝ := fun y => soninUnitBumpData y ^ (2 : ℕ)

/-- The square of the reference profile, complexified. -/
def soninUnitBumpSqC : ℝ → ℂ := fun y => (soninUnitBumpSq y : ℂ)

theorem soninUnitBumpSq_nonneg (y : ℝ) : 0 ≤ soninUnitBumpSq y := by
  rw [soninUnitBumpSq]
  positivity

theorem soninUnitBumpSq_eq_zero_of_one_le {y : ℝ} (hy : 1 ≤ |y|) : soninUnitBumpSq y = 0 := by
  rw [soninUnitBumpSq, soninUnitBumpData_eq_zero_of_one_le hy]
  ring

theorem continuous_soninUnitBumpSq : Continuous soninUnitBumpSq :=
  soninUnitBumpData.continuous.pow 2

theorem contDiff_soninUnitBumpSqC : ContDiff ℝ ∞ soninUnitBumpSqC :=
  Complex.ofRealCLM.contDiff.comp (soninUnitBumpData.contDiff.pow 2)

theorem hasCompactSupport_soninUnitBumpSqC : HasCompactSupport soninUnitBumpSqC := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro y hy
  have hne : soninUnitBumpSq y ≠ 0 := by
    intro hzero
    exact hy (by simp [soninUnitBumpSqC, hzero])
  have hball : |y| < 1 := by
    by_contra hcon
    push Not at hcon
    exact hne (soninUnitBumpSq_eq_zero_of_one_le hcon)
  rw [Set.mem_Icc]
  rcases abs_lt.mp hball with ⟨h1, h2⟩
  constructor <;> linarith

theorem integrable_soninUnitBumpSq : Integrable soninUnitBumpSq := by
  refine continuous_soninUnitBumpSq.integrable_of_hasCompactSupport ?_
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro y hy
  have hball : |y| < 1 := by
    by_contra hcon
    push Not at hcon
    exact hy (soninUnitBumpSq_eq_zero_of_one_le hcon)
  rw [Set.mem_Icc]
  rcases abs_lt.mp hball with ⟨h1, h2⟩
  constructor <;> linarith

/-- The reference square has positive mass. -/
theorem integral_soninUnitBumpSq_pos : 0 < ∫ y : ℝ, soninUnitBumpSq y := by
  rw [integral_pos_iff_support_of_nonneg soninUnitBumpSq_nonneg integrable_soninUnitBumpSq]
  have hopen : IsOpen (Function.support soninUnitBumpSq) :=
    isOpen_ne.preimage continuous_soninUnitBumpSq
  have hne : (0 : ℝ) ∈ Function.support soninUnitBumpSq := by
    have hone : soninUnitBumpData 0 = 1 := by
      refine soninUnitBumpData.one_of_mem_closedBall ?_
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_zero]
      exact le_of_lt soninUnitBumpData.rIn_pos
    have : soninUnitBumpSq 0 = 1 := by
      rw [soninUnitBumpSq, hone]
      norm_num
    simp only [Function.mem_support, this]
    exact one_ne_zero
  exact hopen.measure_pos volume ⟨_, hne⟩

/-- A lobe's square is a translated dilate of the reference square. -/
theorem soninOneSidedBump_sq (m δ : ℝ) (x : ℝ) :
    soninOneSidedBump m δ x ^ (2 : ℕ) = soninUnitBumpSq ((x - m) / δ) := rfl

/-- **The lobes are disjoint** once the half-width is below the annulus radius. -/
theorem soninOneSidedBump_mul_neg_eq_zero (m δ : ℝ) (hδ : 0 < δ) (hm : δ < m) (x : ℝ) :
    soninOneSidedBump m δ x * soninOneSidedBump m δ (-x) = 0 := by
  by_cases hx : soninOneSidedBump m δ x = 0
  · rw [hx, zero_mul]
  have hxb : |(x - m) / δ| < 1 := by
    by_contra hcon
    push Not at hcon
    exact hx (soninUnitBumpData_eq_zero_of_one_le hcon)
  rw [abs_div, abs_of_pos hδ, div_lt_one hδ] at hxb
  have hother : soninOneSidedBump m δ (-x) = 0 := by
    refine soninUnitBumpData_eq_zero_of_one_le ?_
    rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ, one_mul]
    have habs : δ ≤ |(-x - m)| := by
      rcases le_total 0 (-x - m) with h | h
      · rw [abs_of_nonneg h]
        rcases abs_lt.mp hxb with ⟨h1, h2⟩
        linarith
      · rw [abs_of_nonpos h]
        rcases abs_lt.mp hxb with ⟨h1, h2⟩
        linarith
    exact habs
  rw [hother, mul_zero]

/-- **The squared profile splits into two squared lobes.** -/
theorem soninScaledAnnulusBump_sq (m δ : ℝ) (hδ : 0 < δ) (hm : δ < m) (x : ℝ) :
    soninScaledAnnulusBump m δ x ^ (2 : ℕ) =
      soninOneSidedBump m δ x ^ (2 : ℕ) + soninOneSidedBump m δ (-x) ^ (2 : ℕ) := by
  have hcross := soninOneSidedBump_mul_neg_eq_zero m δ hδ hm x
  rw [soninScaledAnnulusBump_eq_oneSided_add m δ x]
  nlinarith [hcross]

/-- The squared lobe is integrable. -/
theorem integrable_soninOneSidedBump_sq (m δ : ℝ) (hδ : 0 < δ) :
    Integrable fun x : ℝ => soninOneSidedBump m δ x ^ (2 : ℕ) := by
  have hc : Continuous fun x : ℝ => soninOneSidedBump m δ x ^ (2 : ℕ) :=
    (soninUnitBumpData.continuous.comp ((continuous_id.sub continuous_const).div_const δ)).pow 2
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := m - δ) (b := m + δ)) ?_
  intro x hx
  have hbump : soninUnitBumpData ((x - m) / δ) ≠ 0 := by
    intro hzero
    exact hx (by simp [soninOneSidedBump, hzero])
  have hball : |(x - m) / δ| < 1 := by
    by_contra hcon
    push Not at hcon
    exact hbump (soninUnitBumpData_eq_zero_of_one_le hcon)
  rw [abs_div, abs_of_pos hδ, div_lt_one hδ] at hball
  rw [Set.mem_Icc]
  rcases abs_lt.mp hball with ⟨h1, h2⟩
  constructor <;> linarith

/-- The squared lobe carries the half-width times the reference square's mass. -/
theorem integral_soninOneSidedBump_sq (m δ : ℝ) (hδ : 0 < δ) :
    ∫ x : ℝ, soninOneSidedBump m δ x ^ (2 : ℕ) = δ * ∫ y : ℝ, soninUnitBumpSq y := by
  have hshift : ∫ x : ℝ, soninUnitBumpSq ((x + -m) / δ) = ∫ x : ℝ, soninUnitBumpSq (x / δ) :=
    MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun u : ℝ => soninUnitBumpSq (u / δ)) (-m)
  have hpoint : ∀ x : ℝ, soninOneSidedBump m δ x ^ (2 : ℕ) = soninUnitBumpSq ((x + -m) / δ) := by
    intro x
    rw [soninOneSidedBump_sq m δ x, sub_eq_add_neg]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), hshift,
    MeasureTheory.Measure.integral_comp_div soninUnitBumpSq δ, abs_of_pos hδ, smul_eq_mul]

/-- **The squared profile's mass is centre free.** -/
theorem integral_soninScaledAnnulusBump_sq_eq (m δ : ℝ) (hδ : 0 < δ) (hm : δ < m) :
    ∫ x : ℝ, soninScaledAnnulusBump m δ x ^ (2 : ℕ) = 2 * δ * ∫ y : ℝ, soninUnitBumpSq y := by
  have hlobe := integrable_soninOneSidedBump_sq m δ hδ
  have hrefl : ∫ x : ℝ, soninOneSidedBump m δ (-x) ^ (2 : ℕ) =
      ∫ x : ℝ, soninOneSidedBump m δ x ^ (2 : ℕ) :=
    MeasureTheory.integral_neg_eq_self (fun x : ℝ => soninOneSidedBump m δ x ^ (2 : ℕ)) volume
  rw [integral_congr_ae (Filter.Eventually.of_forall (soninScaledAnnulusBump_sq m δ hδ hm)),
    integral_add hlobe hlobe.comp_neg, hrefl, integral_soninOneSidedBump_sq m δ hδ]
  ring

end RHTower
