import GaloisForLFunctions.RHTower.SelbergClass.Basic

/-!
# Equivalent exponential-growth forms of finite order

For an entire function, a global exponential-power bound and such a bound outside a sufficiently
large disk are equivalent.  This verifies that `EntireFiniteOrder.growth` is not stronger than the
usual large-radius formulation: compactness of the omitted disk only changes the leading constant.
-/

open Metric Set

namespace RHTower

/-- Global exponential-power growth, the normalization stored by `EntireFiniteOrder`. -/
def HasGlobalExponentialPowerGrowth (f : ℂ → ℂ) : Prop :=
  ∃ A B ρ : ℝ, 0 < A ∧ 0 < B ∧ 0 ≤ ρ ∧
    ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)

/-- Exponential-power growth only outside a nonnegative-radius disk. -/
def HasExponentialPowerGrowthOutside (f : ℂ → ℂ) : Prop :=
  ∃ A B ρ R : ℝ, 0 < A ∧ 0 < B ∧ 0 ≤ ρ ∧ 0 ≤ R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)

/-- For an entire function, global and outside-a-disk exponential-power bounds are equivalent. -/
theorem hasGlobalExponentialPowerGrowth_iff_outside
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ) :
    HasGlobalExponentialPowerGrowth f ↔ HasExponentialPowerGrowthOutside f := by
  constructor
  · rintro ⟨A, B, ρ, hA, hB, hρ, h⟩
    exact ⟨A, B, ρ, 0, hA, hB, hρ, le_rfl, fun z _ ↦ h z⟩
  · rintro ⟨A, B, ρ, R, hA, hB, hρ, hR, hout⟩
    have hcompact : IsCompact (f '' closedBall 0 R) :=
      (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn
        (hf.continuousOn.mono (subset_univ _))
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hcompact.isBounded
    refine ⟨max A C, B, ρ, hA.trans_le (le_max_left _ _), hB, hρ, ?_⟩
    intro z
    have hexp_nonneg : 0 ≤ Real.exp (B * ‖z‖ ^ ρ) := (Real.exp_pos _).le
    by_cases hz : R ≤ ‖z‖
    · exact (hout z hz).trans
        (mul_le_mul_of_nonneg_right (le_max_left A C) hexp_nonneg)
    · have hzball : z ∈ closedBall (0 : ℂ) R := by
        simpa [mem_closedBall, dist_zero_right] using le_of_not_ge hz
      have hfC : ‖f z‖ ≤ C := hC (f z) ⟨z, hzball, rfl⟩
      have harg : 0 ≤ B * ‖z‖ ^ ρ :=
        mul_nonneg hB.le (Real.rpow_nonneg (norm_nonneg z) ρ)
      calc
        ‖f z‖ ≤ C := hfC
        _ ≤ max A C := le_max_right _ _
        _ = max A C * 1 := (mul_one _).symm
        _ ≤ max A C * Real.exp (B * ‖z‖ ^ ρ) :=
          mul_le_mul_of_nonneg_left (Real.one_le_exp harg) (hA.trans_le (le_max_left _ _)).le

/-- Stored global growth gives the usual large-radius finite-order bound. -/
theorem EntireFiniteOrder.hasExponentialPowerGrowthOutside (H : EntireFiniteOrder) :
    HasExponentialPowerGrowthOutside H :=
  (hasGlobalExponentialPowerGrowth_iff_outside H.analytic).mp H.growth

/-- Construct the exact finite-order carrier from the usual large-radius bound. -/
def EntireFiniteOrder.ofOutside (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hgrowth : HasExponentialPowerGrowthOutside f) : EntireFiniteOrder where
  toFun := f
  analytic := hf
  growth := (hasGlobalExponentialPowerGrowth_iff_outside hf).mpr hgrowth

end RHTower
