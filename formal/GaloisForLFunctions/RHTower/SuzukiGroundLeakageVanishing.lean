import GaloisForLFunctions.RHTower.SuzukiGroundEdgeCayleyUniversality

/-!
# When the ground leakage vanishes

The ground-edge universality law is driven by the hypothesis that the dimensionless odd-channel
leakage tends to zero, and nothing produced it.  The leakage is `τ · oddBudget / (gap · groundMass)`,
so it vanishes exactly when the odd budget does, and it tends to zero whenever the odd budget does
while the clock is bounded and the gap-mass product is bounded away from zero.

That is the practical criterion: no odd budget means no leakage, and a shrinking odd budget against
a nondegenerate ground pole means vanishing leakage.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- With no odd budget there is no leakage. -/
@[simp] theorem suzukiGroundLeakage_of_oddBudget_eq_zero (τ gap groundMass : ℝ) :
    suzukiGroundLeakage τ 0 gap groundMass = 0 := by
  rw [suzukiGroundLeakage]
  simp

/-- An eventually vanishing odd budget makes the leakage tend to zero. -/
theorem tendsto_suzukiGroundLeakage_zero_of_eventually_oddBudget_eq_zero
    {ι : Type*} {l : Filter ι} {τ oddBudget gap groundMass : ι → ℝ}
    (h : ∀ᶠ j in l, oddBudget j = 0) :
    Tendsto (fun j => suzukiGroundLeakage (τ j) (oddBudget j) (gap j) (groundMass j))
      l (nhds 0) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [h] with j hj
  rw [hj, suzukiGroundLeakage_of_oddBudget_eq_zero]

/-- **Vanishing-leakage criterion.**  A shrinking odd budget, a clock bounded in modulus and a
gap-mass product bounded away from zero force the leakage to zero. -/
theorem tendsto_suzukiGroundLeakage_zero_of_tendsto_oddBudget
    {ι : Type*} {l : Filter ι} {τ oddBudget gap groundMass : ι → ℝ} {C c : ℝ}
    (hc : 0 < c)
    (hτ : ∀ᶠ j in l, |τ j| ≤ C)
    (hden : ∀ᶠ j in l, c ≤ gap j * groundMass j)
    (hbudget : Tendsto (fun j => |oddBudget j|) l (nhds 0)) :
    Tendsto (fun j => suzukiGroundLeakage (τ j) (oddBudget j) (gap j) (groundMass j))
      l (nhds 0) := by
  have hmajor : Tendsto (fun j => C / c * |oddBudget j|) l (nhds 0) := by
    simpa using hbudget.const_mul (C / c)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hτ, hden] with j hj hdj
  have hdpos : 0 < gap j * groundMass j := lt_of_lt_of_le hc hdj
  have hCnn : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) hj
  have hbnn : (0 : ℝ) ≤ |oddBudget j| := abs_nonneg _
  rw [Real.norm_eq_abs, suzukiGroundLeakage, abs_div, abs_mul, abs_of_pos hdpos]
  rw [div_le_iff₀ hdpos]
  have hstep : |τ j| * |oddBudget j| ≤ C * |oddBudget j| :=
    mul_le_mul_of_nonneg_right hj hbnn
  have hgrow : C * |oddBudget j| ≤ C / c * |oddBudget j| * (gap j * groundMass j) := by
    have hcc : C / c * |oddBudget j| * c ≤ C / c * |oddBudget j| * (gap j * groundMass j) :=
      mul_le_mul_of_nonneg_left hdj (by positivity)
    have hexact : C / c * |oddBudget j| * c = C * |oddBudget j| := by
      field_simp
    linarith [hexact ▸ hcc]
  linarith

end

end GaloisForLFunctions.RHTower
