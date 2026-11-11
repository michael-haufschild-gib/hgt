import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheActualGcdSumsAreShiftedProfileForms
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCorrectedJetLimitsAllowArbitraryHeights

/-!
# The first three jets of the actual frozen-coefficient gcd sums

Write `u=d₀ log N` and vary displacement as `d=(u+z)/log N`, keeping
the coefficients at `d₀`. The direct normalized shifts move in direction
`(−2,2)`; the reflected shifts move in direction `(2,0)`. Thus the actual
gcd sums inherit the proved polynomial-profile value and derivative limits.
-/

open Filter MeasureTheory Polynomial Topology
open RHTower.ZetaGateProductAFE

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Direct gcd sum with coefficients fixed at normalized displacement `u`. -/
def frozenDirectGcd (P : ℝ → ℝ) (N : ℕ) (u z : ℝ) : ℝ :=
  Real.log N * gcdSum₁ ((u + z) / Real.log N) N (moebiusProfileWeights P N (-u))

/-- Reflected gcd sum with the same frozen coefficients. -/
def frozenReflectedGcd (P : ℝ → ℝ) (N : ℕ) (u z : ℝ) : ℝ :=
  Real.log N * gcdSum₂ ((u + z) / Real.log N) N (moebiusProfileWeights P N (-u))

theorem frozenDirectGcd_eq {N : ℕ} (hN : 1 < N) (P : ℝ → ℝ) (u : ℝ) :
    frozenDirectGcd P N u =
      fun z => shiftedSelbergProfileForm P N (-2 * u + (-2) * z) (u + 2 * z) := by
  funext z
  rw [frozenDirectGcd, gcdSum₁_moebiusProfileWeights hN]
  have hL : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  congr 1 <;> field_simp [hL] <;> ring

theorem frozenReflectedGcd_eq {N : ℕ} (hN : 1 < N) (P : ℝ → ℝ) (u : ℝ) :
    frozenReflectedGcd P N u =
      fun z => shiftedSelbergProfileForm P N (-2 * (-u) + 2 * z) (-u + 0 * z) := by
  funext z
  rw [frozenReflectedGcd, gcdSum₂_moebiusProfileWeights hN]
  have hL : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  congr 1 <;> field_simp [hL] <;> ring

/-- The direct arithmetic value and its first two frozen-coefficient jets converge. -/
theorem tendsto_frozenDirectGcd_first_three (P : ℝ[X]) (hP : P.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {u : ι → ℝ} {u₀ : ℝ} (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun N => frozenDirectGcd P.eval (n N) (u N) 0) l
      (𝓝 (∫ t : ℝ in 0..1, (P.derivative.eval (1 - t) - u₀ * P.eval (1 - t)) ^ 2)) ∧
    Tendsto (fun N => deriv (frozenDirectGcd P.eval (n N) (u N)) 0) l
      (𝓝 (polynomialProfileFirstLimit P P u₀ (-2) 2 0)) ∧
    Tendsto (fun N => iteratedDeriv 2 (frozenDirectGcd P.eval (n N) (u N)) 0) l
      (𝓝 (polynomialProfileSecondLimit P P u₀ (-2) 2 0)) := by
  constructor
  · apply (tendsto_coupledShiftedSelbergForm_reindexed P hP hn hu).congr'
    filter_upwards [hn.eventually_ge_atTop 2] with N hN
    rw [frozenDirectGcd_eq (by omega : 1 < n N)]
    simp only [coupledShiftedSelbergForm, mul_zero, add_zero]
  constructor
  · apply (tendsto_shiftedSelbergProfileForm_deriv_reindexed P hP hn hu (-2) 2).congr'
    filter_upwards [hn.eventually_ge_atTop 2] with N hN
    rw [frozenDirectGcd_eq (by omega : 1 < n N)]
  · apply (tendsto_shiftedSelbergProfileForm_iteratedDeriv_two_reindexed P hP hn hu (-2) 2).congr'
    filter_upwards [hn.eventually_ge_atTop 2] with N hN
    rw [frozenDirectGcd_eq (by omega : 1 < n N)]

/-- The reflected arithmetic value and its first two frozen-coefficient jets converge. -/
theorem tendsto_frozenReflectedGcd_first_three (P : ℝ[X]) (hP : P.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {u : ι → ℝ} {u₀ : ℝ} (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun N => frozenReflectedGcd P.eval (n N) (u N) 0) l
      (𝓝 (∫ t : ℝ in 0..1, (P.derivative.eval (1 - t) - (-u₀) * P.eval (1 - t)) ^ 2)) ∧
    Tendsto (fun N => deriv (frozenReflectedGcd P.eval (n N) (u N)) 0) l
      (𝓝 (polynomialProfileFirstLimit P P (-u₀) 2 0 0)) ∧
    Tendsto (fun N => iteratedDeriv 2 (frozenReflectedGcd P.eval (n N) (u N)) 0) l
      (𝓝 (polynomialProfileSecondLimit P P (-u₀) 2 0 0)) := by
  constructor
  · apply (tendsto_coupledShiftedSelbergForm_reindexed P hP hn hu.neg).congr'
    filter_upwards [hn.eventually_ge_atTop 2] with N hN
    rw [frozenReflectedGcd_eq (by omega : 1 < n N)]
    simp only [coupledShiftedSelbergForm, mul_zero, add_zero]
  constructor
  · apply (tendsto_shiftedSelbergProfileForm_deriv_reindexed P hP hn hu.neg 2 0).congr'
    filter_upwards [hn.eventually_ge_atTop 2] with N hN
    rw [frozenReflectedGcd_eq (by omega : 1 < n N)]
  · apply (tendsto_shiftedSelbergProfileForm_iteratedDeriv_two_reindexed P hP hn hu.neg 2 0).congr'
    filter_upwards [hn.eventually_ge_atTop 2] with N hN
    rw [frozenReflectedGcd_eq (by omega : 1 < n N)]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
