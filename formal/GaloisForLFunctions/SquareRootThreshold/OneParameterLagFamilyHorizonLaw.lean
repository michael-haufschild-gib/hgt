import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilySeesNearTopZerosAtAnExplicitLag

/-!
# The horizon law of the one-parameter lag family

For a zero `½ + z` of `ζ` right of the line put `V₀(z) = V₀(w, |h_w(−iz)|, Re z)`
(`oneParamHorizon`), the lag at which `one_param_near_top_visible_at_explicit_lag` sees `z` once it is
`1/V₀(z)`-near the top.

* **Horizon law** (`one_param_horizon_law`). For a width with `h_w(−iz) ≠ 0` at every zero, if
  `P_v ≥ 0` for every `v ∈ [0, V]`, then from every zero `z₀` right of the line inside the horizon
  (`V₀(z₀) ≤ V`) one reaches a zero `z` beyond it (`V₀(z) > V`) with `Re z > Re z₀ + 1/V`. The
  depth gap is iterated: each step inside the horizon gains `1/V` in depth, and the strip allows
  fewer than `V/2` steps.
* **Visibility from the horizon** (`one_param_visible_of_horizon`). The contrapositive: if every zero
  more than `1/V` to the right of some `z₀` with `V₀(z₀) ≤ V` lies inside the horizon, some `P_v`,
  `v ∈ [0, V]`, is negative. This replaces the attainment of the top by a condition on the zeros
  beyond the horizon only.
* **Prime side** (`one_param_near_top_primeWindow_neg`). For `2w < log 2` the negative `P_v` of
  `one_param_near_top_visible_at_explicit_lag` is a negative prime-window functional
  `Re lagPrimeWindowRHS(v, w, ·)`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The lag horizon `V₀(z) = V₀(w, |h_w(−iz)|, Re z)` of a zero `½ + z`. -/
def oneParamHorizon (w : ℝ) (z : ℂ) : ℝ :=
  oneParamLag w ‖paperFT (scaledBump w) (-(I * z))‖ z.re

/-- `V₀(w, η, δ) ≥ w` for `δ > 0`. -/
theorem le_oneParamLag {w : ℝ} (hw : 0 < w) (η : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    w ≤ oneParamLag w η δ := by
  unfold oneParamLag
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have h1 : 0 ≤ 8 / δ * (13 * π * oneParamOrder w η + 4 +
      |Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2))|) := by positivity
  have h2 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w / oneParamScale w η :=
    div_nonneg (mul_nonneg (by positivity) hJ0) (Real.sqrt_nonneg _)
  linarith

/-- **The horizon law.** Let `h_w(−iz) ≠ 0` at every zero `½ + z` of `ζ`, and let `P_v ≥ 0` for every
lag `v ∈ [0, V]`. Then every zero `½ + z₀` right of the line with `V₀(z₀) ≤ V` has a zero `½ + z`
with `Re z > Re z₀ + 1/V` and `V₀(z) > V`. -/
theorem one_param_horizon_law {w : ℝ} (hw : 0 < w)
    (hgen : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → paperFT (scaledBump w) (-(I * z)) ≠ 0)
    {V : ℝ} (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hV : oneParamHorizon w z₀ ≤ V) :
    ∃ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ z₀.re + 1 / V < z.re ∧
      V < oneParamHorizon w z := by
  by_contra hcon
  push Not at hcon
  have hV0 : 0 < V := lt_of_lt_of_le hw ((le_oneParamLag hw _ hre₀).trans hV)
  -- one step of the depth gap
  have hstep : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → 0 < z.re →
      oneParamHorizon w z ≤ V → ∃ z' : ℂ, (1 / 2 + z') ∈ zetaZeroConfig.carrier ∧
        z.re + 1 / V < z'.re := fun z hz hre hVz => by
    obtain ⟨ρ, hρ, hlt⟩ := one_param_depth_gap_of_lag_positivity hw hpos hz hre
      (norm_pos_iff.mpr (hgen z hz)) le_rfl hVz
    refine ⟨ρ - 1 / 2, by rwa [show (1 / 2 : ℂ) + (ρ - 1 / 2) = ρ by ring], ?_⟩
    have e : (ρ - 1 / 2 : ℂ).re = ρ.re - 1 / 2 := by simp
    rw [e]; exact hlt
  -- the chain stays inside the horizon and gains `1/V` per step
  have hchain : ∀ n : ℕ, ∃ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧
      z₀.re + n / V ≤ z.re ∧ oneParamHorizon w z ≤ V := by
    intro n
    induction n with
    | zero => exact ⟨z₀, hz₀, by simp, hV⟩
    | succ n ih =>
      obtain ⟨z, hz, hzre, hzV⟩ := ih
      have hn : 0 ≤ (n : ℝ) / V := by positivity
      have hre : 0 < z.re := by linarith
      obtain ⟨z', hz', hlt⟩ := hstep z hz hre hzV
      refine ⟨z', hz', ?_, hcon z' hz' (by linarith)⟩
      push_cast
      rw [add_div]
      linarith
  obtain ⟨z, hz, hzre, -⟩ := hchain ⌈V⌉₊
  have hstrip := zetaZeroConfig.strip _ hz
  have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
  have h1 : (1 : ℝ) ≤ (⌈V⌉₊ : ℝ) / V := by
    rw [le_div_iff₀ hV0, one_mul]; exact Nat.le_ceil V
  linarith [hstrip.2]

/-- **Visibility from the horizon.** Let `h_w(−iz) ≠ 0` at every zero. If a zero `½ + z₀` right of
the line has `V₀(z₀) ≤ V` and every zero `½ + z` with `Re z > Re z₀ + 1/V` has `V₀(z) ≤ V`, then
`P_v < 0` for some `v ∈ [0, V]`. -/
theorem one_param_visible_of_horizon {w : ℝ} (hw : 0 < w)
    (hgen : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → paperFT (scaledBump w) (-(I * z)) ≠ 0)
    {V : ℝ} {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hV : oneParamHorizon w z₀ ≤ V)
    (hin : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → z₀.re + 1 / V < z.re →
      oneParamHorizon w z ≤ V) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  by_contra hneg
  push Not at hneg
  obtain ⟨z, hz, hlt, hVz⟩ := one_param_horizon_law hw hgen hneg hz₀ hre₀ hV
  exact absurd (hin z hz hlt) (not_le.mpr hVz)

/-- **The prime side.** For `2w < log 2`, under the hypotheses of
`one_param_near_top_visible_at_explicit_lag`, some prime-window functional is negative:
`Re lagPrimeWindowRHS(v, w, ·) < 0` for some `v ∈ [0, V]`. -/
theorem one_param_near_top_primeWindow_neg {w : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2)
    {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hV : oneParamLag w η z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    ∃ v ∈ Icc (0 : ℝ) V, (lagPrimeWindowRHS v w (EF.weilTest
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re < 0 := by
  obtain ⟨v, hv, hneg⟩ := one_param_near_top_visible_at_explicit_lag hw hz₀ hre₀ hη hηle hV htop
  refine ⟨v, hv, ?_⟩
  rwa [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv.1] at hneg

end GaloisForLFunctions.SquareRootThreshold
