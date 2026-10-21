import GaloisForLFunctions.SquareRootThreshold.ZoneHorizonLawAndTwistedPrimeWindows

/-!
# Attained tops are visible without a separation hypothesis

`ZetaAttainedTopIsVisibleAtAnExplicitLag`, `ZetaAttainedTopIsVisibleAtALogarithmicLag` and
`OneParameterLagFamilySeesAttainedTopsAtAnExplicitLag` see an attained top at a lag that depends on
a separation `g` of the zeros near the top. An attained top is `1/V`-near the top for every `V`, so
the near-top theorems see it at their own explicit lag, with no separation of the zeros at all.

* **The one-parameter family** (`one_param_attained_top_visible_at_horizon`). A zero `½ + z₀` of
  largest real part, `Re z₀ > 0`, `h_w(−iz₀) ≠ 0`, makes `P_v < 0` for some
  `v ≤ V₀(z₀) = oneParamHorizon w z₀`.
* **The modulated family** (`zeta_attained_top_visible_at_polylog_lag`). Above `T_w` and under the
  height condition, the difference test modulated to `γ₀` is negative at some
  `v ≤ V_w(γ₀, δ₀) ≍ (log γ₀)² log log γ₀/δ₀`.
* **Finitely many zeros right of the line** (`one_param_first_negative_lag_of_finite`). If `ζ` had a
  nonempty finite set of zeros right of the line and `h_w(−iz) ≠ 0` there, some `P_v` with
  `v ≤ V₀(z₀)` at a zero `z₀` of largest real part is negative; the prime-window form follows for
  `2w < log 2` (`one_param_first_negative_primeWindow_of_finite`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **An attained top is seen by `P_v` at its horizon.** If `½ + z₀` is a zero of largest real part,
`Re z₀ > 0` and `h_w(−iz₀) ≠ 0`, then `P_v < 0` for some `v ∈ [0, V₀(z₀)]`. -/
theorem one_param_attained_top_visible_at_horizon {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hh : paperFT (scaledBump w) (-(I * z₀)) ≠ 0)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re) :
    ∃ v ∈ Icc (0 : ℝ) (oneParamHorizon w z₀), (zetaZeroConfig.W
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  have hV0 : 0 < oneParamHorizon w z₀ := lt_of_lt_of_le hw (le_oneParamLag hw _ hre₀)
  refine one_param_near_top_visible_at_explicit_lag hw hz₀ hre₀ (norm_pos_iff.mpr hh) le_rfl le_rfl
    fun ρ hρ => ?_
  have := htop ρ hρ
  have : 0 < 1 / oneParamHorizon w z₀ := by positivity
  linarith

/-- `V_w(γ₀, δ₀) ≥ w` for `δ₀ > 0`. -/
theorem le_nearTopLag {w : ℝ} (hw : 0 < w) (γ₀ : ℝ) {δ₀ : ℝ} (hδ : 0 < δ₀) :
    w ≤ nearTopLag w γ₀ δ₀ := by
  unfold nearTopLag
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have h1 : 0 ≤ 8 / δ₀ * (13 * π * nearTopOrder w γ₀ + 4 +
      |Real.log (160 * Real.log (180 * recordHeightEnvelope w γ₀) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2)|) := by positivity
  have h2 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w / nearTopScale w γ₀ :=
    div_nonneg (mul_nonneg (by positivity) hJ0) (Real.sqrt_nonneg _)
  linarith

/-- **An attained top is seen by the modulated family at the polylogarithmic lag.** If `½ + z₀` is a
zero of largest real part, `δ₀ = Re z₀ > 0`, at height `γ₀ = Im z₀ ≥ T_w` with
`1280 log(180Γ)(e^{w/2}B_w)² ≤ (a_w²/(2e))(1 + γ₀)⁴`, then the difference test modulated to `γ₀` is
Weil negative at some `v ∈ [0, V_w(γ₀, δ₀)]`. -/
theorem zeta_attained_top_visible_at_polylog_lag {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    (hγ : 1280 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) * (1 + z₀.im) ^ 4)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re) :
    ∃ v ∈ Icc (0 : ℝ) (nearTopLag w z₀.im z₀.re), (zetaZeroConfig.W
      (twoBump (modScaledBump w z₀.im) v (-1)) (twoBump (modScaledBump w z₀.im) v (-1))).re < 0 := by
  have hV0 : 0 < nearTopLag w z₀.im z₀.re := lt_of_lt_of_le hw (le_nearTopLag hw _ hre₀)
  refine zeta_near_top_visible_at_polylog_lag hw hz₀ hre₀ hTw hγ le_rfl fun ρ hρ => ?_
  have := htop ρ hρ
  have : 0 < 1 / nearTopLag w z₀.im z₀.re := by positivity
  linarith

/-- A nonempty finite set of zeros right of the line has a zero of largest real part. -/
theorem exists_top_of_finite
    (hfin : {ρ : ℂ | ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re}.Finite)
    (hne : ∃ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re) :
    ∃ z₀ : ℂ, (1 / 2 + z₀) ∈ zetaZeroConfig.carrier ∧ 0 < z₀.re ∧
      ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re := by
  obtain ⟨ρ₁, hρ₁, hre₁⟩ := hne
  obtain ⟨ρ₀, hρ₀, hmax⟩ := hfin.exists_maximalFor (fun ρ : ℂ => ρ.re) _ ⟨ρ₁, hρ₁, hre₁⟩
  refine ⟨ρ₀ - 1 / 2, by rw [show (1 / 2 : ℂ) + (ρ₀ - 1 / 2) = ρ₀ by ring]; exact hρ₀.1, ?_, ?_⟩
  · have e : (ρ₀ - 1 / 2 : ℂ).re = ρ₀.re - 1 / 2 := by simp
    rw [e]; linarith [hρ₀.2]
  · intro ρ hρ
    have e : (ρ₀ - 1 / 2 : ℂ).re = ρ₀.re - 1 / 2 := by simp
    rw [e]
    by_cases hr : 1 / 2 < ρ.re
    · by_contra hlt
      push Not at hlt
      have := hmax ⟨hρ, hr⟩ (by linarith)
      linarith
    · push Not at hr; linarith [hρ₀.2]

/-- **Finitely many zeros right of the line are seen at an explicit lag.** Let the zeros of `ζ`
right of the line form a nonempty finite set, and `h_w(−iz) ≠ 0` at each of them. Then some zero
`½ + z₀` right of the line of largest real part has `P_v < 0` for some `v ∈ [0, V₀(z₀)]`. -/
theorem one_param_first_negative_lag_of_finite {w : ℝ} (hw : 0 < w)
    (hfin : {ρ : ℂ | ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re}.Finite)
    (hne : ∃ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re)
    (hgen : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → 0 < z.re →
      paperFT (scaledBump w) (-(I * z)) ≠ 0) :
    ∃ z₀ : ℂ, (1 / 2 + z₀) ∈ zetaZeroConfig.carrier ∧ 0 < z₀.re ∧
      ∃ v ∈ Icc (0 : ℝ) (oneParamHorizon w z₀), (zetaZeroConfig.W
        (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  obtain ⟨z₀, hz₀, hre₀, htop⟩ := exists_top_of_finite hfin hne
  exact ⟨z₀, hz₀, hre₀,
    one_param_attained_top_visible_at_horizon hw hz₀ hre₀ (hgen z₀ hz₀ hre₀) htop⟩

/-- **The prime-window form.** For `2w < log 2`, under the hypotheses of
`one_param_first_negative_lag_of_finite`, some prime-window functional `Re lagPrimeWindowRHS(v, w, ·)`
with `v ≤ V₀(z₀)` is negative. -/
theorem one_param_first_negative_primeWindow_of_finite {w : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2)
    (hfin : {ρ : ℂ | ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re}.Finite)
    (hne : ∃ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re)
    (hgen : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → 0 < z.re →
      paperFT (scaledBump w) (-(I * z)) ≠ 0) :
    ∃ z₀ : ℂ, (1 / 2 + z₀) ∈ zetaZeroConfig.carrier ∧ 0 < z₀.re ∧
      ∃ v ∈ Icc (0 : ℝ) (oneParamHorizon w z₀), (lagPrimeWindowRHS v w (EF.weilTest
        (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re < 0 := by
  obtain ⟨z₀, hz₀, hre₀, v, hv, hneg⟩ := one_param_first_negative_lag_of_finite hw hfin hne hgen
  refine ⟨z₀, hz₀, hre₀, v, hv, ?_⟩
  rwa [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv.1] at hneg

end GaloisForLFunctions.SquareRootThreshold
