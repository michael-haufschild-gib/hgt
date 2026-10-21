import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyWideNearTopZone

/-!
# The zone horizon law and twisted prime windows

* **Zone horizon** (`zoneHorizon`). For `μ > 0` and a zero `½ + z` right of the line,
  `V_μ(z) = V_μ(w, |h_w(−iz)|, Re z)` is the lag at which `one_param_zone_visible` sees `z` once it
  lies within `μ/V` of the top.
* **Zone horizon law** (`one_param_zone_horizon_law`). For a width with `h_w(−iz) ≠ 0` at the zeros
  right of the line, if `P_v ≥ 0` on `[0, V]`, then from every zero `z₀` with `V_μ(z₀) ≤ V` one
  reaches a zero `z` with `Re z > Re z₀ + μ/V` and `V_μ(z) > V`. Each step inside the horizon gains
  `μ/V` in depth, so the chain leaves the horizon within `⌈V/μ⌉` steps.
* **Twisted prime windows** (`zeta_near_top_primeWindow_neg`). For `2w < log 2` the negative
  modulated test of `zeta_near_top_visible_at_polylog_lag` is a negative prime-window functional:
  the sum `Σ Λ(n) n^{−1/2}` over the prime powers in the window of the bump modulated to `γ₀`
  outweighs the archimedean terms at some lag `v ≤ V_w(γ₀, δ₀) ≍ (log γ₀)² log log γ₀/δ₀`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The zone horizon `V_μ(z) = V_μ(w, |h_w(−iz)|, Re z)` of a zero `½ + z`. -/
def zoneHorizon (w μ : ℝ) (z : ℂ) : ℝ := zoneLag w ‖paperFT (scaledBump w) (-(I * z))‖ μ z.re

/-- `V_μ(w, η, δ) ≥ w` for `δ > 0`. -/
theorem le_zoneLag {w : ℝ} (hw : 0 < w) (η μ : ℝ) {δ : ℝ} (hδ : 0 < δ) : w ≤ zoneLag w η μ δ := by
  unfold zoneLag
  have h1 := le_recordLag hw (2 * η ^ 2 * Real.exp (-μ)) (half_pos hδ)
  have h2 : 0 ≤ 2 / δ * |Real.log (80 * Real.log (180 * recordHeightOf w
      (2 * η ^ 2 * Real.exp (-μ))) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2))| := by
    positivity
  linarith

/-- **The zone horizon law.** Let `h_w(−iz) ≠ 0` at every zero `½ + z` right of the line, `μ > 0`,
and `P_v ≥ 0` for every `v ∈ [0, V]`. Then every zero `½ + z₀` right of the line with
`V_μ(z₀) ≤ V` has a zero `½ + z` with `Re z > Re z₀ + μ/V` and `V_μ(z) > V`. -/
theorem one_param_zone_horizon_law {w : ℝ} (hw : 0 < w)
    (hgen : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → 0 < z.re →
      paperFT (scaledBump w) (-(I * z)) ≠ 0) {μ : ℝ} (hμ : 0 < μ)
    {V : ℝ} (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hV : zoneHorizon w μ z₀ ≤ V) :
    ∃ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ z₀.re + μ / V < z.re ∧
      V < zoneHorizon w μ z := by
  by_contra hcon
  push Not at hcon
  have hV0 : 0 < V := lt_of_lt_of_le hw ((le_zoneLag hw _ μ hre₀).trans hV)
  have hμV : 0 < μ / V := div_pos hμ hV0
  -- one step of the zone depth gap
  have hstep : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → 0 < z.re →
      zoneHorizon w μ z ≤ V → ∃ z' : ℂ, (1 / 2 + z') ∈ zetaZeroConfig.carrier ∧
        z.re + μ / V < z'.re := fun z hz hre hVz => by
    obtain ⟨ρ, hρ, hlt⟩ := one_param_zone_depth_gap hw hpos hz hre
      (norm_pos_iff.mpr (hgen z hz hre)) le_rfl hVz
    refine ⟨ρ - 1 / 2, by rwa [show (1 / 2 : ℂ) + (ρ - 1 / 2) = ρ by ring], ?_⟩
    have e : (ρ - 1 / 2 : ℂ).re = ρ.re - 1 / 2 := by simp
    rw [e]; exact hlt
  -- the chain stays inside the horizon and gains `μ/V` per step
  have hchain : ∀ n : ℕ, ∃ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧
      z₀.re + n * (μ / V) ≤ z.re ∧ zoneHorizon w μ z ≤ V := by
    intro n
    induction n with
    | zero => exact ⟨z₀, hz₀, by simp, hV⟩
    | succ n ih =>
      obtain ⟨z, hz, hzre, hzV⟩ := ih
      have hn : 0 ≤ (n : ℝ) * (μ / V) := by positivity
      have hre : 0 < z.re := by linarith
      obtain ⟨z', hz', hlt⟩ := hstep z hz hre hzV
      refine ⟨z', hz', ?_, hcon z' hz' (by linarith)⟩
      push_cast
      linarith
  obtain ⟨z, hz, hzre, -⟩ := hchain ⌈V / μ⌉₊
  have hstrip := zetaZeroConfig.strip _ hz
  have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
  have h1 : (1 : ℝ) ≤ (⌈V / μ⌉₊ : ℝ) * (μ / V) := by
    have := Nat.le_ceil (V / μ)
    have h2 : V / μ * (μ / V) = 1 := by field_simp
    nlinarith
  linarith [hstrip.2]

/-- **Twisted prime windows see near-top zeros.** For `2w < log 2`, under the hypotheses of
`zeta_near_top_visible_at_polylog_lag`, some prime-window functional of the bump modulated to
`γ₀ = Im z₀` is negative: `Re lagPrimeWindowRHS(v, w, ·) < 0` for some `v ∈ [0, V]`. -/
theorem zeta_near_top_primeWindow_neg {w : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    (hγ : 1280 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) * (1 + z₀.im) ^ 4)
    {V : ℝ} (hV : nearTopLag w z₀.im z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    ∃ v ∈ Icc (0 : ℝ) V, (lagPrimeWindowRHS v w (EF.weilTest
      (twoBump (modScaledBump w z₀.im) v (-1)) (twoBump (modScaledBump w z₀.im) v (-1)))).re < 0 := by
  obtain ⟨v, hv, hneg⟩ := zeta_near_top_visible_at_polylog_lag hw hz₀ hre₀ hTw hγ hV htop
  refine ⟨v, hv, ?_⟩
  rwa [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w z₀.im) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w z₀.im) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw z₀.im)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw z₀.im) hw2 hv.1] at hneg

end GaloisForLFunctions.SquareRootThreshold
