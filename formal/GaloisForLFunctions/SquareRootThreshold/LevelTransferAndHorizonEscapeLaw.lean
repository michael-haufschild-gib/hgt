import GaloisForLFunctions.SquareRootThreshold.LocalVisibilityOfAnOffLineLevel
import GaloisForLFunctions.SquareRootThreshold.AttainedTopsAreVisibleWithoutSeparation
import GaloisForLFunctions.SquareRootThreshold.OrderOfTheExplicitVisibilityLags

/-!
# Inter-Level Deficit–Excess Transfer and Horizon Escape Laws

This module establishes the quantitative duality between the depth-deficit transform `G(r, v)` and
the depth-excess transform `E(r, v)` across levels of a general tempered configuration, together
with the height-escape, amplitude-escape, and modulated horizon laws for the zeros of `ζ` beyond
any finite lag horizon.

## Main Results

1. **Inter-level conservation law (`depthDeficit_add_levelWeight_add_depthExcess_eq`,
   `level_transfer_law`):**
   For any tempered configuration `Z`, bump `b`, level `r ∈ ℝ`, and lag `v ≥ 0`, the sum of the
   depth-deficit transform `G(r, v)`, the total level weight `L(r) = levelWeight Z b r`, and the
   depth-excess transform `E(r, v)` equals the off-line moment transform
   `offLineMoment Z b r v = Σ_t |q_t| e^{(Re t − r)v}`. Across any two levels `r₁, r₂ ∈ ℝ`,
   $$G(r_1, v) + L(r_1) + E(r_1, v) = e^{(r_2 - r_1)v}\bigl(G(r_2, v) + L(r_2) + E(r_2, v)\bigr).$$

2. **Excess-to-deficit duality and asymptotic rate below a top (`depthExcess_eq_of_top`,
   `depthExcess_le_exp_mul_depthDeficit_of_unattained_top`,
   `tendsto_exp_neg_mul_depthExcess_of_top`,
   `tendsto_exp_neg_mul_depthExcess_zero_of_unattained_top`):**
   If every active off-line zero has `Re t ≤ R`, then `E(R, v) = 0` and
   $$G(r, v) + L(r) + E(r, v) = e^{(R - r)v}\bigl(G(R, v) + L(R)\bigr).$$
   For every strict sub-level `r < R`, the normalized excess `e^{−(R − r)v} E(r, v)` converges to
   the top-level weight `L(R)` as `v → ∞`. In particular, when the top `R` is unattained
   (`Re t < R` for all active off-line zeros), `L(R) = 0`, `E(r, v) ≤ e^{(R − r)v} G(R, v)` for
   all `v ≥ 0`, `e^{−(R − r)v} E(r, v) → 0` as `v → ∞`, and the initial excess mass `E(r, 0)`
   vanishes as `r → R⁻` (`tendsto_depthExcess_zero_of_unattained_top`).

3. **Explicit visibility windows for unattained tops (`exists_minor_fails_of_unattained_top_level`,
   `exists_minor_fails_of_initial_excess`):**
   For any level `r = Re t₀ = ½ + D` below an unattained top `R`, bounding `E(r, V + 4π/g)` via
   `e^{(R − r)(V + 4π/g)} G(R, V)` or `e^{(R − r)(V + 4π/g)} E(r, 0)` yields an explicit Ingham
   visibility window `[V, V + 4π/g]` where the two-point minor fails.

4. **Depth-antitonicity, box horizons, and height/amplitude escape for `ζ`
   (`oneParamLag_anti_depth`, `zoneLag_anti_depth`, `nearTopLag_anti_depth`,
   `one_param_horizon_law_forces_height_and_amplitude_escape`,
   `one_param_visible_of_height_cutoff`, `modulated_horizon_law`):**
   All explicit visibility lags (`recordLag`, `oneParamLag`, `zoneLag`, `nearTopLag`) are antitone
   in the depth `δ > 0`. Consequently, a deeper zero `z` (`Re z > Re z₀`) can lie beyond the
   horizon of `z₀` only through smaller transform amplitude `|h_w(−iz)|`. By local finiteness of
   `zetaZeroConfig` in the strip, every height box `|Im z| ≤ H` has a finite uniform horizon
   `boxHorizon w H`, so positivity of `P_v` on `[0, V]` for `V ≥ max (oneParamHorizon w z₀) (boxHorizon w H)`
   forces the existence of a zero `½ + z` with `Re z > Re z₀ + 1/V` and `|Im z| > H`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### 1. Off-line moment transform and the inter-level conservation law -/

/-- The total off-line weight `L(r) = Σ_{Re t = r} |q_t|` on the level `Re t = r`. -/
def levelWeight (Z : ZeroConfig) (b : ℝ → ℂ) (r : ℝ) : ℝ :=
  levelTail Z b r ∅

/-- The full off-line moment transform `M(r, v) = Σ_t |q_t| e^{(Re t − r)v}` relative to level `r`. -/
def offLineMoment (Z : ZeroConfig) (b : ℝ → ℂ) (r v : ℝ) : ℝ :=
  ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ * Real.exp (((t : ℂ).re - r) * v)

theorem levelWeight_nonneg (Z : ZeroConfig) (b : ℝ → ℂ) (r : ℝ) :
    0 ≤ levelWeight Z b r :=
  tsum_nonneg fun _ => by split_ifs <;> positivity

theorem depthDeficit_nonneg (Z : ZeroConfig) (b : ℝ → ℂ) (r v : ℝ) :
    0 ≤ depthDeficit Z b r v :=
  tsum_nonneg fun _ => by split_ifs <;> positivity

theorem depthExcess_nonneg (Z : ZeroConfig) (b : ℝ → ℂ) (r v : ℝ) :
    0 ≤ depthExcess Z b r v :=
  tsum_nonneg fun _ => by split_ifs <;> positivity

theorem summable_offLineMoment (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (r : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    Summable fun t : rightZeros Z =>
      ‖offLineWeight b (Z.mult t) t‖ * Real.exp (((t : ℂ).re - r) * v) := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun t => ?_)
    ((summable_norm_offLineWeight Z hZ hb hbs).mul_right (Real.exp ((1 - r) * v)))
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [(Z.strip _ t.2.1).2]) hv))
    (norm_nonneg _)

/-- At any level `r` and lag `v ≥ 0`, the deficit, level weight, and excess sum to `offLineMoment`. -/
theorem depthDeficit_add_levelWeight_add_depthExcess_eq (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (r : ℝ) {v : ℝ}
    (hv : 0 ≤ v) :
    depthDeficit Z b r v + levelWeight Z b r + depthExcess Z b r v = offLineMoment Z b r v := by
  have hG := summable_depthDeficit Z hZ hb hbs r hv
  have hL := summable_levelTail Z hZ hb hbs r ∅
  have hE := summable_depthExcess Z hZ hb hbs r hv
  rw [depthDeficit, levelWeight, levelTail, depthExcess, ← hG.tsum_add hL, ← (hG.add hL).tsum_add hE,
    offLineMoment]
  refine tsum_congr fun t => ?_
  rcases lt_trichotomy (t : ℂ).re r with hlt | heq | hgt
  · rw [if_pos hlt, if_neg (fun h => hlt.ne h.1), if_neg (not_lt.mpr hlt.le), add_zero, add_zero]
  · rw [if_neg heq.not_lt, if_pos ⟨heq, by simp⟩, if_neg heq.symm.not_lt,
      zero_add, add_zero, heq, sub_self, zero_mul, Real.exp_zero, mul_one]
  · rw [if_neg (not_lt.mpr hgt.le), if_neg (fun h => hgt.ne' h.1), if_pos hgt, zero_add, zero_add]

/-- Scaling law of `offLineMoment` between any two levels `r₁` and `r₂`. -/
theorem offLineMoment_eq_exp_mul (Z : ZeroConfig) (b : ℝ → ℂ) (r₁ r₂ v : ℝ) :
    offLineMoment Z b r₁ v = Real.exp ((r₂ - r₁) * v) * offLineMoment Z b r₂ v := by
  rw [offLineMoment, offLineMoment, ← tsum_mul_left]
  refine tsum_congr fun t => ?_
  have hexp : Real.exp (((t : ℂ).re - r₁) * v) =
      Real.exp ((r₂ - r₁) * v) * Real.exp (((t : ℂ).re - r₂) * v) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]; ring

/-- **Inter-level conservation law.** Across any two levels `r₁, r₂ ∈ ℝ` and lag `v ≥ 0`,
`G(r₁, v) + L(r₁) + E(r₁, v) = e^{(r₂ − r₁)v} (G(r₂, v) + L(r₂) + E(r₂, v))`. -/
theorem level_transfer_law (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (r₁ r₂ : ℝ) {v : ℝ}
    (hv : 0 ≤ v) :
    depthDeficit Z b r₁ v + levelWeight Z b r₁ + depthExcess Z b r₁ v =
      Real.exp ((r₂ - r₁) * v) *
        (depthDeficit Z b r₂ v + levelWeight Z b r₂ + depthExcess Z b r₂ v) := by
  rw [depthDeficit_add_levelWeight_add_depthExcess_eq Z hZ hb hbs r₁ hv,
    depthDeficit_add_levelWeight_add_depthExcess_eq Z hZ hb hbs r₂ hv,
    offLineMoment_eq_exp_mul Z b r₁ r₂ v]

/-! ### 2. Excess-to-deficit duality and asymptotic growth below attained and unattained tops -/

/-- When no active zero lies on the level `R`, `levelWeight Z b R = 0`. -/
theorem levelWeight_eq_zero_of_unattained {Z : ZeroConfig} {b : ℝ → ℂ} {R : ℝ}
    (hunatt : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re ≠ R) :
    levelWeight Z b R = 0 := by
  rw [levelWeight, levelTail]
  refine (tsum_congr fun t => ?_).trans tsum_zero
  split_ifs with h
  · by_contra hne
    exact hunatt t t.2 (fun h0 => hne (by rw [h0, norm_zero])) h.1
  · rfl

/-- **Excess-to-deficit identity below an upper bound `R`.** If every active right zero satisfies
`Re t ≤ R`, then for every level `r` and lag `v ≥ 0`,
`E(r, v) = e^{(R − r)v} (G(R, v) + L(R)) − G(r, v) − L(r)`. -/
theorem depthExcess_eq_of_top (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {R : ℝ}
    (htop : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ R) (r : ℝ) {v : ℝ}
    (hv : 0 ≤ v) :
    depthExcess Z b r v =
      Real.exp ((R - r) * v) * (depthDeficit Z b R v + levelWeight Z b R) -
        depthDeficit Z b r v - levelWeight Z b r := by
  have htr := level_transfer_law Z hZ hb hbs r R hv
  rw [depthExcess_eq_zero_of_top htop v, add_zero] at htr
  linarith

/-- **Excess-to-deficit identity and bound below an unattained top `R`.** If every active right
zero satisfies `Re t < R`, then `G(r, v) + L(r) + E(r, v) = e^{(R − r)v} G(R, v)` and
`E(r, v) ≤ e^{(R − r)v} G(R, v)` for every `r` and `v ≥ 0`. -/
theorem depthExcess_le_exp_mul_depthDeficit_of_unattained_top (Z : ZeroConfig)
    (hZ : TemperedConfig Z) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {R : ℝ}
    (hunatt : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re < R) (r : ℝ) {v : ℝ}
    (hv : 0 ≤ v) :
    depthDeficit Z b r v + levelWeight Z b r + depthExcess Z b r v =
        Real.exp ((R - r) * v) * depthDeficit Z b R v ∧
      depthExcess Z b r v ≤ Real.exp ((R - r) * v) * depthDeficit Z b R v := by
  have htr := level_transfer_law Z hZ hb hbs r R hv
  have htop : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ R :=
    fun t ht hq => (hunatt t ht hq).le
  have hne : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re ≠ R :=
    fun t ht hq => (hunatt t ht hq).ne
  rw [depthExcess_eq_zero_of_top htop v, levelWeight_eq_zero_of_unattained hne,
    add_zero, add_zero] at htr
  exact ⟨htr, by linarith [depthDeficit_nonneg Z b r v, levelWeight_nonneg Z b r]⟩

/-- **Exact asymptotic growth rate of `E(r, v)` below any top `R`.** For any upper bound `R` on
active real parts and any strict sub-level `r < R`, `e^{−(R − r)v} E(r, v) → L(R)` as `v → ∞`. -/
theorem tendsto_exp_neg_mul_depthExcess_of_top (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {R r : ℝ}
    (hrR : r < R) (htop : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ R) :
    Tendsto (fun v => Real.exp (-((R - r) * v)) * depthExcess Z b r v) atTop
      (𝓝 (levelWeight Z b R)) := by
  have hG_R := tendsto_depthDeficit Z hZ hb hbs R
  have hG_r := tendsto_depthDeficit Z hZ hb hbs r
  have hexp0 : Tendsto (fun v => Real.exp (-((R - r) * v))) atTop (𝓝 0) := by
    have : (fun v => Real.exp (-((R - r) * v))) = fun v => Real.exp ((r - R) * v) := by
      ext v; congr 1; ring
    rw [this]
    exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have hlim : Tendsto (fun v => depthDeficit Z b R v + levelWeight Z b R -
      Real.exp (-((R - r) * v)) * (depthDeficit Z b r v + levelWeight Z b r)) atTop
      (𝓝 (levelWeight Z b R)) := by
    have h1 : Tendsto (fun v => depthDeficit Z b R v + levelWeight Z b R) atTop
        (𝓝 (0 + levelWeight Z b R)) := hG_R.add tendsto_const_nhds
    have h2 : Tendsto (fun v => Real.exp (-((R - r) * v)) *
        (depthDeficit Z b r v + levelWeight Z b r)) atTop (𝓝 (0 * (0 + levelWeight Z b r))) :=
      hexp0.mul (hG_r.add tendsto_const_nhds)
    simpa using h1.sub h2
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
  rw [depthExcess_eq_of_top Z hZ hb hbs htop r hv]
  have hmul : Real.exp (-((R - r) * v)) * Real.exp ((R - r) * v) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination (depthDeficit Z b R v + levelWeight Z b R) * hmul.symm

/-- **Sub-exponential excess growth at an unattained top.** When the top `R` is unattained
(`Re t < R` for all active right zeros), `e^{−(R − r)v} E(r, v) → 0` as `v → ∞` for every level
`r ∈ ℝ`. -/
theorem tendsto_exp_neg_mul_depthExcess_zero_of_unattained_top (Z : ZeroConfig)
    (hZ : TemperedConfig Z) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {R : ℝ}
    (hunatt : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re < R) (r : ℝ) :
    Tendsto (fun v => Real.exp (-((R - r) * v)) * depthExcess Z b r v) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_depthDeficit Z hZ hb hbs R) ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with v _
    exact mul_nonneg (Real.exp_pos _).le (depthExcess_nonneg Z b r v)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    have hle := (depthExcess_le_exp_mul_depthDeficit_of_unattained_top Z hZ hb hbs hunatt r hv).2
    have hmul := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-((R - r) * v))).le
    have hexp : Real.exp (-((R - r) * v)) * Real.exp ((R - r) * v) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [← mul_assoc, hexp, one_mul] at hmul
    exact hmul

/-- Two-sided growth bound for `E(r, v)` in terms of the initial excess mass `E(r, 0)`. -/
theorem depthExcess_le_exp_mul_depthExcess_zero (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {R : ℝ}
    (htop : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ R) (r : ℝ) {v : ℝ}
    (hv : 0 ≤ v) :
    depthExcess Z b r 0 ≤ depthExcess Z b r v ∧
      depthExcess Z b r v ≤ Real.exp ((R - r) * v) * depthExcess Z b r 0 := by
  refine ⟨depthExcess_mono Z hZ hb hbs r le_rfl hv, ?_⟩
  rw [depthExcess, depthExcess, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun t => ?_) (summable_depthExcess Z hZ hb hbs r hv)
    ((summable_depthExcess Z hZ hb hbs r le_rfl).mul_left _)
  split_ifs with h
  · by_cases hq : offLineWeight b (Z.mult t) t = 0
    · simp [hq]
    · rw [mul_zero, Real.exp_zero, mul_one, mul_comm (Real.exp _)]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [htop t t.2 hq]) hv))
        (norm_nonneg _)
  · simp

/-- As the level `r` approaches an unattained top `R`, the initial excess mass `E(r, 0)` tends to `0`. -/
theorem tendsto_depthExcess_zero_of_unattained_top (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {R : ℝ}
    (hunatt : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re < R) :
    Tendsto (fun r => depthExcess Z b r 0) (𝓝 R) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 R) (g := fun _ : rightZeros Z => 0)
    (f := fun r (t : rightZeros Z) => if r < (t : ℂ).re then
      ‖offLineWeight b (Z.mult t) t‖ * Real.exp (((t : ℂ).re - r) * 0) else 0)
    (summable_norm_offLineWeight Z hZ hb hbs) (fun t => ?_)
    (Eventually.of_forall fun r t => by
      split_ifs <;> simp)
  · simpa [depthExcess] using h
  · by_cases hq : offLineWeight b (Z.mult t) t = 0
    · simp [hq]
    · have hlt : (t : ℂ).re < R := hunatt t t.2 hq
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioi_mem_nhds hlt] with r hr
      change (t : ℂ).re < r at hr
      rw [if_neg (not_lt.mpr hr.le)]

/-! ### 3. Explicit Ingham visibility windows for levels below an unattained top -/

/-- **Local visibility of a level below an unattained top `R` via `G(R, V)`.** Let `R` be an
unattained upper bound (`Re t < R` for all active right zeros) and let `F ∋ t₀` be a finite
`g`-separated set on the level `r = Re t₀ = ½ + D`. If `levelTail ≤ |q_{t₀}|/12`,
`G(r, V) ≤ |q_{t₀}|/12`, `e^{(R − r)(V + 4π/g)} G(R, V + 4π/g) ≤ |q_{t₀}|/12`, and
`2M_b + 3Σ|q_t| < (|q_{t₀}|/4) e^{DV}`, then the two-point minor fails in `[V, V + 4π/g]`. -/
theorem exists_minor_fails_of_unattained_top_level (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {R : ℝ}
    (hunatt : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re < R) {t₀ : ℂ}
    (ht₀ : t₀ ∈ rightZeros Z) {F : Finset ℂ} (hF : ∀ t ∈ F, t ∈ rightZeros Z ∧ t.re = t₀.re)
    (ht₀F : t₀ ∈ F) {g : ℝ} (hg : 0 < g) (hsep : ∀ t ∈ F, ∀ s ∈ F, t ≠ s → g ≤ |t.im - s.im|)
    (htail : levelTail Z b t₀.re F ≤ ‖offLineWeight b (Z.mult t₀) t₀‖ / 12) {V : ℝ} (hV : 0 ≤ V)
    (hG : depthDeficit Z b t₀.re V ≤ ‖offLineWeight b (Z.mult t₀) t₀‖ / 12)
    (hGR : Real.exp ((R - t₀.re) * (V + 4 * π / g)) * depthDeficit Z b R (V + 4 * π / g) ≤
      ‖offLineWeight b (Z.mult t₀) t₀‖ / 12)
    (hM : 2 * onLineMassOf Z b + 3 * ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ <
      ‖offLineWeight b (Z.mult t₀) t₀‖ / 4 * Real.exp ((t₀.re - 1 / 2) * V)) :
    ∃ v : ℝ, V ≤ v ∧ v ≤ V + 4 * π / g ∧
      2 * (lagStructure Z b 0).re < ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  have hv4 : 0 ≤ V + 4 * π / g := by positivity
  have hE : depthExcess Z b t₀.re (V + 4 * π / g) ≤ ‖offLineWeight b (Z.mult t₀) t₀‖ / 12 :=
    (depthExcess_le_exp_mul_depthDeficit_of_unattained_top Z hZ hb hbs hunatt t₀.re hv4).2.trans hGR
  exact exists_minor_fails_of_level Z hZ hb hbs ht₀ hF ht₀F hg hsep htail hV hG hE hM

/-- **Local visibility of a level below `R` via the initial excess mass `E(r, 0)`.** -/
theorem exists_minor_fails_of_initial_excess (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {R : ℝ}
    (htop : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ R) {t₀ : ℂ}
    (ht₀ : t₀ ∈ rightZeros Z) {F : Finset ℂ} (hF : ∀ t ∈ F, t ∈ rightZeros Z ∧ t.re = t₀.re)
    (ht₀F : t₀ ∈ F) {g : ℝ} (hg : 0 < g) (hsep : ∀ t ∈ F, ∀ s ∈ F, t ≠ s → g ≤ |t.im - s.im|)
    (htail : levelTail Z b t₀.re F ≤ ‖offLineWeight b (Z.mult t₀) t₀‖ / 12) {V : ℝ} (hV : 0 ≤ V)
    (hG : depthDeficit Z b t₀.re V ≤ ‖offLineWeight b (Z.mult t₀) t₀‖ / 12)
    (hE0 : Real.exp ((R - t₀.re) * (V + 4 * π / g)) * depthExcess Z b t₀.re 0 ≤
      ‖offLineWeight b (Z.mult t₀) t₀‖ / 12)
    (hM : 2 * onLineMassOf Z b + 3 * ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ <
      ‖offLineWeight b (Z.mult t₀) t₀‖ / 4 * Real.exp ((t₀.re - 1 / 2) * V)) :
    ∃ v : ℝ, V ≤ v ∧ v ≤ V + 4 * π / g ∧
      2 * (lagStructure Z b 0).re < ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  have hv4 : 0 ≤ V + 4 * π / g := by positivity
  have hE : depthExcess Z b t₀.re (V + 4 * π / g) ≤ ‖offLineWeight b (Z.mult t₀) t₀‖ / 12 :=
    (depthExcess_le_exp_mul_depthExcess_zero Z hZ hb hbs htop t₀.re hv4).2.trans hE0
  exact exists_minor_fails_of_level Z hZ hb hbs ht₀ hF ht₀F hg hsep htail hV hG hE hM

/-! ### 4. Depth-antitonicity of the explicit visibility lags and horizon escape laws for `ζ` -/

/-- `recordLag w a σ` is antitone in the depth `σ > 0`. -/
theorem recordLag_anti_depth (w a : ℝ) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ : σ₁ ≤ σ₂) :
    recordLag w a σ₂ ≤ recordLag w a σ₁ := by
  unfold recordLag
  have h1 : 4 / σ₂ ≤ 4 / σ₁ := div_le_div_of_nonneg_left (by norm_num) hσ₁ hσ
  have h2 : 0 ≤ 13 * π * (recordOrder w a : ℝ) + 4 := by positivity
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  linarith

/-- `oneParamLag w η δ` is antitone in the depth `δ > 0`. -/
theorem oneParamLag_anti_depth (w η : ℝ) {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ : δ₁ ≤ δ₂) :
    oneParamLag w η δ₂ ≤ oneParamLag w η δ₁ := by
  unfold oneParamLag
  have h1 : 8 / δ₂ ≤ 8 / δ₁ := div_le_div_of_nonneg_left (by norm_num) hδ₁ hδ
  have h2 : 0 ≤ 13 * π * (oneParamOrder w η : ℝ) + 4 +
      |Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2))| := by positivity
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  linarith

/-- `zoneLag w η μ δ` is antitone in the depth `δ > 0`. -/
theorem zoneLag_anti_depth (w η μ : ℝ) {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ : δ₁ ≤ δ₂) :
    zoneLag w η μ δ₂ ≤ zoneLag w η μ δ₁ := by
  unfold zoneLag
  have hrec := recordLag_anti_depth w (2 * η ^ 2 * Real.exp (-μ)) (half_pos hδ₁)
    (div_le_div_of_nonneg_right hδ (by norm_num))
  have h1 : 2 / δ₂ ≤ 2 / δ₁ := div_le_div_of_nonneg_left (by norm_num) hδ₁ hδ
  have h2 : 0 ≤ |Real.log (80 * Real.log (180 * recordHeightOf w (2 * η ^ 2 * Real.exp (-μ))) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2))| := abs_nonneg _
  exact add_le_add hrec (mul_le_mul_of_nonneg_right h1 h2)

/-- `nearTopLag w γ₀ δ` is antitone in the depth `δ > 0`. -/
theorem nearTopLag_anti_depth (w γ₀ : ℝ) {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ : δ₁ ≤ δ₂) :
    nearTopLag w γ₀ δ₂ ≤ nearTopLag w γ₀ δ₁ := by
  unfold nearTopLag
  have h1 : 8 / δ₂ ≤ 8 / δ₁ := div_le_div_of_nonneg_left (by norm_num) hδ₁ hδ
  have h2 : 0 ≤ 13 * π * (nearTopOrder w γ₀ : ℝ) + 4 +
      |Real.log (160 * Real.log (180 * recordHeightEnvelope w γ₀) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2)| := by positivity
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  linarith

/-- For any zeroconfiguration `Z` and height bound `H`, the set of shifted zeros `z` with
`½ + z ∈ Z.carrier` and `|Im z| ≤ H` is finite. -/
theorem finite_shifted_carrier_abs_im_le (Z : ZeroConfig) (H : ℝ) :
    {z : ℂ | (1 / 2 + z) ∈ Z.carrier ∧ |z.im| ≤ H}.Finite := by
  have hfin := (Z.finite_window (-|H| - 1) |H|).image fun ρ : ℂ => ρ - 1 / 2
  refine hfin.subset fun z hz => ?_
  refine ⟨1 / 2 + z, ⟨hz.1, ?_, ?_⟩, by ring⟩
  · have e : (1 / 2 + z).im = z.im := by simp
    rw [e]
    linarith [neg_abs_le z.im, le_abs_self H, hz.2]
  · have e : (1 / 2 + z).im = z.im := by simp
    rw [e]
    exact (le_abs_self z.im).trans (hz.2.trans (le_abs_self H))

/-- The uniform horizon `boxHorizon w H` of all zeros of `ζ` in the height box `|Im z| ≤ H`. -/
def boxHorizon (w H : ℝ) : ℝ :=
  by
    classical
    exact (insert (0 : ℂ) (finite_shifted_carrier_abs_im_le zetaZeroConfig H).toFinset).sup'
      ⟨0, Finset.mem_insert_self 0 _⟩
      (fun u => max 0 (if (1 / 2 + u) ∈ zetaZeroConfig.carrier ∧ |u.im| ≤ H
        then oneParamHorizon w u else 0))

/-- Every zero `½ + z` of `ζ` with `|Im z| ≤ H` has `oneParamHorizon w z ≤ boxHorizon w H`. -/
theorem oneParamHorizon_le_boxHorizon (w H : ℝ) {z : ℂ}
    (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier) (him : |z.im| ≤ H) :
    oneParamHorizon w z ≤ boxHorizon w H := by
  classical
  unfold boxHorizon
  set S := (finite_shifted_carrier_abs_im_le zetaZeroConfig H).toFinset
  have hzS : z ∈ S := (Set.Finite.mem_toFinset _).mpr ⟨hz, him⟩
  refine le_trans ?_ (Finset.le_sup'
    (f := fun u => max 0 (if (1 / 2 + u) ∈ zetaZeroConfig.carrier ∧ |u.im| ≤ H
      then oneParamHorizon w u else 0))
    (Finset.mem_insert_of_mem hzS))
  rw [if_pos ⟨hz, him⟩]
  exact le_max_right 0 _

/-- **Height and amplitude escape law for `P_v`.** Let `h_w(−iz) ≠ 0` at every zero `½ + z` of `ζ`,
and let `P_v ≥ 0` on `[0, V]` for `V ≥ max (oneParamHorizon w z₀) (boxHorizon w H)`. Then there is
a zero `½ + z` of `ζ` that is strictly deeper (`Re z > Re z₀ + 1/V`), strictly outside the height
box (`|Im z| > H`), and in the small-amplitude tail at fixed depth `Re z₀`
(`V < oneParamLag w ‖h_w(−iz)‖ (Re z₀)`). -/
theorem one_param_horizon_law_forces_height_and_amplitude_escape {w H : ℝ} (hw : 0 < w)
    (hgen : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → paperFT (scaledBump w) (-(I * z)) ≠ 0)
    {V : ℝ} (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hV₀ : oneParamHorizon w z₀ ≤ V) (hVH : boxHorizon w H ≤ V) :
    ∃ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ z₀.re + 1 / V < z.re ∧
      H < |z.im| ∧ V < oneParamHorizon w z ∧
      V < oneParamLag w ‖paperFT (scaledBump w) (-(I * z))‖ z₀.re := by
  obtain ⟨z, hz, hlt, hVz⟩ := one_param_horizon_law hw hgen hpos hz₀ hre₀ hV₀
  have hVpos : 0 < V := lt_of_lt_of_le hw ((le_oneParamLag hw _ hre₀).trans hV₀)
  have h1V : 0 < 1 / V := one_div_pos.mpr hVpos
  have him : H < |z.im| := by
    by_contra hle
    push Not at hle
    have hbox := (oneParamHorizon_le_boxHorizon w H hz hle).trans hVH
    linarith
  have hamp : V < oneParamLag w ‖paperFT (scaledBump w) (-(I * z))‖ z₀.re :=
    hVz.trans_le (oneParamLag_anti_depth w _ hre₀ (by linarith))
  exact ⟨z, hz, hlt, him, hVz, hamp⟩

/-- **Visibility under a high-ordinate depth bound.** If `½ + z₀` is a zero of `ζ` right of the
line and every zero `½ + z` with `|Im z| > H` satisfies `Re z ≤ Re z₀ + 1/V` (in particular if all
zeros above height `H` have `Re ρ − ½ ≤ Re z₀`), then for `V ≥ max (oneParamHorizon w z₀) (boxHorizon w H)`,
some lag `v ∈ [0, V]` has `P_v < 0`. -/
theorem one_param_visible_of_height_cutoff {w H : ℝ} (hw : 0 < w)
    (hgen : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → paperFT (scaledBump w) (-(I * z)) ≠ 0)
    {V : ℝ} {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hV₀ : oneParamHorizon w z₀ ≤ V) (hVH : boxHorizon w H ≤ V)
    (hhigh : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → H < |z.im| →
      z.re ≤ z₀.re + 1 / V) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  by_contra hneg
  push Not at hneg
  obtain ⟨z, hz, hlt, him, -, -⟩ :=
    one_param_horizon_law_forces_height_and_amplitude_escape hw hgen hneg hz₀ hre₀ hV₀ hVH
  linarith [hhigh z hz him]

/-- **Prime-window negativity under a high-ordinate depth bound.** For `2w < log 2`, under the
hypotheses of `one_param_visible_of_height_cutoff`, some prime-window functional
`Re lagPrimeWindowRHS(v, w, ·)` is negative at a lag `v ∈ [0, V]`. -/
theorem one_param_primeWindow_neg_of_height_cutoff {w H : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2)
    (hgen : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → paperFT (scaledBump w) (-(I * z)) ≠ 0)
    {V : ℝ} {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hV₀ : oneParamHorizon w z₀ ≤ V) (hVH : boxHorizon w H ≤ V)
    (hhigh : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → H < |z.im| →
      z.re ≤ z₀.re + 1 / V) :
    ∃ v ∈ Icc (0 : ℝ) V, (lagPrimeWindowRHS v w (EF.weilTest
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re < 0 := by
  obtain ⟨v, hv, hneg⟩ := one_param_visible_of_height_cutoff hw hgen hz₀ hre₀ hV₀ hVH hhigh
  refine ⟨v, hv, ?_⟩
  rwa [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv.1] at hneg

/-- The uniform zone horizon `zoneBoxHorizon w μ H` of all zeros of `ζ` in `|Im z| ≤ H`. -/
def zoneBoxHorizon (w μ H : ℝ) : ℝ :=
  by
    classical
    exact (insert (0 : ℂ) (finite_shifted_carrier_abs_im_le zetaZeroConfig H).toFinset).sup'
      ⟨0, Finset.mem_insert_self 0 _⟩
      (fun u => max 0 (if (1 / 2 + u) ∈ zetaZeroConfig.carrier ∧ |u.im| ≤ H
        then zoneHorizon w μ u else 0))

theorem zoneHorizon_le_zoneBoxHorizon (w μ H : ℝ) {z : ℂ}
    (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier) (him : |z.im| ≤ H) :
    zoneHorizon w μ z ≤ zoneBoxHorizon w μ H := by
  classical
  unfold zoneBoxHorizon
  set S := (finite_shifted_carrier_abs_im_le zetaZeroConfig H).toFinset
  have hzS : z ∈ S := (Set.Finite.mem_toFinset _).mpr ⟨hz, him⟩
  refine le_trans ?_ (Finset.le_sup'
    (f := fun u => max 0 (if (1 / 2 + u) ∈ zetaZeroConfig.carrier ∧ |u.im| ≤ H
      then zoneHorizon w μ u else 0))
    (Finset.mem_insert_of_mem hzS))
  rw [if_pos ⟨hz, him⟩]
  exact le_max_right 0 _

/-- **Zone horizon height-and-amplitude escape law.** Across a zone of width `μ/V` (`μ > 0`),
positivity of `P_v` on `[0, V]` for `V ≥ max (zoneHorizon w μ z₀) (zoneBoxHorizon w μ H)` forces a
zero `½ + z` with `Re z > Re z₀ + μ/V`, `|Im z| > H`, and
`V < zoneLag w ‖h_w(−iz)‖ μ (Re z₀)`. -/
theorem zone_horizon_law_forces_height_and_amplitude_escape {w μ H : ℝ} (hw : 0 < w)
    (hgen : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → 0 < z.re →
      paperFT (scaledBump w) (-(I * z)) ≠ 0) (hμ : 0 < μ)
    {V : ℝ} (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hV₀ : zoneHorizon w μ z₀ ≤ V) (hVH : zoneBoxHorizon w μ H ≤ V) :
    ∃ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ z₀.re + μ / V < z.re ∧
      H < |z.im| ∧ V < zoneHorizon w μ z ∧
      V < zoneLag w ‖paperFT (scaledBump w) (-(I * z))‖ μ z₀.re := by
  obtain ⟨z, hz, hlt, hVz⟩ := one_param_zone_horizon_law hw hgen hμ hpos hz₀ hre₀ hV₀
  have hVpos : 0 < V := lt_of_lt_of_le hw ((le_zoneLag hw _ μ hre₀).trans hV₀)
  have hμV : 0 < μ / V := div_pos hμ hVpos
  have him : H < |z.im| := by
    by_contra hle
    push Not at hle
    have hbox := (zoneHorizon_le_zoneBoxHorizon w μ H hz hle).trans hVH
    linarith
  have hamp : V < zoneLag w ‖paperFT (scaledBump w) (-(I * z))‖ μ z₀.re :=
    hVz.trans_le (zoneLag_anti_depth w _ μ hre₀ (by linarith))
  exact ⟨z, hz, hlt, him, hVz, hamp⟩

/-! ### 5. The modulated horizon law (amplitude-free polylogarithmic lag) -/

/-- A shifted zero `z` is in the high-ordinate modulated regime for width `w` when `Im z ≥ T_w`
and its reflected tail is dominated by the center amplitude `a_w`. -/
def ModulatedAdmissible (w : ℝ) (z : ℂ) : Prop :=
  nearTopHeight w ≤ z.im ∧
    1280 * Real.log (180 * recordHeightEnvelope w z.im) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 ≤
        centerAmplitude w ^ 2 / (2 * Real.exp 1) * (1 + z.im) ^ 4

/-- The modulated polylogarithmic horizon `V_w(Im z, Re z)` of a zero `½ + z`. Unlike
`oneParamHorizon`, it depends only on the ordinate `Im z` and depth `Re z`, never on the
unmodulated transform value `|h_w(−iz)|`. -/
def modulatedHorizon (w : ℝ) (z : ℂ) : ℝ :=
  nearTopLag w z.im z.re

/-- **Modulated horizon law.** Suppose every zero `½ + z` right of the line above `z₀` is
modulated-admissible (when reflected into the upper half-plane via `conj`) and the modulated
difference tests are nonnegative on `[0, V]`. Then from any modulated-admissible zero `z₀` with
`modulatedHorizon w z₀ ≤ V`, in fewer than `⌈V⌉` steps one reaches a zero `½ + z` with
`Re z > Re z₀ + 1/V` and `V < modulatedHorizon w z ≤ nearTopLag w (Im z) (Re z₀)`. -/
theorem modulated_horizon_law {w V : ℝ} (hw : 0 < w)
    (hadm : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → 0 < z.re →
      ModulatedAdmissible w (if 0 ≤ z.im then z else conj z))
    (hpos : ∀ γ : ℝ, ∀ v ∈ Icc (0 : ℝ) V,
      0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w γ) v (-1))
        (twoBump (modScaledBump w γ) v (-1))).re)
    {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hadm₀ : ModulatedAdmissible w z₀) (hV₀ : modulatedHorizon w z₀ ≤ V) :
    ∃ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ ModulatedAdmissible w z ∧
      z₀.re + 1 / V < z.re ∧ V < modulatedHorizon w z ∧
      V < nearTopLag w z.im z₀.re := by
  by_contra hcon
  push Not at hcon
  have hVpos : 0 < V := lt_of_lt_of_le hw ((le_nearTopLag hw _ hre₀).trans hV₀)
  have h1V : 0 < 1 / V := one_div_pos.mpr hVpos
  have hsymm : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier →
      (1 / 2 + conj z) ∈ zetaZeroConfig.carrier := fun z hz => by
    have hc := conj_mem_zetaZeroConfig hz
    have e : conj (1 / 2 + z) = 1 / 2 + conj z := by apply Complex.ext <;> simp
    rwa [e] at hc
  have hstep : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → 0 < z.re →
      ModulatedAdmissible w z → modulatedHorizon w z ≤ V →
      ∃ z' : ℂ, (1 / 2 + z') ∈ zetaZeroConfig.carrier ∧ ModulatedAdmissible w z' ∧
        z.re + 1 / V < z'.re := fun z hz hre hadmz hVz => by
    obtain ⟨ρ, hρ, hlt⟩ := zeta_depth_gap_of_lag_positivity hw hz hre hadmz.1 hadmz.2 hVz
      (hpos z.im)
    set u : ℂ := ρ - 1 / 2
    have hu : (1 / 2 + u) ∈ zetaZeroConfig.carrier := by
      rwa [show (1 / 2 : ℂ) + u = ρ by simp [u]]
    have hure : z.re + 1 / V < u.re := by simpa [u] using hlt
    have hure0 : 0 < u.re := by linarith
    set z' : ℂ := if 0 ≤ u.im then u else conj u
    have hz' : (1 / 2 + z') ∈ zetaZeroConfig.carrier := by
      dsimp [z']; split_ifs
      · exact hu
      · exact hsymm u hu
    have hz're : z'.re = u.re := by dsimp [z']; split_ifs <;> simp
    exact ⟨z', hz', hadm u hu hure0, by linarith⟩
  have hchain : ∀ n : ℕ, ∃ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧
      ModulatedAdmissible w z ∧ z₀.re + n / V ≤ z.re ∧ modulatedHorizon w z ≤ V := by
    intro n
    induction n with
    | zero => exact ⟨z₀, hz₀, hadm₀, by simp, hV₀⟩
    | succ n ih =>
      obtain ⟨z, hz, hadmz, hzre, hzV⟩ := ih
      have hn : 0 ≤ (n : ℝ) / V := by positivity
      have hre : 0 < z.re := by linarith
      obtain ⟨z', hz', hadmz', hlt⟩ := hstep z hz hre hadmz hzV
      have hgt : z₀.re + 1 / V < z'.re := by linarith
      have hz'V : modulatedHorizon w z' ≤ V := by
        by_contra hltV
        push Not at hltV
        have hamp : V < nearTopLag w z'.im z₀.re :=
          hltV.trans_le (nearTopLag_anti_depth w _ hre₀ (by linarith))
        exact absurd hamp (not_lt.mpr (hcon z' hz' hadmz' hgt hltV))
      refine ⟨z', hz', hadmz', ?_, hz'V⟩
      push_cast; rw [add_div]; linarith
  obtain ⟨z, hz, -, hzre, -⟩ := hchain ⌈V⌉₊
  have hstrip := zetaZeroConfig.strip _ hz
  have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
  have h1 : (1 : ℝ) ≤ (⌈V⌉₊ : ℝ) / V := by
    rw [le_div_iff₀ hVpos, one_mul]; exact Nat.le_ceil V
  linarith [hstrip.2]

end GaloisForLFunctions.SquareRootThreshold
