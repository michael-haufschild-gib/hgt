/-
# Böttcher tower — continuity of the Green's function up to `J_c`

The dynamical Green's function `G_c = greenFunctionDyn c` is **continuous on all of `ℂ`** — in
particular `G_c → 0` at every Julia-set point `z₀ ∈ J_c` (since `G_c = 0` on `K_c`). This is the
boundary regularity (`D1`) that supplies `‖φ_c‖ ≥ 1` for the dendrite natural-boundary engine
(`NaturalBoundary.no_unit_min_of_analytic`).

Mechanism: `G_c = lim_n 2⁻ⁿ log⁺‖f_c^[n]‖`, a series of **continuous** functions
(`greenApproxPlus`) whose consecutive differences are bounded **uniformly in `z`** by
`log(1+‖c‖)·2⁻⁽ⁿ⁺¹⁾` — from the cocycle estimate
`|log⁺‖w²+c‖ − 2 log⁺‖w‖| ≤ log(1+‖c‖)` (no escape-regime restriction). A uniformly convergent
series of continuous functions is continuous (`continuous_tsum`), and the limit is `G_c` pointwise.

New file (hRigid connected lane); consumes `BasinBranching`/`GreenFunction`.
-/
import GaloisForLFunctions.Bottcher.BasinBranching

open Filter Topology Metric

namespace Bottcher

/-- **Cocycle estimate (uniform, no regime restriction).** `|log⁺‖w²+c‖ − 2·log⁺‖w‖| ≤ log(1+‖c‖)`,
where `log⁺ x = log(max x 1)`. Both `max(‖w²+c‖,1)` and `max(‖w‖,1)²` are squeezed within a factor
`(1+‖c‖)` of each other, so their logs differ by at most `log(1+‖c‖)`. -/
theorem abs_logMax_quadratic_sub_two_logMax (c w : ℂ) :
    |Real.log (max ‖quadratic c w‖ 1) - 2 * Real.log (max ‖w‖ 1)| ≤ Real.log (1 + ‖c‖) := by
  have hcnn : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hA1 : (1 : ℝ) ≤ max ‖quadratic c w‖ 1 := le_max_right _ _
  have hB1 : (1 : ℝ) ≤ max ‖w‖ 1 := le_max_right _ _
  have hB1sq : (1 : ℝ) ≤ max ‖w‖ 1 ^ (2 : ℕ) := one_le_pow₀ hB1
  have hApos : (0 : ℝ) < max ‖quadratic c w‖ 1 := lt_of_lt_of_le one_pos hA1
  have hBsqpos : (0 : ℝ) < max ‖w‖ 1 ^ (2 : ℕ) := lt_of_lt_of_le one_pos hB1sq
  have hfac : (0 : ℝ) < 1 + ‖c‖ := by linarith
  -- key norm facts
  have hquad : ‖quadratic c w‖ ≤ ‖w‖ ^ (2 : ℕ) + ‖c‖ := by
    unfold quadratic
    calc ‖w ^ (2 : ℕ) + c‖ ≤ ‖w ^ (2 : ℕ)‖ + ‖c‖ := norm_add_le _ _
      _ = ‖w‖ ^ (2 : ℕ) + ‖c‖ := by rw [norm_pow]
  have hrev : ‖w‖ ^ (2 : ℕ) ≤ ‖quadratic c w‖ + ‖c‖ := by
    unfold quadratic
    have : ‖w‖ ^ (2 : ℕ) = ‖w ^ (2 : ℕ)‖ := by rw [norm_pow]
    rw [this]
    calc ‖w ^ (2 : ℕ)‖ = ‖(w ^ (2 : ℕ) + c) - c‖ := by ring_nf
      _ ≤ ‖w ^ (2 : ℕ) + c‖ + ‖c‖ := norm_sub_le _ _
  have hmaxsq : max ‖w‖ 1 ^ (2 : ℕ) = max (‖w‖ ^ (2 : ℕ)) 1 := by
    rcases le_total ‖w‖ 1 with h | h
    · rw [max_eq_right h, one_pow, max_eq_right (by nlinarith [norm_nonneg w])]
    · rw [max_eq_left h, max_eq_left (by nlinarith)]
  -- Claim 1: A ≤ B² (1 + ‖c‖)
  have hclaim1 : max ‖quadratic c w‖ 1 ≤ max ‖w‖ 1 ^ (2 : ℕ) * (1 + ‖c‖) := by
    rw [hmaxsq]
    have h1 : max ‖quadratic c w‖ 1 ≤ max (‖w‖ ^ (2 : ℕ)) 1 + ‖c‖ := by
      apply max_le
      · calc ‖quadratic c w‖ ≤ ‖w‖ ^ (2 : ℕ) + ‖c‖ := hquad
          _ ≤ max (‖w‖ ^ (2 : ℕ)) 1 + ‖c‖ := by gcongr; exact le_max_left _ _
      · have : (1 : ℝ) ≤ max (‖w‖ ^ (2 : ℕ)) 1 := le_max_right _ _; linarith
    calc max ‖quadratic c w‖ 1 ≤ max (‖w‖ ^ (2 : ℕ)) 1 + ‖c‖ := h1
      _ ≤ max (‖w‖ ^ (2 : ℕ)) 1 * (1 + ‖c‖) := by
          have : (1 : ℝ) ≤ max (‖w‖ ^ (2 : ℕ)) 1 := le_max_right _ _; nlinarith
  -- Claim 2: B² ≤ A (1 + ‖c‖)
  have hclaim2 : max ‖w‖ 1 ^ (2 : ℕ) ≤ max ‖quadratic c w‖ 1 * (1 + ‖c‖) := by
    rw [hmaxsq]
    have h1 : max (‖w‖ ^ (2 : ℕ)) 1 ≤ max ‖quadratic c w‖ 1 + ‖c‖ := by
      apply max_le
      · calc ‖w‖ ^ (2 : ℕ) ≤ ‖quadratic c w‖ + ‖c‖ := hrev
          _ ≤ max ‖quadratic c w‖ 1 + ‖c‖ := by gcongr; exact le_max_left _ _
      · have : (1 : ℝ) ≤ max ‖quadratic c w‖ 1 := le_max_right _ _; linarith
    calc max (‖w‖ ^ (2 : ℕ)) 1 ≤ max ‖quadratic c w‖ 1 + ‖c‖ := h1
      _ ≤ max ‖quadratic c w‖ 1 * (1 + ‖c‖) := by
          have : (1 : ℝ) ≤ max ‖quadratic c w‖ 1 := le_max_right _ _; nlinarith
  -- turn the two bounds into log bounds
  have hlogfac : Real.log (1 + ‖c‖) = Real.log (1 + ‖c‖) := rfl
  have hup : Real.log (max ‖quadratic c w‖ 1) - 2 * Real.log (max ‖w‖ 1) ≤ Real.log (1 + ‖c‖) := by
    have := Real.log_le_log hApos hclaim1
    rw [Real.log_mul (ne_of_gt hBsqpos) (ne_of_gt hfac), Real.log_pow] at this
    push_cast at this
    linarith
  have hlo : 2 * Real.log (max ‖w‖ 1) - Real.log (max ‖quadratic c w‖ 1) ≤ Real.log (1 + ‖c‖) := by
    have := Real.log_le_log hBsqpos hclaim2
    rw [Real.log_mul (ne_of_gt hApos) (ne_of_gt hfac), Real.log_pow] at this
    push_cast at this
    linarith
  rw [abs_sub_le_iff]
  exact ⟨hup, by linarith⟩

/-- Uniform geometric bound on the consecutive differences of `greenApproxPlus`, in `z`. -/
theorem abs_greenApproxPlus_succ_sub (c z : ℂ) (n : ℕ) :
    |greenApproxPlus c z (n + 1) - greenApproxPlus c z n|
      ≤ Real.log (1 + ‖c‖) * (1 / 2) ^ (n + 1) := by
  have hwrite : greenApproxPlus c z (n + 1) - greenApproxPlus c z n
      = (2 ^ (n + 1) : ℝ)⁻¹ *
        (Real.log (max ‖quadratic c ((quadratic c)^[n] z)‖ 1)
          - 2 * Real.log (max ‖(quadratic c)^[n] z‖ 1)) := by
    unfold greenApproxPlus
    rw [Function.iterate_succ', Function.comp_apply]
    rw [pow_succ]
    field_simp
  rw [hwrite, abs_mul]
  have h2 : |(2 ^ (n + 1) : ℝ)⁻¹| = (1 / 2 : ℝ) ^ (n + 1) := by
    rw [abs_of_pos (by positivity), ← inv_pow]; norm_num
  rw [h2, mul_comm]
  gcongr
  exact abs_logMax_quadratic_sub_two_logMax c ((quadratic c)^[n] z)

/-- Each `greenApproxPlus c · n` is continuous (polynomial iterate, `log` of `max(‖·‖,1) ≥ 1`). -/
theorem continuous_greenApproxPlus (c : ℂ) (n : ℕ) :
    Continuous (fun z => greenApproxPlus c z n) := by
  unfold greenApproxPlus
  have hiter : Continuous (quadratic c)^[n] := by
    have hq : Continuous (quadratic c) := by unfold quadratic; fun_prop
    exact hq.iterate n
  refine continuous_const.mul (Continuous.log ((hiter.norm).max continuous_const) ?_)
  intro z
  exact ne_of_gt (lt_of_lt_of_le one_pos (le_max_right _ _))

/-- **The continuous representative of `G_c`.** `greenApproxPlus c z 0 + ∑ₙ (gₙ₊₁ − gₙ)`, a uniformly
convergent series of continuous functions. -/
noncomputable def greenContinuous (c z : ℂ) : ℝ :=
  greenApproxPlus c z 0 + ∑' n, (greenApproxPlus c z (n + 1) - greenApproxPlus c z n)

theorem summable_green_diff_bound (c : ℂ) :
    Summable (fun n => Real.log (1 + ‖c‖) * (1 / 2 : ℝ) ^ (n + 1)) := by
  apply Summable.mul_left
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
    (add_left_injective 1)

/-- **`greenContinuous` is continuous on `ℂ`** (uniform limit of continuous functions). -/
theorem continuous_greenContinuous (c : ℂ) : Continuous (greenContinuous c) := by
  unfold greenContinuous
  refine (continuous_greenApproxPlus c 0).add ?_
  refine continuous_tsum (fun n => (continuous_greenApproxPlus c (n + 1)).sub
    (continuous_greenApproxPlus c n)) (summable_green_diff_bound c) (fun n z => ?_)
  rw [Real.norm_eq_abs]
  exact abs_greenApproxPlus_succ_sub c z n

/-- `greenApproxPlus c z ·` converges to `greenContinuous c z` (telescoping + summability). -/
theorem greenApproxPlus_tendsto_greenContinuous (c z : ℂ) :
    Tendsto (fun N => greenApproxPlus c z N) atTop (𝓝 (greenContinuous c z)) := by
  have hsummable : Summable (fun n => greenApproxPlus c z (n + 1) - greenApproxPlus c z n) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_green_diff_bound c)
    rw [Real.norm_eq_abs]; exact abs_greenApproxPlus_succ_sub c z n
  have htel : ∀ N, greenApproxPlus c z N
      = greenApproxPlus c z 0 + ∑ n ∈ Finset.range N,
          (greenApproxPlus c z (n + 1) - greenApproxPlus c z n) := by
    intro N; rw [Finset.sum_range_sub (fun n => greenApproxPlus c z n) N]; ring
  unfold greenContinuous
  rw [show (fun N => greenApproxPlus c z N)
      = (fun N => greenApproxPlus c z 0 + ∑ n ∈ Finset.range N,
          (greenApproxPlus c z (n + 1) - greenApproxPlus c z n)) from funext htel]
  exact tendsto_const_nhds.add hsummable.hasSum.tendsto_sum_nat

/-- **`greenContinuous = greenFunctionDyn`.** The continuous limit is the genuine Green's function:
`0` on `K_c`, `greenLimit` on the basin. -/
theorem greenContinuous_eq_greenFunctionDyn (c z : ℂ) :
    greenContinuous c z = greenFunctionDyn c z := by
  refine tendsto_nhds_unique (greenApproxPlus_tendsto_greenContinuous c z) ?_
  unfold greenFunctionDyn
  by_cases h : z ∈ filledJulia c
  · rw [if_pos h]; exact greenApproxPlus_tendsto_zero_of_mem h
  · rw [if_neg h]
    -- on the basin, greenApproxPlus agrees with greenApprox eventually, which → greenLimit
    have hbasin := greenApprox_tendsto_basin h
    refine hbasin.congr' ?_
    -- greenApprox c z N = greenApproxPlus c z N eventually (once ‖f^N z‖ ≥ 1)
    obtain ⟨N₀, hN₀⟩ := exists_orbit_gt h (max 2 ‖c‖)
    have hc : ‖c‖ ≤ ‖(quadratic c)^[N₀] z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN₀)
    have hz2 : 2 < ‖(quadratic c)^[N₀] z‖ := lt_of_le_of_lt (le_max_left _ _) hN₀
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hge : (1 : ℝ) ≤ ‖(quadratic c)^[N] z‖ := by
      have hk := norm_le_orbit hc hz2 (N - N₀)
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hN] at hk
      linarith
    unfold greenApprox greenApproxPlus
    rw [max_eq_left hge]

/-- **The Green's function is continuous on `ℂ`.** -/
theorem continuous_greenFunctionDyn (c : ℂ) : Continuous (greenFunctionDyn c) :=
  (continuous_greenContinuous c).congr (fun z => greenContinuous_eq_greenFunctionDyn c z)

/-- **`G_c → 0` at every filled-Julia point** (in particular at every Julia point `z₀ ∈ J_c`):
boundary regularity `D1`, supplying `‖φ_c‖ → 1` at `J_c` for the dendrite natural-boundary engine. -/
theorem tendsto_greenFunctionDyn_boundary {c z₀ : ℂ} (hz₀ : z₀ ∈ filledJulia c) :
    Tendsto (greenFunctionDyn c) (𝓝 z₀) (𝓝 0) := by
  have h0 : greenFunctionDyn c z₀ = 0 := (greenFunctionDyn_eq_zero_iff c z₀).mpr hz₀
  have hca : Tendsto (greenFunctionDyn c) (𝓝 z₀) (𝓝 (greenFunctionDyn c z₀)) :=
    (continuous_greenFunctionDyn c).continuousAt
  rwa [h0] at hca

/-- **`∞`-asymptotic of the Green's function** `G_c(z) − log‖z‖ → 0` as `z → ∞` (Robin constant `0`,
`cap(K_c) = 1`). The difference of two Green's functions then `→ 0` at `∞` — the input the
max-principle uniqueness (`K_{c₁}=K_{c₂} ⟹ G_{c₁}=G_{c₂}`, brick E) needs at the `∞` end. -/
theorem tendsto_greenLimit_sub_log (c : ℂ) :
    Tendsto (fun z => greenLimit c z - Real.log ‖z‖) (Bornology.cobounded ℂ) (𝓝 0) := by
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (Bornology.cobounded ℂ) atTop :=
    tendsto_norm_cobounded_atTop
  have hsq : Tendsto (fun z : ℂ => ‖z‖ ^ (2 : ℕ)) (Bornology.cobounded ℂ) atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp hnorm
  have hbd : Tendsto (fun z : ℂ => 2 * ‖c‖ / ‖z‖ ^ (2 : ℕ)) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsq
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hnorm.eventually_gt_atTop (max 2 ‖c‖)] with z hz
  have hc : ‖c‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz)
  have hz2 : 2 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  rw [Real.norm_eq_abs]
  exact greenLimit_abs_sub_log hc hz2

end Bottcher
