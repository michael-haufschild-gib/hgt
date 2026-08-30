/-
# Böttcher tower — Brolin: constructed GAP-A measure core

This module is part of the split Brolin/Riesz-measure interface. Import
`GaloisForLFunctions.Bottcher.Brolin` for the full public surface.
-/
import GaloisForLFunctions.Bottcher.Brolin.TargetShifted

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance gapAMuCoreLocalInst1 : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Zero-target arbitrary-pullback potential identity, stated through the
arbitrary-target finite measure. -/
theorem neg_logPotential_preBrolinMeasureAt_zero_eq_greenApprox {c z : ℂ} {n : ℕ}
    (hz : (quadratic c)^[n] z ≠ 0) :
    - logPotential (preBrolinMeasureAt c 0 n) z = greenApprox c z n := by
  rw [preBrolinMeasureAt_zero]
  exact neg_logPotential_preBrolinMeasure_eq_greenApprox hz

/-- Zero-target arbitrary-pullback Cauchy identity, stated through the
arbitrary-target finite measure. -/
theorem integral_cauchy_preBrolinMeasureAt_zero_eq_derivative_div {c z : ℂ} {n : ℕ}
    (hz : (quadratic c)^[n] z ≠ 0) :
    ∫ ζ, (z - ζ)⁻¹ ∂preBrolinMeasureAt c 0 n =
      ((2 ^ n : ℝ)⁻¹ : ℂ) *
        ((quadraticPolyIterate c n).derivative.eval z / (quadratic c)^[n] z) := by
  rw [preBrolinMeasureAt_zero]
  exact integral_cauchy_preBrolinMeasure_eq_derivative_div hz

/-- Finite GAP-A convergence on the immediate escape region: the normalized
pre-Brolin potentials converge to the dynamical Green function. -/
theorem neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_escape {c z : ℂ}
    (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    Tendsto (fun n => - logPotential (preBrolinMeasure c n) z) atTop
      (𝓝 (greenFunctionDyn c z)) := by
  have hnotK : z ∉ filledJulia c := not_mem_filledJulia hc hz
  have hgreen : greenFunctionDyn c z = greenLimit c z := by
    simp [greenFunctionDyn, hnotK]
  rw [hgreen]
  refine (greenApprox_tendsto hc hz).congr' ?_
  exact Filter.Eventually.of_forall fun n =>
    (neg_logPotential_preBrolinMeasure_eq_greenApprox ((escape_regime_stable hc hz n).2)).symm

/-- For disconnected parameters, the filled Julia set is bounded away from the
critical point `0`.  This is the compactness input needed to control the
zero-target finite potentials on `K_c`. -/
theorem exists_pos_le_norm_on_filledJulia_of_disconnected {c : ℂ}
    (hc : Disconnected c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ filledJulia c, δ ≤ ‖z‖ := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  rcases (filledJulia c).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, ?_⟩
    intro z hz
    rw [hemp] at hz
    simp at hz
  · obtain ⟨z₀, hz₀mem, hz₀min⟩ :=
      (isCompact_filledJulia c).exists_isMinOn hne continuous_norm.continuousOn
    have hz₀ne : z₀ ≠ 0 := fun hz₀ => h0 (hz₀ ▸ hz₀mem)
    exact ⟨‖z₀‖, norm_pos_iff.mpr hz₀ne, fun z hz => hz₀min hz⟩

/-- On `K_c`, and for disconnected `c`, the signed rescaled logarithms
`2⁻ⁿ log ‖f_c^[n](z)‖` tend to zero.  The lower bound comes from the fact that
`0 ∉ K_c`; the upper bound is the standard filled-Julia escape disk. -/
theorem greenApprox_tendsto_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) :
    Tendsto (greenApprox c z) atTop (𝓝 0) := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    exists_pos_le_norm_on_filledJulia_of_disconnected (c := c) hc
  let M : ℝ := max 2 ‖c‖
  let B : ℝ := max |Real.log δ| |Real.log M|
  have hBnonneg : 0 ≤ B := by
    exact le_trans (abs_nonneg (Real.log δ)) (le_max_left _ _)
  have hpow : Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹) atTop (𝓝 0) := by
    simp_rw [← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero_norm' ?_ (by simpa using hpow.mul_const B)
  filter_upwards [eventually_ge_atTop 0] with n _hn
  have hzK : (quadratic c)^[n] z ∈ filledJulia c := filledJulia_forward hz n
  have hδn : δ ≤ ‖(quadratic c)^[n] z‖ := hδ _ hzK
  have hMn : ‖(quadratic c)^[n] z‖ ≤ M := by
    have hmem := filledJulia_subset_closedBall c hzK
    rwa [Metric.mem_closedBall, dist_zero_right] at hmem
  have hMpos : 0 < M := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  have hnormpos : 0 < ‖(quadratic c)^[n] z‖ :=
    lt_of_lt_of_le hδpos hδn
  have hlog_lower :
      Real.log δ ≤ Real.log ‖(quadratic c)^[n] z‖ :=
    Real.log_le_log hδpos hδn
  have hlog_upper :
      Real.log ‖(quadratic c)^[n] z‖ ≤ Real.log M :=
    Real.log_le_log hnormpos hMn
  have hlog_abs :
      |Real.log ‖(quadratic c)^[n] z‖| ≤ B := by
    rw [abs_le]
    constructor
    · exact le_trans
        (neg_le_neg (le_max_left |Real.log δ| |Real.log M|))
        (le_trans (neg_abs_le (Real.log δ)) hlog_lower)
    · exact le_trans hlog_upper
        (le_trans (le_abs_self (Real.log M))
          (le_max_right |Real.log δ| |Real.log M|))
  rw [Real.norm_eq_abs, greenApprox, abs_mul]
  rw [abs_of_nonneg (by positivity : 0 ≤ (2 ^ n : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left hlog_abs (by positivity)

/-- Finite zero-target pre-Brolin potentials vanish on `K_c` for disconnected
parameters.  This is the finite-level zero-potential boundary condition needed
for the hDisc Brolin/Riesz passage. -/
theorem neg_logPotential_preBrolinMeasure_tendsto_zero_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) :
    Tendsto (fun n => - logPotential (preBrolinMeasure c n) z) atTop
      (𝓝 0) := by
  refine (greenApprox_tendsto_zero_of_mem_filledJulia_of_disconnected
    hc hz).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with n _hn
  have hne : (quadratic c)^[n] z ≠ 0 := by
    intro hzero
    have h0K : (0 : ℂ) ∈ filledJulia c := by
      have hzK : (quadratic c)^[n] z ∈ filledJulia c := filledJulia_forward hz n
      rwa [hzero] at hzK
    exact ((disconnected_iff_zero_not_mem c).mp hc) h0K
  exact (neg_logPotential_preBrolinMeasure_eq_greenApprox hne).symm

/-- The compactness-selected zero-target subsequence preserves the finite
zero-potential boundary convergence on `K_c` in the disconnected case. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_tendsto_zero_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) :
    Tendsto
      (fun k =>
        - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
      atTop (𝓝 0) :=
  (neg_logPotential_preBrolinMeasure_tendsto_zero_filledJulia_of_disconnected
    hc hz).comp (brolinLimitSubsequence_tendsto_atTop c)

/-- The same boundary finite-potential convergence holds along the shifted
chosen subsequence.  This is the finite input needed to pass quadratic scaling
from level `ψ k + 1` back to level `ψ k`. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_succ_tendsto_zero_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) :
    Tendsto
      (fun k =>
        - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z)
      atTop (𝓝 0) :=
  (neg_logPotential_preBrolinMeasure_tendsto_zero_filledJulia_of_disconnected
    hc hz).comp
      ((tendsto_add_atTop_nat 1).comp
        (brolinLimitSubsequence_tendsto_atTop c))

/-- A point of `K_c` is never a zero-pullback atom when `c` is disconnected:
otherwise forward invariance would put the escaping critical point `0` in
`K_c`. -/
theorem iterate_ne_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) (n : ℕ) :
    (quadratic c)^[n] z ≠ 0 := by
  intro hzero
  have hzK : (quadratic c)^[n] z ∈ filledJulia c := filledJulia_forward hz n
  have h0K : (0 : ℂ) ∈ filledJulia c := by
    rwa [hzero] at hzK
  exact ((disconnected_iff_zero_not_mem c).mp hc) h0K

/-- Selected zero-target finite potentials are antipodally symmetric on `K_c`
in the disconnected case. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_neg_eq
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) (k : ℕ) :
    - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) (-z) =
      - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z := by
  exact neg_logPotential_preBrolinMeasure_neg_eq
    (c := c) (z := z) (n := brolinLimitSubsequence c k)
    (iterate_ne_zero_of_mem_filledJulia_of_disconnected hc hz
      (brolinLimitSubsequence c k))

/-- The shifted selected finite potentials are also antipodally symmetric on
`K_c` in the disconnected case. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_succ_neg_eq
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) (k : ℕ) :
    - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) (-z) =
      - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z := by
  exact neg_logPotential_preBrolinMeasure_neg_eq
    (c := c) (z := z) (n := brolinLimitSubsequence c k + 1)
    (iterate_ne_zero_of_mem_filledJulia_of_disconnected hc hz
      (brolinLimitSubsequence c k + 1))

/-- Along the selected finite levels, quadratic scaling has no atom obstruction
on `K_c` in the disconnected case. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_quadratic_eq_two_succ
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) (k : ℕ) :
    - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) (quadratic c z) =
      2 * (- logPotential
        (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z) := by
  exact neg_logPotential_preBrolinMeasure_quadratic_eq_two_succ
    (c := c) (z := z) (n := brolinLimitSubsequence c k)
    (iterate_ne_zero_of_mem_filledJulia_of_disconnected hc hz
      (brolinLimitSubsequence c k + 1))

/-- Finite quadratic scaling along the shifted compactness extraction, with
the successor level written as `shiftedBrolinIndex`. -/
theorem neg_logPotential_preBrolinMeasure_shiftedBase_quadratic_eq_two_shiftedIndex
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) (k : ℕ) :
    - logPotential
        (preBrolinMeasure c
          (brolinLimitSubsequence c (shiftedBrolinLimitSubsequence c k)))
        (quadratic c z) =
      2 * (- logPotential
        (preBrolinMeasure c (shiftedBrolinIndex c k)) z) := by
  simpa [shiftedBrolinIndex] using
    neg_logPotential_preBrolinMeasure_limitSubseq_quadratic_eq_two_succ
      (c := c) (z := z) hc hz (shiftedBrolinLimitSubsequence c k)

/-- The shifted finite quadratic-scaling identity has zero boundary limit on
the base side. -/
theorem neg_logPotential_preBrolinMeasure_shiftedBase_quadratic_tendsto_zero_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) :
    Tendsto
      (fun k =>
        - logPotential
          (preBrolinMeasure c
            (brolinLimitSubsequence c (shiftedBrolinLimitSubsequence c k)))
          (quadratic c z))
      atTop (𝓝 0) := by
  have hright :
      Tendsto
        (fun k =>
          2 * (- logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z))
        atTop (𝓝 0) := by
    have hzero :
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
          atTop (𝓝 0) :=
      (neg_logPotential_preBrolinMeasure_tendsto_zero_filledJulia_of_disconnected
        (c := c) (z := z) hc hz).comp (shiftedBrolinIndex_tendsto_atTop c)
    simpa using
      hzero.const_mul 2
  exact hright.congr' (by
    filter_upwards [eventually_ge_atTop 0] with k _hk
    exact
      (neg_logPotential_preBrolinMeasure_shiftedBase_quadratic_eq_two_shiftedIndex
        (c := c) (z := z) hc hz k).symm)

/-- Unsigned selected-level quadratic scaling on `K_c` in the disconnected
case. -/
theorem logPotential_preBrolinMeasure_limitSubseq_quadratic_eq_two_succ
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) (k : ℕ) :
    logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) (quadratic c z) =
      2 * logPotential
        (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z := by
  have h :=
    neg_logPotential_preBrolinMeasure_limitSubseq_quadratic_eq_two_succ
      (c := c) (z := z) hc hz k
  linarith

/-- A basin point has nonzero iterates eventually.  This removes the finite
root-collision obstruction from convergence statements: finitely many early
atoms do not affect the limit. -/
theorem eventually_iterate_ne_zero_of_not_mem_filledJulia {c z : ℂ}
    (hz : z ∉ filledJulia c) :
    ∀ᶠ n in atTop, (quadratic c)^[n] z ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_orbit_gt hz (max 2 ‖c‖)
  have hNc : ‖c‖ ≤ ‖(quadratic c)^[N] z‖ :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  have hN2 : 2 < ‖(quadratic c)^[N] z‖ :=
    lt_of_le_of_lt (le_max_left _ _) hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have htail := norm_le_orbit hNc hN2 (n - N)
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn] at htail
  intro hzero
  rw [hzero, norm_zero] at htail
  linarith

/-- A basin orbit eventually avoids any fixed target.  Once the orbit has
escaped past `max 2 ‖c‖` and `‖a‖`, the escape estimate keeps its norm above
`‖a‖`. -/
theorem eventually_iterate_ne_of_not_mem_filledJulia {c z : ℂ}
    (hz : z ∉ filledJulia c) (a : ℂ) :
    ∀ᶠ n in atTop, (quadratic c)^[n] z ≠ a := by
  obtain ⟨N, hN⟩ := exists_orbit_gt hz (max (max 2 ‖c‖) ‖a‖)
  have hNc : ‖c‖ ≤ ‖(quadratic c)^[N] z‖ :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hN2 : 2 < ‖(quadratic c)^[N] z‖ :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNa : ‖a‖ < ‖(quadratic c)^[N] z‖ :=
    lt_of_le_of_lt (le_max_right _ _) hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have htail := norm_le_orbit hNc hN2 (n - N)
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn] at htail
  intro ha
  rw [ha] at htail
  exact not_le_of_gt hNa htail

/-- If `w` is at least twice as large as `a`, then replacing `w` by `w-a`
changes `log ‖·‖` by at most `log 2`. -/
theorem abs_log_norm_sub_target_sub_log_norm_le_log_two {w a : ℂ}
    (hwpos : 0 < ‖w‖) (ha : 2 * ‖a‖ ≤ ‖w‖) :
    |Real.log ‖w - a‖ - Real.log ‖w‖| ≤ Real.log 2 := by
  have hhalf : ‖w‖ / 2 ≤ ‖w‖ - ‖a‖ := by linarith
  have hlower0 : ‖w‖ / 2 ≤ ‖w - a‖ :=
    le_trans hhalf (norm_sub_norm_le w a)
  have hwa_pos : 0 < ‖w - a‖ := lt_of_lt_of_le (by positivity) hlower0
  have ha_le_half : ‖a‖ ≤ ‖w‖ / 2 := by linarith
  have hupper : ‖w - a‖ ≤ 2 * ‖w‖ := by
    have htri : ‖w - a‖ ≤ ‖w‖ + ‖a‖ := norm_sub_le w a
    nlinarith [htri, ha_le_half, hwpos]
  have hlower' : ‖w‖ ≤ 2 * ‖w - a‖ := by nlinarith [hlower0]
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_sub_le_iff]
  constructor
  · have hlog := Real.log_le_log hwa_pos hupper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hwpos)] at hlog
    linarith
  · have hlog := Real.log_le_log hwpos hlower'
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hwa_pos)] at hlog
    linarith

/-- Finite GAP-A convergence on the whole basin: the normalized pre-Brolin
potentials converge to the dynamical Green function outside `K_c`. -/
theorem neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_basin {c z : ℂ}
    (hz : z ∉ filledJulia c) :
    Tendsto (fun n => - logPotential (preBrolinMeasure c n) z) atTop
      (𝓝 (greenFunctionDyn c z)) := by
  have hgreen : greenFunctionDyn c z = greenLimit c z := by
    simp [greenFunctionDyn, hz]
  rw [hgreen]
  refine (greenApprox_tendsto_basin hz).congr' ?_
  filter_upwards [eventually_iterate_ne_zero_of_not_mem_filledJulia hz] with n hn
  exact (neg_logPotential_preBrolinMeasure_eq_greenApprox hn).symm

/-- Every shifted compactness limit has the same exterior potential as the
dynamical Green function. -/
theorem green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z =
      - logPotential (shiftedLimitingBrolinMeasure c) z := by
  have hfinite :
      Tendsto
        (fun k => - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
        atTop (𝓝 (greenFunctionDyn c z)) :=
    (neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_basin hz).comp
      (shiftedBrolinIndex_tendsto_atTop c)
  exact tendsto_nhds_unique hfinite
    (shiftedLimitingBrolinMeasure_hasSubseqLogPotentialLimit c hz)

/-- In the disconnected case, the finite zero-target pre-Brolin potentials
converge pointwise to the dynamical Green function on the whole plane.  The
basin side is the usual escape-rate limit; the filled-Julia side is the
finite zero-potential boundary convergence above. -/
theorem neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_of_disconnected
    {c : ℂ} (hc : Disconnected c) (z : ℂ) :
    Tendsto (fun n => - logPotential (preBrolinMeasure c n) z) atTop
      (𝓝 (greenFunctionDyn c z)) := by
  by_cases hz : z ∈ filledJulia c
  · have hzero :
        Tendsto (fun n => - logPotential (preBrolinMeasure c n) z) atTop
          (𝓝 0) :=
      neg_logPotential_preBrolinMeasure_tendsto_zero_filledJulia_of_disconnected
        hc hz
    have hG : greenFunctionDyn c z = 0 :=
      (greenFunctionDyn_eq_zero_iff c z).mpr hz
    rwa [hG]
  · exact neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_basin hz

/-- The shifted compactness extraction preserves the disconnected finite
potential convergence on all of `ℂ`.  This is the finite-level input for
passing the boundary scaling law through the shifted limiting measure. -/
theorem neg_logPotential_preBrolinMeasure_shiftedIndex_tendsto_greenFunctionDyn_of_disconnected
    {c : ℂ} (hc : Disconnected c) (z : ℂ) :
    Tendsto
      (fun k => - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
      atTop (𝓝 (greenFunctionDyn c z)) :=
  (neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_of_disconnected
    hc z).comp (shiftedBrolinIndex_tendsto_atTop c)

/-- On `K_c`, the shifted finite potentials converge to zero in the
disconnected case. -/
theorem neg_logPotential_preBrolinMeasure_shiftedIndex_tendsto_zero_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c) :
    Tendsto
      (fun k => - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
      atTop (𝓝 0) := by
  have h :=
    neg_logPotential_preBrolinMeasure_shiftedIndex_tendsto_greenFunctionDyn_of_disconnected
      (c := c) hc z
  simpa [(greenFunctionDyn_eq_zero_iff c z).mpr hz] using h

/-- The compactness-selected zero-target subsequence preserves the whole-plane
finite potential convergence in the disconnected case. -/
theorem neg_logPotential_preBrolinMeasure_limitSubseq_tendsto_greenFunctionDyn_of_disconnected
    {c : ℂ} (hc : Disconnected c) (z : ℂ) :
    Tendsto
      (fun k =>
        - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
      atTop (𝓝 (greenFunctionDyn c z)) :=
  (neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_of_disconnected
    hc z).comp (brolinLimitSubsequence_tendsto_atTop c)

/-- Arbitrary-target logarithmic approximants have the same basin limit as the
zero-target Green approximants. -/
theorem scaled_log_norm_iterate_sub_target_tendsto_greenFunctionDyn_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto
      (fun n => (2 ^ n : ℝ)⁻¹ * Real.log ‖(quadratic c)^[n] z - a‖)
      atTop (𝓝 (greenFunctionDyn c z)) := by
  have hgreen : greenFunctionDyn c z = greenLimit c z := by
    simp [greenFunctionDyn, hz]
  rw [hgreen]
  have hdiff :
      Tendsto
        (fun n =>
          (2 ^ n : ℝ)⁻¹ *
            (Real.log ‖(quadratic c)^[n] z - a‖ -
              Real.log ‖(quadratic c)^[n] z‖))
        atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹) atTop (𝓝 0) := by
      simp_rw [← inv_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hbd : Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * Real.log 2) atTop (𝓝 0) := by
      simpa using hpow.mul_const (Real.log 2)
    refine squeeze_zero_norm' ?_ hbd
    obtain ⟨N, hN⟩ := exists_orbit_gt hz (max (max 2 ‖c‖) (2 * ‖a‖))
    have hNc : ‖c‖ ≤ ‖(quadratic c)^[N] z‖ :=
      le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
    have hN2 : 2 < ‖(quadratic c)^[N] z‖ :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hNa : 2 * ‖a‖ < ‖(quadratic c)^[N] z‖ :=
      lt_of_le_of_lt (le_max_right _ _) hN
    filter_upwards [eventually_ge_atTop N] with n hn
    have htail := norm_le_orbit hNc hN2 (n - N)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn] at htail
    have hpos : 0 < ‖(quadratic c)^[n] z‖ :=
      lt_of_lt_of_le (lt_trans (by norm_num : (0 : ℝ) < 2) hN2) htail
    have hlarge : 2 * ‖a‖ ≤ ‖(quadratic c)^[n] z‖ :=
      le_trans hNa.le htail
    rw [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (by positivity : 0 ≤ (2 ^ n : ℝ)⁻¹)]
    exact mul_le_mul_of_nonneg_left
      (abs_log_norm_sub_target_sub_log_norm_le_log_two hpos hlarge)
      (by positivity)
  have hsum := (greenApprox_tendsto_basin hz).add hdiff
  simpa using hsum.congr' (by
    filter_upwards [eventually_ge_atTop 0] with n _hn
    unfold greenApprox
    ring)

/-- Finite GAP-A convergence for arbitrary target pullbacks on the whole
basin.  The choice of target changes the finite logarithm by only
`O(2⁻ⁿ)`, once the orbit has escaped. -/
theorem neg_logPotential_preBrolinMeasureAt_tendsto_greenFunctionDyn_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto (fun n => - logPotential (preBrolinMeasureAt c a n) z) atTop
      (𝓝 (greenFunctionDyn c z)) := by
  refine (scaled_log_norm_iterate_sub_target_tendsto_greenFunctionDyn_basin
    (c := c) (a := a) hz).congr' ?_
  filter_upwards [eventually_iterate_ne_of_not_mem_filledJulia hz a] with n hn
  have hsub : (quadratic c)^[n] z - a ≠ 0 := by
    intro hzero
    exact hn (sub_eq_zero.mp hzero)
  exact (neg_logPotential_preBrolinMeasureAt_eq_log_norm hsub).symm

/-- The chosen compactness subsequence preserves zero-target finite potential
convergence on the basin. -/
theorem neg_logPotential_preBrolinMeasure_subseq_tendsto_greenFunctionDyn_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto
      (fun k => - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
      atTop (𝓝 (greenFunctionDyn c z)) :=
  (neg_logPotential_preBrolinMeasure_tendsto_greenFunctionDyn_basin hz).comp
    (brolinLimitSubsequence_tendsto_atTop c)

/-- The chosen compactness subsequence preserves arbitrary-target finite
potential convergence on the basin. -/
theorem neg_logPotential_preBrolinMeasureAt_subseq_tendsto_greenFunctionDyn_basin
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto
      (fun k =>
        - logPotential (preBrolinMeasureAt c a (brolinLimitSubsequence c k)) z)
      atTop (𝓝 (greenFunctionDyn c z)) :=
  (neg_logPotential_preBrolinMeasureAt_tendsto_greenFunctionDyn_basin
    (c := c) (a := a) hz).comp (brolinLimitSubsequence_tendsto_atTop c)

/-- Once the logarithmic kernel is known to pass to the chosen subsequential
limit, the exterior potential identity follows from the finite Brolin
potential convergence. -/
theorem green_eq_neg_logPotential_on_basin_of_subseqLogPotentialLimit
    {c : ℂ} {μ : Measure ℂ} (hpot : HasSubseqLogPotentialLimit c μ)
    {z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z = - logPotential μ z := by
  exact tendsto_nhds_unique
    (neg_logPotential_preBrolinMeasure_subseq_tendsto_greenFunctionDyn_basin hz)
    (hpot hz)

/-- Exterior GAP-A potential identity for the constructed limiting Brolin
measure. -/
theorem green_eq_neg_logPotential_limitingBrolinMeasure_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z = - logPotential (limitingBrolinMeasure c) z :=
  green_eq_neg_logPotential_on_basin_of_subseqLogPotentialLimit
    (limitingBrolinMeasure_hasSubseqLogPotentialLimit c) hz

/-- The zero-target limiting Riesz-measure side represented by the constructed
positive functional. -/
noncomputable def limitingBrolinRieszMeasure (c : ℂ) : Measure ℂ :=
  limitingBrolinMeasure c

theorem limitingBrolinRieszMeasure_eq_limitingBrolinMeasure (c : ℂ) :
    limitingBrolinRieszMeasure c = limitingBrolinMeasure c := by
  rfl

theorem limitingBrolinRieszMeasure_integral_eq_functional
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂limitingBrolinRieszMeasure c =
      limitingBrolinRieszFunctional c φ := by
  rw [limitingBrolinRieszMeasure_eq_limitingBrolinMeasure,
    limitingBrolinRieszFunctional_apply]

theorem limitingBrolinRieszMeasure_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (limitingBrolinRieszMeasure c) (filledJulia c) := by
  rw [limitingBrolinRieszMeasure_eq_limitingBrolinMeasure]
  exact limitingBrolinMeasure_isProbOn_filledJulia c

theorem limitingBrolinRieszMeasure_isWeakSubseqLimitOfPreBrolin (c : ℂ) :
    IsWeakSubseqLimitOfPreBrolin c (limitingBrolinRieszMeasure c) := by
  rw [limitingBrolinRieszMeasure_eq_limitingBrolinMeasure]
  exact limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin c

theorem limitingBrolinRieszMeasure_hasSubseqLogPotentialLimit (c : ℂ) :
    HasSubseqLogPotentialLimit c (limitingBrolinRieszMeasure c) := by
  rw [limitingBrolinRieszMeasure_eq_limitingBrolinMeasure]
  exact limitingBrolinMeasure_hasSubseqLogPotentialLimit c

theorem green_eq_neg_logPotential_limitingBrolinRieszMeasure_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z =
      - logPotential (limitingBrolinRieszMeasure c) z := by
  rw [limitingBrolinRieszMeasure_eq_limitingBrolinMeasure]
  exact green_eq_neg_logPotential_limitingBrolinMeasure_on_basin
    (c := c) (z := z) hz

/-- The hDisc-side constructed limiting measure, used as the candidate `μ_c`. -/
noncomputable def brolinMu (c : ℂ) : Measure ℂ :=
  limitingBrolinMeasure c

theorem brolinMu_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (brolinMu c) (filledJulia c) := by
  simpa [brolinMu] using limitingBrolinMeasure_isProbOn_filledJulia c

theorem brolinMu_isWeakSubseqLimitOfPreBrolin (c : ℂ) :
    IsWeakSubseqLimitOfPreBrolin c (brolinMu c) := by
  simpa [brolinMu] using limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin c

theorem brolinMu_hasSubseqLogPotentialLimit (c : ℂ) :
    HasSubseqLogPotentialLimit c (brolinMu c) := by
  simpa [brolinMu] using limitingBrolinMeasure_hasSubseqLogPotentialLimit c

/-- Exterior GAP-A potential identity for the constructed `μ_c`. -/
theorem brolinMu_green_eq_neg_logPotential_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z = - logPotential (brolinMu c) z := by
  simpa [brolinMu] using
    green_eq_neg_logPotential_limitingBrolinMeasure_on_basin (c := c) (z := z) hz

/-- The hDisc-side core of Brolin/GAP-A now available for the constructed
candidate `μ_c`: probability on `K_c`, weak subsequential construction, logarithmic
potential convergence, and exterior potential representation. -/
theorem brolinMu_hDiscCore (c : ℂ) :
    IsProbOn (brolinMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMu c) ∧
      HasSubseqLogPotentialLimit c (brolinMu c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (brolinMu c) z :=
  ⟨brolinMu_isProbOn_filledJulia c,
    brolinMu_isWeakSubseqLimitOfPreBrolin c,
    brolinMu_hasSubseqLogPotentialLimit c,
    fun z hz => brolinMu_green_eq_neg_logPotential_on_basin (c := c) (z := z) hz⟩

/-- hDisc zero-target Brolin core with the finite potential boundary condition:
for disconnected `c`, the selected zero-target finite potentials converge
pointwise to `G_c` on all of `ℂ`, including `K_c`.  This is the finite-level
input still needed for the singular-kernel passage to the limiting potential. -/
theorem brolinMu_hDiscFinitePotentialCore {c : ℂ} (hc : Disconnected c) :
    IsProbOn (brolinMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMu c) ∧
      HasSubseqLogPotentialLimit c (brolinMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (brolinMu c) z) ∧
      ∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (brolinMu_hDiscCore c).1
  · exact (brolinMu_hDiscCore c).2.1
  · exact (brolinMu_hDiscCore c).2.2.1
  · exact (brolinMu_hDiscCore c).2.2.2
  · intro z
    exact neg_logPotential_preBrolinMeasure_limitSubseq_tendsto_greenFunctionDyn_of_disconnected
      hc z

/-- The positive Riesz-Markov functional represented by the zero-target
constructed hDisc measure `μ_c`. -/
noncomputable def brolinMuRieszFunctional
    (c : ℂ) : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  limitingBrolinRieszFunctional c

theorem brolinMuRieszFunctional_apply
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    brolinMuRieszFunctional c φ =
      ∫ z, φ z ∂brolinMu c := by
  rfl

/-- The zero-target hDisc Riesz-measure side represented by the constructed
limiting functional. -/
noncomputable def brolinMuRieszMeasure (c : ℂ) : Measure ℂ :=
  limitingBrolinRieszMeasure c

/-- GAP-A notation for the constructed zero-target limiting/Riesz measure
`μ_c`. -/
noncomputable def gapAMu (c : ℂ) : Measure ℂ :=
  brolinMuRieszMeasure c

theorem brolinMuRieszMeasure_eq_brolinMu (c : ℂ) :
    brolinMuRieszMeasure c = brolinMu c := by
  rw [brolinMuRieszMeasure,
    limitingBrolinRieszMeasure_eq_limitingBrolinMeasure, brolinMu]

theorem gapAMu_eq_brolinMuRieszMeasure (c : ℂ) :
    gapAMu c = brolinMuRieszMeasure c := by
  rfl

theorem gapAMu_eq_brolinMu (c : ℂ) :
    gapAMu c = brolinMu c := by
  rw [gapAMu, brolinMuRieszMeasure_eq_brolinMu]

/-- Measure-level antipodal invariance of the hDisc candidate `μ_c`. -/
theorem map_brolinMu_neg (c : ℂ) :
    Measure.map Neg.neg (brolinMu c) = brolinMu c := by
  simpa [brolinMu] using map_limitingBrolinMeasure_neg c

/-- GAP-A notation for antipodal invariance of the constructed measure `μ_c`. -/
theorem map_gapAMu_neg (c : ℂ) :
    Measure.map Neg.neg (gapAMu c) = gapAMu c := by
  rw [gapAMu_eq_brolinMu]
  exact map_brolinMu_neg c

/-- Antipodal symmetry of `μ_c` makes the antipodal kernel integral equal to
the original kernel integral. -/
theorem integral_logKernel_neg_right_gapAMu_eq
    (c z : ℂ) :
    ∫ w, logKernel z (-w) ∂gapAMu c =
      ∫ w, logKernel z w ∂gapAMu c := by
  let μ : Measure ℂ := gapAMu c
  calc
    ∫ w, logKernel z (-w) ∂gapAMu c
        = ∫ w, logKernel z (-w) ∂μ := by rfl
    _ = ∫ w, logKernel z w ∂Measure.map Neg.neg μ := by
          rw [integral_map]
          · exact continuous_neg.measurable.aemeasurable
          · exact logKernel_aestronglyMeasurable z (Measure.map Neg.neg μ)
    _ = ∫ w, logKernel z w ∂gapAMu c := by
          rw [show μ = gapAMu c from rfl, map_gapAMu_neg c]

/-- The GAP-A potential is even under `z ↦ -z`. -/
theorem logPotential_gapAMu_neg_eq (c z : ℂ) :
    logPotential (gapAMu c) (-z) = logPotential (gapAMu c) z := by
  calc
    logPotential (gapAMu c) (-z)
        = ∫ w, logKernel z (-w) ∂gapAMu c := by
          unfold logPotential
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall
            (fun w => (logKernel_neg_right z w).symm)
    _ = logPotential (gapAMu c) z := by
          rw [integral_logKernel_neg_right_gapAMu_eq]
          rfl

/-- GAP-A-facing form of the shifted balancedness bridge.  The shifted cluster
limit may be a priori different, but its quadratic pushforward has the same
compact-test integrals as the constructed measure `μ_c`. -/
theorem shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
      ∫ z, φ z ∂gapAMu c := by
  rw [gapAMu_eq_brolinMu, brolinMu]
  exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_limitingBrolinMeasure
    c φ

/-- Measure-level shifted balancedness: the quadratic pushforward of the
shifted compactness limit is the constructed GAP-A measure. -/
theorem map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu (c : ℂ) :
    Measure.map (quadratic c) (shiftedLimitingBrolinMeasure c) = gapAMu c := by
  rw [gapAMu_eq_brolinMu, brolinMu]
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [integral_map]
  · exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_limitingBrolinMeasure c φ
  · exact (continuous_quadratic c).measurable.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- Bounded-continuous integral form of shifted balancedness. -/
theorem shiftedLimitingBrolinMeasure_quadratic_boundedContinuousIntegral_eq_gapAMu
    (c : ℂ) (g : BoundedContinuousFunction ℂ ℝ) :
    ∫ z, g (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
      ∫ z, g z ∂gapAMu c := by
  rw [← map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu c]
  rw [integral_map]
  · exact (continuous_quadratic c).measurable.aemeasurable
  · exact g.continuous.aestronglyMeasurable

theorem shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_gapAMu
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      ∫ w, truncatedLogKernel z δ w ∂gapAMu c := by
  rw [gapAMu_eq_brolinMu, brolinMu]
  exact
    shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_limitingBrolinMeasure
      c z hδ

/-- The shifted compactness limit is a genuine second hDisc limiting measure:
it is a probability measure on `K_c`, it has exterior potential `G_c`, and its
quadratic pushforward is the GAP-A measure in compact-test form. -/
theorem shiftedLimitingBrolinMeasure_hDiscExteriorCore (c : ℂ) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      ∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c := by
  refine ⟨?_, ?_, ?_⟩
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ

/-- Measure-balanced hDisc exterior core: the shifted compactness limit has
exterior potential `G_c` and pushes forward exactly to `μ_c` under `f_c`. -/
theorem shiftedLimitingBrolinMeasure_hDiscBalancedExteriorCore (c : ℂ) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      Measure.map (quadratic c) (shiftedLimitingBrolinMeasure c) = gapAMu c ∧
      (∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c) ∧
      ∀ g : BoundedContinuousFunction ℂ ℝ,
        ∫ z, g (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, g z ∂gapAMu c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · exact map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu c
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ
  · intro g
    exact shiftedLimitingBrolinMeasure_quadratic_boundedContinuousIntegral_eq_gapAMu c g

/-- Disconnected hDisc finite-potential core for the shifted compactness
limit: the shifted finite measures converge pointwise to `G_c`, while the
shifted limiting measure already has the exterior potential identity and
pushes forward to `μ_c`. -/
theorem shiftedLimitingBrolinMeasure_hDiscFinitePotentialCore
    {c : ℂ} (hc : Disconnected c) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      Measure.map (quadratic c) (shiftedLimitingBrolinMeasure c) = gapAMu c ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
          atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · exact map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu c
  · intro z
    exact
      neg_logPotential_preBrolinMeasure_shiftedIndex_tendsto_greenFunctionDyn_of_disconnected
        hc z
  · intro z hz
    exact
      neg_logPotential_preBrolinMeasure_shiftedIndex_tendsto_zero_filledJulia_of_disconnected
        hc hz

/-- Shifted finite-scaling core for the disconnected hDisc passage.  The exact
finite quadratic scaling law is stated with the same shifted indices that
define the shifted limiting measure. -/
theorem shiftedLimitingBrolinMeasure_hDiscFiniteScalingCore
    {c : ℂ} (hc : Disconnected c) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      Measure.map (quadratic c) (shiftedLimitingBrolinMeasure c) = gapAMu c ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
          atTop (𝓝 0)) ∧
      (∀ z : ℂ, z ∈ filledJulia c → ∀ k : ℕ,
        - logPotential
            (preBrolinMeasure c
              (brolinLimitSubsequence c (shiftedBrolinLimitSubsequence c k)))
            (quadratic c z) =
          2 * (- logPotential
            (preBrolinMeasure c (shiftedBrolinIndex c k)) z)) ∧
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            - logPotential
              (preBrolinMeasure c
                (brolinLimitSubsequence c (shiftedBrolinLimitSubsequence c k)))
              (quadratic c z))
          atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (shiftedLimitingBrolinMeasure_hDiscFinitePotentialCore hc).1
  · exact (shiftedLimitingBrolinMeasure_hDiscFinitePotentialCore hc).2.1
  · exact (shiftedLimitingBrolinMeasure_hDiscFinitePotentialCore hc).2.2.1
  · exact (shiftedLimitingBrolinMeasure_hDiscFinitePotentialCore hc).2.2.2.1
  · exact (shiftedLimitingBrolinMeasure_hDiscFinitePotentialCore hc).2.2.2.2
  · intro z hz k
    exact
      neg_logPotential_preBrolinMeasure_shiftedBase_quadratic_eq_two_shiftedIndex
        (c := c) (z := z) hc hz k
  · intro z hz
    exact
      neg_logPotential_preBrolinMeasure_shiftedBase_quadratic_tendsto_zero_filledJulia_of_disconnected
        (c := c) (z := z) hc hz

/-- hDisc shifted-potential package for GAP-A.  This is the measure-theoretic
bridge needed for the boundary scaling step: the canonical `gapAMu`, the
shifted compactness limit, both exterior potential identities, and both
compact-test and truncated-log-kernel pushforward identities. -/
theorem gapAMu_hDiscShiftedPotentialCore (c : ℂ) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      (∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c) ∧
      ∀ z : ℂ, ∀ {δ : ℝ}, 0 < δ →
        ∫ w, truncatedLogKernel z δ (quadratic c w)
            ∂shiftedLimitingBrolinMeasure c =
          ∫ w, truncatedLogKernel z δ w ∂gapAMu c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · rw [gapAMu_eq_brolinMu]
    exact brolinMu_isProbOn_filledJulia c
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · intro z hz
    rw [gapAMu_eq_brolinMu]
    exact brolinMu_green_eq_neg_logPotential_on_basin hz
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ
  · intro z δ hδ
    exact
      shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_gapAMu
        c z hδ

theorem brolinMuRieszMeasure_integral_eq_functional
    (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂brolinMuRieszMeasure c =
      brolinMuRieszFunctional c φ := by
  rw [brolinMuRieszMeasure_eq_brolinMu,
    brolinMuRieszFunctional_apply]

theorem gapAMu_integral_eq_functional (c : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ z ∂gapAMu c = brolinMuRieszFunctional c φ := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact brolinMuRieszMeasure_integral_eq_functional c φ

/-- The constructed GAP-A measure is exactly the Riesz-Markov measure
represented by the limiting positive functional. -/
theorem gapAMu_eq_rieszMeasureOf_brolinMuRieszFunctional (c : ℂ) :
    gapAMu c = rieszMeasureOfFunctional (brolinMuRieszFunctional c) := by
  rw [gapAMu_eq_brolinMu, brolinMu]
  change limitingBrolinMeasure c = RealRMK.rieszMeasure (brolinMuRieszFunctional c)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [RealRMK.integral_rieszMeasure, brolinMuRieszFunctional,
    limitingBrolinRieszFunctional_apply]

/-- The zero-target Riesz-measure name is also the Riesz-Markov measure of the
same limiting positive functional. -/
theorem brolinMuRieszMeasure_eq_rieszMeasureOf_brolinMuRieszFunctional (c : ℂ) :
    brolinMuRieszMeasure c = rieszMeasureOfFunctional (brolinMuRieszFunctional c) := by
  rw [← gapAMu_eq_brolinMuRieszMeasure,
    gapAMu_eq_rieszMeasureOf_brolinMuRieszFunctional]

/-- Riesz-Markov core for the constructed GAP-A measure: `μ_c` is the
Riesz-Markov measure of the limiting positive functional, that functional is
the weak limit of the finite zero-pullback functionals, and it is carried by
every positive Green sublevel in compact-test form. -/
theorem gapAMu_hDiscRieszMarkovCore (c : ℂ) :
    gapAMu c = rieszMeasureOfFunctional (brolinMuRieszFunctional c) ∧
      (∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ z ∂gapAMu c = brolinMuRieszFunctional c φ) ∧
      IsWeakSubseqLimitFunctionalOfPreBrolin c (brolinMuRieszFunctional c) ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ φ : C_c(ℂ, ℝ),
        (∀ z, z ∈ greenSublevel c ε → φ z = 0) →
          brolinMuRieszFunctional c φ = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_rieszMeasureOf_brolinMuRieszFunctional c
  · intro φ
    exact gapAMu_integral_eq_functional c φ
  · simpa [brolinMuRieszFunctional] using
      limitingBrolinRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolin c
  · intro ε hε φ hφ
    simpa [brolinMuRieszFunctional] using
      limitingBrolinRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel
        c hε φ hφ

theorem brolinMuRieszMeasure_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (brolinMuRieszMeasure c) (filledJulia c) := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact (brolinMu_hDiscCore c).1

theorem gapAMu_isProbOn_filledJulia (c : ℂ) :
    IsProbOn (gapAMu c) (filledJulia c) := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact brolinMuRieszMeasure_isProbOn_filledJulia c

/-- Carrier-only lower bound for the canonical GAP-A potential at every point
of the fixed escape disk. -/
theorem logPotential_gapAMu_lower_bound_of_mem_escapeDisk
    {c z : ℂ} (hz : z ∈ escapeDisk c) :
    - Real.log (2 * max 2 ‖c‖) ≤ logPotential (gapAMu c) z :=
  logPotential_lower_bound_of_isProbOn_filledJulia_of_mem_escapeDisk
    (gapAMu_isProbOn_filledJulia c) hz

/-- Filled-Julia specialization of the carrier-only GAP-A potential lower
bound. -/
theorem logPotential_gapAMu_lower_bound_of_mem_filledJulia
    {c z : ℂ} (hz : z ∈ filledJulia c) :
    - Real.log (2 * max 2 ‖c‖) ≤ logPotential (gapAMu c) z :=
  logPotential_gapAMu_lower_bound_of_mem_escapeDisk
    (mem_escapeDisk_of_mem_filledJulia hz)

/-- Carrier-only upper bound for the negative GAP-A potential on `K_c`. -/
theorem neg_logPotential_gapAMu_upper_bound_of_mem_filledJulia
    {c z : ℂ} (hz : z ∈ filledJulia c) :
    - logPotential (gapAMu c) z ≤ Real.log (2 * max 2 ‖c‖) := by
  have h := logPotential_gapAMu_lower_bound_of_mem_filledJulia
    (c := c) (z := z) hz
  linarith

theorem brolinMuRieszMeasure_isWeakSubseqLimitOfPreBrolin (c : ℂ) :
    IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact (brolinMu_hDiscCore c).2.1

theorem gapAMu_isWeakSubseqLimitOfPreBrolin (c : ℂ) :
    IsWeakSubseqLimitOfPreBrolin c (gapAMu c) := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact brolinMuRieszMeasure_isWeakSubseqLimitOfPreBrolin c

theorem brolinMuRieszMeasure_hasSubseqLogPotentialLimit (c : ℂ) :
    HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact (brolinMu_hDiscCore c).2.2.1

theorem gapAMu_hasSubseqLogPotentialLimit (c : ℂ) :
    HasSubseqLogPotentialLimit c (gapAMu c) := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact brolinMuRieszMeasure_hasSubseqLogPotentialLimit c

theorem green_eq_neg_logPotential_brolinMuRieszMeasure_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z =
      - logPotential (brolinMuRieszMeasure c) z := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact (brolinMu_hDiscCore c).2.2.2 z hz

theorem green_eq_neg_logPotential_gapAMu_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    greenFunctionDyn c z = - logPotential (gapAMu c) z := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact green_eq_neg_logPotential_brolinMuRieszMeasure_on_basin hz

/-- GAP-A limiting/Riesz-measure core for the constructed `μ_c`.  This is the
canonical zero-target Brolin limit, stated with the GAP-A name. -/
theorem gapAMu_hDiscLimitingRieszMeasureCore (c : ℂ) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (gapAMu c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_isWeakSubseqLimitOfPreBrolin c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz

theorem gapAMu_hDiscShiftedBalancedCore (c : ℂ) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (gapAMu c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      ∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_isWeakSubseqLimitOfPreBrolin c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ

/-- For the constructed GAP-A measure, the full potential representation is
equivalent to the zero-potential boundary statement on `K_c`.  The exterior
identity is already part of the limiting construction. -/
theorem gapAMu_hasGreenPotentialRepresentation_iff_boundary_zero (c : ℂ) :
    HasGreenPotentialRepresentation c (gapAMu c) ↔
      ∀ z : ℂ, z ∈ filledJulia c → - logPotential (gapAMu c) z = 0 := by
  constructor
  · intro h z hz
    have hpot := (hasGreenPotentialRepresentation_iff c (gapAMu c)).mp h z
    rw [(greenFunctionDyn_eq_zero_iff c z).mpr hz] at hpot
    exact hpot.symm
  · intro hK
    rw [hasGreenPotentialRepresentation_iff]
    intro z
    by_cases hz : z ∈ filledJulia c
    · rw [(greenFunctionDyn_eq_zero_iff c z).mpr hz, hK z hz]
    · exact green_eq_neg_logPotential_gapAMu_on_basin hz

/-- The zero-target hDisc Riesz functional is the weak limit of the finite
zero-pullback Riesz functionals. -/
theorem brolinMuRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolin
    (c : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolin c (brolinMuRieszFunctional c) := by
  simpa [brolinMuRieszFunctional] using
    limitingBrolinRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolin c

/-- The zero-target hDisc Riesz functional is carried, in compact-test form, by
every positive Green sublevel. -/
theorem brolinMuRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) (φ : C_c(ℂ, ℝ))
    (hφ : ∀ z, z ∈ greenSublevel c ε → φ z = 0) :
    brolinMuRieszFunctional c φ = 0 := by
  simpa [brolinMuRieszFunctional] using
    limitingBrolinRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel
      c hε φ hφ

/-- Riesz-functional core for the zero-target constructed hDisc measure.  This
records the actual limiting functional, separated from the later
distributional identity `(2π)⁻¹ΔG_c`. -/
theorem brolinMu_hDiscRieszFunctionalCore (c : ℂ) :
    IsWeakSubseqLimitFunctionalOfPreBrolin c (brolinMuRieszFunctional c) ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ φ : C_c(ℂ, ℝ),
        (∀ z, z ∈ greenSublevel c ε → φ z = 0) →
          brolinMuRieszFunctional c φ = 0 := by
  refine ⟨?_, ?_⟩
  · exact brolinMuRieszFunctional_isWeakSubseqLimitFunctionalOfPreBrolin c
  · intro ε hε φ hφ
    exact brolinMuRieszFunctional_eq_zero_of_eq_zero_on_greenSublevel c hε φ hφ

/-- Canonical zero-target hDisc limiting/Riesz-measure package: the represented
measure is the constructed limiting Brolin measure, it is carried by `K_c`, and
its exterior logarithmic potential is `G_c`. -/
theorem brolinMu_hDiscLimitingRieszMeasureCore (c : ℂ) :
    brolinMuRieszMeasure c = brolinMu c ∧
      IsProbOn (brolinMuRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) ∧
      HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuRieszMeasure c) z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact brolinMuRieszMeasure_eq_brolinMu c
  · exact brolinMuRieszMeasure_isProbOn_filledJulia c
  · exact brolinMuRieszMeasure_isWeakSubseqLimitOfPreBrolin c
  · exact brolinMuRieszMeasure_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_brolinMuRieszMeasure_on_basin hz

/-- Disconnected-case zero-target limiting/Riesz-measure package with the
finite potential convergence needed for the singular-kernel passage on `K_c`. -/
theorem brolinMuRieszMeasure_hDiscFinitePotentialCore {c : ℂ}
    (hc : Disconnected c) :
    brolinMuRieszMeasure c = brolinMu c ∧
      IsProbOn (brolinMuRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) ∧
      HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuRieszMeasure c) z) ∧
      ∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact brolinMuRieszMeasure_eq_brolinMu c
  · exact brolinMuRieszMeasure_isProbOn_filledJulia c
  · exact brolinMuRieszMeasure_isWeakSubseqLimitOfPreBrolin c
  · exact brolinMuRieszMeasure_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_brolinMuRieszMeasure_on_basin hz
  · intro z
    exact (brolinMu_hDiscFinitePotentialCore hc).2.2.2.2 z

/-- Disconnected GAP-A finite-potential core for `μ_c`: the constructed
limiting/Riesz measure has the weak construction, exterior potential identity,
and the finite zero-pullback potentials converge to `G_c` at every point. -/
theorem gapAMu_hDiscFinitePotentialCore {c : ℂ} (hc : Disconnected c) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (gapAMu c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      ∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_isWeakSubseqLimitOfPreBrolin c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.2

theorem gapAMu_hDiscFiniteScalingCore {c : ℂ} (hc : Disconnected c) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (gapAMu c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            - logPotential
              (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z)
          atTop (𝓝 0)) ∧
      ∀ z : ℂ, z ∈ filledJulia c → ∀ k : ℕ,
        - logPotential
            (preBrolinMeasure c (brolinLimitSubsequence c k))
            (quadratic c z) =
          2 * (- logPotential
            (preBrolinMeasure c (brolinLimitSubsequence c k + 1)) z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_isWeakSubseqLimitOfPreBrolin c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · exact (gapAMu_hDiscFinitePotentialCore hc).2.2.2.2.2
  · intro z hz
    exact
      neg_logPotential_preBrolinMeasure_limitSubseq_succ_tendsto_zero_filledJulia_of_disconnected
        hc hz
  · intro z hz k
    exact neg_logPotential_preBrolinMeasure_limitSubseq_quadratic_eq_two_succ
      hc hz k

end Bottcher
