import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheStateHasAContinuousEdgeAtTheWall
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateHasOneSignAtTheWallInTheMean

/-!
# The edge constant is fixed by the confinement mass

Let `Φ` be continuous with `Φ(s) √log(1/s) → ℓ` as `s → 0⁺`. Then
* the mean `k⁻¹ ∫_0^k Φ` is `ℓ/√log(1/k) · (1 + o(1))` (`tendsto_mean_mul_sqrt_log`): with
  `A = log(1/k) ≤ B = log(1/s)`, `|Φ(s)√A − ℓ| ≤ |Φ(s)√B − ℓ| + |ℓ| (B − A)/A` and
  `k⁻¹ ∫_0^k (log k − log s) ds = 1`;
* the logarithmic moment `∫_k^δ Φ(v)/v dv` is `2ℓ √log(1/k) · (1 + o(1))`
  (`tendsto_logMoment_div_sqrt_log`), since `−2√log(1/v)` is a primitive of `1/(v √log(1/v))`.

For the critical state the law of the wall in the mean says that the product of the terminal mean
and the logarithmic moment tends to `16 a ∫ F² e^{−8u}`. With the continuous edge of the state:

**Theorem** (`criticalState_pointwise_edge_law`). The state agrees near the wall with a continuous
function `Φ`, `F(−s) √log(1/s) → ℓ`, and `ℓ² = 8 a(W₀) ∫ F² e^{−8u}`. In particular `ℓ ≠ 0`: near the
wall the state has one strict sign and `|F(−s)| ~ |ℓ|/√log(1/s)`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations _root_.RHTower

/-! ### Means and logarithmic moments of a profile with a logarithmic edge -/

/-- **The mean of a logarithmic edge.** If `Φ(s) √log(1/s) → ℓ`, then
`(k⁻¹ ∫_0^k Φ) √log(1/k) → ℓ`. -/
theorem tendsto_mean_mul_sqrt_log {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {ℓ : ℝ}
    (hψ : Tendsto (fun s => Φ s * Real.sqrt (Real.log (1 / s))) (𝓝[>] 0) (𝓝 ℓ)) :
    Tendsto (fun k => (∫ s in (0)..k, Φ s) / k * Real.sqrt (Real.log (1 / k))) (𝓝[>] 0)
      (𝓝 ℓ) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hψ ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, hψδ⟩ := hψ (ε / 2) (half_pos hε)
  refine ⟨min (min δ₁ 1) (Real.exp (-(2 * |ℓ| / ε))), by positivity, fun k hk hkd => ?_⟩
  have hk0 : (0 : ℝ) < k := hk
  rw [Real.dist_eq, sub_zero, abs_of_pos hk0] at hkd
  have hkδ : k < δ₁ := lt_of_lt_of_le hkd (le_trans (min_le_left _ _) (min_le_left _ _))
  have hke : k < Real.exp (-(2 * |ℓ| / ε)) := lt_of_lt_of_le hkd (min_le_right _ _)
  set A := Real.log (1 / k) with hAdef
  have hAk : A = -Real.log k := by rw [hAdef, one_div, Real.log_inv]
  have hlogk : Real.log k < -(2 * |ℓ| / ε) := (Real.log_lt_iff_lt_exp hk0).mpr hke
  have hA : 2 * |ℓ| / ε < A := by rw [hAk]; linarith
  have hA0 : 0 < A := lt_of_le_of_lt (by positivity) hA
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA0
  have hA2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0.le
  have hpt : ∀ s ∈ Ioc 0 k,
      ‖Φ s * Real.sqrt A - ℓ‖ ≤ ε / 2 + |ℓ| / A * (Real.log k - Real.log s) := by
    intro s hs
    have hs0 : 0 < s := hs.1
    set B := Real.log (1 / s) with hBdef
    have hBs : B = -Real.log s := by rw [hBdef, one_div, Real.log_inv]
    have hAB : A ≤ B := by rw [hAk, hBs]; linarith [Real.log_le_log hs0 hs.2]
    have hψs : |Φ s * Real.sqrt B - ℓ| < ε / 2 := by
      have h := hψδ (show s ∈ Ioi (0 : ℝ) from hs0)
        (by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; linarith [hs.2])
      rwa [Real.dist_eq] at h
    have hsB : Real.sqrt A ≤ Real.sqrt B := Real.sqrt_le_sqrt hAB
    have hsB0 : 0 < Real.sqrt B := lt_of_lt_of_le hsA hsB
    have hB2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt (hA0.le.trans hAB)
    set ρ := Real.sqrt A / Real.sqrt B with hρdef
    have hρ0 : 0 < ρ := div_pos hsA hsB0
    have hρ1 : ρ ≤ 1 := (div_le_one hsB0).mpr hsB
    have hdecomp : Φ s * Real.sqrt A - ℓ = (Φ s * Real.sqrt B - ℓ) * ρ + ℓ * (ρ - 1) := by
      rw [hρdef]
      field_simp
      ring
    have h1ρ : 1 - ρ ≤ (Real.log k - Real.log s) / A := by
      have hρ2 : ρ ^ 2 = A / B := by rw [hρdef, div_pow, hA2, hB2]
      have e1 : 1 - ρ ≤ 1 - ρ ^ 2 := by nlinarith
      have hB0 : 0 < B := hA0.trans_le hAB
      have e2 : 1 - ρ ^ 2 = (B - A) / B := by
        rw [hρ2, sub_div, div_self hB0.ne']
      have e3 : (B - A) / B ≤ (B - A) / A :=
        div_le_div_of_nonneg_left (by linarith) hA0 hAB
      have e4 : B - A = Real.log k - Real.log s := by rw [hAk, hBs]; ring
      rw [← e4]
      linarith
    rw [Real.norm_eq_abs, hdecomp]
    calc |(Φ s * Real.sqrt B - ℓ) * ρ + ℓ * (ρ - 1)| ≤
          |Φ s * Real.sqrt B - ℓ| * 1 + |ℓ| * (1 - ρ) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul, abs_of_pos hρ0]
            exact mul_le_mul_of_nonneg_left hρ1 (abs_nonneg _)
          · rw [abs_mul, abs_sub_comm ρ 1, abs_of_nonneg (show (0 : ℝ) ≤ 1 - ρ by linarith)]
      _ ≤ ε / 2 + |ℓ| * ((Real.log k - Real.log s) / A) := by
          rw [mul_one]
          exact add_le_add hψs.le (mul_le_mul_of_nonneg_left h1ρ (abs_nonneg _))
      _ = ε / 2 + |ℓ| / A * (Real.log k - Real.log s) := by ring
  have hlog := intervalIntegral.intervalIntegrable_log' (a := 0) (b := k)
  have hint : IntervalIntegrable (fun s => ε / 2 + |ℓ| / A * (Real.log k - Real.log s)) volume 0 k :=
    intervalIntegrable_const.add ((intervalIntegrable_const.sub hlog).const_mul _)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hk0.le
    (Eventually.of_forall fun s hs => hpt s hs) hint
  have hcomp : (∫ s in (0)..k, (ε / 2 + |ℓ| / A * (Real.log k - Real.log s))) =
      ε / 2 * k + |ℓ| / A * k := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((intervalIntegrable_const.sub hlog).const_mul _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub intervalIntegrable_const hlog,
      intervalIntegral.integral_const, integral_log]
    simp only [Real.log_zero, mul_zero, sub_zero, smul_eq_mul, add_zero]
    ring
  have hΦi : IntervalIntegrable Φ volume 0 k := hΦ.intervalIntegrable 0 k
  have heq : (∫ s in (0)..k, Φ s) / k * Real.sqrt A - ℓ =
      (∫ s in (0)..k, (Φ s * Real.sqrt A - ℓ)) / k := by
    rw [intervalIntegral.integral_sub (hΦi.mul_const _) intervalIntegrable_const,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    field_simp
  have hℓA : |ℓ| / A < ε / 2 := by
    rw [div_lt_iff₀ hA0]
    rw [div_lt_iff₀ hε] at hA
    linarith
  rw [Real.dist_eq, heq, abs_div, abs_of_pos hk0, div_lt_iff₀ hk0]
  calc |∫ s in (0)..k, (Φ s * Real.sqrt A - ℓ)| ≤ ε / 2 * k + |ℓ| / A * k := by
        rw [← hcomp]
        simpa only [Real.norm_eq_abs] using hnorm
    _ < ε * k := by nlinarith

/-- `−2√log(1/v)` is a primitive of `1/(v √log(1/v))` on `(0, 1)`. -/
theorem hasDerivAt_neg_two_sqrt_log {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt (fun v => -(2 * Real.sqrt (Real.log (1 / v))))
      (1 / (v * Real.sqrt (Real.log (1 / v)))) v := by
  have hL : HasDerivAt (fun v => Real.log (1 / v)) (-v⁻¹) v := by
    have h := (Real.hasDerivAt_log hv0.ne').neg
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
    simp only [one_div, Real.log_inv, Pi.neg_apply]
  have hpos : 0 < Real.log (1 / v) := by
    rw [one_div, Real.log_inv]
    linarith [Real.log_neg hv0 hv1]
  have hs := ((hL.sqrt hpos.ne').const_mul 2).neg
  have hsq : Real.sqrt (Real.log (1 / v)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hv' : v ≠ 0 := hv0.ne'
  have e : -(2 * (-v⁻¹ / (2 * Real.sqrt (Real.log (1 / v))))) =
      1 / (v * Real.sqrt (Real.log (1 / v))) := by
    field_simp
  rw [e] at hs
  exact hs

/-- **The logarithmic moment of a logarithmic edge.** If `Φ(s) √log(1/s) → ℓ` and `0 < δ < 1`, then
`(∫_k^δ Φ(v)/v dv) / √log(1/k) → 2ℓ`. -/
theorem tendsto_logMoment_div_sqrt_log {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {ℓ : ℝ}
    (hψ : Tendsto (fun s => Φ s * Real.sqrt (Real.log (1 / s))) (𝓝[>] 0) (𝓝 ℓ)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Tendsto (fun k => (∫ v in k..δ, Φ v / v) / Real.sqrt (Real.log (1 / k))) (𝓝[>] 0)
      (𝓝 (2 * ℓ)) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hψ ⊢
  intro ε hε
  obtain ⟨s₁, hs₁, hψδ⟩ := hψ (ε / 4) (by positivity)
  set s₀ := min (s₁ / 2) δ with hs₀def
  have hs₀ : 0 < s₀ := lt_min (half_pos hs₁) hδ0
  have hs₀δ : s₀ ≤ δ := min_le_right _ _
  have hs₀1 : s₀ < 1 := lt_of_le_of_lt hs₀δ hδ1
  have hs₀s₁ : s₀ < s₁ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hs₁)
  set c := ∫ v in s₀..δ, Φ v / v with hcdef
  set K := 2 * |ℓ| * Real.sqrt (Real.log (1 / s₀)) + |c| with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨min s₀ (Real.exp (-((2 * K / ε) ^ 2 + 1))), by positivity, fun k hk hkd => ?_⟩
  have hk0 : (0 : ℝ) < k := hk
  rw [Real.dist_eq, sub_zero, abs_of_pos hk0] at hkd
  have hks₀ : k < s₀ := lt_of_lt_of_le hkd (min_le_left _ _)
  have hke : k < Real.exp (-((2 * K / ε) ^ 2 + 1)) := lt_of_lt_of_le hkd (min_le_right _ _)
  have hk1 : k < 1 := hks₀.trans hs₀1
  set L : ℝ → ℝ := fun v => Real.log (1 / v) with hLdef
  have hLpos : ∀ v, 0 < v → v < 1 → 0 < L v := fun v hv0 hv1 => by
    simp only [hLdef, one_div, Real.log_inv]
    linarith [Real.log_neg hv0 hv1]
  have hLk : (2 * K / ε) ^ 2 < L k := by
    have h := (Real.log_lt_iff_lt_exp hk0).mpr hke
    simp only [hLdef, one_div, Real.log_inv]
    linarith
  have hsLk : 2 * K / ε < Real.sqrt (L k) := by
    rw [show 2 * K / ε = Real.sqrt ((2 * K / ε) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_lt_sqrt (by positivity) hLk
  have hsLk0 : 0 < Real.sqrt (L k) := lt_of_le_of_lt (by positivity) hsLk
  -- the primitive
  have hder : ∀ v ∈ uIcc k s₀, HasDerivAt (fun v => -(2 * Real.sqrt (L v)))
      (1 / (v * Real.sqrt (L v))) v := fun v hv => by
    rw [uIcc_of_le hks₀.le] at hv
    exact hasDerivAt_neg_two_sqrt_log (hk0.trans_le hv.1) (lt_of_le_of_lt hv.2 hs₀1)
  have hcontw : ContinuousOn (fun v => 1 / (v * Real.sqrt (L v))) (uIcc k s₀) := by
    rw [uIcc_of_le hks₀.le]
    refine ContinuousOn.div continuousOn_const (continuousOn_id.mul ?_) fun v hv => ?_
    · refine (Real.continuous_sqrt.comp_continuousOn ?_)
      exact (Real.continuousOn_log.comp (continuousOn_const.div continuousOn_id
        fun v hv => (hk0.trans_le hv.1).ne') fun v hv => by
          simp only [mem_compl_iff, mem_singleton_iff, one_div]
          exact inv_ne_zero (hk0.trans_le hv.1).ne')
    · exact mul_ne_zero (hk0.trans_le hv.1).ne'
        (Real.sqrt_pos.mpr (hLpos v (hk0.trans_le hv.1) (lt_of_le_of_lt hv.2 hs₀1))).ne'
  have hwint : IntervalIntegrable (fun v => 1 / (v * Real.sqrt (L v))) volume k s₀ :=
    hcontw.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hwint
  have hΦv : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable (fun v => Φ v / v) volume a b :=
    fun a b ha hab => (ContinuousOn.div hΦ.continuousOn continuousOn_id fun v hv => by
      rw [uIcc_of_le hab] at hv
      exact (ha.trans_le hv.1).ne').intervalIntegrable
  -- pointwise control on (k, s₀]
  have hpt : ∀ v ∈ Ioc k s₀, ‖Φ v / v - ℓ * (1 / (v * Real.sqrt (L v)))‖ ≤
      ε / 4 * (1 / (v * Real.sqrt (L v))) := by
    intro v hv
    have hv0 : 0 < v := hk0.trans hv.1
    have hv1 : v < 1 := lt_of_le_of_lt hv.2 hs₀1
    have hsL : 0 < Real.sqrt (L v) := Real.sqrt_pos.mpr (hLpos v hv0 hv1)
    have hψv : |Φ v * Real.sqrt (L v) - ℓ| < ε / 4 := by
      have h := hψδ (show v ∈ Ioi (0 : ℝ) from hv0)
        (by rw [Real.dist_eq, sub_zero, abs_of_pos hv0]; linarith [hv.2])
      rwa [Real.dist_eq] at h
    have e : Φ v / v - ℓ * (1 / (v * Real.sqrt (L v))) =
        (Φ v * Real.sqrt (L v) - ℓ) * (1 / (v * Real.sqrt (L v))) := by
      field_simp
    rw [e, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 1 / (v * Real.sqrt (L v)))]
    exact mul_le_mul_of_nonneg_right hψv.le (by positivity)
  have hdiffint : IntervalIntegrable (fun v => Φ v / v - ℓ * (1 / (v * Real.sqrt (L v))))
      volume k s₀ := (hΦv k s₀ hk0 hks₀.le).sub (hwint.const_mul ℓ)
  have hE := intervalIntegral.norm_integral_le_of_norm_le hks₀.le
    (Eventually.of_forall fun v hv => hpt v hv) (hwint.const_mul (ε / 4))
  rw [intervalIntegral.integral_const_mul, hFTC] at hE
  rw [intervalIntegral.integral_sub (hΦv k s₀ hk0 hks₀.le) (hwint.const_mul ℓ),
    intervalIntegral.integral_const_mul, hFTC] at hE
  have hsplit : (∫ v in k..δ, Φ v / v) = (∫ v in k..s₀, Φ v / v) + c :=
    (intervalIntegral.integral_add_adjacent_intervals (hΦv k s₀ hk0 hks₀.le)
      (hΦv s₀ δ hs₀ hs₀δ)).symm
  have hs0nn : 0 ≤ Real.sqrt (L s₀) := Real.sqrt_nonneg _
  rw [Real.dist_eq, hsplit, div_sub' hsLk0.ne', abs_div, abs_of_pos hsLk0, div_lt_iff₀ hsLk0]
  set I := ∫ v in k..s₀, Φ v / v
  have hE' : |I - ℓ * (-(2 * Real.sqrt (L s₀)) - -(2 * Real.sqrt (L k)))| ≤
      ε / 4 * (-(2 * Real.sqrt (L s₀)) - -(2 * Real.sqrt (L k))) := by
    simpa only [Real.norm_eq_abs] using hE
  have hKε : K < ε / 2 * Real.sqrt (L k) := by
    rw [div_lt_iff₀ hε] at hsLk
    linarith
  have habs : |ℓ * Real.sqrt (L s₀)| ≤ |ℓ| * Real.sqrt (L s₀) := by
    rw [abs_mul, abs_of_nonneg hs0nn]
  calc |I + c - Real.sqrt (L k) * (2 * ℓ)| ≤
        |I - ℓ * (-(2 * Real.sqrt (L s₀)) - -(2 * Real.sqrt (L k)))| +
          (2 * |ℓ * Real.sqrt (L s₀)| + |c|) := by
        have e : I + c - Real.sqrt (L k) * (2 * ℓ) =
            (I - ℓ * (-(2 * Real.sqrt (L s₀)) - -(2 * Real.sqrt (L k)))) +
              (c - 2 * (ℓ * Real.sqrt (L s₀))) := by ring
        rw [e]
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_two]
        linarith
    _ ≤ ε / 4 * (2 * Real.sqrt (L k)) + K := by
        have : ε / 4 * (-(2 * Real.sqrt (L s₀)) - -(2 * Real.sqrt (L k))) ≤
            ε / 4 * (2 * Real.sqrt (L k)) := by nlinarith
        rw [hKdef]
        linarith
    _ < ε * Real.sqrt (L k) := by linarith

/-! ### The pointwise edge law at the wall -/

/-- `√log(1/k) → ∞` as `k → 0⁺`. -/
theorem tendsto_sqrt_log_one_div : Tendsto (fun k : ℝ => Real.sqrt (Real.log (1 / k))) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun k : ℝ => Real.log (1 / k)) (𝓝[>] 0) atTop := by
    refine (Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr fun k => ?_
    simp only [Function.comp_apply, one_div, Real.log_inv]
  exact Real.tendsto_sqrt_atTop.comp h1

/-- The terminal mean and the logarithmic moment of the state in terms of its continuous edge. -/
theorem criticalState_terminal_eq_edge {F Φ : ℝ → ℝ}
    (hFΦ : ∀ᵐ s, s ∈ Ioo (0 : ℝ) (1 / 4) → F (-s) = Φ s) {k : ℝ} (hk0 : 0 < k) (hk : k < 1 / 4) :
    (∫ u in Ioo (-k) 0, F u) = ∫ s in (0)..k, Φ s := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := k) F
  rw [neg_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hFΦ] with s hs hsI
  rw [uIoc_of_le hk0.le] at hsI
  exact hs ⟨hsI.1, lt_of_le_of_lt hsI.2 hk⟩

theorem criticalState_wallLogMoment_eq_edge {F Φ : ℝ → ℝ} (hFm : Measurable F) (hFi : Integrable F)
    (hFΦ : ∀ᵐ s, s ∈ Ioo (0 : ℝ) (1 / 4) → F (-s) = Φ s) {k : ℝ} (hk0 : 0 < k) (hk : k < 1 / 8) :
    wallLogMoment F k = (∫ v in k..(1 / 8), Φ v / v) + ∫ v in Ioi (1 / 8 : ℝ), F (-v) / v := by
  have hfm : Measurable fun v : ℝ => F (-v) := hFm.comp measurable_neg
  have hfi : Integrable fun v : ℝ => F (-v) := hFi.comp_neg
  unfold wallLogMoment
  rw [← intervalIntegral.integral_interval_add_Ioi (integrableOn_div_self hfm hfi hk0)
    (integrableOn_div_self hfm hfi (k := 1 / 8) (by norm_num))]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hFΦ] with s hs hsI
  rw [uIoc_of_le hk.le] at hsI
  rw [hs ⟨hk0.trans hsI.1, by linarith [hsI.2]⟩]

/-- The logarithmic moment of the state grows like `2ℓ √log(1/k)`. -/
theorem tendsto_wallLogMoment_div_sqrt_log {F Φ : ℝ → ℝ} (hFm : Measurable F) (hFi : Integrable F)
    (hΦ : Continuous Φ) (hFΦ : ∀ᵐ s, s ∈ Ioo (0 : ℝ) (1 / 4) → F (-s) = Φ s) {ℓ : ℝ}
    (hψ : Tendsto (fun s => Φ s * Real.sqrt (Real.log (1 / s))) (𝓝[>] 0) (𝓝 ℓ)) :
    Tendsto (fun k => wallLogMoment F k / Real.sqrt (Real.log (1 / k))) (𝓝[>] 0) (𝓝 (2 * ℓ)) := by
  have hB := tendsto_logMoment_div_sqrt_log hΦ hψ (δ := 1 / 8) (by norm_num) (by norm_num)
  have hc := (tendsto_const_nhds (x := ∫ v in Ioi (1 / 8 : ℝ), F (-v) / v)).div_atTop
    tendsto_sqrt_log_one_div
  have h := hB.add hc
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))] with k hk hk'
  rw [criticalState_wallLogMoment_eq_edge hFm hFi hFΦ hk hk', add_div]

/-- **The pointwise edge law at the wall.** The state agrees almost everywhere near the wall with a
continuous function `Φ`, `Φ(s) √log(1/s) → ℓ` as `s → 0⁺`, and the edge constant is fixed by the
confinement mass: `ℓ² = 8 a(W₀) ∫ F² e^{−8u}`. -/
theorem criticalState_pointwise_edge_law {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ (∀ᵐ s, s ∈ Ioo (0 : ℝ) (1 / 4) → F (-s) = Φ s) ∧
      ∃ ℓ : ℝ, Tendsto (fun s => Φ s * Real.sqrt (Real.log (1 / s))) (𝓝[>] 0) (𝓝 ℓ) ∧
        ℓ ^ 2 = 8 * criticalAliasCoefficient W₀ * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  obtain ⟨Φ, hΦc, hFΦ, ℓ, hψ⟩ := criticalState_exists_continuous_edge hW ht hF
  refine ⟨Φ, hΦc, hFΦ, ℓ, hψ, ?_⟩
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hA := tendsto_mean_mul_sqrt_log hΦc hψ
  have hB := tendsto_wallLogMoment_div_sqrt_log hd.meas hd.integrable hΦc hFΦ hψ
  have hmine : Tendsto (fun k : ℝ => (∫ u in Ioo (-k) 0, F u) / k * wallLogMoment F k) (𝓝[>] 0)
      (𝓝 (ℓ * (2 * ℓ))) := by
    refine (hA.mul hB).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))] with k hk hk'
    have hk0 : (0 : ℝ) < k := hk
    have hk' : k < 1 / 8 := hk'
    have hL : 0 < Real.log (1 / k) := by
      rw [one_div, Real.log_inv]
      linarith [Real.log_neg hk0 (by linarith : k < 1)]
    have hsL : Real.sqrt (Real.log (1 / k)) ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
    rw [criticalState_terminal_eq_edge hFΦ hk0 (by linarith)]
    field_simp
  have h := tendsto_nhds_unique hmine (criticalState_tendsto_terminalMean_mul_wallLogMoment hW ht hF)
  linear_combination h / 2

/-- The confinement mass of the state is at least its mass: `∫ F² e^{−8u} ≥ ∫ F² = 1`. -/
theorem criticalState_one_le_confinementMass {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) : 1 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  rw [← hF.2.2.2.1]
  refine integral_mono hF.2.2.1 hF.2.2.2.2.1 fun u => ?_
  rcases le_or_gt 0 u with h0 | h0
  · rw [hF.2.2.2.2.2.1 u h0]
    simp
  · exact le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by linarith))

/-- **The state has a strict sign at the wall.** The edge constant does not vanish, so near the wall
the state is, almost everywhere, of the strict sign of `ℓ`, and `|F(−s)| √log(1/s) → |ℓ|` with
`ℓ² ≥ 8 a(W₀) > 0`. -/
theorem criticalState_edge_constant_ne_zero {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ (∀ᵐ s, s ∈ Ioo (0 : ℝ) (1 / 4) → F (-s) = Φ s) ∧
      ∃ ℓ : ℝ, Tendsto (fun s => Φ s * Real.sqrt (Real.log (1 / s))) (𝓝[>] 0) (𝓝 ℓ) ∧
        8 * criticalAliasCoefficient W₀ ≤ ℓ ^ 2 ∧
        ∃ δ > 0, ∀ᵐ s, s ∈ Ioo (0 : ℝ) δ → 0 < ℓ * F (-s) := by
  obtain ⟨Φ, hΦc, hFΦ, ℓ, hψ, hℓ⟩ := criticalState_pointwise_edge_law hW ht hF
  have ha := criticalAliasCoefficient_positive hW
  have hI := criticalState_one_le_confinementMass hF
  have h8 : 8 * criticalAliasCoefficient W₀ ≤ ℓ ^ 2 := by
    rw [hℓ]
    nlinarith
  have hℓ0 : 0 < ℓ ^ 2 := lt_of_lt_of_le (by positivity) h8
  have hsign : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < ℓ * (Φ s * Real.sqrt (Real.log (1 / s))) :=
    (hψ.const_mul ℓ).eventually (lt_mem_nhds (by rw [← sq]; exact hℓ0))
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.mp hsign
  refine ⟨Φ, hΦc, hFΦ, ℓ, hψ, h8, min δ (1 / 4), lt_min hδ (by norm_num), ?_⟩
  filter_upwards [hFΦ] with s hs hsI
  have hs0 : (0 : ℝ) < s := hsI.1
  have hsδ : s < δ := lt_of_lt_of_le hsI.2 (min_le_left _ _)
  have hs4 : s < 1 / 4 := lt_of_lt_of_le hsI.2 (min_le_right _ _)
  have h : 0 < ℓ * (Φ s * Real.sqrt (Real.log (1 / s))) :=
    hδs ⟨Metric.mem_ball.mpr (by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; exact hsδ), hs0⟩
  rw [hs ⟨hs0, hs4⟩]
  have hsq : 0 ≤ Real.sqrt (Real.log (1 / s)) := Real.sqrt_nonneg _
  rw [← mul_assoc] at h
  exact (pos_and_pos_or_neg_and_neg_of_mul_pos h).elim (fun h' => h'.1)
    fun h' => absurd h'.2 (not_lt.mpr hsq)

#print axioms criticalState_pointwise_edge_law
#print axioms criticalState_edge_constant_ne_zero

/-! ### The profile beyond the wall -/

/-- The Stieltjes potential of the state grows like `2ℓ √log(1/x)`: it differs from the logarithmic
moment by a bounded amount. -/
theorem tendsto_wallPotential_div_sqrt_log {F Φ : ℝ → ℝ} (hFm : Measurable F) (hFi : Integrable F)
    {C : ℝ} (hb : ∀ᵐ u, |F u| ≤ C) (hΦ : Continuous Φ)
    (hFΦ : ∀ᵐ s, s ∈ Ioo (0 : ℝ) (1 / 4) → F (-s) = Φ s) {ℓ : ℝ}
    (hψ : Tendsto (fun s => Φ s * Real.sqrt (Real.log (1 / s))) (𝓝[>] 0) (𝓝 ℓ)) :
    Tendsto (fun x => wallPotential F x / Real.sqrt (Real.log (1 / x))) (𝓝[>] 0) (𝓝 (2 * ℓ)) := by
  have hB := tendsto_wallLogMoment_div_sqrt_log hFm hFi hΦ hFΦ hψ
  have hup := (tendsto_const_nhds (x := 5 * C)).div_atTop tendsto_sqrt_log_one_div
  have hlo := (tendsto_const_nhds (x := -(5 * C))).div_atTop tendsto_sqrt_log_one_div
  have hbd : ∀ᶠ x in 𝓝[>] (0 : ℝ), |wallPotential F x - wallLogMoment F x| ≤ 5 * C := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have h := abs_wallPotential_sub_wallLogMoment_le hFm hFi hb hx0 le_rfl
    rwa [mul_assoc, ← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero, mul_one,
      show C + 4 * C = 5 * C by ring] at h
  have hdiff : Tendsto (fun x => (wallPotential F x - wallLogMoment F x) /
      Real.sqrt (Real.log (1 / x))) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
    · filter_upwards [hbd] with x hx
      exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp hx).1]) (Real.sqrt_nonneg _)
    · filter_upwards [hbd] with x hx
      exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp hx).2]) (Real.sqrt_nonneg _)
  have h := hB.add hdiff
  rw [add_zero] at h
  refine h.congr fun x => ?_
  rw [← add_div]
  ring_nf

/-- **The profile beyond the wall at the wall.** With the edge constant `ℓ` of the state,
`a F⁺(x) = −ℓ √log(1/x) (1 + o(1))` as `x → 0⁺`: for every `ε > 0` there is `δ > 0` with
`‖a F⁺(x) + ℓ √log(1/x)‖ ≤ ε √log(1/x)` for almost every `x ∈ (0, δ)`. -/
theorem criticalState_beyondWall_edge_law {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ (∀ᵐ s, s ∈ Ioo (0 : ℝ) (1 / 4) → F (-s) = Φ s) ∧
      ∃ ℓ : ℝ, Tendsto (fun s => Φ s * Real.sqrt (Real.log (1 / s))) (𝓝[>] 0) (𝓝 ℓ) ∧
        ℓ ^ 2 = 8 * criticalAliasCoefficient W₀ * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ∧
        ∀ ε > 0, ∃ δ > 0, ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) δ)),
          ‖(criticalAliasCoefficient W₀ : ℂ) *
              beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x +
            ((ℓ * Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ)‖ ≤ ε * Real.sqrt (Real.log (1 / x)) := by
  obtain ⟨Φ, hΦc, hFΦ, ℓ, hψ, hℓ⟩ := criticalState_pointwise_edge_law hW ht hF
  refine ⟨Φ, hΦc, hFΦ, ℓ, hψ, hℓ, fun ε hε => ?_⟩
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, -, -, hb⟩ := criticalState_ae_abs_le hW ht hF
  obtain ⟨B, hB0, hBae⟩ := criticalState_exists_ae_norm_beyondWall_add_wallPotential_le hW ht hF
  have hP := tendsto_wallPotential_div_sqrt_log hd.meas hd.integrable hb hΦc hFΦ hψ
  have hP' : Tendsto (fun x => (1 / 2 * wallPotential F x) / Real.sqrt (Real.log (1 / x)))
      (𝓝[>] 0) (𝓝 ℓ) := by
    have h := hP.const_mul (1 / 2)
    rw [show 1 / 2 * (2 * ℓ) = ℓ by ring] at h
    exact h.congr fun x => by ring
  have hev1 : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      |(1 / 2 * wallPotential F x) / Real.sqrt (Real.log (1 / x)) - ℓ| < ε / 2 :=
    (Metric.tendsto_nhds.mp hP') (ε / 2) (half_pos hε) |>.mono fun x hx => by
      rwa [Real.dist_eq] at hx
  have hev2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), 2 * B / ε < Real.sqrt (Real.log (1 / x)) :=
    tendsto_sqrt_log_one_div.eventually_gt_atTop _
  have hev3 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.mp ((hev1.and hev2).and hev3)
  refine ⟨min δ 1, lt_min hδ one_pos, ?_⟩
  have hsub : Ioo (0 : ℝ) (min δ 1) ⊆ Ioo 0 1 := Ioo_subset_Ioo_right (min_le_right _ _)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hBae,
    ae_restrict_mem measurableSet_Ioo] with x hx hmem
  have hx0 : (0 : ℝ) < x := hmem.1
  have hxδ : x < δ := lt_of_lt_of_le hmem.2 (min_le_left _ _)
  obtain ⟨⟨h1, h2⟩, h3⟩ : _ := hδs
    ⟨Metric.mem_ball.mpr (by rw [Real.dist_eq, sub_zero, abs_of_pos hx0]; exact hxδ), hx0⟩
  have hL : 0 < Real.sqrt (Real.log (1 / x)) := lt_of_le_of_lt (by positivity) h2
  have hpot : |1 / 2 * wallPotential F x - ℓ * Real.sqrt (Real.log (1 / x))| ≤
      ε / 2 * Real.sqrt (Real.log (1 / x)) := by
    have e : 1 / 2 * wallPotential F x - ℓ * Real.sqrt (Real.log (1 / x)) =
        ((1 / 2 * wallPotential F x) / Real.sqrt (Real.log (1 / x)) - ℓ) *
          Real.sqrt (Real.log (1 / x)) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hL]
    exact mul_le_mul_of_nonneg_right h1.le hL.le
  have hBε : B ≤ ε / 2 * Real.sqrt (Real.log (1 / x)) := by
    rw [div_lt_iff₀ hε] at h2
    linarith
  calc ‖(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x +
        ((ℓ * Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ)‖ ≤
      ‖(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hd x +
          ((1 / 2 * wallPotential F x : ℝ) : ℂ)‖ +
        ‖((ℓ * Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ) - ((1 / 2 * wallPotential F x : ℝ) : ℂ)‖ := by
        refine le_trans (le_of_eq ?_) (norm_add_le _ _)
        congr 1
        ring
    _ ≤ B + ε / 2 * Real.sqrt (Real.log (1 / x)) := by
        refine add_le_add hx ?_
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        exact hpot
    _ ≤ ε * Real.sqrt (Real.log (1 / x)) := by linarith

#print axioms criticalState_beyondWall_edge_law

end GaloisForLFunctions.ExclusionOfTheCriticalState
