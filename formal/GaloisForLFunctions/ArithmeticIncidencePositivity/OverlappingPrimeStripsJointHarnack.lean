import GaloisForLFunctions.ArithmeticIncidencePositivity.WideMicroFoldExactRates
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimePowerEvenPartHarnack

/-!
# Harnack across the overlapping strips of `2` and `3`

For odd `F` supported in `[−r, r]` the atom of `n` couples `x ↔ log n − x` on the strip
`S_n = [log n − r, r]`. Past `r = ½ log 3` the strips overlap, `S₃ ⊂ S₂`, and both atoms would draw on
the archimedean surplus of `S₃ × S₃`. At `r = 221/400` the strip of `2` is wide: its half-width
`η = r − ½ log 2 ≈ 0.206` exceeds its distance `p = log 2 − r ≈ 0.141` to the origin, beyond the
sharp micro-fold (`η ≤ p`, `η ≤ 1/12`).

* **Integrated wide weight** (`integral_wideFoldWeight_eq`). In folded coordinates `u, v ∈ [0, η]`
  the exact-rate weight of `WideMicroFoldExactRates` splits as `W = 2k(1 − q) − 2D(1 − q) + 4R₊`,
  `q = (β + v)/(β + u)`: the surplus kernel `k` gives the surplus potential in the gauge `β + t`; the
  defect `D(u, v) = ω(L − u − v) − ω(L − |u − v|)` costs `≤ (c₁u³/6 + c₀u²/2)/(β + u)`
  (`integral_wideFoldDefect_le`); the crossing rate integrates to three windows of `ω` and costs at
  most `log L − log(L − η)` by concavity of `log` (`wideCrossRate_integral_ge`).
* **Withholding a square** (`integral_wideFoldWeightBand_ge`, `wideFoldWeight_le_band`). Removing
  the pairs of `[c, r]²` from the fold kills the weight on the band `u, v ≥ c − L/2` and costs at most
  `M(η − b)`, `M` the explicit bound of `W` there.
* **Potential of the strip of `2`** (`wideBandFold_potential_logTwo`). At `r = 221/400`, gauge
  `1/50 + t`, the band of `S₃` withheld: `∫_0^η W_band(u, v) dv ≥ 1` at every folded point, against the
  atom's `2Λ(2)/√2 = √2 log 2 < 0.9805`.
* **Sharing** (`integral_box_eq_withheld_add`). The surplus of `S₂ × S₂` is the surplus with
  `S₃ × S₃` withheld plus the surplus of `S₃ × S₃`.
* **Joint Harnack** (`two_mul_primeTwoThreeShifts_le_stripSurplus_sub`). `S₃ × S₃` pays the atom of
  `3` by the sharp micro-fold, the rest of `S₂ × S₂` pays the atom of `2` by the wide micro-fold, and
  both strips keep potential: `1/62` per unit of `∫_{S₂} F²` and `½` per unit of `∫_{S₃} F²`.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### Integrals of `ω` to second order -/

theorem continuousOn_archLevyDensity_uIcc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn archLevyDensity (uIcc a b) :=
  continuousOn_archLevyDensity.mono fun t ht => by
    rw [uIcc_of_le hab] at ht; exact mem_Ioi.mpr (lt_of_lt_of_le ha ht.1)

/-- `∫_a^b ω ≥ ½ log(b/a) + (b − a)/4 − (b² − a²)/96 − (b³ − a³)/96` for `0 < a ≤ b ≤ 3/4`. -/
theorem integral_archLevyDensity_ge_secondOrder {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 3 / 4) :
    (Real.log b - Real.log a) / 2 + (b - a) / 4 - (b ^ 2 - a ^ 2) / 96 - (b ^ 3 - a ^ 3) / 96 ≤
      ∫ t in a..b, archLevyDensity t := by
  have hF : ∀ t ∈ uIcc a b, HasDerivAt (fun t => Real.log t / 2 + t / 4 - t ^ 2 / 96 - t ^ 3 / 96)
      (1 / (2 * t) + 1 / 4 - t / 48 - t ^ 2 / 32) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have h := ((((Real.hasDerivAt_log ht0.ne').div_const 2).add ((hasDerivAt_id t).div_const 4)).sub
      ((hasDerivAt_pow 2 t).div_const 96)).sub ((hasDerivAt_pow 3 t).div_const 96)
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    field_simp
    ring
  have hcont : ContinuousOn (fun t => 1 / (2 * t) + 1 / 4 - t / 48 - t ^ 2 / 32) (uIcc a b) := by
    refine ((ContinuousOn.add ?_ continuousOn_const).sub (by fun_prop)).sub (by fun_prop)
    refine continuousOn_const.div (by fun_prop) fun t ht => ?_
    rw [uIcc_of_le hab] at ht; have := lt_of_lt_of_le ha ht.1; positivity
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable
  have hmono : (∫ t in a..b, (1 / (2 * t) + 1 / 4 - t / 48 - t ^ 2 / 32)) ≤
      ∫ t in a..b, archLevyDensity t :=
    intervalIntegral.integral_mono_on hab hcont.intervalIntegrable
      (continuousOn_archLevyDensity_uIcc ha hab).intervalIntegrable fun t ht =>
        (archLevyDensity_secondOrder_bounds (lt_of_lt_of_le ha ht.1) (le_trans ht.2 hb)).1
  rw [hint] at hmono
  linarith

/-- `∫_a^b ω ≤ ½ log(b/a) + (b − a)/4 − (b² − a²)/96 − (b³ − a³)/96 + (b⁴ − a⁴)/1000` for
`0 < a ≤ b ≤ 3/4`. -/
theorem integral_archLevyDensity_le_secondOrder {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 3 / 4) :
    (∫ t in a..b, archLevyDensity t) ≤
      (Real.log b - Real.log a) / 2 + (b - a) / 4 - (b ^ 2 - a ^ 2) / 96 - (b ^ 3 - a ^ 3) / 96 +
        (b ^ 4 - a ^ 4) / 1000 := by
  have hF : ∀ t ∈ uIcc a b, HasDerivAt
      (fun t => Real.log t / 2 + t / 4 - t ^ 2 / 96 - t ^ 3 / 96 + t ^ 4 / 1000)
      (1 / (2 * t) + 1 / 4 - t / 48 - t ^ 2 / 32 + t ^ 3 / 250) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have h := (((((Real.hasDerivAt_log ht0.ne').div_const 2).add ((hasDerivAt_id t).div_const 4)).sub
      ((hasDerivAt_pow 2 t).div_const 96)).sub ((hasDerivAt_pow 3 t).div_const 96)).add
      ((hasDerivAt_pow 4 t).div_const 1000)
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    field_simp
    ring
  have hcont : ContinuousOn (fun t => 1 / (2 * t) + 1 / 4 - t / 48 - t ^ 2 / 32 + t ^ 3 / 250)
      (uIcc a b) := by
    refine (((ContinuousOn.add ?_ continuousOn_const).sub (by fun_prop)).sub (by fun_prop)).add
      (by fun_prop)
    refine continuousOn_const.div (by fun_prop) fun t ht => ?_
    rw [uIcc_of_le hab] at ht; have := lt_of_lt_of_le ha ht.1; positivity
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable
  have hmono : (∫ t in a..b, archLevyDensity t) ≤
      ∫ t in a..b, (1 / (2 * t) + 1 / 4 - t / 48 - t ^ 2 / 32 + t ^ 3 / 250) :=
    intervalIntegral.integral_mono_on hab (continuousOn_archLevyDensity_uIcc ha hab).intervalIntegrable
      hcont.intervalIntegrable fun t ht =>
        (archLevyDensity_secondOrder_bounds (lt_of_lt_of_le ha ht.1) (le_trans ht.2 hb)).2
  rw [hint] at hmono
  linarith

/-! ### The integrated wide weight -/

/-- The crossing rate integrates to three windows of `ω`:
`∫_0^η R₊(u, v) dv = ∫_u^{u+η} ω − ∫_{L−u}^{L} ω − ∫_{L+u−η}^{L} ω`. -/
theorem integral_wideCrossRate {L η u : ℝ} (hu : 0 < u) (huη : u ≤ η) (hLη : η < L) :
    (∫ v in (0 : ℝ)..η, wideCrossRate L u v) =
      (∫ t in u..(u + η), archLevyDensity t) - (∫ t in (L - u)..L, archLevyDensity t) -
        ∫ t in (L + u - η)..L, archLevyDensity t := by
  unfold wideCrossRate
  have hη : 0 ≤ η := by linarith
  have h1 : IntervalIntegrable (fun v => archLevyDensity (u + v)) volume 0 η := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_archLevyDensity.comp (by fun_prop) fun v hv => ?_
    rw [uIcc_of_le hη] at hv; exact mem_Ioi.mpr (by linarith [hv.1])
  have hc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ η →
      ContinuousOn (fun v => archLevyDensity (L - |u - v|)) (uIcc a b) := fun a b ha hab hb => by
    refine continuousOn_archLevyDensity.comp (by fun_prop) fun v hv => ?_
    rw [uIcc_of_le hab] at hv
    have : |u - v| < L := abs_lt.mpr ⟨by linarith [hv.1, hv.2], by linarith [hv.1, hv.2]⟩
    exact mem_Ioi.mpr (by linarith)
  have h2 : IntervalIntegrable (fun v => archLevyDensity (L - |u - v|)) volume 0 η :=
    (hc 0 η le_rfl hη le_rfl).intervalIntegrable
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_comp_add_left
    (fun t => archLevyDensity t) u, add_zero]
  -- split the reflected window at `v = u`
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := u)
    (hc 0 u le_rfl hu.le huη).intervalIntegrable (hc u η hu.le huη le_rfl).intervalIntegrable]
  have eL : (∫ v in (0 : ℝ)..u, archLevyDensity (L - |u - v|)) = ∫ t in (L - u)..L, archLevyDensity t := by
    have e : EqOn (fun v => archLevyDensity (L - |u - v|)) (fun v => archLevyDensity ((L - u) + v))
        (uIcc 0 u) := fun v hv => by
      rw [uIcc_of_le hu.le] at hv
      simp only [abs_of_nonneg (by linarith [hv.2] : 0 ≤ u - v)]; ring_nf
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_comp_add_left
      (fun t => archLevyDensity t) (L - u), add_zero, sub_add_cancel]
  have eR : (∫ v in u..η, archLevyDensity (L - |u - v|)) = ∫ t in (L + u - η)..L, archLevyDensity t := by
    have e : EqOn (fun v => archLevyDensity (L - |u - v|)) (fun v => archLevyDensity ((L + u) - v))
        (uIcc u η) := fun v hv => by
      rw [uIcc_of_le huη] at hv
      simp only [abs_of_nonpos (by linarith [hv.1] : u - v ≤ 0)]; ring_nf
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_comp_sub_left
      (fun t => archLevyDensity t) (L + u), show L + u - u = L by ring]
  rw [eL, eR]
  ring

/-- The surplus in the gauge `β + t`, as an interval integral. -/
theorem integral_surplus_affineGauge {β η u : ℝ} (hη : 0 ≤ η) :
    (∫ v in (0 : ℝ)..η, surplusKernel u v * (1 - (β + v) / (β + u))) =
      surplusPotential (cubicGauge β 1 0 0) η u := by
  unfold surplusPotential
  rw [intervalIntegral.integral_of_le hη]
  refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
  simp only [cubicGauge]; ring_nf

/-- The defect `D(u, v) = ω(L − u − v) − ω(L − |u − v|)` of the wide fold. -/
def wideFoldDefect (L u v : ℝ) : ℝ := archLevyDensity (L - (u + v)) - archLevyDensity (L - |u - v|)

theorem wideFoldWeight_eq (L β u v : ℝ) :
    wideFoldWeight L β u v = 2 * (surplusKernel u v * (1 - (β + v) / (β + u))) -
      2 * (wideFoldDefect L u v * (1 - (β + v) / (β + u))) + 4 * wideCrossRate L u v := by
  unfold wideFoldWeight wideSameRate wideCrossRate wideFoldDefect surplusKernel
  ring

/-- **The defect integral.** For `0 < u ≤ η`, `2η < L ≤ 3/4`:
`∫_0^η D(u, v)(1 − (β + v)/(β + u)) dv ≤ (c₁ u³/6 + c₀ u²/2)/(β + u)`, with
`c₁ ≥ 1/(L(L − 2η)) + 1/24 + L/8` and `c₀ ≥ L³/250`: the defect lives on `v < u`, where
`D ≤ v/((L − u)² − v²) + v/24 + (L − u)v/8 + (L − u − v)³/250`. -/
theorem integral_wideFoldDefect_le {L β η u c₁ c₀ : ℝ} (hβ : 0 < β) (hu : 0 < u) (huη : u ≤ η)
    (hLη : 2 * η < L) (hL : L ≤ 3 / 4) (hc₁ : 1 / (L * (L - 2 * η)) + 1 / 24 + L / 8 ≤ c₁)
    (hc₀ : L ^ 3 / 250 ≤ c₀) :
    (∫ v in (0 : ℝ)..η, wideFoldDefect L u v * (1 - (β + v) / (β + u))) ≤
      (c₁ * u ^ 3 / 6 + c₀ * u ^ 2 / 2) / (β + u) := by
  have hβu : 0 < β + u := by linarith
  have hc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ η →
      ContinuousOn (fun v => wideFoldDefect L u v * (1 - (β + v) / (β + u))) (uIcc a b) :=
    fun a b ha hab hb => by
      unfold wideFoldDefect
      have hpos : ∀ v ∈ uIcc a b, 0 < L - (u + v) ∧ 0 < L - |u - v| := fun v hv => by
        rw [uIcc_of_le hab] at hv
        have : |u - v| ≤ u + v := abs_le.mpr ⟨by linarith [hv.1, hv.2], by linarith [hv.1, hv.2]⟩
        constructor <;> linarith [hv.1, hv.2]
      refine ContinuousOn.mul (ContinuousOn.sub ?_ ?_) (by fun_prop)
      · exact continuousOn_archLevyDensity.comp (by fun_prop) fun v hv => mem_Ioi.mpr (hpos v hv).1
      · exact continuousOn_archLevyDensity.comp (by fun_prop) fun v hv => mem_Ioi.mpr (hpos v hv).2
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := u)
    (hc 0 u le_rfl hu.le huη).intervalIntegrable (hc u η hu.le huη le_rfl).intervalIntegrable]
  -- above `u` the defect term is nonpositive
  have hR : (∫ v in u..η, wideFoldDefect L u v * (1 - (β + v) / (β + u))) ≤ 0 := by
    refine (intervalIntegral.integral_mono_on huη (hc u η hu.le huη le_rfl).intervalIntegrable
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (0 : ℝ)) volume u η)
      fun v hv => ?_).trans_eq (by simp)
    have hab : |u - v| ≤ u + v := abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.1]⟩
    have hD : 0 ≤ wideFoldDefect L u v := by
      unfold wideFoldDefect
      exact sub_nonneg.mpr (strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith [hv.2]))
        (mem_Ioi.mpr (by linarith [hv.2])) (by linarith))
    have hq : 1 - (β + v) / (β + u) ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hβu]; linarith [hv.1]
    exact mul_nonpos_of_nonneg_of_nonpos hD hq
  -- below `u` the defect is at most `c₁ v + c₀`
  have hL0 : 0 < L - 2 * η := by linarith
  have hLpos : 0 < L := by linarith
  have hpt : ∀ v ∈ Icc (0 : ℝ) u, wideFoldDefect L u v * (1 - (β + v) / (β + u)) ≤
      (c₁ * v + c₀) * (u - v) / (β + u) := fun v hv => by
    have hvu : |u - v| = u - v := abs_of_nonneg (by linarith [hv.2])
    have ha0 : 0 < L - (u + v) := by linarith [hv.2]
    have hb0 : 0 < L - (u - v) := by linarith [hv.1, hv.2]
    have hb1 : L - (u - v) ≤ 3 / 4 := by linarith [hv.1, hv.2]
    obtain ⟨-, hω1⟩ := archLevyDensity_secondOrder_bounds ha0 (by linarith [hv.1])
    obtain ⟨hω2, -⟩ := archLevyDensity_secondOrder_bounds hb0 hb1
    have hprod : L * (L - 2 * η) ≤ (L - (u + v)) * (L - (u - v)) := by nlinarith [hv.1, hv.2]
    have hpp : 0 < L * (L - 2 * η) := by positivity
    have hinv : 1 / (2 * (L - (u + v))) - 1 / (2 * (L - (u - v))) ≤ v * (1 / (L * (L - 2 * η))) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
      have h1 : v * (1 / (L * (L - 2 * η))) * (2 * (L - (u + v)) * (2 * (L - (u - v)))) =
          4 * v * ((L - (u + v)) * (L - (u - v)) / (L * (L - 2 * η))) := by field_simp; ring
      rw [h1]
      have h2 : 1 ≤ (L - (u + v)) * (L - (u - v)) / (L * (L - 2 * η)) := by rw [le_div_iff₀ hpp]; linarith
      nlinarith [hv.1]
    have hcube : (L - (u + v)) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ ha0.le (by linarith [hv.1]) 3
    have hD : wideFoldDefect L u v ≤ c₁ * v + c₀ := by
      unfold wideFoldDefect
      rw [hvu]
      have hv0 : 0 ≤ v := hv.1
      have hc1v : (1 / (L * (L - 2 * η)) + 1 / 24 + L / 8) * v ≤ c₁ * v := mul_le_mul_of_nonneg_right hc₁ hv0
      nlinarith [hinv, hcube]
    have hq : 1 - (β + v) / (β + u) = (u - v) / (β + u) := by field_simp; ring
    rw [hq, mul_div_assoc']
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hD (by linarith [hv.2])) hβu.le
  have hF : ∀ v ∈ uIcc 0 u, HasDerivAt
      (fun v => (c₁ * u / 2 * v ^ 2 - c₁ / 3 * v ^ 3 + c₀ * u * v - c₀ / 2 * v ^ 2) / (β + u))
      ((c₁ * v + c₀) * (u - v) / (β + u)) v := fun v _ => by
    have h := (((((hasDerivAt_pow 2 v).const_mul (c₁ * u / 2)).sub
      ((hasDerivAt_pow 3 v).const_mul (c₁ / 3))).add ((hasDerivAt_id' v).const_mul (c₀ * u))).sub
      ((hasDerivAt_pow 2 v).const_mul (c₀ / 2))).div_const (β + u)
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  have hint : IntervalIntegrable (fun v => (c₁ * v + c₀) * (u - v) / (β + u)) volume 0 u := by
    apply Continuous.intervalIntegrable; fun_prop
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  have hmono := intervalIntegral.integral_mono_on hu.le (hc 0 u le_rfl hu.le huη).intervalIntegrable hint hpt
  rw [hval] at hmono
  have e : (c₁ * u / 2 * u ^ 2 - c₁ / 3 * u ^ 3 + c₀ * u * u - c₀ / 2 * u ^ 2) / (β + u) -
      (c₁ * u / 2 * 0 ^ 2 - c₁ / 3 * 0 ^ 3 + c₀ * u * 0 - c₀ / 2 * 0 ^ 2) / (β + u) =
      (c₁ * u ^ 3 / 6 + c₀ * u ^ 2 / 2) / (β + u) := by ring
  rw [e] at hmono
  linarith

/-- **The wide weight on the band.** For `0 < b ≤ u, v ≤ η`, `2η < L ≤ 1`:
`W(u, v) ≤ (1 + (η − b)/2)/(β + b) + 2ω(L − 2η)(η − b)/(β + b) + 4(ω(2b) − ω(L))`. -/
theorem wideFoldWeight_le_band {L β η b u v : ℝ} (hβ : 0 < β) (hb : 0 < b) (hbu : b ≤ u)
    (hu : u ≤ η) (hbv : b ≤ v) (hv : v ≤ η) (hLη : 2 * η < L) (hL : L ≤ 1) :
    wideFoldWeight L β u v ≤ (1 + (η - b) / 2) / (β + b) +
      2 * archLevyDensity (L - 2 * η) * (η - b) / (β + b) +
        4 * (archLevyDensity (2 * b) - archLevyDensity L) := by
  have hβu : 0 < β + u := by linarith
  have hβb : 0 < β + b := by linarith
  have hq : 1 - (β + v) / (β + u) = (u - v) / (β + u) := by field_simp; ring
  have hab : |u - v| ≤ u + v := abs_le.mpr ⟨by linarith, by linarith⟩
  have hωL := archLevyDensity_pos (show 0 < L by linarith)
  have hω2η := archLevyDensity_pos (show 0 < L - 2 * η by linarith)
  -- the surplus part: only `v < u` contributes, at most `(1/2 + (u − v)/4)/(β + u)`
  have h1 : 2 * (surplusKernel u v * (1 - (β + v) / (β + u))) ≤ (1 + (η - b) / 2) / (β + b) := by
    rw [hq]
    have hR : 0 ≤ (1 + (η - b) / 2) / (β + b) := div_nonneg (by linarith) hβb.le
    rcases le_or_gt u v with huv | huv
    · have : surplusKernel u v * ((u - v) / (β + u)) ≤ 0 := by
        rcases eq_or_lt_of_le huv with h | h
        · rw [h, sub_self, zero_div, mul_zero]
        · exact mul_nonpos_of_nonneg_of_nonpos (surplusKernel_nonneg (by linarith) (by linarith) h.ne)
            (div_nonpos_of_nonpos_of_nonneg (by linarith) hβu.le)
      linarith
    · have hd : 0 < u - v := by linarith
      have hm := mul_archLevyDensity_le hd (by linarith)
      have hk : surplusKernel u v * (u - v) ≤ 1 / 2 + (u - v) / 4 := by
        unfold surplusKernel
        rw [abs_of_pos hd]
        have := archLevyDensity_pos (show 0 < u + v by linarith)
        nlinarith
      rw [show 2 * (surplusKernel u v * ((u - v) / (β + u))) =
        2 * (surplusKernel u v * (u - v)) / (β + u) by ring, div_le_div_iff₀ hβu hβb]
      have h2 : 2 * (surplusKernel u v * (u - v)) ≤ 1 + (η - b) / 2 := by linarith
      have h3 : 0 ≤ 1 + (η - b) / 2 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left (show β + b ≤ β + u by linarith) h3]
  -- the defect part: only `v > u` contributes, at most `2ω(L − 2η)(η − b)/(β + b)`
  have hD0 : 0 ≤ wideFoldDefect L u v := by
    unfold wideFoldDefect
    exact sub_nonneg.mpr (strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith))
      (mem_Ioi.mpr (by linarith)) (by linarith))
  have hD1 : wideFoldDefect L u v ≤ archLevyDensity (L - 2 * η) := by
    unfold wideFoldDefect
    have h := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : 0 < L - 2 * η))
      (mem_Ioi.mpr (by linarith : 0 < L - (u + v))) (by linarith)
    have := archLevyDensity_pos (show 0 < L - |u - v| by linarith)
    linarith
  have h2 : -(2 * (wideFoldDefect L u v * (1 - (β + v) / (β + u)))) ≤
      2 * archLevyDensity (L - 2 * η) * (η - b) / (β + b) := by
    rw [hq]
    have hR : 0 ≤ 2 * archLevyDensity (L - 2 * η) * (η - b) / (β + b) :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) hβb.le
    rcases le_or_gt v u with hvu | hvu
    · have : 0 ≤ wideFoldDefect L u v * ((u - v) / (β + u)) :=
        mul_nonneg hD0 (div_nonneg (by linarith) hβu.le)
      linarith
    · rw [show -(2 * (wideFoldDefect L u v * ((u - v) / (β + u)))) =
        2 * (wideFoldDefect L u v * (v - u)) / (β + u) by ring, div_le_div_iff₀ hβu hβb]
      have h4 : wideFoldDefect L u v * (v - u) ≤ archLevyDensity (L - 2 * η) * (η - b) :=
        mul_le_mul hD1 (by linarith) (by linarith) hω2η.le
      have h5 : 0 ≤ archLevyDensity (L - 2 * η) * (η - b) := mul_nonneg hω2η.le (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left (show β + b ≤ β + u by linarith) h5,
        mul_le_mul_of_nonneg_right h4 hβb.le]
  -- the crossing part
  have h3 : wideCrossRate L u v ≤ archLevyDensity (2 * b) - archLevyDensity L := by
    unfold wideCrossRate
    have h6 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : 0 < 2 * b))
      (mem_Ioi.mpr (by linarith : 0 < u + v)) (by linarith)
    have h7 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : 0 < L - |u - v|))
      (mem_Ioi.mpr (by linarith : 0 < L)) (by linarith [abs_nonneg (u - v)])
    linarith
  rw [wideFoldWeight_eq]
  linarith

theorem measurable_wideFoldWeight (L β : ℝ) : Measurable (Function.uncurry (wideFoldWeight L β)) := by
  unfold wideFoldWeight wideSameRate wideCrossRate
  have h1 : Measurable fun z : ℝ × ℝ => archLevyDensity |z.1 - z.2| :=
    measurable_archLevyDensity.comp (measurable_fst.sub measurable_snd).abs
  have h2 : Measurable fun z : ℝ × ℝ => archLevyDensity (L - (z.1 + z.2)) :=
    measurable_archLevyDensity.comp (measurable_const.sub (measurable_fst.add measurable_snd))
  have h3 : Measurable fun z : ℝ × ℝ => archLevyDensity (z.1 + z.2) :=
    measurable_archLevyDensity.comp (measurable_fst.add measurable_snd)
  have h4 : Measurable fun z : ℝ × ℝ => archLevyDensity (L - |z.1 - z.2|) :=
    measurable_archLevyDensity.comp (measurable_const.sub (measurable_fst.sub measurable_snd).abs)
  exact ((((h1.sub h2).sub (h3.sub h4)).mul (measurable_const.sub ((measurable_const.add measurable_snd).div
    (measurable_const.add measurable_fst)))).const_mul 2).add ((h3.sub h4).const_mul 4)

/-- The wide weight at a folded point `u > 0` is bounded on `[0, η]`. -/
theorem abs_wideFoldWeight_le_of_mem {L β η u v : ℝ} (hβ : 0 < β) (hu : 0 < u) (huη : u ≤ η)
    (hv : v ∈ Icc 0 η) (hLη : 2 * η < L) (hη1 : η ≤ 1 / 2) :
    |wideFoldWeight L β u v| ≤ 3 / β + 2 * archLevyDensity (L - 2 * η) * η / β +
      4 * (archLevyDensity u + archLevyDensity (L - 2 * η)) := by
  have h := abs_wideFoldWeight_le (L := L) (p := (L - 2 * η) / 2) hβ (by linarith) hu hv.1 huη hv.2
    hη1 (by linarith)
  rw [show 2 * ((L - 2 * η) / 2) = L - 2 * η by ring] at h
  have hm : archLevyDensity (u + v) ≤ archLevyDensity u :=
    strictAntiOn_archLevyDensity.antitoneOn hu (show 0 < u + v by linarith [hv.1]) (by linarith [hv.1])
  linarith

/-- **The integrated wide weight**, split into the surplus, the defect and the crossing rate. -/
theorem integral_wideFoldWeight_eq {L β η u : ℝ} (hβ : 0 < β) (hu : 0 < u) (huη : u ≤ η)
    (hLη : 2 * η < L) (hη1 : η ≤ 1 / 2) :
    (∫ v in (0 : ℝ)..η, wideFoldWeight L β u v) =
      2 * surplusPotential (cubicGauge β 1 0 0) η u -
        2 * (∫ v in (0 : ℝ)..η, wideFoldDefect L u v * (1 - (β + v) / (β + u))) +
        4 * ∫ v in (0 : ℝ)..η, wideCrossRate L u v := by
  have hη : 0 ≤ η := by linarith
  have hi1 : IntervalIntegrable (fun v => surplusKernel u v * (1 - (β + v) / (β + u))) volume 0 η := by
    refine intervalIntegrable_of_abs_le (C := 3 / 2 * |(1 : ℝ)| / β) hη
      ((measurable_surplusKernel.of_uncurry_left).mul (measurable_const.sub
        ((measurable_const.add measurable_id).div measurable_const))) fun v hv => ?_
    rcases eq_or_lt_of_le hv.1 with h0 | h0
    · rw [← h0, surplusKernel_comm, surplusKernel_zero_left hu.le, zero_mul, abs_zero]
      positivity
    exact abs_surplusKernel_mul_le (h := fun t => β + t) hu h0
      (by rw [abs_le]; constructor <;> linarith [hv.1, hv.2]) hβ (by linarith)
      (by simp only [one_mul]; rw [show β + u - (β + v) = u - v by ring])
  have hi2 : IntervalIntegrable (fun v => wideFoldDefect L u v * (1 - (β + v) / (β + u))) volume 0 η := by
    refine ContinuousOn.intervalIntegrable ?_
    unfold wideFoldDefect
    have hpos : ∀ v ∈ uIcc 0 η, 0 < L - (u + v) ∧ 0 < L - |u - v| := fun v hv => by
      rw [uIcc_of_le hη] at hv
      have : |u - v| ≤ u + v := abs_le.mpr ⟨by linarith [hv.1, hv.2], by linarith [hv.1, hv.2]⟩
      constructor <;> linarith [hv.1, hv.2]
    refine ContinuousOn.mul (ContinuousOn.sub ?_ ?_) ?_
    · exact continuousOn_archLevyDensity.comp (by fun_prop) fun v hv => mem_Ioi.mpr (hpos v hv).1
    · exact continuousOn_archLevyDensity.comp (by fun_prop) fun v hv => mem_Ioi.mpr (hpos v hv).2
    · exact continuousOn_const.sub ((continuousOn_const.add continuousOn_id).div continuousOn_const
        fun _ _ => by linarith)
  have hi3 : IntervalIntegrable (fun v => wideCrossRate L u v) volume 0 η := by
    refine ContinuousOn.intervalIntegrable ?_
    unfold wideCrossRate
    refine ContinuousOn.sub ?_ ?_
    · refine continuousOn_archLevyDensity.comp (by fun_prop) fun v hv => ?_
      rw [uIcc_of_le hη] at hv; exact mem_Ioi.mpr (by linarith [hv.1])
    · refine continuousOn_archLevyDensity.comp (by fun_prop) fun v hv => ?_
      rw [uIcc_of_le hη] at hv
      have : |u - v| ≤ η := abs_le.mpr ⟨by linarith [hv.1, hv.2], by linarith [hv.1, hv.2]⟩
      exact mem_Ioi.mpr (by linarith)
  have e : (fun v => wideFoldWeight L β u v) = fun v =>
      2 * (surplusKernel u v * (1 - (β + v) / (β + u))) -
        2 * (wideFoldDefect L u v * (1 - (β + v) / (β + u))) + 4 * wideCrossRate L u v :=
    funext fun v => wideFoldWeight_eq L β u v
  rw [e, intervalIntegral.integral_add ((hi1.const_mul 2).sub (hi2.const_mul 2)) (hi3.const_mul 4),
    intervalIntegral.integral_sub (hi1.const_mul 2) (hi2.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_surplus_affineGauge hη]

theorem integral_indicator_Icc_one {b η : ℝ} (hb : 0 < b) (hbη : b ≤ η) :
    (∫ v in (0 : ℝ)..η, (Icc b η).indicator (fun _ => (1 : ℝ)) v) = η - b := by
  have hsub : Icc b η ∩ Ioc 0 η = Icc b η :=
    Set.inter_eq_left.mpr fun v hv => ⟨by linarith [hv.1], hv.2⟩
  rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, hsub, setIntegral_const,
    Real.volume_real_Icc_of_le hbη, smul_eq_mul, mul_one]

/-- **The band costs at most `M(η − b)`.** If `W(u, v) ≤ M` on the band, the band weight integrates to
at least `∫_0^η W − M(η − b)`. -/
theorem integral_wideFoldWeightBand_ge {L β η b u M : ℝ} (hβ : 0 < β) (hu : 0 < u) (huη : u ≤ η)
    (hLη : 2 * η < L) (hη1 : η ≤ 1 / 2) (hb : 0 < b) (hbη : b ≤ η)
    (hM : ∀ v, b ≤ u → b ≤ v → v ≤ η → wideFoldWeight L β u v ≤ M) (hM0 : 0 ≤ M) :
    (∫ v in (0 : ℝ)..η, wideFoldWeight L β u v) - M * (η - b) ≤
      ∫ v in (0 : ℝ)..η, wideFoldWeightBand L β b u v := by
  have hη : 0 ≤ η := by linarith
  set C := 3 / β + 2 * archLevyDensity (L - 2 * η) * η / β +
    4 * (archLevyDensity u + archLevyDensity (L - 2 * η)) with hC
  have hiW : IntervalIntegrable (fun v => wideFoldWeight L β u v) volume 0 η :=
    intervalIntegrable_of_abs_le hη (measurable_wideFoldWeight L β).of_uncurry_left
      fun v hv => abs_wideFoldWeight_le_of_mem hβ hu huη hv hLη hη1
  have hiB : IntervalIntegrable (fun v => wideFoldWeightBand L β b u v) volume 0 η :=
    intervalIntegrable_of_abs_le (C := C) hη (measurable_wideFoldWeightBand L β b).of_uncurry_left
      fun v hv => by
        unfold wideFoldWeightBand; split_ifs
        · rw [abs_zero]
          exact (abs_nonneg _).trans (abs_wideFoldWeight_le_of_mem hβ hu huη hv hLη hη1)
        · exact abs_wideFoldWeight_le_of_mem hβ hu huη hv hLη hη1
  have hiI : IntervalIntegrable (fun v => M * (Icc b η).indicator (fun _ => (1 : ℝ)) v) volume 0 η := by
    refine (intervalIntegrable_of_abs_le (C := 1) hη
      ((measurable_const.indicator measurableSet_Icc)) fun v _ => ?_).const_mul M
    simp only [Set.indicator_apply]; split_ifs <;> simp
  have hmono := intervalIntegral.integral_mono_on hη (hiW.sub hiI) hiB fun v hv => by
    show wideFoldWeight L β u v - M * (Icc b η).indicator (fun _ => (1 : ℝ)) v ≤
      wideFoldWeightBand L β b u v
    unfold wideFoldWeightBand
    by_cases h : b ≤ u ∧ b ≤ v
    · rw [if_pos h, Set.indicator_of_mem (show v ∈ Icc b η from ⟨h.2, hv.2⟩), mul_one]
      linarith [hM v h.1 h.2 hv.2]
    · rw [if_neg h]
      have : 0 ≤ (Icc b η).indicator (fun _ => (1 : ℝ)) v :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) v
      nlinarith
  rw [intervalIntegral.integral_sub hiW hiI, intervalIntegral.integral_const_mul,
    integral_indicator_Icc_one hb hbη] at hmono
  exact hmono

/-! ### The strip of `2` at the window `221/400` -/

/-- Numerical bounds for the window `r = 221/400`, `L = log 2`, `η = r − L/2`,
`b = log 3 − r − L/2`. -/
theorem logTwoStrip_numerics :
    0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 ∧
      1.0986122 < Real.log 3 ∧ Real.log 3 < 1.0986123 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2⟩

/-- `Λ = log L − log(L − η) ≤ 0.35256` for `L = log 2`, `η = 221/400 − L/2`: `L/(L − η) ≤ 1.4227`,
tangent of `log` at `64/45`. -/
theorem logTwoStrip_logRatio_le :
    Real.log (Real.log 2) - Real.log (Real.log 2 - (221 / 400 - Real.log 2 / 2)) ≤ 35256 / 100000 := by
  obtain ⟨h1, h2, -, -⟩ := logTwoStrip_numerics
  have hpos : 0 < Real.log 2 - (221 / 400 - Real.log 2 / 2) := by linarith
  have hL : 0 < Real.log 2 := by linarith
  rw [← Real.log_div hL.ne' hpos.ne']
  have hq : Real.log 2 / (Real.log 2 - (221 / 400 - Real.log 2 / 2)) ≤ 14227 / 10000 := by
    rw [div_le_iff₀ hpos]; linarith
  have ht := log_le_tangent (div_pos hL hpos) (show (0 : ℝ) < 64 / 45 by norm_num)
  have e := log_smooth_div 6 0 0 0 0 2 1 0
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  norm_num at e
  rw [e] at ht
  have : Real.log 2 / (Real.log 2 - (221 / 400 - Real.log 2 / 2)) / (64 / 45) ≤ 14227 / 10000 / (64 / 45) :=
    div_le_div_of_nonneg_right hq (by norm_num)
  linarith [l3.1, l5.1]

/-- The window data at `r = 221/400`: `η = r − log 2/2`, `b = log 3 − r − log 2/2`. -/
theorem logTwoStrip_window :
    2 * (221 / 400 - Real.log 2 / 2) < Real.log 2 ∧ 221 / 400 - Real.log 2 / 2 ≤ 1 / 2 ∧
      20592640 / 100000000 ≤ 221 / 400 - Real.log 2 / 2 ∧
      221 / 400 - Real.log 2 / 2 ≤ 20592641 / 100000000 ∧
      0 < Real.log 3 - 221 / 400 - Real.log 2 / 2 ∧
      Real.log 3 - 221 / 400 - Real.log 2 / 2 ≤ 221 / 400 - Real.log 2 / 2 ∧
      (221 / 400 - Real.log 2 / 2) - (Real.log 3 - 221 / 400 - Real.log 2 / 2) ≤ 63878 / 10000000 ∧
      1995386 / 10000000 ≤ Real.log 3 - 221 / 400 - Real.log 2 / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := logTwoStrip_numerics
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **The band of the strip of `3` costs the fold of `2` at most `0.044`.** -/
theorem logTwoStrip_band_cost {u : ℝ} (hu : 0 < u) (huη : u ≤ 221 / 400 - Real.log 2 / 2) :
    (∫ v in (0 : ℝ)..(221 / 400 - Real.log 2 / 2), wideFoldWeight (Real.log 2) (1 / 50) u v) - 44 / 1000 ≤
      ∫ v in (0 : ℝ)..(221 / 400 - Real.log 2 / 2),
        wideFoldWeightBand (Real.log 2) (1 / 50) (Real.log 3 - 221 / 400 - Real.log 2 / 2) u v := by
  obtain ⟨h1, h2, h3, h4⟩ := logTwoStrip_numerics
  obtain ⟨hLη, hη1, hη0, hη0', hb0, hbη, hηb, hb1⟩ := logTwoStrip_window
  set L := Real.log 2 with hLdef
  set η := 221 / 400 - L / 2 with hηdef
  set b := Real.log 3 - 221 / 400 - L / 2 with hbdef
  have hω1 : archLevyDensity (L - 2 * η) ≤ 202 / 100 := by
    have hm := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (show (0 : ℝ) < 2812 / 10000 by norm_num))
      (mem_Ioi.mpr (by linarith : 0 < L - 2 * η)) (by rw [hηdef]; linarith)
    have := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 2812 / 10000 by norm_num) (by norm_num)).2
    norm_num at this
    linarith
  have hω2 : archLevyDensity (2 * b) ≤ 14901 / 10000 := by
    have hm := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (show (0 : ℝ) < 399 / 1000 by norm_num))
      (mem_Ioi.mpr (by linarith : 0 < 2 * b)) (by linarith)
    have := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 399 / 1000 by norm_num) (by norm_num)).2
    norm_num at this
    linarith
  have hω3 : 9418 / 10000 ≤ archLevyDensity L := by
    have hm := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : 0 < L))
      (mem_Ioi.mpr (show (0 : ℝ) < 6932 / 10000 by norm_num)) (by linarith)
    have := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 6932 / 10000 by norm_num) (by norm_num)).1
    norm_num at this
    linarith
  have hM : ∀ v, b ≤ u → b ≤ v → v ≤ η → wideFoldWeight L (1 / 50) u v ≤ 68804 / 10000 := by
    intro v hbu hbv hv
    have hW := wideFoldWeight_le_band (β := 1 / 50) (by norm_num) hb0 hbu huη hbv hv hLη (by linarith)
    have hpos : 0 < 1 / 50 + b := by linarith
    have t1 : (1 + (η - b) / 2) / (1 / 50 + b) ≤ 45696 / 10000 := by
      rw [div_le_iff₀ hpos]; linarith
    have t2 : 2 * archLevyDensity (L - 2 * η) * (η - b) / (1 / 50 + b) ≤ 1176 / 10000 := by
      rw [div_le_iff₀ hpos]
      have hωp := archLevyDensity_pos (show 0 < L - 2 * η by linarith)
      nlinarith [mul_le_mul hω1 hηb (by linarith) (by norm_num)]
    linarith
  have hband := integral_wideFoldWeightBand_ge (β := 1 / 50) (by norm_num) hu huη hLη hη1 hb0 hbη hM
    (by norm_num)
  have : 68804 / 10000 * (η - b) ≤ 44 / 1000 := by linarith
  linarith

/-- The polynomial remainders of the crossing rate: `4P₁ ≤ (3η² + 7η³)/24`, `Q₂, Q₃ ≥ 0`,
`4Q₄ ≤ 8L⁴/1000`. -/
theorem wideCrossRate_poly_aux {L η u : ℝ} (hu : 0 < u) (huη : u ≤ η) (hLη : η < L) :
    ((u + η) ^ 2 - u ^ 2) / 96 + ((u + η) ^ 3 - u ^ 3) / 96 ≤ (3 * η ^ 2 + 7 * η ^ 3) / 96 ∧
      0 ≤ (L ^ 2 - (L - u) ^ 2) / 96 + (L ^ 3 - (L - u) ^ 3) / 96 ∧
      0 ≤ (L ^ 2 - (L + u - η) ^ 2) / 96 + (L ^ 3 - (L + u - η) ^ 3) / 96 ∧
      (L ^ 4 - (L - u) ^ 4) / 1000 + (L ^ 4 - (L + u - η) ^ 4) / 1000 ≤ 2 * L ^ 4 / 1000 := by
  have hη : 0 ≤ η := by linarith
  have hLu : 0 ≤ L - u := by linarith
  have hLuη : 0 ≤ L + u - η := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have a1 : u * η ≤ η * η := mul_le_mul_of_nonneg_right huη hη
    have a2 : u * η ^ 2 ≤ η * η ^ 2 := mul_le_mul_of_nonneg_right huη (sq_nonneg η)
    have a3 : u ^ 2 * η ≤ η ^ 2 * η :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu.le huη 2) hη
    linarith only [a1, a2, a3]
  · have a1 : (L - u) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hLu (by linarith) 2
    have a2 : (L - u) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hLu (by linarith) 3
    linarith only [a1, a2]
  · have a1 : (L + u - η) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hLuη (by linarith) 2
    have a2 : (L + u - η) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hLuη (by linarith) 3
    linarith only [a1, a2]
  · have a1 := pow_nonneg hLu 4
    have a2 := pow_nonneg hLuη 4
    linarith only [a1, a2]

/-- **The crossing part of the wide fold.** For `0 < u ≤ η`, `2η < L ≤ 3/4` and
`log L − log(L − η) ≤ Λ`: `4 ∫_0^η R₊ ≥ 2ℓ − 2Λ − (3η² + 7η³)/24 − 8L⁴/1000`, `ℓ = log((u + η)/u)`.
The two reflected windows `[L − u, L]`, `[L + u − η, L]` cost at most `Λ` by concavity of `log`. -/
theorem wideCrossRate_integral_ge {L η u Λ : ℝ} (hu : 0 < u) (huη : u ≤ η) (hLη : 2 * η < L)
    (hL : L ≤ 3 / 4) (hΛ : Real.log L - Real.log (L - η) ≤ Λ) :
    2 * (Real.log (u + η) - Real.log u) - 2 * Λ - (3 * η ^ 2 + 7 * η ^ 3) / 24 - 8 * L ^ 4 / 1000 ≤
      4 * ∫ v in (0 : ℝ)..η, wideCrossRate L u v := by
  have hR := integral_wideCrossRate (L := L) hu huη (by linarith)
  have hI1 := integral_archLevyDensity_ge_secondOrder hu (by linarith : u ≤ u + η) (by linarith)
  have hI2 := integral_archLevyDensity_le_secondOrder (by linarith : 0 < L - u) (by linarith : L - u ≤ L) hL
  have hI3 := integral_archLevyDensity_le_secondOrder (by linarith : 0 < L + u - η)
    (by linarith : L + u - η ≤ L) hL
  have hprod : Real.log L + Real.log (L - η) ≤ Real.log (L - u) + Real.log (L + u - η) := by
    rw [← Real.log_mul (by linarith) (by linarith), ← Real.log_mul (by linarith) (by linarith)]
    have hd : L * (L - η) ≤ (L - u) * (L + u - η) := by
      have : 0 ≤ u * (η - u) := mul_nonneg hu.le (by linarith)
      linarith only [this]
    exact Real.log_le_log (by nlinarith) hd
  obtain ⟨hP1, hQ2, hQ3, hQ4⟩ := wideCrossRate_poly_aux hu huη (by linarith : η < L)
  rw [hR]
  linarith only [hI1, hI2, hI3, hprod, hΛ, hP1, hQ2, hQ3, hQ4]

/-- **The crossing part of the fold of `2`** at the window `221/400`, with `Λ ≤ 0.35256`. -/
theorem logTwoStrip_crossRate_ge {u : ℝ} (hu : 0 < u) (huη : u ≤ 221 / 400 - Real.log 2 / 2) :
    2 * (Real.log (u + (221 / 400 - Real.log 2 / 2)) - Real.log u) - 2 * (35256 / 100000) -
        (3 * (221 / 400 - Real.log 2 / 2) ^ 2 + 7 * (221 / 400 - Real.log 2 / 2) ^ 3) / 24 -
        8 * Real.log 2 ^ 4 / 1000 ≤
      4 * ∫ v in (0 : ℝ)..(221 / 400 - Real.log 2 / 2), wideCrossRate (Real.log 2) u v :=
  wideCrossRate_integral_ge hu huη logTwoStrip_window.1
    (by linarith [Real.log_two_lt_d9]) logTwoStrip_logRatio_le

/-- **The surplus and the defect of the fold of `2`.** In the gauge `G = 1/50 + u`:
`G · (2U − 2∫D(1 − q)) ≥ 2u(1 − ℓ) − 2(η³/24 + η⁴/32) − (c₁u³/3 + c₀u²)`. -/
theorem logTwoStrip_surplusDefect_ge {u : ℝ} (hu : 0 < u) (huη : u ≤ 221 / 400 - Real.log 2 / 2) :
    2 * u * (1 - (Real.log (u + (221 / 400 - Real.log 2 / 2)) - Real.log u)) -
        2 * ((221 / 400 - Real.log 2 / 2) ^ 3 / 24 + (221 / 400 - Real.log 2 / 2) ^ 4 / 32) -
        (5258 / 1000 * u ^ 3 / 3 + 1333 / 1000000 * u ^ 2) ≤
      (1 / 50 + u) * (2 * surplusPotential (cubicGauge (1 / 50) 1 0 0) (221 / 400 - Real.log 2 / 2) u -
        2 * ∫ v in (0 : ℝ)..(221 / 400 - Real.log 2 / 2),
          wideFoldDefect (Real.log 2) u v * (1 - (1 / 50 + v) / (1 / 50 + u))) := by
  obtain ⟨h1, h2, h3, h4⟩ := logTwoStrip_numerics
  obtain ⟨hLη, hη1, hη0, hη0', -, -, -, -⟩ := logTwoStrip_window
  set L := Real.log 2 with hLdef
  set η := 221 / 400 - L / 2 with hηdef
  have hG0 : 0 < 1 / 50 + u := by linarith
  have hD := integral_wideFoldDefect_le (L := L) (β := 1 / 50) (c₁ := 5258 / 1000) (c₀ := 1333 / 1000000)
    (by norm_num) hu huη hLη (by linarith)
    (by
      have hp : 194970 / 1000000 ≤ L * (L - 2 * η) := by rw [hηdef]; nlinarith
      have : 1 / (L * (L - 2 * η)) ≤ 1 / (194970 / 1000000) := one_div_le_one_div_of_le (by norm_num) hp
      norm_num at this ⊢
      linarith)
    (by nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ L) h2.le 3])
  have hU := mul_surplusPotential_cubicGauge_ge (1 / 50) 1 0 0 (L := 1) hu huη hη1
    (by unfold cubicGauge; linarith) (fun _ _ _ _ _ _ => by norm_num)
  have hg : cubicGauge (1 / 50) 1 0 0 u = 1 / 50 + u := by unfold cubicGauge; ring
  rw [hg] at hU
  have hmain : cubicSurplusMain 1 0 0 η u = u * (1 - (Real.log (u + η) - Real.log u)) := by
    unfold cubicSurplusMain; rw [add_comm u η]; ring
  rw [hmain, one_mul] at hU
  have hrem : surplusRemainder η u ≤ η ^ 3 / 24 + η ^ 4 / 32 := by
    unfold surplusRemainder
    nlinarith [mul_nonneg hu.le (sub_nonneg.2 huη), mul_nonneg (mul_nonneg hu.le hu.le) (sub_nonneg.2 huη),
      mul_nonneg (mul_nonneg hu.le (sub_nonneg.2 huη)) (sub_nonneg.2 huη), pow_nonneg hu.le 3,
      mul_nonneg (pow_nonneg hu.le 2) (sub_nonneg.2 huη), mul_nonneg (pow_nonneg hu.le 3) (sub_nonneg.2 huη),
      mul_nonneg (mul_nonneg (pow_nonneg hu.le 2) (sub_nonneg.2 huη)) (sub_nonneg.2 huη),
      mul_nonneg (mul_nonneg hu.le (sub_nonneg.2 huη)) (mul_nonneg hu.le (sub_nonneg.2 huη))]
  set Dint := ∫ v in (0 : ℝ)..η, wideFoldDefect L u v * (1 - (1 / 50 + v) / (1 / 50 + u)) with hDint
  set U := surplusPotential (cubicGauge (1 / 50) 1 0 0) η u with hUdef
  have hDG : (1 / 50 + u) * Dint ≤ 5258 / 1000 * u ^ 3 / 6 + 1333 / 1000000 * u ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left hD hG0.le
    rwa [mul_div_cancel₀ _ hG0.ne'] at this
  linarith only [hU, hDG, hrem]

/-- The polynomial core of the potential of the fold of `2`. -/
theorem logTwoStrip_poly {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 20592641 / 100000000) :
    2 / 25 * u ≤ (2 * u + 1 / 25 * (6931471803 / 10000000000 + 1) - 842 / 1000000 -
      (5258 / 1000 * u ^ 3 / 3 + 1333 / 1000000 * u ^ 2) - (1 / 50 + u) * (1758817 / 1000000)) *
        (u + 20592640 / 100000000) := by
  nlinarith [mul_nonneg hu (sub_nonneg.2 hu'), mul_nonneg (mul_nonneg hu hu) (sub_nonneg.2 hu'),
    pow_nonneg hu 3, mul_nonneg (pow_nonneg hu 3) (sub_nonneg.2 hu'), pow_nonneg hu 4]

/-- **The potential of the wide fold of `2` at the window `221/400`.** With the gauge `1/50 + t` and the
band of the strip of `3` withheld, the folded weight integrates over `[0, η]` to at least `1` at every
folded point. -/
theorem wideBandFold_potential_logTwo {u : ℝ} (hu : 0 < u) (huη : u ≤ 221 / 400 - Real.log 2 / 2) :
    1 ≤ ∫ v in (0 : ℝ)..(221 / 400 - Real.log 2 / 2),
      wideFoldWeightBand (Real.log 2) (1 / 50) (Real.log 3 - 221 / 400 - Real.log 2 / 2) u v := by
  obtain ⟨h1, h2, h3, h4⟩ := logTwoStrip_numerics
  obtain ⟨hLη, hη1, hη0, hη0', -, -, -, -⟩ := logTwoStrip_window
  have hband := logTwoStrip_band_cost hu huη
  have hcr := logTwoStrip_crossRate_ge hu huη
  have hsd := logTwoStrip_surplusDefect_ge hu huη
  have hsplit := integral_wideFoldWeight_eq (L := Real.log 2) (β := 1 / 50) (by norm_num) hu huη hLη hη1
  set L := Real.log 2 with hLdef
  set η := 221 / 400 - L / 2 with hηdef
  set ℓ := Real.log (u + η) - Real.log u with hℓ
  -- the window ratio, by the tangent at `2`
  have hℓt : L + 1 - 2 * u / (u + η) ≤ ℓ := by
    have := log_ge_tangent (show 0 < (u + η) / u by positivity) (show (0 : ℝ) < 2 by norm_num)
    rw [Real.log_div (by positivity) hu.ne'] at this
    have e : 2 / ((u + η) / u) = 2 * u / (u + η) := by field_simp
    rw [e] at this; rw [hℓ]; linarith
  have hT : 2 * u / (u + η) * (u + η) = 2 * u := by field_simp
  set Wint := ∫ v in (0 : ℝ)..η, wideFoldWeight L (1 / 50) u v with hW
  set Bint := ∫ v in (0 : ℝ)..η, wideFoldWeightBand L (1 / 50) (Real.log 3 - 221 / 400 - L / 2) u v with hB
  set C4 := ∫ v in (0 : ℝ)..η, wideCrossRate L u v with hC4
  set SD := 2 * surplusPotential (cubicGauge (1 / 50) 1 0 0) η u -
    2 * ∫ v in (0 : ℝ)..η, wideFoldDefect L u v * (1 - (1 / 50 + v) / (1 / 50 + u)) with hSD
  set T := 2 * u / (u + η) with hTdef
  clear_value Wint Bint C4 SD T ℓ
  have hG0 : 0 < 1 / 50 + u := by linarith
  have hWe : Wint = SD + 4 * C4 := by rw [hsplit, hSD]
  -- `G · W ≥ 2u + 2βℓ − … − G K`, `K = 2Λ + 4P₁ + 4Q₄`
  have hL4 : L ^ 4 ≤ 23084 / 100000 :=
    calc L ^ 4 ≤ (6931471808 / 10000000000) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      _ ≤ 23084 / 100000 := by norm_num
  have hηsq : η ^ 2 ≤ (20592641 / 100000000) ^ 2 := pow_le_pow_left₀ (by linarith) hη0' 2
  have hηcu : η ^ 3 ≤ (20592641 / 100000000) ^ 3 := pow_le_pow_left₀ (by linarith) hη0' 3
  have hηqu : η ^ 4 ≤ (20592641 / 100000000) ^ 4 := pow_le_pow_left₀ (by linarith) hη0' 4
  have hK : (3 * η ^ 2 + 7 * η ^ 3) / 24 ≤ 785 / 100000 := by
    norm_num at hηsq hηcu ⊢; linarith
  have hGW : (1 / 50 + u) * (2 * ℓ - 2 * (35256 / 100000) - 785 / 100000 - 1847 / 1000000) ≤
      (1 / 50 + u) * (4 * C4) := by
    refine mul_le_mul_of_nonneg_left ?_ hG0.le
    linarith
  have hη3 : η ^ 3 / 24 + η ^ 4 / 32 ≤ 421 / 1000000 := by
    norm_num at hηcu hηqu ⊢; linarith
  -- the window ratio against the polynomial core
  have hTb : 1 / 25 * T ≤ 2 * u + 1 / 25 * (6931471803 / 10000000000 + 1) - 842 / 1000000 -
      (5258 / 1000 * u ^ 3 / 3 + 1333 / 1000000 * u ^ 2) - (1 / 50 + u) * (1758817 / 1000000) := by
    have hc0 : 0 < u + 20592640 / 100000000 := by linarith
    have hpoly := logTwoStrip_poly hu.le (huη.trans hη0')
    have hT1 : T ≤ 2 * u / (u + 20592640 / 100000000) := by
      rw [hTdef]; exact div_le_div_of_nonneg_left (by linarith) hc0 (by linarith)
    have hT2 : 1 / 25 * (2 * u / (u + 20592640 / 100000000)) ≤
        2 * u + 1 / 25 * (6931471803 / 10000000000 + 1) - 842 / 1000000 -
          (5258 / 1000 * u ^ 3 / 3 + 1333 / 1000000 * u ^ 2) - (1 / 50 + u) * (1758817 / 1000000) := by
      rw [show 1 / 25 * (2 * u / (u + 20592640 / 100000000)) = 2 / 25 * u / (u + 20592640 / 100000000) by ring,
        div_le_iff₀ hc0]
      exact hpoly
    linarith
  have hmain : (1 / 50 + u) * (1 + 44 / 1000) ≤ (1 / 50 + u) * Wint := by
    rw [hWe, mul_add]
    have e : (1 / 50 + u) * (2 * ℓ - 2 * (35256 / 100000) - 785 / 100000 - 1847 / 1000000) =
        (1 / 50 + u) * (2 * ℓ) - (1 / 50 + u) * (2 * (35256 / 100000) + 785 / 100000 + 1847 / 1000000) := by
      ring
    rw [e] at hGW
    linarith only [hsd, hGW, hη3, hℓt, hTb, h1]
  have hW1 : 1 + 44 / 1000 ≤ Wint := le_of_mul_le_mul_left hmain hG0
  linarith

/-- The folded potential of the strip of `2` in the form the wide micro-fold consumes. -/
theorem logTwoStrip_hpot {u : ℝ} (hu : 0 < u)
    (huη : u ≤ (221 / 400 - (Real.log 2 - 221 / 400)) / 2) :
    2 * 1 ≤ ∫ y in (Real.log 2 - 221 / 400)..(221 / 400),
      wideFoldWeightBand (Real.log 2) (1 / 50) (Real.log 3 - 221 / 400 - Real.log 2 / 2) u
        |y - Real.log 2 / 2| := by
  obtain ⟨hLη, hη1, hη0, -, -, -, -, -⟩ := logTwoStrip_window
  have huη' : u ≤ 221 / 400 - Real.log 2 / 2 := by linarith
  have h := integral_abs_sub_symm (m := Real.log 2 / 2) (η := 221 / 400 - Real.log 2 / 2)
    (C := 3 / (1 / 50) + 2 * archLevyDensity (Real.log 2 - 2 * (221 / 400 - Real.log 2 / 2)) *
      (221 / 400 - Real.log 2 / 2) / (1 / 50) + 4 * (archLevyDensity u +
        archLevyDensity (Real.log 2 - 2 * (221 / 400 - Real.log 2 / 2))))
    (w := fun v => wideFoldWeightBand (Real.log 2) (1 / 50) (Real.log 3 - 221 / 400 - Real.log 2 / 2) u v)
    (by linarith) (measurable_wideFoldWeightBand _ _ _).of_uncurry_left fun v hv => by
      unfold wideFoldWeightBand; split_ifs
      · rw [abs_zero]
        exact (abs_nonneg _).trans (abs_wideFoldWeight_le_of_mem (by norm_num) hu huη' hv hLη hη1)
      · exact abs_wideFoldWeight_le_of_mem (by norm_num) hu huη' hv hLη hη1
  rw [show Real.log 2 / 2 - (221 / 400 - Real.log 2 / 2) = Real.log 2 - 221 / 400 by ring,
    show Real.log 2 / 2 + (221 / 400 - Real.log 2 / 2) = 221 / 400 by ring] at h
  rw [h]
  linarith [wideBandFold_potential_logTwo hu huη']

/-- `∫_p^r 1_{[c, ∞)} h = ∫_c^r h` for `p < c ≤ r`. -/
theorem integral_indicator_Ici_eq {h : ℝ → ℝ} {p c r : ℝ} (hpc : p < c) (hcr : c ≤ r) :
    (∫ y in p..r, (Ici c).indicator h y) = ∫ y in c..r, h y := by
  have hs : Ici c ∩ Ioc p r = Icc c r := by
    ext y
    simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  rw [intervalIntegral.integral_of_le (hpc.le.trans hcr), intervalIntegral.integral_of_le hcr,
    MeasureTheory.integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici, hs,
    integral_Icc_eq_integral_Ioc]

/-- **Sharing the square of a sub-strip.** For `0 < p < c ≤ r`, the surplus of the box `[p, r]²`
splits into the surplus with the pairs of `[c, r]²` withheld and the surplus of `[c, r]²`. -/
theorem integral_box_eq_withheld_add {F : ℝ → ℝ} {K p c r : ℝ} (hF : Continuous F)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hp : 0 < p) (hpc : p < c) (hcr : c ≤ r)
    (hr1 : r - p ≤ 1) :
    (∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2) =
      (∫ x in p..r, ∫ y in p..r, withheldKernel c x y * (F x - F y) ^ 2) +
        ∫ x in c..r, ∫ y in c..r, surplusKernel x y * (F x - F y) ^ 2 := by
  have hpr : p ≤ r := hpc.le.trans hcr
  have hmg : Measurable (Function.uncurry fun x y => surplusKernel x y * (F x - F y) ^ 2) :=
    measurable_stripIntegrand hF
  have hmw : Measurable (Function.uncurry fun x y => withheldKernel c x y * (F x - F y) ^ 2) := by
    unfold withheldKernel
    refine Measurable.mul (Measurable.ite ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)) measurable_const measurable_surplusKernel) ?_
    exact ((hF.measurable.comp measurable_fst).sub (hF.measurable.comp measurable_snd)).pow_const 2
  have hbg : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r,
      |(fun x y => surplusKernel x y * (F x - F y) ^ 2) x y| ≤ 3 / 2 * K ^ 2 * (r - p) :=
    fun x hx y hy => abs_strip_integrand_le hFL hp hr1 hx hy
  have hbw : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r,
      |(fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y| ≤ 3 / 2 * K ^ 2 * (r - p) :=
    fun x hx y hy => by
      have h := abs_strip_integrand_le hFL hp hr1 hx hy
      simp only
      unfold withheldKernel
      split_ifs
      · rw [zero_mul, abs_zero]; exact (abs_nonneg _).trans h
      · exact h
  obtain ⟨hig, hog⟩ := intervalIntegrable_iterated hpr hmg hbg
  obtain ⟨hiw, how⟩ := intervalIntegrable_iterated hpr hmw hbw
  -- row by row, the difference is the row of `[c, r]²`
  have key : ∀ x ∈ uIcc p r, (∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2) -
      (∫ y in p..r, withheldKernel c x y * (F x - F y) ^ 2) =
        (Ici c).indicator (fun x => ∫ y in c..r, surplusKernel x y * (F x - F y) ^ 2) x := by
    intro x hx
    rw [uIcc_of_le hpr] at hx
    rw [← intervalIntegral.integral_sub (hig x hx) (hiw x hx)]
    by_cases hxc : c ≤ x
    · rw [Set.indicator_of_mem (show x ∈ Ici c from hxc), ← integral_indicator_Ici_eq hpc hcr]
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [Set.indicator_apply, mem_Ici, withheldKernel]
      by_cases hyc : c ≤ y
      · simp [hxc, hyc]
      · simp [hyc]
    · rw [Set.indicator_of_notMem (show x ∉ Ici c from hxc)]
      have e : (fun y => surplusKernel x y * (F x - F y) ^ 2 - withheldKernel c x y * (F x - F y) ^ 2) =
          fun _ => (0 : ℝ) := funext fun y => by
        simp only [withheldKernel]; rw [if_neg (fun h => hxc h.1)]; ring
      rw [e, intervalIntegral.integral_zero]
  have h := intervalIntegral.integral_sub hog how
  rw [intervalIntegral.integral_congr key, integral_indicator_Ici_eq hpc hcr] at h
  linarith

/-- The micro-fold constant of the strip of `3` at the window `221/400`: `λ₃ ≥ 1.8939`, enough for
the atom of `3` with the even part kept at `t = 2/5`. -/
theorem logThreeStrip_lam :
    (1 + 2 / 5) * (2 * vonMangoldtAtom 3) ≤ 1 * (19 / 10 -
      (221 / 400 - (Real.log 3 - 221 / 400)) / 2 / (Real.log 3 - 221 / 400) -
        3 * ((221 / 400 - (Real.log 3 - 221 / 400)) / 2) ^ 2) := by
  obtain ⟨-, hΛ1⟩ := vonMangoldtAtom_three_bounds
  obtain ⟨l1, l2⟩ := log_three_bounds
  have hp : 0 < Real.log 3 - 221 / 400 := by linarith
  have hq : (221 / 400 - (Real.log 3 - 221 / 400)) / 2 / (Real.log 3 - 221 / 400) ≤ 6 / 1000 := by
    rw [div_le_iff₀ hp]; linarith
  have hη0 : 0 ≤ (221 / 400 - (Real.log 3 - 221 / 400)) / 2 := by linarith
  have hsq : ((221 / 400 - (Real.log 3 - 221 / 400)) / 2) ^ 2 ≤ (32 / 10000) ^ 2 :=
    pow_le_pow_left₀ hη0 (by linarith) 2
  norm_num at hsq
  linarith

/-- **Harnack across the overlapping strips of `2` and `3`.** For every odd Lipschitz `F` supported
in `[−221/400, 221/400]` (past `½ log 3`, where the strip `S₃ = [log 3 − r, r]` of `3` lies inside the
strip `S₂ = [log 2 − r, r]` of `2`), the two atoms together cost less than the archimedean surplus of
`S₂` and leave potential on both strips:

    2 Λ(2)/√2 ∫ F F(· + log 2) + 2 Λ(3)/√3 ∫ F F(· + log 3)
      ≤ 2 stripSurplus_{S₂} − (1/62) ∫_{S₂} F² − ½ ∫_{S₃} F².

The surplus of `S₃ × S₃` goes to the atom of `3` (sharp micro-fold, `λ₃ ≥ 1.89`); the atom of `2` is
paid by the wide micro-fold of `S₂` with `S₃ × S₃` withheld (potential `≥ 1 > √2 log 2`). -/
theorem two_mul_primeTwoThreeShifts_le_stripSurplus_sub {F : ℝ → ℝ} {K : ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (hsupp : ∀ x, 221 / 400 < |x| → F x = 0) :
    2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) +
        2 * (vonMangoldtAtom 3 * ∫ x, F x * F (x + Real.log 3)) ≤
      2 * stripSurplus F (Real.log 2 - 221 / 400) (221 / 400) -
        1 / 62 * (∫ x in (Real.log 2 - 221 / 400)..(221 / 400), F x ^ 2) -
        1 / 2 * ∫ x in (Real.log 3 - 221 / 400)..(221 / 400), F x ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := logTwoStrip_numerics
  obtain ⟨hΛ3, -⟩ := vonMangoldtAtom_three_bounds
  obtain ⟨-, hΛ2⟩ := vonMangoldtAtom_two_bounds
  have hΛ2' := vonMangoldtAtom_two_ge
  have hp : 0 < Real.log 2 - 221 / 400 := by linarith
  have hpr : Real.log 2 - 221 / 400 < 221 / 400 := by linarith
  have hpc : Real.log 2 - 221 / 400 < Real.log 3 - 221 / 400 := by linarith
  have hcr : Real.log 3 - 221 / 400 ≤ 221 / 400 := by linarith
  have hr1 : 221 / 400 - (Real.log 2 - 221 / 400) ≤ 1 := by linarith
  -- the atom of `3` on `S₃ × S₃`, with the even part kept at `t = 2/5`
  have hA3 := two_mul_primePowerShift_le_stripSurplus_sub_evenPart (n := 3) (θ := 1) (t := 2 / 5)
    (by norm_num) hF hFc hodd hFL hsupp (by push_cast; linarith) (by push_cast; linarith)
    (by norm_num) (by norm_num) (by push_cast; exact logThreeStrip_lam)
  push_cast at hA3
  -- the atom of `2` on its odd part, with the even part kept at `t = 1/60`
  have hA2 := integral_mul_shift_le_interp hF hFc hodd (r := 221 / 400) (L := Real.log 2) (by norm_num)
    (by linarith) hsupp (t := 1 / 60) (by norm_num)
  -- the wide micro-fold of `S₂` with `S₃ × S₃` withheld
  have hW := wideBandMicroFold_strip_ge (L := Real.log 2) (β := 1 / 50) (c := Real.log 3 - 221 / 400)
    (lam := 1) hF hFL hp hpr (by ring) hr1 (by norm_num) fun u hu huη => logTwoStrip_hpot hu huη
  -- the box of `S₂` = the withheld box + the box of `S₃`
  have hbox := integral_box_eq_withheld_add hF hFL hp hpc hcr hr1
  have hT2 := integral_strip_eq_two_mul_stripSurplus hF hFL hp hpr.le hr1
  have hT3 := integral_strip_eq_two_mul_stripSurplus hF hFL (by linarith) hcr (by linarith)
  have hS2 : 0 ≤ ∫ x in (Real.log 2 - 221 / 400)..(221 / 400), F x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have hS3 : 0 ≤ ∫ x in (Real.log 3 - 221 / 400)..(221 / 400), F x ^ 2 :=
    intervalIntegral.integral_nonneg hcr fun _ _ => sq_nonneg _
  have hα : 0 ≤ ∫ x in (Real.log 2 - 221 / 400)..(221 / 400), reflectedOddPart F (Real.log 2) x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have k1 := mul_le_mul_of_nonneg_left hA2 (vonMangoldtAtom_nonneg 2)
  have k2 := mul_le_mul_of_nonneg_right (show vonMangoldtAtom 2 * (1 + 1 / 60) ≤ 1 / 2 by linarith) hα
  have k3 := mul_le_mul_of_nonneg_right (show 1 / 124 ≤ vonMangoldtAtom 2 * (1 / 60) by linarith) hS2
  have k4 := mul_le_mul_of_nonneg_right (show 1 / 2 ≤ 2 * vonMangoldtAtom 3 * (2 / 5) by linarith) hS3
  unfold stripIntegrand at hT2 hT3
  linarith only [hA3, k1, k2, k3, k4, hW, hbox, hT2, hT3]

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
