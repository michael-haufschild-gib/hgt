import GaloisForLFunctions.ArithmeticProduction.TheNecessaryLengthOfAMollifier
import GaloisForLFunctions.RHTower.ZetaLineLogMeanLittlewoodBudget
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.NearLineDensityBesselCertificateAndSeparation

/-!
# Long mollifiers imply critical clustering

The second-moment route to the near-line questions, in one exact form.

* **The ceiling** (`exists_logIntegral_le_of_secondMoment`).  A real mollifier with `∫_T^{2T}|ζM|² ≤ (1+ε)T` gives `∫_T^{2T} log|ζ(½+it)| ≤ εT/2 + O(log T + log N)`.
* **Clustering** (`logMean_tendsto_zero_of_mollifiedSecondMomentLaw`, `criticalClustering_of_mollifiedSecondMomentLaw`).  A second moment tending to `1`, at any length `exp(o(T))`, implies `100%` critical-scale clustering.
* **Occupancy at a rate** (`logFreeNearLineZeroDensity_of_secondMomentRate`).  The excess `K/log T`, one logarithm below the clustering statement, gives the log-free density `D_zero`, hence `D_win`.
* **Both fail at every fixed exponent** (`not_secondMomentLaw_of_bounded_exponent`, `not_secondMomentRate_of_bounded_exponent`).  By the necessary-length law, neither can be realized with `N ≤ T^θ`.
* **The rate needs length `exp(c log²T)`** (`log_length_ge_of_secondMomentRate`).  An excess `K/log T` forces `log N ≥ min(1/24, 1/(14K)) log²T`.

So a second-moment proof of clustering needs length beyond every power of `T`, and a second-moment proof of `D_zero` needs length at least `exp(c log²T)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

/-- **The ceiling.**  The log-integral of `ζ` on `[T, 2T]` is at most half the excess of a mollified second moment, up to the logarithm of the length. -/
theorem exists_logIntegral_le_of_secondMoment :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ T : ℝ, 22 ≤ T → ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) → ∀ ε : ℝ, 0 ≤ ε →
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (1 + ε) * T →
      (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤
        ε / 2 * T + C + K * (Real.log T + Real.log N) := by
  obtain ⟨C₀, K₀, hC₀, hK₀, hs⟩ := exists_zetaLine_logMean_sandwich
  obtain ⟨Cz, hCz0, hCz⟩ := exists_norm_riemannZeta_le_leftStrip
  refine ⟨1 + C₀ + K₀ + 2 * Real.log (Cz + 1) + 8, 5 * K₀ + 4, ?_, by positivity, ?_⟩
  · have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ Cz + 1)
    linarith
  intro T hT b N hN hb1 hb hbr ε hε hsecond
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  obtain ⟨T₁, hT₁, T₂, hT₂, hs1, hs2⟩ := exists_admissible_slices (b := b) (N := N) hN hb1 hb
    (A₁ := T) (B₁ := T + 1) (A₂ := 2 * T - 1) (B₂ := 2 * T)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨hT₁a, hT₁b⟩ := hT₁
  obtain ⟨hT₂a, hT₂b⟩ := hT₂
  have hT12 : T₁ < T₂ := by linarith
  -- the second moment on the inner interval
  have hcont := continuous_norm_sq_zeta_mul_edPoly b N (c := 1 / 2) (by norm_num)
  have hMsq : (∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) ≤ (1 + ε) * T := by
    refine le_trans (intervalIntegral.integral_mono_interval hT₁a.le hT12.le hT₂b.le
      (Filter.Eventually.of_forall fun t => ?_) (hcont.intervalIntegrable _ _)) hsecond
    show 0 ≤ _
    positivity
  have hMsq0 : 0 < (1 + ε) * T := by positivity
  have hMb1 : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hN)
  have hsw := (hs b N hN hb1 hb hbr ((N : ℝ) ^ 5) hMb1 (sum_norm_mul_rpow_four_le hb) T₁ T₂ ((1 + ε) * T)
    (by linarith) hT12 hMsq0 (fun x hx => (hs1 x hx).1) (fun x hx => (hs2 x hx).1)
    (fun x hx => (hs1 x hx).2) (fun x hx => (hs2 x hx).2) hMsq).2
  -- Jensen, in the tangent form
  have hL0 : 0 < T₂ - T₁ := by linarith
  have hjensen : (T₂ - T₁) / 2 * Real.log ((1 + ε) * T / (T₂ - T₁)) ≤ ε / 2 * T + 1 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hMsq0 hL0)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (T₂ - T₁) / 2)
    have h3 : (T₂ - T₁) / 2 * ((1 + ε) * T / (T₂ - T₁) - 1) = ((1 + ε) * T - (T₂ - T₁)) / 2 := by
      field_simp
    rw [h3] at h2
    have h4 : (1 + ε) * T = T + ε * T := by ring
    have h5 : ε / 2 * T = ε * T / 2 := by ring
    linarith
  have hlogT₂ : Real.log T₂ ≤ Real.log T + 1 := by
    have h1 : Real.log T₂ ≤ Real.log (2 * T) := Real.log_le_log (by linarith) hT₂b.le
    rw [Real.log_mul two_ne_zero hT0.ne'] at h1
    have h2 := Real.log_two_lt_d9
    linarith
  have hlogMb : Real.log ((N : ℝ) ^ 5) = 5 * Real.log N := by
    rw [Real.log_pow]
    norm_num
  -- the two short tails
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = Real.log (Cz + 1) + 2 * Real.log 3 + 2 * Real.log T := ⟨_, rfl⟩
  have hCz1 : 0 ≤ Real.log (Cz + 1) := Real.log_nonneg (by linarith)
  have hlog30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hpoint : ∀ t ∈ Icc T (2 * T),
      Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ Y := by
    intro t ht
    by_cases h0 : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ = 0
    · rw [h0, Real.log_zero]
      exact hY0
    have hpos : 0 < ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h1 := hCz (1 / 2) t (by norm_num) (by norm_num)
    have ht0 : 0 ≤ t := by linarith [ht.1]
    rw [abs_of_nonneg ht0] at h1
    have h2 : ((1 + t) : ℝ) ^ 2 ≤ (3 * T) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 2
    have h3 : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ (Cz + 1) * (3 * T) ^ 2 :=
      h1.trans (mul_le_mul (by linarith) h2 (by positivity) (by linarith))
    have h4 := Real.log_le_log hpos h3
    refine h4.trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_mul (by norm_num) hT0.ne', hY]
    push_cast
    ring
  have htail : ∀ a c : ℝ, T ≤ a → a ≤ c → c ≤ 2 * T → c - a ≤ 1 →
      (∫ t in a..c, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤ Y := by
    intro a c ha hac hc hlen
    have h1 : (∫ t in a..c, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤
        ∫ _t in a..c, Y :=
      intervalIntegral.integral_mono_on hac (intervalIntegrable_log_norm_riemannZeta_line a c)
        intervalIntegrable_const fun t ht => hpoint t ⟨ha.trans ht.1, ht.2.trans hc⟩
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    refine h1.trans ?_
    calc (c - a) * Y ≤ 1 * Y := mul_le_mul_of_nonneg_right hlen hY0
      _ = Y := one_mul Y
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_log_norm_riemannZeta_line T T₁) (intervalIntegrable_log_norm_riemannZeta_line T₁ T₂)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_log_norm_riemannZeta_line T T₂) (intervalIntegrable_log_norm_riemannZeta_line T₂ (2 * T))
  have ht1 := htail T T₁ le_rfl hT₁a.le (by linarith) (by linarith)
  have ht2 := htail T₂ (2 * T) (by linarith) hT₂b.le le_rfl (by linarith)
  rw [hlogMb] at hsw
  rw [← hsplit2, ← hsplit]
  rw [hY] at ht1 ht2
  have hK1 : K₀ * (Real.log T₂ + 5 * Real.log N) ≤ K₀ * (Real.log T + 1 + 5 * Real.log N) :=
    mul_le_mul_of_nonneg_left (by linarith) hK₀.le
  have hK2 : K₀ * Real.log T ≤ 5 * K₀ * Real.log T :=
    mul_le_mul_of_nonneg_right (by linarith) hlogT
  have hexp : (5 * K₀ + 4) * (Real.log T + Real.log N) =
      5 * K₀ * Real.log T + 5 * K₀ * Real.log N + 4 * Real.log T + 4 * Real.log N := by ring
  have hexp2 : K₀ * (Real.log T + 1 + 5 * Real.log N) =
      K₀ * Real.log T + K₀ + 5 * K₀ * Real.log N := by ring
  rw [hexp]
  linarith

/-- A mollified second moment tending to `1`, at length `exp(o(T))`. -/
def MollifiedSecondMomentLaw : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∃ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N ∧ b 1 = 1 ∧
    (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
    (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧ Real.log N ≤ ε * T ∧
    (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (1 + ε) * T

/-- The floor of the log-integral: Littlewood, with the off-line moment nonnegative. -/
theorem exists_logIntegral_floor :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ T : ℝ, 21 ≤ T →
      -(C + K * Real.log (2 * T)) ≤
        ∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  obtain ⟨C, K, hC, hK, h⟩ := exists_zetaLine_littlewood_edge_budget_all_heights
  refine ⟨C, K, hC, hK, fun T hT => ?_⟩
  have h1 := (abs_le.mp (h T hT)).1
  have h2 : 0 ≤ ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) :=
    Finset.sum_nonneg fun z hz =>
      mul_nonneg (Nat.cast_nonneg _) (by linarith [(Finset.mem_filter.mp hz).2])
  have h3 : 0 ≤ 2 * Real.pi * ∑ z ∈ (shellZeros T (2 * T)).filter (fun z => 1 / 2 < z.re),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) :=
    mul_nonneg (by positivity) h2
  linarith

/-- **A second moment tending to one implies that the log-mean of `ζ` tends to zero.** -/
theorem logMean_tendsto_zero_of_mollifiedSecondMomentLaw (h : MollifiedSecondMomentLaw) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T),
      Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) atTop (𝓝 0) := by
  obtain ⟨C, K, hC, hK, hup⟩ := exists_logIntegral_le_of_secondMoment
  obtain ⟨C', K', hC', hK', hlow⟩ := exists_logIntegral_floor
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = η / (4 * (1 / 2 + K)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεK : ε / 2 + K * ε = η / 4 := by
    rw [hε]
    field_simp
  have hlog1 := eventually_log_pow_mul_exp_le 1 (c := 1) (ε := η / (8 * (K + K'))) one_pos (by positivity)
  filter_upwards [h ε hε0, hlog1, eventually_ge_atTop (22 : ℝ),
    eventually_ge_atTop (8 * (C + C' + K') / η)] with T hlaw hl hT22 hTC
  obtain ⟨b, N, hN, hb1, hb, hbr, hlogN, hmom⟩ := hlaw
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hu := hup T hT22 b N hN hb1 hb hbr ε hε0.le hmom
  have hd := hlow T (by linarith)
  have hlogT' : (K + K') * Real.log T ≤ η / 8 * T := by
    have hTe : Real.exp (-(1 * Real.log T)) = T⁻¹ := by
      rw [one_mul, Real.exp_neg, Real.exp_log hT0]
    rw [hTe, pow_one, ← div_eq_mul_inv, div_le_iff₀ hT0] at hl
    have h1 := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ K + K')
    refine h1.trans (le_of_eq ?_)
    field_simp
  have hTC' : C + C' + K' ≤ η / 8 * T := by
    have h1 := (div_le_iff₀ hη).mp hTC
    linarith
  have hlog2T : Real.log (2 * T) ≤ Real.log T + 1 := by
    rw [Real.log_mul two_ne_zero hT0.ne']
    have := Real.log_two_lt_d9
    linarith
  have hKK : K * Real.log T + K' * Real.log T = (K + K') * Real.log T := by ring
  have hK0 : 0 ≤ K * Real.log T := by positivity
  have hK'0 : 0 ≤ K' * Real.log T := by positivity
  have hup2 : (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤
      η / 2 * T := by
    have h1 : K * (Real.log T + Real.log N) ≤ K * Real.log T + K * (ε * T) := by
      rw [mul_add]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogN hK.le)
    have h2 : ε / 2 * T + K * (ε * T) = (ε / 2 + K * ε) * T := by ring
    rw [hεK] at h2
    have h3 : η / 4 * T + η / 8 * T + η / 8 * T = η / 2 * T := by ring
    have hC'K' : 0 < C' + K' := by positivity
    linarith
  have hlow2 : -(η / 2 * T) ≤
      ∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    have h1 : K' * Real.log (2 * T) ≤ K' * Real.log T + K' := by
      calc K' * Real.log (2 * T) ≤ K' * (Real.log T + 1) := mul_le_mul_of_nonneg_left hlog2T hK'.le
        _ = _ := by ring
    have h3 : η / 8 * T + η / 8 * T ≤ η / 2 * T := by
      have : 0 < η * T := by positivity
      linarith
    linarith
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (inv_pos.mpr hT0)]
  have habs := abs_le.mpr ⟨hlow2, hup2⟩
  have h5 : T⁻¹ * |∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤
      T⁻¹ * (η / 2 * T) := mul_le_mul_of_nonneg_left habs (inv_pos.mpr hT0).le
  have h6 : T⁻¹ * (η / 2 * T) = η / 2 := by
    field_simp
  linarith

/-- **`100%` critical-scale clustering from long mollifiers.** -/
theorem criticalClustering_of_mollifiedSecondMomentLaw (h : MollifiedSecondMomentLaw) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun V : ℝ => _root_.RHTower.offLineCountBeyond (κ / Real.log V) V /
      (V * Real.log V)) atTop (𝓝 0) := by
  have hTFAE := criticalClustering_logMean_mollifier_hecke_tfae (c := 1 / 4) (by norm_num) (by norm_num)
  have h04 := hTFAE.out 0 4
  exact h04.mp (logMean_tendsto_zero_of_mollifiedSecondMomentLaw h) κ hκ

/-- **The law fails at every fixed exponent.** -/
theorem not_secondMomentLaw_of_bounded_exponent {θ : ℝ} (hθ : 0 < θ) :
    ¬ ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∃ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N ∧ (N : ℝ) ≤ T ^ θ ∧ b 1 = 1 ∧
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (1 + ε) * T := by
  intro h
  obtain ⟨T₀, hT₀⟩ := necessary_length hθ
  have hc : 0 < 1 / (8 + 6 * θ) := by positivity
  obtain ⟨T, ⟨b, N, hN, hNT, hb1, hb, hbr, hmom⟩, hT, hT0⟩ :=
    ((h (1 / (8 + 6 * θ) / 2) (by positivity)).and
      ((eventually_ge_atTop T₀).and (eventually_gt_atTop (0 : ℝ)))).exists
  have h1 := hT₀ T hT b N hN hNT hb1 hb hbr
  have h2 := h1.trans hmom
  have h3 : 0 < 1 / (8 + 6 * θ) * T := by positivity
  have h4 : (1 + 1 / (8 + 6 * θ) / 2) * T = T + 1 / (8 + 6 * θ) * T / 2 := by ring
  have h5 : (1 + 1 / (8 + 6 * θ)) * T = T + 1 / (8 + 6 * θ) * T := by ring
  linarith

/-! ### Occupancy at a rate -/

/-- Off-line multiplicity against the first horizontal moment, folded by the reflection of the line. -/
theorem sum_order_filter_abs_le {V₁ V₂ x : ℝ} (hx : 0 < x) :
    ∑ z ∈ (shellZeros V₁ V₂).filter (fun z => x ≤ |z.re - 1 / 2|),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) ≤
      2 / x * ∑ z ∈ (shellZeros V₁ V₂).filter (fun z => 1 / 2 < z.re),
        ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, S = shellZeros V₁ V₂ := ⟨_, rfl⟩
  rw [← hS]
  set o : ℂ → ℝ := fun z => ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) with ho
  have ho0 : ∀ z, 0 ≤ o z := fun z => Nat.cast_nonneg _
  have hsplit : ∑ z ∈ S.filter (fun z => x ≤ |z.re - 1 / 2|), o z ≤
      ∑ z ∈ S.filter (fun z => x ≤ z.re - 1 / 2), o z +
        ∑ z ∈ S.filter (fun z => x ≤ 1 / 2 - z.re), o z := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    by_cases h1 : x ≤ |z.re - 1 / 2|
    · rw [if_pos h1]
      rcases le_abs'.mp h1 with h2 | h2
      · have h3 : x ≤ 1 / 2 - z.re := by linarith
        rw [if_pos h3]
        have : 0 ≤ if x ≤ z.re - 1 / 2 then o z else 0 := by
          split_ifs
          · exact ho0 z
          · exact le_rfl
        linarith
      · rw [if_pos h2]
        have : 0 ≤ if x ≤ 1 / 2 - z.re then o z else 0 := by
          split_ifs
          · exact ho0 z
          · exact le_rfl
        linarith
    · rw [if_neg h1]
      refine add_nonneg ?_ ?_ <;> split_ifs
      · exact ho0 z
      · exact le_rfl
      · exact ho0 z
      · exact le_rfl
  have hreflect : ∑ z ∈ S.filter (fun z => x ≤ 1 / 2 - z.re), o z =
      ∑ z ∈ S.filter (fun z => x ≤ z.re - 1 / 2), o z := by
    refine Finset.sum_nbij' lineReflect lineReflect ?_ ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hS ▸ lineReflect_mem_shellZeros (hS ▸ hz.1), ?_⟩
      rw [lineReflect_re]
      linarith [hz.2]
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hS ▸ lineReflect_mem_shellZeros (hS ▸ hz.1), ?_⟩
      rw [lineReflect_re]
      linarith [hz.2]
    · intro z _
      exact lineReflect_involutive z
    · intro z _
      exact lineReflect_involutive z
    · intro z _
      simp only [ho]
      rw [xi_orderAt_lineReflect]
  have hmoment : ∑ z ∈ S.filter (fun z => x ≤ z.re - 1 / 2), o z ≤
      1 / x * ∑ z ∈ S.filter (fun z => 1 / 2 < z.re), o z * (z.re - 1 / 2) := by
    rw [Finset.mul_sum]
    calc ∑ z ∈ S.filter (fun z => x ≤ z.re - 1 / 2), o z
        ≤ ∑ z ∈ S.filter (fun z => x ≤ z.re - 1 / 2), 1 / x * (o z * (z.re - 1 / 2)) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have h1 := (Finset.mem_filter.mp hz).2
          have h2 : o z * x ≤ o z * (z.re - 1 / 2) := mul_le_mul_of_nonneg_left h1 (ho0 z)
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hx]
          exact h2
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_) fun z hz _ => ?_
          · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hz
            exact Finset.mem_filter.mpr ⟨h1, by linarith⟩
          · have h2 := (Finset.mem_filter.mp hz).2
            exact mul_nonneg (by positivity) (mul_nonneg (ho0 z) (by linarith))
  rw [hreflect] at hsplit
  have h2 : 2 / x = 2 * (1 / x) := by ring
  rw [h2, mul_assoc]
  linarith

/-- An excess of size `K₀/log T` at length `exp(T/log T)`. -/
def SecondMomentRate (K₀ : ℝ) : Prop :=
  ∀ᶠ T : ℝ in atTop, ∃ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N ∧ b 1 = 1 ∧
    (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
    (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧ Real.log N ≤ T / Real.log T ∧
    (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (1 + K₀ / Real.log T) * T

/-- **An excess `K₀/log T` gives the log-free density**, hence window occupancy and clustering. -/
theorem logFreeNearLineZeroDensity_of_secondMomentRate {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (h : SecondMomentRate K₀) :
    LogFreeNearLineZeroDensity := by
  obtain ⟨C, K, hC, hK, hup⟩ := exists_logIntegral_le_of_secondMoment
  obtain ⟨C', K', hC', hK', hbud⟩ := exists_zetaLine_littlewood_edge_budget_all_heights
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = K₀ / 2 + K + 1 := ⟨_, rfl⟩
  have hK₁0 : 0 < K₁ := by rw [hK₁]; positivity
  have hπ := Real.pi_pos
  refine ⟨fun A => K₁ / Real.pi / A, tendsto_const_nhds.div_atTop tendsto_id, fun A hA => ?_⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = C + C' + K' + K + K' + 1 := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  filter_upwards [h, eventually_log_pow_mul_exp_le 2 (c := 1) (ε := 1 / D) one_pos (by positivity),
    eventually_ge_atTop (22 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1] with V hrate hsm hV22 hℓ
  obtain ⟨b, N, hN, hb1, hb, hbr, hlogN, hmom⟩ := hrate
  have hV0 : 0 < V := by linarith
  have hℓ0 : 0 < Real.log V := by linarith
  have hexc : 0 ≤ K₀ / Real.log V := by positivity
  have hu := hup V hV22 b N hN hb1 hb hbr _ hexc hmom
  have hbudget := (abs_le.mp (hbud V (by linarith))).1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ z ∈ (shellZeros V (2 * V)).filter (fun z => 1 / 2 < z.re),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) := ⟨_, rfl⟩
  rw [← hM] at hbudget
  -- lower-order terms against `V / log V`
  have hsm2 : D * Real.log V ^ 2 ≤ V := by
    have hTe : Real.exp (-(1 * Real.log V)) = V⁻¹ := by
      rw [one_mul, Real.exp_neg, Real.exp_log hV0]
    rw [hTe, ← div_eq_mul_inv, div_le_iff₀ hV0] at hsm
    have h1 := mul_le_mul_of_nonneg_left hsm hD0.le
    refine h1.trans (le_of_eq ?_)
    field_simp
  have hVdiv : D * Real.log V ≤ V / Real.log V := by
    rw [le_div_iff₀ hℓ0]
    calc D * Real.log V * Real.log V = D * Real.log V ^ 2 := by ring
      _ ≤ V := hsm2
  have hlog2V : Real.log (2 * V) ≤ Real.log V + 1 := by
    rw [Real.log_mul two_ne_zero hV0.ne']
    have := Real.log_two_lt_d9
    linarith
  have hsum : 2 * Real.pi * M ≤ K₁ * (V / Real.log V) := by
    have h1 : K * (Real.log V + Real.log N) ≤ K * Real.log V + K * (V / Real.log V) := by
      rw [mul_add]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogN hK.le)
    have h2 : K' * Real.log (2 * V) ≤ K' * Real.log V + K' :=
      calc K' * Real.log (2 * V) ≤ K' * (Real.log V + 1) := mul_le_mul_of_nonneg_left hlog2V hK'.le
        _ = _ := by ring
    have h3 : K₀ / Real.log V / 2 * V = K₀ / 2 * (V / Real.log V) := by ring
    have h4 : K₁ * (V / Real.log V) =
        K₀ / 2 * (V / Real.log V) + K * (V / Real.log V) + V / Real.log V := by
      rw [hK₁]
      ring
    have h5 : C + C' + K' + (K + K') * Real.log V ≤ D * Real.log V := by
      have h6 : C + C' + K' ≤ (C + C' + K') * Real.log V := le_mul_of_one_le_right (by positivity) hℓ
      rw [hD]
      have h7 : (C + C' + K' + K + K' + 1) * Real.log V =
          (C + C' + K') * Real.log V + (K + K') * Real.log V + Real.log V := by ring
      rw [h7]
      linarith
    linarith
  have hfold := sum_order_filter_abs_le (V₁ := V) (V₂ := 2 * V) (x := A / Real.log V) (by positivity)
  rw [← hM] at hfold
  refine hfold.trans ?_
  have hval : 2 / (A / Real.log V) * M = Real.log V / (Real.pi * A) * (2 * Real.pi * M) := by
    field_simp
  rw [hval]
  calc Real.log V / (Real.pi * A) * (2 * Real.pi * M)
      ≤ Real.log V / (Real.pi * A) * (K₁ * (V / Real.log V)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = K₁ / Real.pi / A * V := by
        field_simp

/-- **The rate fails at every fixed exponent**: the excess of a polynomial-length mollifier is at least a constant. -/
theorem not_secondMomentRate_of_bounded_exponent {θ K₀ : ℝ} (hθ : 0 < θ) :
    ¬ ∀ᶠ T : ℝ in atTop, ∃ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N ∧ (N : ℝ) ≤ T ^ θ ∧ b 1 = 1 ∧
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          (1 + K₀ / Real.log T) * T := by
  intro h
  obtain ⟨T₀, hT₀⟩ := necessary_length hθ
  have hc : 0 < 1 / (8 + 6 * θ) := by positivity
  have hsmall : ∀ᶠ T : ℝ in atTop, K₀ / Real.log T < 1 / (8 + 6 * θ) := by
    have h1 : Tendsto (fun T : ℝ => K₀ / Real.log T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    exact h1.eventually (gt_mem_nhds hc)
  obtain ⟨T, ⟨b, N, hN, hNT, hb1, hb, hbr, hmom⟩, hK, hT, hT0⟩ :=
    (h.and (hsmall.and ((eventually_ge_atTop T₀).and (eventually_gt_atTop (0 : ℝ))))).exists
  have h1 := (hT₀ T hT b N hN hNT hb1 hb hbr).trans hmom
  have h2 := le_of_mul_le_mul_right h1 hT0
  linarith

/-- **The rate needs length `exp(c log²T)`.**  A mollifier with excess `K₀/log T` has `log N ≥ min(1/24, 1/(14K₀)) log²T`. -/
theorem log_length_ge_of_secondMomentRate {K₀ : ℝ} (hK₀ : 0 < K₀) :
    ∀ᶠ T : ℝ in atTop, ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          (1 + K₀ / Real.log T) * T →
      min (1 / 24) (1 / (14 * K₀)) * Real.log T ^ 2 ≤ Real.log N := by
  obtain ⟨T₀, hT₀⟩ := log_length_ge_of_excess
  filter_upwards [eventually_ge_atTop T₀, Real.tendsto_log_atTop.eventually_gt_atTop (14 * K₀)] with
    T hT hℓ b N hN hb1 hb hbr hmom
  have hℓ0 : 0 < Real.log T := by linarith
  have hκ0 : 0 < K₀ / Real.log T := by positivity
  have hκ : K₀ / Real.log T < 1 / 14 := by
    rw [div_lt_iff₀ hℓ0]
    linarith
  have h := hT₀ T hT b N hN hb1 hb hbr _ hκ0 hκ hmom
  refine le_trans ?_ h
  have hval : Real.log T / (14 * (K₀ / Real.log T)) = 1 / (14 * K₀) * Real.log T ^ 2 := by
    field_simp
  rw [hval]
  refine le_min ?_ ?_
  · calc min (1 / 24) (1 / (14 * K₀)) * Real.log T ^ 2 ≤ 1 / 24 * Real.log T ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)

end GaloisForLFunctions.ArithmeticProduction
