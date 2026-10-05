import GaloisForLFunctions.HTGeometry.PrimitiveWorkTransmutation
import GaloisForLFunctions.HTGeometry.HyperbolicBounds
import GaloisForLFunctions.RHTower.SourceHorizontalWoldHolomorphicProfileNoGo

/-!
# The Wold primitive-work polarization and its signature wall

For the Wold response `I_W(u) = cosh u - sinh u / u`, the polar work is the reflected work
`P(u) = (log 2)/2 · u · C_W(u)` with `C_W = ∫₀ᵘ I_W` `(PW.12)`.

* **`(PW.13)`.**  `I_W = u²/3 + O(u⁴)` and `P = (log 2)/18 · u⁴ + O(u⁶)`: the Wold series gives
  `u²/3 ≤ I_W(u) ≤ u²/3 + u⁴ I_W(1)` on `[-1, 1]`, and the primitive divides the leading coefficient
  by the new order.
* **`(PW.14)`–`(PW.15)`.**  The normalized roots `q_vis` (odd) and `q_ori` (even) of `I_W - P` and
  `P` give `I_W = q_vis² + q_ori²`, `P = q_ori²`, realized with target reflection `diag(1, -1)`.
* **Theorem 5.1.**  `Δ_W = I_W - P` is even and positive near `0`, negative for `u ≥ 25`
  (`I_W ≤ eᵘ` while `P ≥ (log 2)/16 · u eᵘ`), and vanishes at some `u_* > 0`: the polarization is
  Euclidean near the event and Lorentzian far away, with one negative channel.
* **`(PW.18)`–`(PW.20)`.**  `C_W = sinh - Shi`, `I_W / eᵘ → 1/2`, `Shi / eᵘ → 0`, `C_W / eᵘ → 1/2`,
  and `P / I_W → ∞`.
-/

open Filter Topology Set
open scoped InnerProductSpace RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### The Wold work -/

/-- The Wold polar work `P(u) = (log 2)/2 · u · C_W(u)` `(PW.12)`. -/
abbrev woldWork : ℝ → ℝ := RHTower.sourceHorizontalWoldPrimeClockPolarRateWork

/-- The Wold current is the primitive of the response. -/
theorem woldCurrent_eq_primitive :
    RHTower.sourceHorizontalWoldPrimeClockCurrent = primitiveAtZero woldResponse := by
  funext u
  exact RHTower.sourceHorizontalWoldPrimeClockCurrent_eq_integral u

/-- **The polar work is the reflected work of the Wold response with `c = (log 2)/2`.** -/
theorem woldWork_eq_reflectedWork : woldWork = reflectedWork (Real.log 2 / 2) woldResponse := by
  funext u
  rw [woldWork, RHTower.sourceHorizontalWoldPrimeClockPolarRateWork_eq_mul_current,
    woldCurrent_eq_primitive, reflectedWork]

/-! ### `(PW.13)` -/

/-- The Wold series terms. -/
def woldTerm (u : ℝ) (n : ℕ) : ℝ :=
  ((2 * n : ℕ) : ℝ) / (2 * n + 1 : ℕ) * (u ^ (2 * n) / (2 * n).factorial)

theorem woldResponse_eq_tsum (u : ℝ) : woldResponse u = ∑' n, woldTerm u n := rfl

theorem woldTerm_nonneg (u : ℝ) (n : ℕ) : 0 ≤ woldTerm u n := by
  unfold woldTerm
  have h2 : 0 ≤ u ^ (2 * n) := by rw [pow_mul]; positivity
  positivity

/-- The quartic upper bound `I_W(u) ≤ u²/3 + u⁴ I_W(1)` on `[-1, 1]`. -/
theorem woldResponse_le (u : ℝ) (hu : |u| ≤ 1) :
    woldResponse u ≤ u ^ 2 / 3 + u ^ 4 * woldResponse 1 := by
  have hs : Summable (woldTerm u) := RHTower.summable_sourceHorizontalWoldPrimeClockResponse u
  have hs1 : Summable (woldTerm 1) := RHTower.summable_sourceHorizontalWoldPrimeClockResponse 1
  have hu2 : u ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg u) hu
  have hterm : ∀ n, woldTerm u n ≤
      (if n = 1 then u ^ 2 / 3 else 0) + u ^ 4 * woldTerm 1 n := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp [woldTerm]
      · simp only [woldTerm, if_true]
        norm_num
        nlinarith [sq_nonneg u, pow_nonneg (sq_nonneg u) 2]
    · have hn1 : n ≠ 1 := by omega
      rw [if_neg hn1, zero_add]
      have hpow : u ^ (2 * n) ≤ u ^ 4 := by
        rw [pow_mul, show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
        exact pow_le_pow_of_le_one (sq_nonneg u) hu2 hn
      unfold woldTerm
      rw [one_pow]
      have hc : 0 ≤ ((2 * n : ℕ) : ℝ) / (2 * n + 1 : ℕ) := by positivity
      have hf : 0 < ((2 * n).factorial : ℝ) := by positivity
      calc ((2 * n : ℕ) : ℝ) / (2 * n + 1 : ℕ) * (u ^ (2 * n) / (2 * n).factorial)
          ≤ ((2 * n : ℕ) : ℝ) / (2 * n + 1 : ℕ) * (u ^ 4 / (2 * n).factorial) := by
            gcongr
        _ = u ^ 4 * (((2 * n : ℕ) : ℝ) / (2 * n + 1 : ℕ) * (1 / (2 * n).factorial)) := by ring
  have hsum : Summable fun n => (if n = 1 then u ^ 2 / 3 else 0) + u ^ 4 * woldTerm 1 n :=
    (summable_of_ne_finset_zero (s := {1}) (by intro n hn; simp_all)).add (hs1.mul_left _)
  calc woldResponse u = ∑' n, woldTerm u n := rfl
    _ ≤ ∑' n, ((if n = 1 then u ^ 2 / 3 else 0) + u ^ 4 * woldTerm 1 n) :=
        Summable.tsum_le_tsum hterm hs hsum
    _ = u ^ 2 / 3 + u ^ 4 * woldResponse 1 := by
        rw [Summable.tsum_add (summable_of_ne_finset_zero (s := {1}) (by intro n hn; simp_all))
          (hs1.mul_left _), tsum_ite_eq, tsum_mul_left]
        rfl

/-- **`(PW.13)`: `I_W = u²/3 + O(u⁴)`**, contact order two with leading coefficient `1/3`. -/
theorem woldResponse_contact : AnalyticContact woldResponse 2 (1 / 3) := by
  obtain ⟨U, hU, -, -, hfac⟩ := woldResponse_evenPositive.exists_unit
  have hfac' : ∀ᶠ t in 𝓝 0, woldResponse t = t ^ 2 * U t := by simpa using hfac
  have hcont : Tendsto U (𝓝[≠] 0) (𝓝 (U 0)) :=
    hU.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlow : ∀ᶠ t in 𝓝[≠] 0, 1 / 3 ≤ U t := by
    filter_upwards [nhdsWithin_le_nhds hfac', self_mem_nhdsWithin] with t ht ht0
    have hl : t ^ 2 / 3 ≤ woldResponse t :=
      RHTower.sourceHorizontalWoldPrimeClockResponse_quadratic_lower t
    rw [ht] at hl
    have ht2 : 0 < t ^ 2 := by
      have : t ≠ 0 := ht0
      positivity
    nlinarith
  have hup : ∀ᶠ t in 𝓝[≠] 0, U t ≤ 1 / 3 + t ^ 2 * woldResponse 1 := by
    filter_upwards [nhdsWithin_le_nhds (hfac'.and (Metric.ball_mem_nhds 0 one_pos)),
      self_mem_nhdsWithin] with t ⟨ht, hb⟩ ht0
    have hb' : |t| ≤ 1 := by
      rw [Real.dist_eq, sub_zero] at hb
      exact hb.le
    have hu := woldResponse_le t hb'
    rw [ht] at hu
    have ht2 : 0 < t ^ 2 := by
      have : t ≠ 0 := ht0
      positivity
    have h4 : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    rw [h4] at hu
    nlinarith
  have hlim : Tendsto (fun t : ℝ => 1 / 3 + t ^ 2 * woldResponse 1) (𝓝[≠] 0) (𝓝 (1 / 3)) := by
    have h : Continuous fun t : ℝ => 1 / 3 + t ^ 2 * woldResponse 1 := by fun_prop
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have hU0 : U 0 = 1 / 3 :=
    le_antisymm (le_of_tendsto_of_tendsto hcont hlim hup) (ge_of_tendsto hcont hlow)
  exact ⟨U, hU, hU0, by norm_num, by simpa [smul_eq_mul] using hfac'⟩

/-- **`(PW.13)`: the current `C_W = u³/9 + …`.** -/
theorem woldCurrent_contact : AnalyticContact (primitiveAtZero woldResponse) 3 (1 / 9) := by
  have h := woldResponse_contact.primitive
  norm_num at h
  exact h

/-- **`(PW.13)`: `P = (log 2)/18 · u⁴ + O(u⁶)`.** -/
theorem woldWork_contact : AnalyticContact woldWork 4 (Real.log 2 / 18) := by
  obtain ⟨V, hV, hV0, -, hfac⟩ := woldCurrent_contact
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨fun t => Real.log 2 / 2 * V t, analyticAt_const.mul hV,
    by show Real.log 2 / 2 * V 0 = _; rw [hV0]; ring,
    (div_pos hlog (by norm_num)).ne', ?_⟩
  filter_upwards [hfac] with t ht
  rw [woldWork_eq_reflectedWork, reflectedWork, ht, smul_eq_mul, smul_eq_mul]
  ring

/-! ### `(PW.14)`–`(PW.15)` -/

theorem channelReflection_one :
    channelReflection 1 planeE0 = planeE0 ∧ channelReflection 1 planeE1 = -planeE1 := by
  rw [channelReflection_e0, channelReflection_e1]
  norm_num

/-- **`(PW.14)`–`(PW.15)`: the Wold primitive-work polarization.**  The normalized roots `q_vis` of
`I_W - P` (odd) and `q_ori` of `P` (even) satisfy `I_W = q_vis² + q_ori²`, `P = q_ori²`, and their
primitive is an oriented realization with target reflection `diag(1, -1)`. -/
theorem wold_primitiveWork_polarization :
    ∃ qvis qori : ℝ → ℝ, IsNormalizedRoot (fun u => woldResponse u - woldWork u) 1 qvis ∧
      IsNormalizedRoot woldWork 2 qori ∧ (∀ᶠ u in 𝓝 0, qvis (-u) = -qvis u) ∧
      (∀ᶠ u in 𝓝 0, qori (-u) = qori u) ∧
      (∀ᶠ u in 𝓝 0, woldResponse u = qvis u ^ 2 + qori u ^ 2) ∧
      (∀ᶠ u in 𝓝 0, woldWork u = qori u ^ 2) ∧
      ∃ ρ : OrientedRealization woldResponse (EuclideanSpace ℝ (Fin 2)),
        ρ.refl = channelReflection 1 ∧
        ρ.curve = fun t => primitiveAtZero qvis t • planeE0 + primitiveAtZero qori t • planeE1 := by
  have hc : 0 < Real.log 2 / 2 := div_pos (Real.log_pos one_lt_two) two_pos
  have hI := woldResponse_evenPositive
  obtain ⟨q, w, hq, hw⟩ := hI.exists_work_roots hc
  obtain ⟨hqc, hwc⟩ := hI.work_root_characters hq hw
  rw [← woldWork_eq_reflectedWork] at hq hw
  obtain ⟨-, ρ, hρ⟩ := hI.primitiveWork_polarization (c := Real.log 2 / 2)
    (by rw [← woldWork_eq_reflectedWork]; exact hq) (by rw [← woldWork_eq_reflectedWork]; exact hw)
  obtain ⟨-, -, -, -, hqsq⟩ := id hq
  obtain ⟨-, -, -, -, hwsq⟩ := id hw
  refine ⟨q, w, hq, hw, ?_, ?_, ?_, ?_, ρ, hρ⟩
  · filter_upwards [hqc] with t ht
    rw [ht, pow_one, neg_one_mul]
  · filter_upwards [hwc] with t ht
    rw [ht]
    norm_num
  · filter_upwards [hqsq, hwsq] with t h1 h2
    rw [h1, h2]
    ring
  · filter_upwards [hwsq] with t h
    rw [h]

/-! ### Theorem 5.1: the signature wall -/

/-- `Δ_W = I_W - P` `(PW.16)`. -/
def woldGap (u : ℝ) : ℝ := woldResponse u - woldWork u

theorem woldGap_even (u : ℝ) : woldGap (-u) = woldGap u := by
  unfold woldGap woldResponse woldWork
  rw [RHTower.sourceHorizontalWoldPrimeClockResponse_even,
    RHTower.sourceHorizontalWoldPrimeClockPolarRateWork_neg]

/-- **Theorem 5.1 (1).**  `Δ_W` is positive on a punctured neighbourhood of `0`. -/
theorem woldGap_pos : ∀ᶠ u in 𝓝[≠] 0, 0 < woldGap u := by
  obtain ⟨qvis, -, ⟨H, hH, hH0, hr, hsq⟩, -⟩ := wold_primitiveWork_polarization
  have hHpos : ∀ᶠ t in 𝓝 0, 0 < H t :=
    (hH.continuousAt : Tendsto H (𝓝 0) (𝓝 (H 0))).eventually_const_lt hH0
  filter_upwards [nhdsWithin_le_nhds (hr.and (hsq.and hHpos)), self_mem_nhdsWithin]
    with t ⟨h1, h2, h3⟩ ht0
  rw [woldGap, ← h2, h1]
  have : t ≠ 0 := ht0
  positivity

/-- **The polar work is positive away from `0`.** -/
theorem woldWork_pos {u : ℝ} (hu : u ≠ 0) : 0 < woldWork u :=
  lt_of_le_of_ne (RHTower.sourceHorizontalWoldPrimeClockPolarRateWork_nonneg u)
    (Ne.symm ((RHTower.sourceHorizontalWoldPrimeClockPolarRateWork_eq_zero_iff u).not.mpr hu))

theorem woldResponse_nonneg (u : ℝ) : 0 ≤ woldResponse u :=
  le_trans (by positivity) (RHTower.sourceHorizontalWoldPrimeClockResponse_quadratic_lower u)

theorem woldResponse_le_exp {u : ℝ} (hu : 0 ≤ u) : woldResponse u ≤ Real.exp u := by
  rw [show woldResponse u = Real.cosh u - RHTower.woldRemovableSinhc u from
    RHTower.sourceHorizontalWoldPrimeClockResponse_eq_cosh_sub_sinhc u]
  have hs : 0 ≤ RHTower.woldRemovableSinhc u := by
    by_cases h0 : u = 0
    · rw [h0, RHTower.woldRemovableSinhc_zero]
      norm_num
    · rw [RHTower.woldRemovableSinhc_eq h0]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hu) hu
  have hc : Real.cosh u ≤ Real.exp u := by
    rw [Real.cosh_eq]
    have : Real.exp (-u) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
    linarith
  linarith

theorem exp_div_four_le_woldResponse {v : ℝ} (hv : 2 ≤ v) : Real.exp v / 4 ≤ woldResponse v := by
  have hv0 : v ≠ 0 := by linarith
  rw [show woldResponse v = Real.cosh v - Real.sinh v / v from
    RHTower.sourceHorizontalWoldPrimeClockResponse_eq_cosh_sub_sinh_div hv0]
  have hsinh : 0 ≤ Real.sinh v := Real.sinh_nonneg_iff.mpr (by linarith)
  have h1 : Real.sinh v / v ≤ Real.sinh v / 2 := div_le_div_of_nonneg_left hsinh two_pos hv
  have h2 : Real.sinh v < Real.cosh v := Real.sinh_lt_cosh v
  have h3 : Real.exp v / 2 ≤ Real.cosh v := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-v)
    linarith
  linarith

theorem woldCurrent_ge {u : ℝ} (hu : 2 ≤ u) :
    (Real.exp u - Real.exp 2) / 4 ≤ primitiveAtZero woldResponse u := by
  have hcont := RHTower.continuous_sourceHorizontalWoldPrimeClockResponse
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 2)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 2 u)
  have h02 : 0 ≤ ∫ v in (0 : ℝ)..2, woldResponse v :=
    intervalIntegral.integral_nonneg (by norm_num) fun v _ => woldResponse_nonneg v
  have h2u : ∫ v in (2 : ℝ)..u, Real.exp v / 4 ≤ ∫ v in (2 : ℝ)..u, woldResponse v :=
    intervalIntegral.integral_mono_on hu
      ((Real.continuous_exp.div_const 4).intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
      fun v hv => exp_div_four_le_woldResponse hv.1
  rw [intervalIntegral.integral_div, integral_exp] at h2u
  change (Real.exp u - Real.exp 2) / 4 ≤ ∫ v in (0 : ℝ)..u, woldResponse v
  rw [← hsplit]
  linarith

theorem woldWork_ge {u : ℝ} (hu : 25 ≤ u) :
    Real.log 2 / 16 * u * Real.exp u ≤ woldWork u := by
  have hC := woldCurrent_ge (by linarith : (2 : ℝ) ≤ u)
  have hexp : 2 * Real.exp 2 ≤ Real.exp u := by
    have h := Real.add_one_le_exp (u - 2)
    have h' : Real.exp u = Real.exp 2 * Real.exp (u - 2) := by
      rw [← Real.exp_add]
      ring_nf
    rw [h']
    have he := Real.exp_pos 2
    nlinarith
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [woldWork_eq_reflectedWork, reflectedWork]
  have hu0 : 0 ≤ u := by linarith
  have hC' : Real.exp u / 8 ≤ primitiveAtZero woldResponse u := by linarith
  calc Real.log 2 / 16 * u * Real.exp u = Real.log 2 / 2 * u * (Real.exp u / 8) := by ring
    _ ≤ Real.log 2 / 2 * u * primitiveAtZero woldResponse u := by gcongr

/-- **Theorem 5.1 (2).**  `Δ_W(u) < 0` for `u ≥ 25`. -/
theorem woldGap_neg {u : ℝ} (hu : 25 ≤ u) : woldGap u < 0 := by
  have h1 := woldResponse_le_exp (by linarith : (0 : ℝ) ≤ u)
  have h2 := woldWork_ge hu
  have hlog := Real.log_two_gt_d9
  have he := Real.exp_pos u
  have h3 : Real.exp u < Real.log 2 / 16 * u * Real.exp u := by
    have : 1 < Real.log 2 / 16 * u := by nlinarith
    nlinarith
  rw [woldGap]
  linarith

theorem continuous_woldWork : Continuous woldWork :=
  continuous_iff_continuousAt.mpr fun u =>
    (RHTower.hasDerivAt_sourceHorizontalWoldPrimeClockPolarRateWork u).continuousAt

theorem continuous_woldGap : Continuous woldGap :=
  RHTower.continuous_sourceHorizontalWoldPrimeClockResponse.sub continuous_woldWork

/-- **Theorem 5.1 (3).**  The gap vanishes at some `u_* > 0`. -/
theorem exists_woldGap_eq_zero : ∃ u > 0, woldGap u = 0 := by
  have hsub : Ioi (0 : ℝ) ⊆ {0}ᶜ := fun u (hu : 0 < u) => ne_of_gt hu
  have hpos : ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < woldGap u := nhdsWithin_mono 0 hsub woldGap_pos
  obtain ⟨ε, hε, hε0, hε25⟩ := (hpos.and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 25))).exists
  have hivt := intermediate_value_Icc' hε25.le continuous_woldGap.continuousOn
  obtain ⟨u, hu, hu0⟩ := hivt ⟨(woldGap_neg le_rfl).le, hε.le⟩
  exact ⟨u, lt_of_lt_of_le hε0 hu.1, hu0⟩

/-- **Theorem 5.1, `(PW.17)`: the signature transition.**  The response splits as work plus gap;
near `0` both parts are positive (Euclidean); for `u ≥ 25` the response is work minus a positive
excess (Lorentzian, exactly one negative channel since the work stays positive); and the gap
crosses zero at a finite `u_* > 0`. -/
theorem wold_signature_transition :
    (∀ u, woldResponse u = woldWork u + woldGap u) ∧
      (∀ᶠ u in 𝓝[≠] 0, 0 < woldWork u ∧ 0 < woldGap u) ∧
      (∀ u, 25 ≤ u → 0 < woldWork u ∧ 0 < woldWork u - woldResponse u ∧
        woldResponse u = woldWork u - (woldWork u - woldResponse u)) ∧
      ∃ u > 0, woldGap u = 0 := by
  refine ⟨fun u => by rw [woldGap]; ring, ?_, fun u hu => ⟨woldWork_pos (by linarith), ?_,
    by ring⟩, exists_woldGap_eq_zero⟩
  · filter_upwards [woldGap_pos, self_mem_nhdsWithin] with u h1 h2
    exact ⟨woldWork_pos h2, h1⟩
  · have := woldGap_neg hu
    rw [woldGap] at this
    linarith

/-! ### `(PW.18)`–`(PW.20)`: exponential asymptotics -/

/-- The hyperbolic sine integral `Shi(u) = ∫₀ᵘ sinh v / v` `(PW.18)`. -/
def sinhIntegral (u : ℝ) : ℝ := ∫ v in (0 : ℝ)..u, RHTower.woldRemovableSinhc v

/-- **`(PW.18)`: `C_W = sinh - Shi`.** -/
theorem woldCurrent_eq_sinh_sub_sinhIntegral (u : ℝ) :
    primitiveAtZero woldResponse u = Real.sinh u - sinhIntegral u := by
  have hcosh : ∫ v in (0 : ℝ)..u, Real.cosh v = Real.sinh u := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => Real.hasDerivAt_sinh x)
      (Real.continuous_cosh.intervalIntegrable _ _), Real.sinh_zero, sub_zero]
  show ∫ v in (0 : ℝ)..u, RHTower.sourceHorizontalWoldPrimeClockResponse v = _
  simp_rw [RHTower.sourceHorizontalWoldPrimeClockResponse_eq_cosh_sub_sinhc]
  rw [intervalIntegral.integral_sub (Real.continuous_cosh.intervalIntegrable _ _)
    (RHTower.continuous_woldRemovableSinhc.intervalIntegrable _ _), hcosh, sinhIntegral]

theorem tendsto_exp_neg_two_mul : Tendsto (fun u : ℝ => Real.exp (-(2 * u))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop two_pos)

theorem exp_neg_two_mul_eq (u : ℝ) : Real.exp (-(2 * u)) = Real.exp (-u) / Real.exp u := by
  rw [← Real.exp_sub]
  ring_nf

/-- **`(PW.19)`: `I_W(u) / eᵘ → 1/2`.** -/
theorem tendsto_woldResponse_div_exp :
    Tendsto (fun u => woldResponse u / Real.exp u) atTop (𝓝 (1 / 2)) := by
  have h1 := tendsto_exp_neg_two_mul
  have hlim : Tendsto (fun u : ℝ => (1 + Real.exp (-(2 * u))) / 2 -
      (1 - Real.exp (-(2 * u))) / 2 * u⁻¹) atTop (𝓝 (1 / 2)) := by
    have := ((h1.const_add 1).div_const 2).sub ((((h1.const_sub 1)).div_const 2).mul
      tendsto_inv_atTop_zero)
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with u hu
  rw [show woldResponse u = Real.cosh u - Real.sinh u / u from
    RHTower.sourceHorizontalWoldPrimeClockResponse_eq_cosh_sub_sinh_div hu.ne', Real.cosh_eq,
    Real.sinh_eq, exp_neg_two_mul_eq]
  have he := Real.exp_pos u
  field_simp

theorem woldRemovableSinhc_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ RHTower.woldRemovableSinhc v := by
  by_cases h0 : v = 0
  · rw [h0, RHTower.woldRemovableSinhc_zero]
    norm_num
  · rw [RHTower.woldRemovableSinhc_eq h0]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hv) hv

theorem sinh_le_exp (v : ℝ) : Real.sinh v ≤ Real.exp v := by
  rw [Real.sinh_eq]
  have := Real.exp_pos (-v)
  have := Real.exp_pos v
  linarith

theorem woldRemovableSinhc_le_exp {v : ℝ} (hv : 0 ≤ v) :
    RHTower.woldRemovableSinhc v ≤ Real.exp v := by
  by_cases h0 : v = 0
  · rw [h0, RHTower.woldRemovableSinhc_zero, Real.exp_zero]
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm h0)
    rw [RHTower.woldRemovableSinhc_eq h0, div_le_iff₀ hvpos]
    have h1 := HTGeometry.sinh_le_self_mul_cosh hv
    have h2 : Real.cosh v ≤ Real.exp v := by
      rw [Real.cosh_eq]
      have : Real.exp (-v) ≤ Real.exp v := Real.exp_le_exp.mpr (by linarith)
      linarith
    nlinarith

theorem woldRemovableSinhc_le_of_half {u v : ℝ} (hu : 0 < u) (hv : u / 2 ≤ v) :
    RHTower.woldRemovableSinhc v ≤ 2 / u * Real.exp v := by
  have hvpos : 0 < v := by linarith
  rw [RHTower.woldRemovableSinhc_eq hvpos.ne', div_le_iff₀ hvpos]
  have h1 := sinh_le_exp v
  have he := Real.exp_pos v
  have h2 : Real.exp v ≤ 2 / u * Real.exp v * v := by
    have : 1 ≤ 2 / u * v := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hu]
      linarith
    nlinarith
  linarith

theorem sinhIntegral_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ sinhIntegral u :=
  intervalIntegral.integral_nonneg hu fun _ hv => woldRemovableSinhc_nonneg hv.1

theorem sinhIntegral_le {u : ℝ} (hu : 0 < u) :
    sinhIntegral u ≤ Real.exp (u / 2) + 2 / u * Real.exp u := by
  have hcont := RHTower.continuous_woldRemovableSinhc
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (u / 2))
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) (u / 2) u)
  have hA : ∫ v in (0 : ℝ)..u / 2, RHTower.woldRemovableSinhc v ≤
      ∫ v in (0 : ℝ)..u / 2, Real.exp v :=
    intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
      (Real.continuous_exp.intervalIntegrable _ _) fun v hv => woldRemovableSinhc_le_exp hv.1
  have hB : ∫ v in u / 2..u, RHTower.woldRemovableSinhc v ≤
      ∫ v in u / 2..u, 2 / u * Real.exp v :=
    intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
      ((continuous_const.mul Real.continuous_exp).intervalIntegrable _ _)
      fun v hv => woldRemovableSinhc_le_of_half hu hv.1
  rw [integral_exp, Real.exp_zero] at hA
  rw [intervalIntegral.integral_const_mul, integral_exp] at hB
  have h1 := Real.exp_pos (u / 2)
  have h2 : 0 ≤ 2 / u * Real.exp (u / 2) := by positivity
  rw [sinhIntegral, ← hsplit]
  nlinarith

/-- `Shi(u) / eᵘ → 0`. -/
theorem tendsto_sinhIntegral_div_exp :
    Tendsto (fun u => sinhIntegral u / Real.exp u) atTop (𝓝 0) := by
  have hupper : Tendsto (fun u : ℝ => Real.exp (-(u / 2)) + 2 * u⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => Real.exp (-(u / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const two_pos)
    simpa using h1.add (tendsto_inv_atTop_zero.const_mul 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with u hu
    exact div_nonneg (sinhIntegral_nonneg hu.le) (Real.exp_pos u).le
  · filter_upwards [eventually_gt_atTop 0] with u hu
    have he := Real.exp_pos u
    rw [div_le_iff₀ he]
    have h1 := sinhIntegral_le hu
    have h2 : Real.exp (-(u / 2)) * Real.exp u = Real.exp (u / 2) := by
      rw [← Real.exp_add]
      ring_nf
    calc sinhIntegral u ≤ Real.exp (u / 2) + 2 / u * Real.exp u := h1
      _ = (Real.exp (-(u / 2)) + 2 * u⁻¹) * Real.exp u := by
          rw [add_mul, h2]
          ring

/-- `C_W(u) / eᵘ → 1/2`. -/
theorem tendsto_woldCurrent_div_exp :
    Tendsto (fun u => primitiveAtZero woldResponse u / Real.exp u) atTop (𝓝 (1 / 2)) := by
  have hsinh : Tendsto (fun u : ℝ => (1 - Real.exp (-(2 * u))) / 2) atTop (𝓝 (1 / 2)) := by
    simpa using (tendsto_exp_neg_two_mul.const_sub 1).div_const 2
  have h := hsinh.sub tendsto_sinhIntegral_div_exp
  rw [sub_zero] at h
  refine h.congr' (Eventually.of_forall fun u => ?_)
  show _ = primitiveAtZero woldResponse u / Real.exp u
  rw [woldCurrent_eq_sinh_sub_sinhIntegral, Real.sinh_eq, exp_neg_two_mul_eq]
  have he := Real.exp_pos u
  field_simp

/-- **`(PW.20)`: `P / I_W → ∞`.** -/
theorem tendsto_woldWork_div_woldResponse :
    Tendsto (fun u => woldWork u / woldResponse u) atTop atTop := by
  have hlog : 0 < Real.log 2 / 16 := div_pos (Real.log_pos one_lt_two) (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop hlog)
  filter_upwards [eventually_ge_atTop 25] with u hu
  have hW := woldResponse_le_exp (by linarith : (0 : ℝ) ≤ u)
  have hWpos : 0 < woldResponse u := by
    have hl : u ^ 2 / 3 ≤ woldResponse u :=
      RHTower.sourceHorizontalWoldPrimeClockResponse_quadratic_lower u
    have : 0 < u ^ 2 / 3 := by
      have : 0 < u := by linarith
      positivity
    linarith
  have hP := woldWork_ge hu
  have he := Real.exp_pos u
  rw [id, le_div_iff₀ hWpos]
  have hu0 : 0 ≤ Real.log 2 / 16 * u := by positivity
  calc Real.log 2 / 16 * u * woldResponse u ≤ Real.log 2 / 16 * u * Real.exp u := by gcongr
    _ ≤ woldWork u := hP

end GaloisForLFunctions.HTGeometry
