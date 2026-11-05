import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.NearLineDensityBesselCertificateAndSeparation
import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge

/-!
# The proportion hierarchy of the near-line questions

`100%` critical-scale clustering `(B20)` and log-free unit-window occupancy `(D_win, B21)` sit at
different levels relative to the critical-line proportion `N₀(V)/N(V)`.

1. **Proportion one gives clustering.** If `N₀(V)/N(V) → 1`, every off-line count beyond
   `κ / log V` is `o(V log V)` (`criticalClustering_of_tendsto_xiCriticalRatio_one`), hence all
   eight equivalent forms of `(L)` hold (`logMean_tendsto_zero_of_tendsto_xiCriticalRatio_one`).
2. **Proportion one and every exponential depth rate do not give occupancy.** `rootModel` places, in
   every unit window `m ≥ 256`, `2b_m − 2` simple critical zeros and one conjugate pair at depth
   `d_m = √(log log m) / log m`. It satisfies local Riemann–von Mangoldt, reflection symmetry, simple
   critical proportion `→ 1` in every window, near-line depth tails `≪_r e^{−ra} V` for every rate
   `r > 0`, `(L)` and clustering, and violates `(D_win)` and `(D_zero)`
   (`exists_proportionOne_allRates_model_not_windowOccupancy`).

So `(B20)` is a proportion statement and `(B21)` is not: no critical-line proportion and no fixed
exponential rate of the depth tail decides window occupancy; it needs depth decay at rate
`≍ log log V`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-! ## §1. Proportion one implies `100%` critical-scale clustering -/

/-- Zeros beyond `½ + a` (`a > 0`) are off the critical line. -/
theorem offLineCountBeyond_le_xiOffLineZeroCount {a : ℝ} (ha : 0 < a) (V : ℝ) :
    _root_.RHTower.offLineCountBeyond a V ≤ (_root_.RHTower.xiOffLineZeroCount V : ℝ) := by
  unfold _root_.RHTower.offLineCountBeyond _root_.RHTower.xiOffLineZeroCount
  push_cast
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_) (fun _ _ _ => Nat.cast_nonneg _)
  simp only [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, fun h => by linarith [hz.2]⟩

/-- The off-line copies are the census times the off-line proportion `1 − N₀/N`. -/
theorem xiOffLineZeroCount_le_mul (V : ℝ) :
    (_root_.RHTower.xiOffLineZeroCount V : ℝ) ≤
      (_root_.RHTower.xiPosZeroCount V : ℝ) * (1 - _root_.RHTower.xiCriticalRatio V) := by
  have hsum := _root_.RHTower.xiPosCriticalZeroCount_add_xiOffLineZeroCount V
  have hsumR : (_root_.RHTower.xiPosCriticalZeroCount V : ℝ) +
      (_root_.RHTower.xiOffLineZeroCount V : ℝ) = (_root_.RHTower.xiPosZeroCount V : ℝ) := by
    exact_mod_cast hsum
  rcases Nat.eq_zero_or_pos (_root_.RHTower.xiPosZeroCount V) with h0 | hpos
  · have h0R : (_root_.RHTower.xiPosZeroCount V : ℝ) = 0 := by exact_mod_cast h0
    have hc : (0 : ℝ) ≤ _root_.RHTower.xiPosCriticalZeroCount V := Nat.cast_nonneg _
    rw [h0R, zero_mul]
    linarith
  · have hposR : (0 : ℝ) < _root_.RHTower.xiPosZeroCount V := by exact_mod_cast hpos
    rw [_root_.RHTower.xiCriticalRatio, mul_sub, mul_one, mul_div_cancel₀ _ hposR.ne']
    linarith

/-- Riemann–von Mangoldt in the crude form `N(V) ≤ 2 V log V`. -/
theorem eventually_xiPosZeroCount_le_two_mul :
    ∀ᶠ V : ℝ in atTop, (_root_.RHTower.xiPosZeroCount V : ℝ) ≤ 2 * (V * Real.log V) := by
  obtain ⟨T₀, hT₀, hclose⟩ := _root_.RHTower.exists_xiZeroCount_close 1 one_pos
  filter_upwards [eventually_ge_atTop T₀] with V hV
  have hV0 : (0 : ℝ) ≤ V := by linarith
  have hcast : ((_root_.RHTower.xiPosZeroCount V : ℤ) : ℝ) =
      ((_root_.RHTower.xiZeroCount V : ℤ) : ℝ) :=
    congrArg (fun n : ℤ => (n : ℝ)) (_root_.RHTower.xiPosZeroCount_eq_xiZeroCount hV0)
  have habs := (abs_le.mp (hclose V hV)).2
  have hL : 0 ≤ V * Real.log V := mul_nonneg hV0 (Real.log_nonneg (by linarith))
  have hπ : 1 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
  push_cast at hcast
  rw [hcast]
  nlinarith

/-- **Proportion one gives `100%` critical-scale clustering.** If the proportion of the zero copies
of `ξ` in `(0, V]` lying on the critical line tends to `1`, then for every `κ > 0` the zeros beyond
`½ + κ / log V` are `o(V log V)`. -/
theorem criticalClustering_of_tendsto_xiCriticalRatio_one
    (h : Tendsto _root_.RHTower.xiCriticalRatio atTop (𝓝 1)) :
    ∀ κ : ℝ, 0 < κ →
      Tendsto (fun V : ℝ => _root_.RHTower.offLineCountBeyond (κ / Real.log V) V /
        (V * Real.log V)) atTop (𝓝 0) := by
  intro κ hκ
  have hup : Tendsto (fun V => 2 * (1 - _root_.RHTower.xiCriticalRatio V)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
    simpa using this.const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with V hV
    have hL : 0 < V * Real.log V := mul_pos (by linarith) (Real.log_pos (by linarith))
    refine div_nonneg ?_ hL.le
    unfold _root_.RHTower.offLineCountBeyond
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  · filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_xiPosZeroCount_le_two_mul] with V hV hN
    have hlog : 0 < Real.log V := Real.log_pos (by linarith)
    have hL : 0 < V * Real.log V := mul_pos (by linarith) hlog
    have hcrit : _root_.RHTower.xiCriticalRatio V ≤ 1 := by
      unfold _root_.RHTower.xiCriticalRatio
      exact div_le_one_of_le₀ (by exact_mod_cast _root_.RHTower.xiPosCriticalZeroCount_le V)
        (Nat.cast_nonneg _)
    have h1 := offLineCountBeyond_le_xiOffLineZeroCount (div_pos hκ hlog) V
    have h2 := xiOffLineZeroCount_le_mul V
    have h3 : (_root_.RHTower.xiPosZeroCount V : ℝ) * (1 - _root_.RHTower.xiCriticalRatio V) ≤
        2 * (V * Real.log V) * (1 - _root_.RHTower.xiCriticalRatio V) :=
      mul_le_mul_of_nonneg_right hN (by linarith)
    rw [div_le_iff₀ hL]
    nlinarith

/-- **Proportion one gives `(L)`.** If the critical-line proportion tends to `1`, the critical-line
log-mean `T⁻¹ ∫_T^{2T} log |ζ(½ + it)| dt` tends to `0` (with the other seven equivalent forms of
`criticalClustering_logMean_mollifier_hecke_tfae`). -/
theorem logMean_tendsto_zero_of_tendsto_xiCriticalRatio_one
    (h : Tendsto _root_.RHTower.xiCriticalRatio atTop (𝓝 1)) :
    Tendsto (fun T : ℝ =>
      T⁻¹ * ∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      atTop (𝓝 0) :=
  ((criticalClustering_logMean_mollifier_hecke_tfae (c := 1 / 4) (by norm_num)
    (by norm_num)).out 4 0).mp (criticalClustering_of_tendsto_xiCriticalRatio_one h)

/-! ## §2. `(D_zero) ⇒ (D_win)` in every unit-window model -/

/-- A bad window holds a deep zero of multiplicity `≥ 1`, so log-free zero density bounds the
number of bad windows. -/
theorem UnitWindowStripZeroModel.windowOccupancy_of_logFreeZeroDensity
    (M : UnitWindowStripZeroModel) (h : M.LogFreeZeroDensity) : M.WindowOccupancy := by
  obtain ⟨ε, hε, hev⟩ := h
  refine ⟨ε, hε, fun A hA => (hev A hA).mono fun V hV => le_trans ?_ hV⟩
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  calc ∑ m ∈ (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
        (fun m => ∃ z ∈ M.Z m, A / Real.log V ≤ |z.re - 1 / 2|), (1 : ℝ)
      ≤ ∑ m ∈ (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
          (fun m => ∃ z ∈ M.Z m, A / Real.log V ≤ |z.re - 1 / 2|),
          ∑ z ∈ (M.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|), (M.mult z : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        obtain ⟨z, hz, hdeep⟩ := (Finset.mem_filter.mp hm).2
        have hz' : z ∈ (M.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|) :=
          Finset.mem_filter.mpr ⟨hz, hdeep⟩
        calc (1 : ℝ) ≤ (M.mult z : ℝ) := by exact_mod_cast M.mult_pos m z hz
          _ ≤ _ := Finset.single_le_sum (f := fun z => (M.mult z : ℝ))
              (fun _ _ => Nat.cast_nonneg _) hz'
    _ ≤ ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ z ∈ (M.Z m).filter (fun z => A / Real.log V ≤ |z.re - 1 / 2|), (M.mult z : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

/-! ## §3. The root model: proportion one, every exponential depth rate, no occupancy -/

/-- `log x > 5` for `x ≥ 256`. -/
private lemma five_lt_log_of_le {x : ℝ} (hx : 256 ≤ x) : 5 < Real.log x := by
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  have h2 := Real.log_two_gt_d9
  have hle : Real.log 256 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  linarith

private lemma sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `√(log y) < y / 2` for `y > 5`. -/
private lemma sqrt_log_lt_half {y : ℝ} (hy : 5 < y) : Real.sqrt (Real.log y) < y / 2 := by
  have h1 : Real.log y ≤ y := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h2 : Real.sqrt (Real.log y) ≤ Real.sqrt y := Real.sqrt_le_sqrt h1
  have h3 : 2 < Real.sqrt y := by
    have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 4) (by linarith : (4 : ℝ) < y)
    rwa [sqrt_four] at this
  have h5 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
  nlinarith

private lemma card_window_le {V : ℝ} (hV : 1 ≤ V) :
    ((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).card : ℝ) ≤ 2 * V := by
  have hc : 1 ≤ Nat.ceil V := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; have := Nat.ceil_eq_zero.mp h0; linarith)
  have h1 : (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).card ≤ Nat.floor (2 * V) := by
    rw [Nat.card_Icc]; omega
  exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))

private lemma half_le_card_window {V : ℝ} (hV : 2 ≤ V) :
    V / 2 ≤ ((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).card : ℝ) := by
  have hceil_lt : (Nat.ceil V : ℝ) < V + 1 := Nat.ceil_lt_add_one (by linarith)
  have hfl_gt : 2 * V - 1 < (Nat.floor (2 * V) : ℝ) := Nat.sub_one_lt_floor (2 * V)
  have hle_cf : Nat.ceil V ≤ Nat.floor (2 * V) := by
    have : (Nat.ceil V : ℝ) < (Nat.floor (2 * V) : ℝ) := by linarith
    exact (Nat.cast_lt.mp this).le
  have hcard_eq : ((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).card : ℝ) =
      (Nat.floor (2 * V) : ℝ) + 1 - (Nat.ceil V : ℝ) := by
    rw [Nat.card_Icc]
    have : Nat.floor (2 * V) + 1 - Nat.ceil V + Nat.ceil V = Nat.floor (2 * V) + 1 := by omega
    have hc : ((Nat.floor (2 * V) + 1 - Nat.ceil V : ℕ) : ℝ) + (Nat.ceil V : ℝ) =
        (Nat.floor (2 * V) : ℝ) + 1 := by exact_mod_cast this
    linarith
  linarith

/-- Depth of the off-line pair of window `m`: `√(log log m) / log m` for `m ≥ 256`. -/
def dRoot (m : ℕ) : ℝ :=
  if m < 256 then 0 else Real.sqrt (Real.log (Real.log (m : ℝ))) / Real.log (m : ℝ)

lemma qSparse_dRoot_spec (m : ℕ) : qSparse m = 0 ∨ (0 < dRoot m ∧ dRoot m < 1 / 2) := by
  by_cases hm : m < 256
  · exact Or.inl (by simp [qSparse, hm])
  · refine Or.inr ?_
    have hm' : (256 : ℝ) ≤ m := by exact_mod_cast Nat.not_lt.mp hm
    have hy := five_lt_log_of_le hm'
    have hll : 0 < Real.log (Real.log (m : ℝ)) := Real.log_pos (by linarith)
    simp only [dRoot, if_neg hm]
    refine ⟨div_pos (Real.sqrt_pos.mpr hll) (by linarith), ?_⟩
    rw [div_lt_iff₀ (by linarith)]
    have := sqrt_log_lt_half hy
    linarith

lemma qSparse_dRoot_or (m : ℕ) : qSparse m = 0 ∨ 0 < dRoot m :=
  (qSparse_dRoot_spec m).imp id And.left

/-- On the windows `m ∈ [⌈V⌉, ⌊2V⌋]`, `V ≥ 512`, with `u = √(log log V)`:
`u / (2 log V) ≤ dRoot m ≤ 2u / log V`. -/
lemma dRoot_window {V : ℝ} (hV : 512 ≤ V) {m : ℕ}
    (hm : m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))) :
    ¬ m < 256 ∧
      Real.sqrt (Real.log (Real.log V)) / (2 * Real.log V) ≤ dRoot m ∧
      dRoot m ≤ 2 * Real.sqrt (Real.log (Real.log V)) / Real.log V := by
  obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm
  have hV_pos : 0 < V := by linarith
  have hm_ge_V : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast hm_lo)
  have hm_le_2V : (m : ℝ) ≤ 2 * V :=
    ((Nat.cast_le (α := ℝ)).mpr hm_hi).trans (Nat.floor_le (by positivity))
  have hm_not : ¬ m < 256 := by
    intro hlt; have : (m : ℝ) < 256 := by exact_mod_cast hlt
    linarith
  have hlogV : 5 < Real.log V := five_lt_log_of_le (by linarith)
  have hlogV_pos : 0 < Real.log V := by linarith
  have hlog_ge : Real.log V ≤ Real.log (m : ℝ) := Real.log_le_log hV_pos hm_ge_V
  have hlog_le : Real.log (m : ℝ) ≤ 2 * Real.log V := by
    have h1 : Real.log (m : ℝ) ≤ Real.log (2 * V) := Real.log_le_log (by linarith) hm_le_2V
    rw [Real.log_mul two_ne_zero hV_pos.ne'] at h1
    linarith [Real.log_two_lt_d9]
  have hll_ge : Real.log (Real.log V) ≤ Real.log (Real.log (m : ℝ)) :=
    Real.log_le_log hlogV_pos hlog_ge
  have hll_two : Real.log 2 ≤ Real.log (Real.log V) := Real.log_le_log two_pos (by linarith)
  have hll_le : Real.log (Real.log (m : ℝ)) ≤ 4 * Real.log (Real.log V) := by
    have h1 : Real.log (Real.log (m : ℝ)) ≤ Real.log (2 * Real.log V) :=
      Real.log_le_log (by linarith) hlog_le
    rw [Real.log_mul two_ne_zero hlogV_pos.ne'] at h1
    have hll0 : 0 ≤ Real.log (Real.log V) := le_trans (Real.log_nonneg one_le_two) hll_two
    linarith
  have hsq4 : Real.sqrt (4 * Real.log (Real.log V)) =
      2 * Real.sqrt (Real.log (Real.log V)) := by
    rw [Real.sqrt_mul (by norm_num), sqrt_four]
  have hlog_m_pos : 0 < Real.log (m : ℝ) := by linarith
  simp only [dRoot, if_neg hm_not]
  refine ⟨hm_not, ?_, ?_⟩
  · calc Real.sqrt (Real.log (Real.log V)) / (2 * Real.log V)
        ≤ Real.sqrt (Real.log (Real.log (m : ℝ))) / (2 * Real.log V) :=
          div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hll_ge) (by positivity)
      _ ≤ Real.sqrt (Real.log (Real.log (m : ℝ))) / Real.log (m : ℝ) :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hlog_m_pos hlog_le
  · calc Real.sqrt (Real.log (Real.log (m : ℝ))) / Real.log (m : ℝ)
        ≤ Real.sqrt (4 * Real.log (Real.log V)) / Real.log (m : ℝ) :=
          div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hll_le) hlog_m_pos.le
      _ ≤ Real.sqrt (4 * Real.log (Real.log V)) / Real.log V :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hlogV_pos hlog_ge
      _ = 2 * Real.sqrt (Real.log (Real.log V)) / Real.log V := by rw [hsq4]

/-- **Every exponential depth rate.** For every `r > 0`, eventually in `V` and for all `a ≥ 1`, the
right-half packet zeros beyond `½ + a / log V` in the windows of `[V, 2V]` obey the Selberg-type tail
bound with constant `8π` and rate `r`: for `a ≤ 2u` (`u = √(log log V)`) one uses
`u e^{ra} ≤ e^{(2r+1)u} ≤ e^{u²} = log V`, and beyond `2u` the windows are empty. -/
theorem rootPacket_depthTail {r : ℝ} (hr : 0 < r) :
    ∀ᶠ V : ℝ in atTop, ∀ a : ℝ, 1 ≤ a →
      2 * Real.pi * ((a / Real.log V) *
        ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ _z ∈ (packetWin m (nSparse m) (qSparse m) (dRoot m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ)) ≤
        8 * Real.pi * Real.exp (-(r * a)) * V := by
  have ht_ll : Tendsto (fun V : ℝ => Real.log (Real.log V)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (512 : ℝ),
    ht_ll.eventually_ge_atTop ((2 * r + 1) ^ 2)] with V hV hll a ha1
  have hV_pos : 0 < V := by linarith
  have hlogV : 5 < Real.log V := five_lt_log_of_le (by linarith)
  have hlogV_pos : 0 < Real.log V := by linarith
  set ℓ := Real.log (Real.log V) with hℓ
  set u := Real.sqrt ℓ with hu
  have hℓ0 : 0 ≤ ℓ := le_trans (sq_nonneg _) hll
  have hu_ge : 2 * r + 1 ≤ u := by
    rw [hu, ← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 2 * r + 1)]
    exact Real.sqrt_le_sqrt hll
  have hexpℓ : Real.exp ℓ = Real.log V := Real.exp_log hlogV_pos
  have huu : u * u = ℓ := Real.mul_self_sqrt hℓ0
  have hb : 0 < a / Real.log V := div_pos (by linarith) hlogV_pos
  rcases lt_or_ge (2 * u) a with ha_gt | ha_le
  · have hzero : ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        ∑ _z ∈ (packetWin m (nSparse m) (qSparse m) (dRoot m)).filter
          (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_eq_zero,
        packetWin_filter_right_card hb (qSparse_dRoot_or m), if_neg]
      have h1 := (dRoot_window hV hm).2.2
      have h2 : 2 * u / Real.log V < a / Real.log V := div_lt_div_of_pos_right ha_gt hlogV_pos
      linarith
    rw [hzero, mul_zero, mul_zero]
    positivity
  · have hcnt : ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        ∑ _z ∈ (packetWin m (nSparse m) (qSparse m) (dRoot m)).filter
          (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) ≤ 2 * V := by
      have hterm : ∀ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ _z ∈ (packetWin m (nSparse m) (qSparse m) (dRoot m)).filter
            (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ) ≤ 1 := by
        intro m _
        rw [Finset.sum_const, nsmul_eq_mul, mul_one,
          packetWin_filter_right_card hb (qSparse_dRoot_or m)]
        split_ifs
        · simp only [qSparse]; split_ifs <;> norm_num
        · norm_num
      calc _ ≤ ∑ _m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)), (1 : ℝ) :=
            Finset.sum_le_sum hterm
        _ = ((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).card : ℝ) := by simp
        _ ≤ 2 * V := card_window_le (by linarith)
    -- `u e^{ra} ≤ e^{(2r+1)u} ≤ e^{u²} = log V`
    have hkey : u * Real.exp (r * a) ≤ Real.log V := by
      have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
      have h2 : Real.exp (r * a) ≤ Real.exp (2 * r * u) := by
        refine Real.exp_le_exp.mpr ?_
        have := mul_le_mul_of_nonneg_left ha_le hr.le
        linarith
      have h3 : Real.exp u * Real.exp (2 * r * u) ≤ Real.exp (u * u) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have := mul_le_mul_of_nonneg_left hu_ge (Real.sqrt_nonneg ℓ)
        nlinarith
      calc u * Real.exp (r * a) ≤ Real.exp u * Real.exp (2 * r * u) :=
            mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
        _ ≤ Real.exp (u * u) := h3
        _ = Real.log V := by rw [huu, hexpℓ]
    have hratio : u / Real.log V ≤ Real.exp (-(r * a)) := by
      rw [div_le_iff₀ hlogV_pos]
      have he : Real.exp (r * a) * Real.exp (-(r * a)) = 1 := by
        rw [← Real.exp_add]; simp
      calc u = u * Real.exp (r * a) * Real.exp (-(r * a)) := by rw [mul_assoc, he, mul_one]
        _ ≤ Real.log V * Real.exp (-(r * a)) :=
            mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
        _ = Real.exp (-(r * a)) * Real.log V := mul_comm _ _
    calc 2 * Real.pi * ((a / Real.log V) *
          ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
            ∑ _z ∈ (packetWin m (nSparse m) (qSparse m) (dRoot m)).filter
              (fun z => 1 / 2 + a / Real.log V ≤ z.re), (1 : ℝ))
        ≤ 2 * Real.pi * ((2 * u / Real.log V) * (2 * V)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul (div_le_div_of_nonneg_right ha_le hlogV_pos.le) hcnt
            (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => zero_le_one)
            (by positivity)
      _ = 8 * Real.pi * (u / Real.log V) * V := by ring
      _ ≤ 8 * Real.pi * Real.exp (-(r * a)) * V :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (by positivity)) hV_pos.le

/-- **The root model.** In window `m ≥ 256`: `2b_m − 2` simple critical zeros and one simple
conjugate pair at `½ ± √(log log m) / log m`. -/
def rootModel : UnitWindowStripZeroModel where
  Z m := packetWin m (nSparse m) (qSparse m) (dRoot m)
  mult _ := 1
  in_unit_strip m := packetWin_in_unit_strip (qSparse_dRoot_spec m)
  mult_pos _ _ _ := zero_lt_one
  refl_mem m := packetWin_refl_mem m (nSparse m) (qSparse m) (dRoot m)
  refl_mult _ _ _ := rfl
  local_rvm := by
    refine ⟨2, by norm_num, fun m hm => ?_⟩
    rw [Finset.sum_const, smul_eq_mul, mul_one, packetWin_card (qSparse_dRoot_or m),
      nSparse_add_two_qSparse m]
    exact basePairs_rvm hm
  critical_simple_majority := by
    filter_upwards [eventually_ge_atTop 256,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 80]
      with m hm256 hlog80
    dsimp only [Function.comp_def] at hlog80
    rw [Finset.sum_const, smul_eq_mul, mul_one, packetWin_card (qSparse_dRoot_or m),
      nSparse_add_two_qSparse m, packetWin_filter_crit_card (qSparse_dRoot_or m)]
    have hm_not : ¬ m < 256 := not_lt.mpr hm256
    have hbp : 1 ≤ basePairs m := by simp only [basePairs, if_neg hm_not]; omega
    have hn_eq : (nSparse m : ℝ) = ((2 * basePairs m : ℕ) : ℝ) - 2 := by
      simp only [nSparse, if_neg hm_not]
      exact_mod_cast (Nat.cast_sub (by omega : 2 ≤ 2 * basePairs m))
    rw [hn_eq]
    have hrvm := (abs_le.mp (basePairs_rvm (by omega : 16 ≤ m))).1
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have hlog_div : 10 ≤ Real.log (m : ℝ) / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  selberg_arbitrary_rate := by
    intro r hr0 _
    refine ⟨8 * Real.pi, by positivity, ?_⟩
    filter_upwards [rootPacket_depthTail hr0] with V hV a ha
    simpa only [Nat.cast_one] using hV a ha

/-- The simple critical proportion of every root window tends to `1`. -/
theorem rootModel_simpleCritical_proportion (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      (1 - ε) * ((∑ z ∈ rootModel.Z m, rootModel.mult z : ℕ) : ℝ) ≤
        (((rootModel.Z m).filter (fun z => z.re = 1 / 2 ∧ rootModel.mult z = 1)).card : ℝ) := by
  filter_upwards [eventually_ge_atTop 256,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (4 * Real.pi / ε)] with m hm256 hlog
  dsimp only [Function.comp_def] at hlog
  show (1 - ε) * ((∑ _z ∈ packetWin m (nSparse m) (qSparse m) (dRoot m), (1 : ℕ) : ℕ) : ℝ) ≤
    (((packetWin m (nSparse m) (qSparse m) (dRoot m)).filter
      (fun z => z.re = 1 / 2 ∧ (1 : ℕ) = 1)).card : ℝ)
  rw [Finset.sum_const, smul_eq_mul, mul_one, packetWin_card (qSparse_dRoot_or m),
    nSparse_add_two_qSparse m, packetWin_filter_crit_card (qSparse_dRoot_or m)]
  have hm_not : ¬ m < 256 := not_lt.mpr hm256
  have hbp : 1 ≤ basePairs m := by simp only [basePairs, if_neg hm_not]; omega
  have hb_ge : Real.log (m : ℝ) / (4 * Real.pi) ≤ (basePairs m : ℝ) := by
    simp only [basePairs, if_neg hm_not]
    push_cast
    exact (Nat.lt_floor_add_one _).le
  have hn_eq : (nSparse m : ℝ) = 2 * (basePairs m : ℝ) - 2 := by
    simp only [nSparse, if_neg hm_not]
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hn_eq]
  push_cast
  have h1 : Real.log (m : ℝ) ≤ 4 * Real.pi * basePairs m := by
    rw [div_le_iff₀ (by positivity)] at hb_ge; linarith
  have h2 : 4 * Real.pi / ε ≤ 4 * Real.pi * basePairs m := hlog.trans h1
  have h3 : 1 ≤ ε * basePairs m := by
    rw [div_le_iff₀ hε] at h2
    have hπ : 0 < 4 * Real.pi := by positivity
    nlinarith
  linarith

/-- The near-line depth tail of the root model decays at every exponential rate. -/
theorem rootModel_depthTail_allRates {r : ℝ} (hr : 0 < r) :
    ∀ᶠ V : ℝ in atTop, ∀ a : ℝ, 1 ≤ a →
      2 * Real.pi * ((a / Real.log V) *
        ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ z ∈ (rootModel.Z m).filter (fun z => 1 / 2 + a / Real.log V ≤ z.re),
            (rootModel.mult z : ℝ)) ≤ 8 * Real.pi * Real.exp (-(r * a)) * V := by
  filter_upwards [rootPacket_depthTail hr] with V hV a ha
  simpa only [rootModel, Nat.cast_one] using hV a ha

/-- `(L)` for the root model: the off-line moment is `≤ 4u V/log V ≤ 4V/u`, `u = √(log log V)`. -/
theorem rootModel_horizontalMomentLittleO : rootModel.HorizontalMomentLittleO := by
  have ht_ll : Tendsto (fun V : ℝ => Real.log (Real.log V)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hsq : Tendsto (fun V : ℝ => Real.sqrt (Real.log (Real.log V))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ht_ll
  have hup : Tendsto (fun V : ℝ => 4 / Real.sqrt (Real.log (Real.log V))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsq
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with V hV
    refine mul_nonneg (inv_nonneg.mpr (by linarith)) (Finset.sum_nonneg fun m _ =>
      Finset.sum_nonneg fun z hz => mul_nonneg (Nat.cast_nonneg _) ?_)
    linarith [(Finset.mem_filter.mp hz).2]
  · filter_upwards [eventually_ge_atTop (512 : ℝ)] with V hV
    have hV_pos : 0 < V := by linarith
    have hlogV : 5 < Real.log V := five_lt_log_of_le (by linarith)
    have hlogV_pos : 0 < Real.log V := by linarith
    set ℓ := Real.log (Real.log V) with hℓ
    set u := Real.sqrt ℓ with hu
    have hℓ_pos : 0 < ℓ := Real.log_pos (by linarith)
    have hu_pos : 0 < u := Real.sqrt_pos.mpr hℓ_pos
    have huu : u * u = ℓ := Real.mul_self_sqrt hℓ_pos.le
    have hℓ_le : ℓ ≤ Real.log V := by
      have := Real.add_one_le_exp ℓ
      rw [Real.exp_log hlogV_pos] at this; linarith
    have hterm : ∀ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        ∑ z ∈ (rootModel.Z m).filter (fun z => 1 / 2 < z.re),
          (rootModel.mult z : ℝ) * (z.re - 1 / 2) ≤ 2 * u / Real.log V := by
      intro m hm
      obtain ⟨hm_not, -, hd⟩ := dRoot_window hV hm
      simp only [rootModel, Nat.cast_one]
      rw [packetWin_right_moment_sum (qSparse_dRoot_or m)]
      simp only [qSparse, if_neg hm_not, Nat.cast_one, one_mul]
      exact hd
    have hs := (Finset.sum_le_sum hterm).trans_eq (by rw [Finset.sum_const, nsmul_eq_mul])
    have hcard := card_window_le (V := V) (by linarith)
    have htot : ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        ∑ z ∈ (rootModel.Z m).filter (fun z => 1 / 2 < z.re),
          (rootModel.mult z : ℝ) * (z.re - 1 / 2) ≤ 2 * V * (2 * u / Real.log V) :=
      hs.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
    have hfrac : 4 * u / Real.log V ≤ 4 / u := by
      rw [div_le_div_iff₀ hlogV_pos hu_pos]
      nlinarith
    calc V⁻¹ * ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
          ∑ z ∈ (rootModel.Z m).filter (fun z => 1 / 2 < z.re),
            (rootModel.mult z : ℝ) * (z.re - 1 / 2)
        ≤ V⁻¹ * (2 * V * (2 * u / Real.log V)) :=
          mul_le_mul_of_nonneg_left htot (inv_nonneg.mpr hV_pos.le)
      _ = 4 * u / Real.log V := by field_simp; ring
      _ ≤ 4 / u := hfrac

/-- Clustering for the root model: at most two off-line zeros per window, so `O(V) = o(V log V)`. -/
theorem rootModel_criticalClustering : rootModel.CriticalClustering := by
  intro κ hκ
  refine Metric.tendsto_atTop.mpr fun η hη => ?_
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (4 / η + 1))
  refine ⟨max 16 V₀, fun V hV => ?_⟩
  have hV16 : 16 ≤ V := (le_max_left _ _).trans hV
  have hV_pos : 0 < V := by linarith
  have hlog_η : 4 / η + 1 ≤ Real.log V := hV₀ V ((le_max_right _ _).trans hV)
  have hlogV_pos : 0 < Real.log V := by
    have h4η : 0 < 4 / η := by positivity
    linarith
  have hnn : 0 ≤ (∑ m ∈ Finset.range (Nat.floor V + 1),
      ∑ z ∈ (rootModel.Z m).filter (fun z => κ / Real.log V ≤ |z.re - 1 / 2|),
        (rootModel.mult z : ℝ)) / (V * Real.log V) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      (by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, div_lt_iff₀ (mul_pos hV_pos hlogV_pos)]
  have hterm : ∀ m ∈ Finset.range (Nat.floor V + 1),
      ∑ z ∈ (rootModel.Z m).filter (fun z => κ / Real.log V ≤ |z.re - 1 / 2|),
        (rootModel.mult z : ℝ) ≤ 2 := by
    intro m _
    simp only [rootModel, Nat.cast_one]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      packetWin_filter_abs_card (div_pos hκ hlogV_pos) (qSparse_dRoot_or m)]
    split_ifs
    · simp only [qSparse]; split_ifs <;> norm_num
    · norm_num
  have hsum_le : ∑ m ∈ Finset.range (Nat.floor V + 1),
      ∑ z ∈ (rootModel.Z m).filter (fun z => κ / Real.log V ≤ |z.re - 1 / 2|),
        (rootModel.mult z : ℝ) ≤ 4 * V := by
    have hs := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    have hfl : ((Nat.floor V + 1 : ℕ) : ℝ) ≤ V + 1 := by
      push_cast; linarith [Nat.floor_le hV_pos.le]
    linarith
  have h4_lt : 4 < η * Real.log V := by
    have h1 : 4 / η < Real.log V := by linarith
    have h2 := mul_lt_mul_of_pos_left h1 hη
    rwa [mul_div_cancel₀ 4 hη.ne'] at h2
  calc _ ≤ 4 * V := hsum_le
    _ < (η * Real.log V) * V := mul_lt_mul_of_pos_right h4_lt hV_pos
    _ = η * (V * Real.log V) := by ring

/-- The root model violates `(D_win)`: for every fixed `A`, once `√(log log V) ≥ 2A` every window
of `[V, 2V]` holds a zero of depth `≥ A / log V`. -/
theorem rootModel_not_windowOccupancy : ¬ rootModel.WindowOccupancy := by
  rintro ⟨δ, hδ_lim, hδ_ev⟩
  obtain ⟨A₀, hA₀⟩ := Metric.tendsto_atTop.mp hδ_lim (1 / 4) (by norm_num)
  set A : ℝ := max A₀ 1
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hδ_lt : δ A < 1 / 4 := by
    have h := hA₀ A (le_max_left _ _)
    rw [Real.dist_eq, sub_zero] at h
    linarith [le_abs_self (δ A)]
  have ht_ll : Tendsto (fun V : ℝ => Real.log (Real.log V)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  obtain ⟨V₁, hV₁⟩ := eventually_atTop.mp
    ((hδ_ev A hA_pos).and ((eventually_ge_atTop (512 : ℝ)).and
      (ht_ll.eventually_ge_atTop ((2 * A) ^ 2))))
  obtain ⟨hocc, hV512, hll⟩ := hV₁ V₁ le_rfl
  have hlogV_pos : 0 < Real.log V₁ := by
    linarith [five_lt_log_of_le (by linarith : (256 : ℝ) ≤ V₁)]
  have hu : 2 * A ≤ Real.sqrt (Real.log (Real.log V₁)) := by
    rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 2 * A)]
    exact Real.sqrt_le_sqrt hll
  have hall : (Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁))).filter
      (fun m => ∃ z ∈ rootModel.Z m, A / Real.log V₁ ≤ |z.re - 1 / 2|) =
      Finset.Icc (Nat.ceil V₁) (Nat.floor (2 * V₁)) := by
    refine Finset.filter_eq_self.mpr fun m hm => ?_
    obtain ⟨hm_not, hd_lo, -⟩ := dRoot_window hV512 hm
    show ∃ z ∈ packetWin m (nSparse m) (qSparse m) (dRoot m), A / Real.log V₁ ≤ |z.re - 1 / 2|
    rw [packetWin_exists_abs_iff (div_pos hA_pos hlogV_pos) (qSparse_dRoot_or m)]
    refine ⟨by simp [qSparse, hm_not], ?_⟩
    calc A / Real.log V₁ = (2 * A) / (2 * Real.log V₁) :=
          (mul_div_mul_left A (Real.log V₁) two_ne_zero).symm
      _ ≤ Real.sqrt (Real.log (Real.log V₁)) / (2 * Real.log V₁) :=
          div_le_div_of_nonneg_right hu (by positivity)
      _ ≤ dRoot m := hd_lo
  rw [hall] at hocc
  have hcard_lo := half_le_card_window (V := V₁) (by linarith)
  have hmul_δ : δ A * V₁ < (1 / 4) * V₁ := mul_lt_mul_of_pos_right hδ_lt (by linarith)
  linarith

/-- **Proportion one and every exponential depth rate do not give window occupancy.** There is a
reflection-symmetric unit-window zero model with local Riemann–von Mangoldt, simple critical
proportion tending to `1` in every window, near-line depth tails `≪ e^{−ra} V` for every `r > 0`,
`(L)` and `100%` critical-scale clustering, which violates `(D_win)` and `(D_zero)`. -/
theorem exists_proportionOne_allRates_model_not_windowOccupancy :
    ∃ M : UnitWindowStripZeroModel,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
        (1 - ε) * ((∑ z ∈ M.Z m, M.mult z : ℕ) : ℝ) ≤
          (((M.Z m).filter (fun z => z.re = 1 / 2 ∧ M.mult z = 1)).card : ℝ)) ∧
      (∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 < C ∧ ∀ᶠ V : ℝ in atTop, ∀ a : ℝ, 1 ≤ a →
        2 * Real.pi * ((a / Real.log V) *
          ∑ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
            ∑ z ∈ (M.Z m).filter (fun z => 1 / 2 + a / Real.log V ≤ z.re), (M.mult z : ℝ)) ≤
          C * Real.exp (-(r * a)) * V) ∧
      M.HorizontalMomentLittleO ∧ M.CriticalClustering ∧
      ¬ M.WindowOccupancy ∧ ¬ M.LogFreeZeroDensity :=
  ⟨rootModel, rootModel_simpleCritical_proportion,
    fun _ hr => ⟨8 * Real.pi, by positivity, rootModel_depthTail_allRates hr⟩,
    rootModel_horizontalMomentLittleO, rootModel_criticalClustering,
    rootModel_not_windowOccupancy,
    fun h => rootModel_not_windowOccupancy (rootModel.windowOccupancy_of_logFreeZeroDensity h)⟩

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.logMean_tendsto_zero_of_tendsto_xiCriticalRatio_one
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_proportionOne_allRates_model_not_windowOccupancy
