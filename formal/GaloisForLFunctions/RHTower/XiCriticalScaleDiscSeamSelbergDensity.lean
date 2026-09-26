import GaloisForLFunctions.RHTower.SelbergNearLineZeroDensity
import GaloisForLFunctions.RHTower.XiCriticalScaleDiscSeamProportion
import GaloisForLFunctions.RHTower.XiHorizontalSliceDensityFromMeanSquare
import GaloisForLFunctions.RHTower.ZetaLineLogMeanLittlewoodBudget

/-!
# Almost every critical-scale right disc has a contracting seam

Take the discs of radius `r = 2a/log U` centred at `1/2 + 2r + 3rk·i` whose heights lie in the
window `[T₁, T₂] ⊂ [U/4, U/2]` (`criticalScaleWindow`). A disc is exceptional when it contains a
zero of `ξ`; off the exceptional discs the adjoint seam of the `ξ` phase is a strict contraction
(`criticalScaleDisc_adjointSeam_lt_one`).

Every exceptional disc contains a zero with `Re ρ ≥ 1/2 + r`, different discs contain different
zeros, and the Selberg-type density `exists_selberg_nearLine_zeroDensity` bounds those zeros by
`(T₂ − T₁) log U · r_A(a)/(4πa) + O(log² U / a)` while the window holds about
`(T₂ − T₁) log U/(6a)` discs. Since `r_A(a) → 0`:

for every `ε > 0` there is `a₀` such that for every `a ≥ a₀` and all large `U` the exceptional
discs are at most an `ε`-fraction of the window (`exists_criticalScale_badDisc_proportion_le`).

This is the large-`a` complement of the `HD(1)` proportion producer: at the zero-spacing scale,
route 1's criterion holds on all but a vanishing proportion of the right discs.
-/

noncomputable section

open Complex Metric Set Filter

namespace RHTower

/-- Indices of the critical-scale discs of radius `r` with heights inside `[T₁, T₂]`. -/
def criticalScaleWindow (r T₁ T₂ : ℝ) : Finset ℕ :=
  Finset.Icc ⌈(T₁ + r) / (3 * r)⌉₊ ⌊(T₂ - r) / (3 * r)⌋₊

/-- The exceptional discs of the window. -/
def badCriticalScaleWindowDiscs (r T₁ T₂ : ℝ) : Finset ℕ := by
  classical
  exact (criticalScaleWindow r T₁ T₂).filter
    (fun k => ∃ z ∈ closedBall (criticalScaleCenter r k) r, xi z = 0)

theorem mem_criticalScaleWindow_heights {r T₁ T₂ : ℝ} (hr : 0 < r) (hT₂ : r ≤ T₂) {k : ℕ}
    (hk : k ∈ criticalScaleWindow r T₁ T₂) :
    T₁ + r ≤ 3 * r * k ∧ 3 * r * k ≤ T₂ - r := by
  unfold criticalScaleWindow at hk
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
  have h3r : 0 < 3 * r := by positivity
  constructor
  · have := (Nat.ceil_le.mp h1)
    rw [div_le_iff₀ h3r] at this
    linarith
  · have h0 : 0 ≤ (T₂ - r) / (3 * r) := div_nonneg (by linarith) h3r.le
    have := (Nat.le_floor_iff h0).mp h2
    rw [le_div_iff₀ h3r] at this
    linarith

/-- **Exceptional discs of the window are at most the zeros right of `1/2 + r`.** -/
theorem card_badCriticalScaleWindowDiscs_le {r T₁ T₂ : ℝ} (hr : 0 < r) (hr8 : r ≤ 1 / 8)
    (hT₁ : 0 < T₁) (hT₂ : r ≤ T₂) {Z : Finset ℂ}
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) :
    ((badCriticalScaleWindowDiscs r T₁ T₂).card : ℝ) ≤
      ∑ w ∈ Z.filter (fun w => 1 / 2 + r ≤ w.re), ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
  classical
  have hchoose : ∀ k ∈ badCriticalScaleWindowDiscs r T₁ T₂,
      ∃ z ∈ closedBall (criticalScaleCenter r k) r, xi z = 0 := by
    intro k hk
    unfold badCriticalScaleWindowDiscs at hk
    exact (Finset.mem_filter.mp hk).2
  choose! w hwball hwzero using hchoose
  have hwin : ∀ k ∈ badCriticalScaleWindowDiscs r T₁ T₂, k ∈ criticalScaleWindow r T₁ T₂ := by
    intro k hk
    unfold badCriticalScaleWindowDiscs at hk
    exact (Finset.mem_filter.mp hk).1
  have hmaps : ∀ k ∈ badCriticalScaleWindowDiscs r T₁ T₂,
      w k ∈ Z.filter (fun w => 1 / 2 + r ≤ w.re) := by
    intro k hk
    obtain ⟨h1, h2, h3, h4⟩ := re_im_of_mem_criticalScaleDisc (hwball k hk)
    obtain ⟨hk1, hk2⟩ := mem_criticalScaleWindow_heights hr hT₂ (hwin k hk)
    have hre0 : 0 < (w k).re := by linarith
    have hne1 : w k ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at h2
      linarith
    have hζ : riemannZeta (w k) = 0 := (xi_eq_zero_iff hre0 hne1).mp (hwzero k hk)
    rw [Finset.mem_filter, hZ]
    refine ⟨⟨?_, hζ⟩, h1⟩
    rw [Complex.mem_reProdIm, uIcc_of_le (by norm_num), uIcc_of_le (by linarith)]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hinj : Set.InjOn w (badCriticalScaleWindowDiscs r T₁ T₂ : Set ℕ) := by
    intro k hk l hl hkl
    obtain ⟨-, -, hk1, hk2⟩ := re_im_of_mem_criticalScaleDisc (hwball k hk)
    obtain ⟨-, -, hl1, hl2⟩ := re_im_of_mem_criticalScaleDisc (hwball l hl)
    rw [hkl] at hk1 hk2
    have f1 : (k : ℝ) - l < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have f2 : (l : ℝ) - k < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have g1 : (k : ℤ) - l < 1 := by exact_mod_cast f1
    have g2 : (l : ℤ) - k < 1 := by exact_mod_cast f2
    omega
  have hcard := Finset.card_le_card_of_injOn w hmaps hinj
  have hmult : ((Z.filter (fun w => 1 / 2 + r ≤ w.re)).card : ℝ) ≤
      ∑ w ∈ Z.filter (fun w => 1 / 2 + r ≤ w.re), ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun z hz => ?_
    have hzZ := (Finset.mem_filter.mp hz).1
    obtain ⟨hmem, hζ⟩ := (hZ z).mp hzZ
    have hz1 : z ≠ 1 := by
      intro h
      have him := (Complex.mem_reProdIm.mp hmem).2
      rw [h, Complex.one_im, uIcc_of_le (by linarith)] at him
      linarith [him.1]
    exact_mod_cast one_le_analyticOrderAt_riemannZeta_toNat hz1 hζ
  calc ((badCriticalScaleWindowDiscs r T₁ T₂).card : ℝ)
      ≤ ((Z.filter (fun w => 1 / 2 + r ≤ w.re)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := hmult

/-- The window holds at least `(T₂ − T₁)/(3r) − 2` discs. -/
theorem card_criticalScaleWindow_ge {r T₁ T₂ : ℝ} (hr : 0 < r) (hT₁ : 0 ≤ T₁)
    (hT : T₁ + 2 * r ≤ T₂) :
    (T₂ - T₁) / (3 * r) - 2 ≤ ((criticalScaleWindow r T₁ T₂).card : ℝ) := by
  unfold criticalScaleWindow
  have h3r : 0 < 3 * r := by positivity
  set k₁ : ℕ := ⌈(T₁ + r) / (3 * r)⌉₊ with hk₁
  set k₂ : ℕ := ⌊(T₂ - r) / (3 * r)⌋₊ with hk₂
  have h0 : 0 ≤ (T₁ + r) / (3 * r) := by positivity
  have hk₁lt : (k₁ : ℝ) < (T₁ + r) / (3 * r) + 1 := Nat.ceil_lt_add_one h0
  have hk₂gt : (T₂ - r) / (3 * r) - 1 < (k₂ : ℝ) := by
    have := Nat.lt_floor_add_one ((T₂ - r) / (3 * r))
    linarith
  rw [Nat.card_Icc]
  rcases le_or_gt k₁ (k₂ + 1) with h | h
  · rw [Nat.cast_sub h]
    push_cast
    have e : (T₂ - T₁) / (3 * r) - 2 ≤ ((T₂ - r) / (3 * r) - 1) + 1 - ((T₁ + r) / (3 * r) + 1) +
        1 / 3 := by
      rw [show ((T₂ - r) / (3 * r) - 1) + 1 - ((T₁ + r) / (3 * r) + 1) + 1 / 3 =
        (T₂ - T₁) / (3 * r) - 2 / (3 * r) * r + 1 / 3 - 1 by field_simp; ring]
      have : 2 / (3 * r) * r = 2 / 3 := by field_simp
      linarith
    linarith
  · have : (T₂ - T₁) / (3 * r) - 2 ≤ 0 := by
      have hk : (k₂ : ℝ) + 1 < k₁ := by exact_mod_cast h
      have : (T₂ - r) / (3 * r) - 1 + 1 < (T₁ + r) / (3 * r) + 1 := by linarith
      rw [show (T₂ - T₁) / (3 * r) - 2 = ((T₂ - r) / (3 * r) - 1 + 1) - ((T₁ + r) / (3 * r) + 1)
        + 2 / (3 * r) * r - 1 by field_simp; ring]
      have : 2 / (3 * r) * r = 2 / 3 := by field_simp
      linarith
    exact this.trans (Nat.cast_nonneg _)

/-- **Almost every critical-scale right disc has a contracting seam.** -/
theorem exists_criticalScale_badDisc_proportion_le {ε : ℝ} (hε : 0 < ε) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a → ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ((badCriticalScaleWindowDiscs (2 * a / Real.log U) T₁ T₂).card : ℝ) ≤
          ε * (criticalScaleWindow (2 * a / Real.log U) T₁ T₂).card := by
  obtain ⟨A, K, hA, hK, hdens⟩ := exists_selberg_nearLine_zeroDensity
  have hrate := tendsto_selbergNearLineRate A
  have hev : ∀ᶠ a in atTop, selbergNearLineRate A a ≤ Real.pi * ε / 3 :=
    hrate.eventually (ge_mem_nhds (by positivity))
  obtain ⟨a₁, ha₁⟩ := eventually_atTop.mp hev
  refine ⟨max a₁ 1, le_max_right _ _, fun a ha => ?_⟩
  have ha1 : 1 ≤ a := le_trans (le_max_right _ _) ha
  have hra : selbergNearLineRate A a ≤ Real.pi * ε / 3 := ha₁ a (le_trans (le_max_left _ _) ha)
  -- the logarithmic growth is eventually negligible against the window length
  have hlogsmall : ∀ᶠ U in atTop,
      (K * Real.log U + 2 * Real.pi * ε / 3) * 24 ≤ ε * U / 4 ∧ 16 * a ≤ Real.log U ∧
        100 ≤ U := by
    have h1 : Tendsto (fun U : ℝ => Real.log U / U) atTop (nhds 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa using this
    have h2 : ∀ᶠ U in atTop, Real.log U / U ≤ ε / (200 * (K + 1)) :=
      h1.eventually (ge_mem_nhds (by positivity))
    filter_upwards [h2, Real.tendsto_log_atTop.eventually_ge_atTop (16 * a),
      eventually_ge_atTop (max 100 (400 * Real.pi / 3 + 100))] with U hU hlog hU100
    have hU0 : 0 < U := by linarith [le_max_left 100 (400 * Real.pi / 3 + 100)]
    refine ⟨?_, hlog, le_trans (le_max_left _ _) hU100⟩
    rw [div_le_div_iff₀ hU0 (by positivity)] at hU
    have hUpi : 400 * Real.pi / 3 + 100 ≤ U := le_trans (le_max_right _ _) hU100
    have hlog0 : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
    nlinarith [Real.pi_pos]
  filter_upwards [hdens a ha1, hlogsmall] with U hU hsmall
  obtain ⟨hsm, hlogU, hU100⟩ := hsmall
  obtain ⟨T₁, hT₁, T₂, hT₂, hcount⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, ?_⟩
  have hL0 : 0 < Real.log U := by linarith
  set L : ℝ := Real.log U with hL
  set r : ℝ := 2 * a / L with hr
  have hr0 : 0 < r := by positivity
  have hr8 : r ≤ 1 / 8 := by
    rw [hr, div_le_iff₀ hL0]; linarith
  have hT₁0 : 0 < T₁ := by linarith [hT₁.1]
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  have hbad := card_badCriticalScaleWindowDiscs_le hr0 hr8 hT₁0 (by linarith [hT₂.1]) hZ
  have hc := hcount Z hZ
  have hfilter : Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re) =
      Z.filter (fun w => 1 / 2 + r ≤ w.re) := by
    refine Finset.filter_congr fun w _ => ?_
    rw [hr]
  rw [hfilter] at hc
  set S : ℝ := ∑ w ∈ Z.filter (fun w => 1 / 2 + r ≤ w.re),
    ((analyticOrderAt riemannZeta w).toNat : ℝ) with hS
  have hwin := card_criticalScaleWindow_ge hr0 hT₁0.le (by linarith [hT₁.2, hT₂.1])
  -- `S ≤ L/(2πa) ((T₂−T₁)/2 · rate + K L)` and the window holds `≥ (T₂−T₁) L/(6a) − 2` discs
  have ha0 : 0 < a := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  have hSb : S ≤ L / (2 * Real.pi * a) *
      ((T₂ - T₁) / 2 * selbergNearLineRate A a + K * L) := by
    rw [le_div_iff₀ (by positivity) |>.symm.le_iff_le] at *
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : 2 * Real.pi * (a / L * S) = S * (2 * Real.pi * a) / L := by field_simp
    rw [this, div_le_iff₀ hL0] at hc
    linarith
  have hlen : U / 5 ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have hdiv : (T₂ - T₁) / (3 * r) = (T₂ - T₁) * L / (6 * a) := by
    rw [hr]; field_simp; ring
  rw [hdiv] at hwin
  calc ((badCriticalScaleWindowDiscs r T₁ T₂).card : ℝ) ≤ S := hbad
    _ ≤ L / (2 * Real.pi * a) * ((T₂ - T₁) / 2 * selbergNearLineRate A a + K * L) := hSb
    _ ≤ ε * ((T₂ - T₁) * L / (6 * a) - 2) := by
        have hrate0 := selbergNearLineRate_nonneg hA.le a
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have h1 : (T₂ - T₁) / 2 * selbergNearLineRate A a ≤ (T₂ - T₁) / 2 * (Real.pi * ε / 3) :=
          mul_le_mul_of_nonneg_left hra (by linarith)
        have hLa : 16 * a ≤ L := hlogU
        have hK' : K * L * L + 2 * Real.pi * ε / 3 * L ≤ ε * (T₂ - T₁) / 12 * L := by
          have := hsm
          nlinarith
        have e : ε * ((T₂ - T₁) * L / (6 * a) - 2) * (2 * Real.pi * a) =
            ε * (T₂ - T₁) * L * Real.pi / 3 - 4 * Real.pi * ε * a := by
          field_simp; ring
        rw [e]
        have h4a : 4 * Real.pi * ε * a ≤ Real.pi * ε * L / 4 := by nlinarith
        nlinarith
    _ ≤ ε * (criticalScaleWindow r T₁ T₂).card := mul_le_mul_of_nonneg_left hwin hε.le

end RHTower
