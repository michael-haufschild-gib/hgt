import GaloisForLFunctions.ArithmeticCriticalityTheory.CurvedGaugeWindowPotential

/-!
# Weil positivity on `[−39/200, 39/200]` from a curved gauge

The flat (plateau) gauge proves `Ẑ ≥ 0` on every window whose centre potential is positive, which stops
at `R ≈ 0.15`: the flat gauge discards the regional jump energy of the window, the part of the
archimedean form responsible for Suzuki's limiting constant `μ₁`. A curved gauge keeps part of it. With
`q(y) = 1 − 15 y²` and the plateau `P` of radius `1/5`, the gauge `M = q P` (`quadraticWindowGauge`)
has, at a point `x` of the plateau,

    −𝒲M(x) ≥ q(x) [N(a) + N(b) − (3/4)(a + b) + (a² + b²)/12 − (γ + log π)]
              + 15 [G(a) + G(b) − (11/5) x²],          a = 1/5 − x, b = 1/5 + x,

`N(s) = −½ log(1 − e^{−2s})`, `G(s) = s²/4 + s³/12 − s⁴/64 ≤ ∫_0^s u² ω`
(`neg_poleFreeWeilOperator_quadraticWindowGauge_ge`): the regional term `15 G` is the curvature gain, the
`x`-linear part of the regional integral costs `−15 · (11/5) x²` (`∫ u ω ≤ ½ + u/4` across the window).
With `N(s) ≥ −½ log(2s) + s/2 − s²/12` the second-order terms cancel and the bracket becomes
`log(5/2) − 1/10 − (γ + log π) − ½ log(1 − 25x²)`.

The pole is the mass `2 ∫ M cosh ≥ 2 ∫_{−39/200}^{39/200} q` and the negative density `2cosh(t/2) − ω`
beyond the plastic threshold costs at most `6.5 (1/5 + |x| − 0.275)₊²` (`integral_kappa_mul_quadraticWindowGauge_le`).
A one-dimensional inequality (`quadraticGauge_window_inequality`: ten logarithmic anchors
`1 − 25y² = (3/4)^k`, a chord bound for the cost, concave quadratics on each piece) shows that the total
potential exceeds `q(x)/50`.

**Theorem** (`fullZeroForm_ge_of_support_le_curved`). Every real `F ∈ C²_c` vanishing outside
`[−39/200, 39/200]` satisfies `Ẑ(F) ≥ (1/50) ∫ F²`; hence `μ(A) ≥ 1/50` for every aperture
`A ≤ 39/200` (`one_div_fifty_le_ccmRestrictedWeilGroundEnergy`). The support reached is `1.86` times the
Markov window `21/200` and lies beyond the reach `≈ 0.1526` of every flat gauge.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The gauge -/

/-- The curvature profile `q(y) = 1 − 15 y²`. -/
def quadraticProfile (y : ℝ) : ℝ := 1 - 15 * y ^ 2

/-- The curved window gauge `M = q P`, `P` the plateau of radius `1/5` with collar `1/200`. -/
def quadraticWindowGauge (y : ℝ) : ℝ := curvedWindowGauge 15 (1 / 5) (1 / 200) y

theorem contDiff_quadraticProfile : ContDiff ℝ 2 quadraticProfile := contDiff_curvedProfile 15

theorem contDiff_quadraticWindowGauge : ContDiff ℝ 2 quadraticWindowGauge :=
  contDiff_curvedWindowGauge _ _ _

theorem hasCompactSupport_quadraticWindowGauge : HasCompactSupport quadraticWindowGauge :=
  hasCompactSupport_curvedWindowGauge _ _ (by norm_num)

theorem quadraticProfile_ge {y : ℝ} (hy : |y| ≤ 1 / 5) : 2 / 5 ≤ quadraticProfile y := by
  have := curvedProfile_ge_of_le (c := 15) (by norm_num) hy
  unfold curvedProfile at this
  unfold quadraticProfile
  linarith

theorem quadraticProfile_le (y : ℝ) : quadraticProfile y ≤ 1 := curvedProfile_le (by norm_num) y

theorem quadraticWindowGauge_eq_zero {y : ℝ} (hy : 1 / 5 ≤ |y|) : quadraticWindowGauge y = 0 :=
  curvedWindowGauge_eq_zero 15 (by norm_num) hy

theorem quadraticWindowGauge_eq {y : ℝ} (hy : |y| ≤ 39 / 200) :
    quadraticWindowGauge y = quadraticProfile y :=
  curvedWindowGauge_eq 15 (by norm_num) (by linarith)

theorem quadraticWindowGauge_nonneg (y : ℝ) : 0 ≤ quadraticWindowGauge y :=
  curvedWindowGauge_nonneg (by norm_num) (by norm_num) (by norm_num) y

theorem quadraticWindowGauge_le_profile {y : ℝ} (hy : |y| ≤ 1 / 5) :
    quadraticWindowGauge y ≤ quadraticProfile y :=
  curvedWindowGauge_le_profile (by norm_num) (by norm_num) hy

theorem quadraticWindowGauge_le_one (y : ℝ) : quadraticWindowGauge y ≤ 1 :=
  curvedWindowGauge_le_one (by norm_num) (by norm_num) (by norm_num) y

/-! ### The potential of the curved gauge -/

/-- **The potential of the curved gauge of radius `1/5`** at a plateau point. -/
theorem neg_poleFreeWeilOperator_quadraticWindowGauge_ge {x : ℝ} (hx : |x| ≤ 39 / 200) :
    quadraticProfile x *
        ((-(1 / 2) * Real.log (1 - Real.exp (-2 * (1 / 5 - x))) - 3 / 4 * (1 / 5 - x) +
            (1 / 5 - x) ^ 2 / 12) +
          (-(1 / 2) * Real.log (1 - Real.exp (-2 * (1 / 5 + x))) - 3 / 4 * (1 / 5 + x) +
            (1 / 5 + x) ^ 2 / 12) - 2 * archConstantReal) +
      15 * (sqMomentFloor (1 / 5 - x) + sqMomentFloor (1 / 5 + x) - 11 / 5 * x ^ 2) ≤
      -poleFreeWeilOperator quadraticWindowGauge x := by
  have h := neg_poleFreeWeilOperator_curvedWindowGauge_ge (c := 15) (R := 1 / 5) (δ := 1 / 200)
    (x := x) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith)
  rw [show 2 * (1 + 1 / 5 / 2) * x ^ 2 = 11 / 5 * x ^ 2 by ring] at h
  exact h

/-! ### The negative density past the plastic threshold -/

/-- The majorant `κ(t) = 6.5 (t − 0.275)₊` of the pole-minus-Lévy density. -/
def plasticExcessMajorant (t : ℝ) : ℝ := 6.5 * max (t - 0.275) 0

theorem continuous_plasticExcessMajorant : Continuous plasticExcessMajorant := by
  unfold plasticExcessMajorant
  fun_prop

theorem plasticExcessMajorant_nonneg (t : ℝ) : 0 ≤ plasticExcessMajorant t := by
  unfold plasticExcessMajorant
  have := le_max_right (t - 0.275) 0
  linarith

/-- `ω(t) − 2cosh(t/2) ≥ −κ(t)` on `(0, 2/5]`. -/
theorem neg_plasticExcessMajorant_le {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 2 / 5) :
    -plasticExcessMajorant t ≤ archLevyDensity t - 2 * Real.cosh (t / 2) := by
  unfold plasticExcessMajorant
  by_cases h : t ≤ 0.275
  · rw [max_eq_right (by linarith)]
    have := two_mul_cosh_le_archLevyDensity_of_le_plastic h0 (by linarith)
    linarith
  · rw [max_eq_left (by linarith)]
    have := two_mul_cosh_sub_archLevyDensity_le_linear (t := t) (by linarith) (by linarith)
    linarith

/-- **The cost of the negative density** at a point:
`∫_0^∞ κ(t)(M(x+t) + M(x−t)) dt ≤ 3.25 (max(1/5 + |x|, 0.275) − 0.275)²`. -/
theorem integral_kappa_mul_quadraticWindowGauge_le (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), plasticExcessMajorant t *
        (quadraticWindowGauge (x + t) + quadraticWindowGauge (x - t))) ≤
      13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2 := by
  set m := max (1 / 5 + |x|) 0.275 with hmdef
  have hm : 0.275 ≤ m := le_max_right _ _
  have hm' : 1 / 5 + |x| ≤ m := le_max_left _ _
  have hgi : Integrable ((Ioc (0.275 : ℝ) m).indicator fun t => 6.5 * (t - 0.275))
      (volume.restrict (Ioi 0)) :=
    (((continuous_const.mul (continuous_id.sub continuous_const)).integrableOn_Icc
      (a := 0.275) (b := m)).mono_set Ioc_subset_Icc_self |>.integrable_indicator
        measurableSet_Ioc).restrict
  have hpt : ∀ t ∈ Ioi (0 : ℝ), plasticExcessMajorant t *
      (quadraticWindowGauge (x + t) + quadraticWindowGauge (x - t)) ≤
        (Ioc (0.275 : ℝ) m).indicator (fun t => 6.5 * (t - 0.275)) t := by
    intro t ht
    have hκ := plasticExcessMajorant_nonneg t
    have hM1 := quadraticWindowGauge_nonneg (x + t)
    have hM2 := quadraticWindowGauge_nonneg (x - t)
    by_cases h1 : t ≤ 0.275
    · have : plasticExcessMajorant t = 0 := by
        unfold plasticExcessMajorant; rw [max_eq_right (by linarith)]; ring
      rw [this, zero_mul]
      exact Set.indicator_nonneg (fun t ht => by linarith [ht.1]) t
    · have hone : quadraticWindowGauge (x + t) + quadraticWindowGauge (x - t) ≤ 1 := by
        by_cases hp : |x + t| < 1 / 5
        · have : 1 / 5 ≤ |x - t| := by
            by_contra hq
            push Not at hq
            have := abs_sub_abs_le_abs_sub (x + t) (x - t)
            have h2 : |(x + t) - (x - t)| ≤ |x + t| + |x - t| := abs_sub _ _
            rw [show (x + t) - (x - t) = 2 * t by ring, abs_of_pos (by linarith : (0 : ℝ) < 2 * t)] at h2
            linarith
          rw [quadraticWindowGauge_eq_zero this, add_zero]
          exact quadraticWindowGauge_le_one _
        · rw [quadraticWindowGauge_eq_zero (not_lt.mp hp), zero_add]
          exact quadraticWindowGauge_le_one _
      by_cases h2 : t ≤ m
      · rw [Set.indicator_of_mem (show t ∈ Ioc (0.275 : ℝ) m from ⟨not_le.mp h1, h2⟩)]
        unfold plasticExcessMajorant
        rw [max_eq_left (by linarith)]
        have h65 : 0 ≤ 6.5 * (t - 0.275) := by linarith
        nlinarith
      · rw [Set.indicator_of_notMem (fun h => h2 h.2)]
        have e1 : quadraticWindowGauge (x + t) = 0 := quadraticWindowGauge_eq_zero (by
          have := abs_sub_abs_le_abs_sub t (-x)
          rw [abs_neg, sub_neg_eq_add, add_comm, abs_of_pos (ht : (0 : ℝ) < t)] at this
          linarith)
        have e2 : quadraticWindowGauge (x - t) = 0 := quadraticWindowGauge_eq_zero (by
          have := abs_sub_abs_le_abs_sub t x
          rw [abs_sub_comm, abs_of_pos (ht : (0 : ℝ) < t)] at this
          linarith)
        rw [e1, e2]
        simp
  have hval : (∫ t in Ioi (0 : ℝ), (Ioc (0.275 : ℝ) m).indicator (fun t => 6.5 * (t - 0.275)) t) =
      13 / 4 * (m - 0.275) ^ 2 := by
    rw [setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr fun t ht => mem_Ioi.mpr (by linarith [ht.1]),
      ← intervalIntegral.integral_of_le hm, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun t => t), integral_id]
    ring
  rw [← hval]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => mul_nonneg
    (plasticExcessMajorant_nonneg t) (add_nonneg (quadraticWindowGauge_nonneg _)
      (quadraticWindowGauge_nonneg _))) hgi ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpt)

/-- `κ I` is integrable on the half line. -/
theorem integrableOn_kappa_mul_gaugeJumpProfile {u : ℝ → ℝ} (hu : Continuous u) :
    IntegrableOn (fun t => plasticExcessMajorant t * gaugeJumpProfile quadraticWindowGauge u t)
      (Ioi 0) := by
  have hMB : ∀ x, quadraticWindowGauge x ≠ 0 → |x| ≤ 1 / 5 := fun x hx => by
    by_contra h
    exact hx (quadraticWindowGauge_eq_zero (not_le.mp h).le)
  have hM := contDiff_quadraticWindowGauge.continuous
  have hfull : Integrable (fun p : ℝ × ℝ =>
      plasticExcessMajorant p.1 * signedShiftJump quadraticWindowGauge u p.1 p.2)
      ((volume : Measure ℝ).prod volume) := by
    unfold signedShiftJump
    have hκ := continuous_plasticExcessMajorant
    refine integrable_prod_of_box (B := 2 * |(1 / 5 : ℝ)|) (by fun_prop) fun p hp => ?_
    have h1 : quadraticWindowGauge p.2 ≠ 0 := fun h => hp (by rw [h]; ring)
    have h2 : quadraticWindowGauge (p.2 + p.1) ≠ 0 := fun h => hp (by rw [h]; ring)
    have a1 := (hMB _ h1).trans (le_abs_self (1 / 5 : ℝ))
    have a2 := (hMB _ h2).trans (le_abs_self (1 / 5 : ℝ))
    have h3 : |p.1| ≤ |p.2 + p.1| + |p.2| := by
      have := abs_sub (p.2 + p.1) p.2
      rwa [add_sub_cancel_left] at this
    exact ⟨by linarith, by linarith [abs_nonneg (1 / 5 : ℝ)]⟩
  exact (hfull.integral_prod_left.congr (Eventually.of_forall fun t => by
    simp only [gaugeJumpProfile]
    rw [integral_const_mul])).integrableOn

/-! ### The pole mass of the curved gauge -/

/-- `∫ M(y) cosh((x−y)/2) dy ≥ ∫_{−39/200}^{39/200} q = 39/100 − 10 (39/200)³`. -/
theorem integral_quadraticWindowGauge_cosh_ge (x : ℝ) :
    39 / 100 - 10 * (39 / 200) ^ 3 ≤
      ∫ y, quadraticWindowGauge y * Real.cosh ((x - y) / 2) := by
  set r : ℝ := 39 / 200 with hrdef
  have hint : Integrable fun y => quadraticWindowGauge y * Real.cosh ((x - y) / 2) :=
    (contDiff_quadraticWindowGauge.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_quadraticWindowGauge.mul_right
  have hset : (∫ y in Icc (-r) r, quadraticWindowGauge y * Real.cosh ((x - y) / 2)) ≤
      ∫ y, quadraticWindowGauge y * Real.cosh ((x - y) / 2) :=
    setIntegral_le_integral hint (Eventually.of_forall fun y =>
      mul_nonneg (quadraticWindowGauge_nonneg y) (Real.cosh_pos _).le)
  have hq : IntegrableOn quadraticProfile (Icc (-r) r) :=
    contDiff_quadraticProfile.continuous.integrableOn_Icc
  have hlow : (∫ y in Icc (-r) r, quadraticProfile y) ≤
      ∫ y in Icc (-r) r, quadraticWindowGauge y * Real.cosh ((x - y) / 2) :=
    setIntegral_mono_on hq hint.integrableOn measurableSet_Icc fun y hy => by
      have hy' : -(39 / 200) ≤ y ∧ y ≤ 39 / 200 := hy
      rw [quadraticWindowGauge_eq (abs_le.mpr hy')]
      have h1 := Real.one_le_cosh ((x - y) / 2)
      have h0 := quadraticProfile_ge (y := y) (abs_le.mpr ⟨by linarith [hy'.1], by linarith [hy'.2]⟩)
      nlinarith
  have hval : (∫ y in Icc (-r) r, quadraticProfile y) = 39 / 100 - 10 * (39 / 200) ^ 3 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    unfold quadraticProfile
    rw [intervalIntegral.integral_sub (f := fun _ => (1 : ℝ)) (g := fun x : ℝ => 15 * x ^ 2)
      intervalIntegrable_const ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow]
    rw [hrdef]
    norm_num
  linarith

/-! ### The one-dimensional window inequality -/

/-- Tangent bound of the edge logarithm at an anchor `1 − s = c`: if `L ≤ −log c`, then
`−½ log(1 − s) ≥ L/2 + (s − (1 − c))/(2c)`. -/
theorem neg_half_log_one_sub_ge_anchor {s c L : ℝ} (hs : s < 1) (hc : 0 < c)
    (hL : L ≤ -Real.log c) : L / 2 + (s - (1 - c)) / (2 * c) ≤ -(1 / 2) * Real.log (1 - s) := by
  have h1 : 0 < 1 - s := by linarith
  have hsplit : Real.log (1 - s) = Real.log c + Real.log ((1 - s) / c) := by
    rw [← Real.log_mul hc.ne' (div_pos h1 hc).ne', mul_div_cancel₀ _ hc.ne']
  have hle := Real.log_le_sub_one_of_pos (div_pos h1 hc)
  have e : (s - (1 - c)) / (2 * c) = -(1 / 2) * ((1 - s) / c - 1) := by field_simp; ring
  rw [hsplit, e]
  nlinarith

/-- The anchors `c = (3/4)^k`: `−½ log(1 − s) ≥ 0.1438 k + (s − (1 − (3/4)^k))/(2(3/4)^k)`. -/
theorem neg_half_log_one_sub_ge_anchor_pow {s : ℝ} (hs : s < 1) (k : ℕ) :
    0.1438 * k + (s - (1 - (3 / 4 : ℝ) ^ k)) / (2 * (3 / 4) ^ k) ≤
      -(1 / 2) * Real.log (1 - s) := by
  have hL : 0.2876 * k ≤ -Real.log ((3 / 4 : ℝ) ^ k) := by
    rw [Real.log_pow, show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
    have := log_four_thirds_gt
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have h := neg_half_log_one_sub_ge_anchor hs (by positivity) hL
  linarith

/-- **The window inequality.** For `0 ≤ y ≤ 39/200` and `D ≥ −0.9058289`, with `q = 1 − 15y²`:
`q/50 ≤ q (D − ½ log(1 − 25y²)) + 0.31925 − 24.1125 y² − 0.46875 y⁴ + 0.6317025 −
6.5 (max(1/5 + y, 0.275) − 0.275)²`. -/
theorem quadraticGauge_window_inequality {y D : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 39 / 200)
    (hD : -0.9058289 ≤ D) :
    1 / 50 * (1 - 15 * y ^ 2) ≤
      (1 - 15 * y ^ 2) * (D + -(1 / 2) * Real.log (1 - 25 * y ^ 2)) +
        (0.31925 - 24.1125 * y ^ 2 - 0.46875 * y ^ 4) + 0.6317025 -
          6.5 * (max (1 / 5 + y) 0.275 - 0.275) ^ 2 := by
  have hy2 : y ^ 2 ≤ (39 / 200) ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have hq : 0 ≤ 1 - 15 * y ^ 2 := by nlinarith
  have h25 : 25 * y ^ 2 < 1 := by nlinarith
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have anc := fun k : ℕ => mul_le_mul_of_nonneg_left
    (neg_half_log_one_sub_ge_anchor_pow (s := 25 * y ^ 2) h25 k) hq
  set ℓ := -(1 / 2) * Real.log (1 - 25 * y ^ 2) with hℓ
  rcases le_or_gt y (3 / 40) with h1 | h1
  · -- no cost below `3/40`
    rw [max_eq_right (by linarith)]
    have h := anc 0
    norm_num at h
    nlinarith [mul_nonneg (sq_nonneg y) (by nlinarith : (0 : ℝ) ≤ (3 / 40) ^ 2 - y ^ 2)]
  rw [max_eq_left (by linarith)]
  -- the pieces `[t_k, t_{k+1}]` with anchor `k`
  have piece : ∀ (k : ℕ) (lo hi : ℝ), lo ≤ y → y ≤ hi → 0 ≤ lo →
      (0 ≤ (y - lo) * (hi - y) ∧ 0 ≤ (y ^ 2 - lo ^ 2) * (hi ^ 2 - y ^ 2)) := by
    intro k lo hi hl hh h0
    exact ⟨mul_nonneg (by linarith) (by linarith),
      mul_nonneg (by nlinarith) (by nlinarith)⟩
  rcases le_or_gt y (1 / 10) with h2 | h2
  · obtain ⟨p1, p2⟩ := piece 0 (3 / 40) (1 / 10) h1.le h2 (by norm_num)
    have h := anc 0; norm_num at h; nlinarith
  rcases le_or_gt y 0.1322 with h3 | h3
  · obtain ⟨p1, p2⟩ := piece 1 (1 / 10) 0.1322 h2.le h3 (by norm_num)
    have h := anc 1; norm_num at h; nlinarith
  rcases le_or_gt y 0.152 with h4 | h4
  · obtain ⟨p1, p2⟩ := piece 2 0.1322 0.152 h3.le h4 (by norm_num)
    have h := anc 2; norm_num at h; nlinarith
  rcases le_or_gt y 0.1653 with h5 | h5
  · obtain ⟨p1, p2⟩ := piece 3 0.152 0.1653 h4.le h5 (by norm_num)
    have h := anc 3; norm_num at h; nlinarith
  rcases le_or_gt y 0.1746 with h6 | h6
  · obtain ⟨p1, p2⟩ := piece 4 0.1653 0.1746 h5.le h6 (by norm_num)
    have h := anc 4; norm_num at h; nlinarith
  rcases le_or_gt y 0.1813 with h7 | h7
  · obtain ⟨p1, p2⟩ := piece 5 0.1746 0.1813 h6.le h7 (by norm_num)
    have h := anc 5; norm_num at h; nlinarith
  rcases le_or_gt y 0.1861 with h8 | h8
  · obtain ⟨p1, p2⟩ := piece 6 0.1813 0.1861 h7.le h8 (by norm_num)
    have h := anc 6; norm_num at h; nlinarith
  rcases le_or_gt y 0.1897 with h9 | h9
  · obtain ⟨p1, p2⟩ := piece 7 0.1861 0.1897 h8.le h9 (by norm_num)
    have h := anc 7; norm_num at h; nlinarith
  rcases le_or_gt y 0.1923 with h10 | h10
  · obtain ⟨p1, p2⟩ := piece 8 0.1897 0.1923 h9.le h10 (by norm_num)
    have h := anc 8; norm_num at h; nlinarith
  · obtain ⟨p1, p2⟩ := piece 9 0.1923 (39 / 200) h10.le hy (by norm_num)
    have h := anc 9; norm_num at h; nlinarith

/-! ### Coercive positivity on `[−39/200, 39/200]` -/

/-- The killing bracket of the curved gauge is at least
`log(5/2) − 1/10 − (γ + log π) − ½ log(1 − 25x²)`: the second-order terms cancel. -/
theorem quadraticGauge_bracket_ge {x : ℝ} (hx : |x| ≤ 39 / 200) :
    Real.log (5 / 2) - 1 / 10 - 2 * archConstantReal + -(1 / 2) * Real.log (1 - 25 * x ^ 2) ≤
      (-(1 / 2) * Real.log (1 - Real.exp (-2 * (1 / 5 - x))) - 3 / 4 * (1 / 5 - x) +
          (1 / 5 - x) ^ 2 / 12) +
        (-(1 / 2) * Real.log (1 - Real.exp (-2 * (1 / 5 + x))) - 3 / 4 * (1 / 5 + x) +
          (1 / 5 + x) ^ 2 / 12) - 2 * archConstantReal := by
  have hx' := abs_le.mp hx
  have ha : 0 < 1 / 5 - x := by linarith
  have hb : 0 < 1 / 5 + x := by linarith
  have hNa := neg_half_log_one_sub_exp_ge_sharp ha (by linarith)
  have hNb := neg_half_log_one_sub_exp_ge_sharp hb (by linarith)
  have h25 : 0 < 1 - 25 * x ^ 2 := by nlinarith
  have hlog : Real.log (2 * (1 / 5 - x)) + Real.log (2 * (1 / 5 + x)) =
      -2 * Real.log (5 / 2) + Real.log (1 - 25 * x ^ 2) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      show 2 * (1 / 5 - x) * (2 * (1 / 5 + x)) = ((5 / 2 : ℝ)⁻¹) ^ 2 * (1 - 25 * x ^ 2) by ring,
      Real.log_mul (by positivity) h25.ne', Real.log_pow, Real.log_inv]
    push_cast
    ring
  linarith

/-- **Weil positivity on `[−39/200, 39/200]` from the curved gauge.** Every real `F ∈ C²_c` vanishing
outside `[−39/200, 39/200]` satisfies `Ẑ(F) ≥ (1/50) ∫ F²`. -/
theorem fullZeroForm_ge_of_support_le_curved {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hsupp : ∀ x, 39 / 200 < |x| → F x = 0) :
    1 / 50 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set M := quadraticWindowGauge with hMdef
  set u : ℝ → ℝ := fun x => F x * (quadraticProfile x)⁻¹ with hudef
  have hMd : ContDiff ℝ 2 M := contDiff_quadraticWindowGauge
  have hMcs : HasCompactSupport M := hasCompactSupport_quadraticWindowGauge
  have hnn : ∀ y, 0 ≤ M y := quadraticWindowGauge_nonneg
  have hle : ∀ y, M y ≤ 1 := quadraticWindowGauge_le_one
  have hzero : ∀ y, 1 / 5 ≤ |y| → M y = 0 := fun y hy => quadraticWindowGauge_eq_zero hy
  have hMB : ∀ x, M x ≠ 0 → |x| ≤ 1 / 5 := fun x hx => by
    by_contra h
    exact hx (hzero x (not_le.mp h).le)
  have hlog2 : 2 * (1 / 5 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; norm_num; linarith
  -- the profile
  have hu : ContDiff ℝ 2 u := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : |y| < 1 / 5
    · exact hF.contDiffAt.mul (contDiff_quadraticProfile.contDiffAt.inv
        (by linarith [quadraticProfile_ge hy.le] : quadraticProfile y ≠ 0) |>.congr_of_eventuallyEq
          (Eventually.of_forall fun _ => rfl))
    · have hopen : IsOpen {z : ℝ | 39 / 200 < |z|} := isOpen_lt continuous_const continuous_abs
      have hev : u =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds (show 39 / 200 < |y| by linarith [not_lt.mp hy])] with z hz
        simp [hudef, hsupp z hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have huc : HasCompactSupport u := hFc.mul_right
  have hFu : (fun x => M x * u x) = F := funext fun x => by
    by_cases hx : |x| ≤ 39 / 200
    · have hq := quadraticProfile_ge (y := x) (by linarith)
      simp only [hudef, hMdef]
      rw [quadraticWindowGauge_eq hx]
      field_simp
    · simp only [hudef, hsupp x (not_le.mp hx), zero_mul, mul_zero]
  -- the representation
  have hrep := fullZeroForm_mul_eq_gauge_window hu huc hMd hMcs hle hnn hzero hlog2
  rw [hFu] at hrep
  -- the jump part
  obtain ⟨Ku, -, hKu⟩ := exists_lipschitz_bound_of_compactSupport (hu.of_le (by norm_num)) huc
  have huL : ∀ a b, |u a - u b| ≤ Ku * |a - b| := fun a b => hKu b a
  have hωI := integrableOn_archLevy_mul_gaugeJumpProfile hle hnn hzero (by norm_num) (by norm_num)
    hu.continuous hMd.continuous hMcs huL
  have hcI : Integrable fun t => Real.cosh (t / 2) * gaugeJumpProfile M u t :=
    (integrable_gaugeJump_kernel hu.continuous hMd.continuous hMB).integral_prod_left.congr
      (Eventually.of_forall fun t => by
        simp only [gaugeJumpProfile]
        rw [integral_const_mul])
  have hκI : IntegrableOn (fun t => plasticExcessMajorant t * gaugeJumpProfile M u t) (Ioi 0) :=
    integrableOn_kappa_mul_gaugeJumpProfile hu.continuous
  have hneg : IntegrableOn (fun t => -(plasticExcessMajorant t * gaugeJumpProfile M u t)) (Ioi 0) :=
    hκI.neg
  have hjump : -(∫ t in Ioi (0 : ℝ), plasticExcessMajorant t * gaugeJumpProfile M u t) ≤
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M u t) -
        2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t := by
    have hrhs : IntegrableOn (fun t => archLevyDensity t * gaugeJumpProfile M u t -
        2 * (Real.cosh (t / 2) * gaugeJumpProfile M u t)) (Ioi 0) :=
      hωI.sub (hcI.integrableOn.const_mul 2)
    have hm := setIntegral_mono_on hneg hrhs measurableSet_Ioi fun t ht => by
      have ht0 : (0 : ℝ) < t := ht
      have hI0 : 0 ≤ gaugeJumpProfile M u t := integral_nonneg fun x => by
        unfold signedShiftJump
        exact mul_nonneg (mul_nonneg (hnn _) (hnn _)) (sq_nonneg _)
      by_cases h2 : t ≤ 2 / 5
      · have hk := neg_plasticExcessMajorant_le ht0 h2
        nlinarith [mul_le_mul_of_nonneg_right hk hI0]
      · rw [gaugeJumpProfile_eq_zero_of_ge hzero (by linarith)]
        simp
    rw [integral_neg, integral_sub hωI (hcI.integrableOn.const_mul 2), integral_const_mul] at hm
    exact hm
  have habs := integral_mul_gaugeJumpProfile_le hu.continuous hMd.continuous hMB hnn
    continuous_plasticExcessMajorant plasticExcessMajorant_nonneg
  -- the potential integrands
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hML : ∀ a b, |M a - M b| ≤ KM * |a - b| := fun a b => hKM b a
  have hdec8 : ∀ y, |M y| ≤ Real.exp (8 * (1 / 5)) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < 1 / 5
    · rw [abs_of_nonneg (hnn y), ← Real.exp_add]
      exact (hle y).trans (Real.one_le_exp (by nlinarith))
    · rw [hzero y (not_lt.mp hy), abs_zero]
      positivity
  have hW : Continuous fun x => -poleFreeWeilOperator M x :=
    (continuous_poleFreeWeilOperator hMd.continuous hML hdec8).neg
  have hG : Continuous fun x => ∫ y, M y * Real.cosh ((x - y) / 2) := by
    have e := funext (integral_gauge_cosh_eq hMd.continuous hMcs)
    rw [e]
    fun_prop
  have hcost : Continuous fun x : ℝ => 13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2 := by
    fun_prop
  have hu2M : Continuous fun x => u x ^ 2 * M x := (hu.continuous.pow 2).mul hMd.continuous
  have hu2Mc : HasCompactSupport fun x => u x ^ 2 * M x := (hasCompactSupport_sq huc).mul_right
  have i1 : Integrable fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x :=
    (hu2M.mul hW).integrable_of_hasCompactSupport hu2Mc.mul_right
  have i2 : Integrable fun x => u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2) :=
    (hu2M.mul hG).integrable_of_hasCompactSupport hu2Mc.mul_right
  have i3 : Integrable fun x => u x ^ 2 * M x * (13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2) :=
    (hu2M.mul hcost).integrable_of_hasCompactSupport hu2Mc.mul_right
  -- the cost of the negative density
  have hc3 : (∫ x, u x ^ 2 * M x * ∫ t in Ioi (0 : ℝ), plasticExcessMajorant t * (M (x + t) + M (x - t))) ≤
      ∫ x, u x ^ 2 * M x * (13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => mul_nonneg
      (mul_nonneg (sq_nonneg _) (hnn x)) (setIntegral_nonneg measurableSet_Ioi fun t _ =>
        mul_nonneg (plasticExcessMajorant_nonneg t) (add_nonneg (hnn _) (hnn _)))) i3
      (Eventually.of_forall fun x => mul_le_mul_of_nonneg_left
        (integral_kappa_mul_quadraticWindowGauge_le x) (mul_nonneg (sq_nonneg _) (hnn x)))
  -- the pointwise potential
  have hD : -0.9058289 ≤ Real.log (5 / 2) - 1 / 10 - 2 * archConstantReal := by
    have h1 := log_five_halves_gt
    have h2 := two_mul_archConstantReal_lt_sharp
    linarith
  have hpt : ∀ x, 1 / 50 * F x ^ 2 ≤ u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * (∫ y, M y * Real.cosh ((x - y) / 2)) -
        2 * (13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2)) := by
    intro x
    by_cases hx : |x| ≤ 39 / 200
    · have hMx : M x = quadraticProfile x := quadraticWindowGauge_eq hx
      have hq := quadraticProfile_ge (y := x) (by linarith)
      have hFx : F x = M x * u x := (congrFun hFu x).symm
      have hWx : quadraticProfile x *
            ((-(1 / 2) * Real.log (1 - Real.exp (-2 * (1 / 5 - x))) - 3 / 4 * (1 / 5 - x) +
                (1 / 5 - x) ^ 2 / 12) +
              (-(1 / 2) * Real.log (1 - Real.exp (-2 * (1 / 5 + x))) - 3 / 4 * (1 / 5 + x) +
                (1 / 5 + x) ^ 2 / 12) - 2 * archConstantReal) +
          15 * (sqMomentFloor (1 / 5 - x) + sqMomentFloor (1 / 5 + x) - 11 / 5 * x ^ 2) ≤
          -poleFreeWeilOperator M x := neg_poleFreeWeilOperator_quadraticWindowGauge_ge hx
      have hbr := quadraticGauge_bracket_ge hx
      have hreg : 15 * (sqMomentFloor (1 / 5 - x) + sqMomentFloor (1 / 5 + x) - 11 / 5 * x ^ 2) =
          0.31925 - 24.1125 * x ^ 2 - 0.46875 * x ^ 4 := by
        unfold sqMomentFloor; ring
      have hGx : 39 / 100 - 10 * (39 / 200) ^ 3 ≤ ∫ y, M y * Real.cosh ((x - y) / 2) :=
        integral_quadraticWindowGauge_cosh_ge x
      have h1D := quadraticGauge_window_inequality (abs_nonneg x) hx hD
      have h4 : |x| ^ 4 = x ^ 4 := by
        rw [show |x| ^ 4 = (|x| ^ 2) ^ 2 by ring, sq_abs]; ring
      rw [h4, sq_abs] at h1D
      have hpot : 1 / 50 * quadraticProfile x ≤ -poleFreeWeilOperator M x +
          2 * (∫ y, M y * Real.cosh ((x - y) / 2)) -
            2 * (13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2) := by
        have hqbr := mul_le_mul_of_nonneg_left hbr (by linarith : (0 : ℝ) ≤ quadraticProfile x)
        unfold quadraticProfile at hqbr hq hWx ⊢
        linarith [hqbr, hWx, hreg, hGx, h1D]
      rw [hFx, hMx]
      have hu2 : 0 ≤ u x ^ 2 * quadraticProfile x := mul_nonneg (sq_nonneg _) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hpot hu2]
    · have hF0 : F x = 0 := hsupp x (not_le.mp hx)
      have hu0 : u x = 0 := by simp [hudef, hF0]
      rw [hF0, hu0]
      simp
  -- assemble
  have hF2 : Integrable fun x => 1 / 50 * F x ^ 2 :=
    ((hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)).const_mul _
  have hsum : Integrable fun x => u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * (∫ y, M y * Real.cosh ((x - y) / 2)) -
        2 * (13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2)) := by
    refine ((i1.add (i2.const_mul 2)).sub (i3.const_mul 2)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hint := integral_mono hF2 hsum hpt
  have hsplit : (∫ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * (∫ y, M y * Real.cosh ((x - y) / 2)) -
        2 * (13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2))) =
      (∫ x, u x ^ 2 * M x * -poleFreeWeilOperator M x) +
        2 * (∫ x, u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2)) -
          2 * ∫ x, u x ^ 2 * M x * (13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2) := by
    have e : ∀ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
        2 * (∫ y, M y * Real.cosh ((x - y) / 2)) -
          2 * (13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2)) =
        (u x ^ 2 * M x * -poleFreeWeilOperator M x +
          2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2))) -
          2 * (u x ^ 2 * M x * (13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2)) := fun x => by ring
    rw [integral_congr_ae (Eventually.of_forall e),
      integral_sub (f := fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x +
          2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2)))
        (g := fun x => 2 * (u x ^ 2 * M x * (13 / 4 * (max (1 / 5 + |x|) 0.275 - 0.275) ^ 2)))
        (i1.add (i2.const_mul 2)) (i3.const_mul 2),
      integral_add (f := fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x)
        (g := fun x => 2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2))) i1 (i2.const_mul 2),
      integral_const_mul, integral_const_mul]
  rw [integral_const_mul] at hint
  rw [hrep]
  linarith [hjump, habs, hc3, hint, hsplit]

/-! ### Complex tests and the restricted Weil ground energy -/

/-- **Coercive zeta positivity for complex tests on `[−39/200, 39/200]`.** -/
theorem zetaZeroConfig_re_W_ge_of_support_le_curved {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-(39 / 200)) (39 / 200)) :
    1 / 50 * ∫ x, ‖g x‖ ^ 2 ≤ (zetaZeroConfig.W g g).re := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hzero : ∀ x, 39 / 200 < |x| → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hgs h
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hre : ContDiff ℝ 2 fun u => (g u).re := Complex.reCLM.contDiff.comp hg
  have him : ContDiff ℝ 2 fun u => (g u).im := Complex.imCLM.contDiff.comp hg
  have hrec : HasCompactSupport fun u => (g u).re := hgc.comp_left Complex.zero_re
  have himc : HasCompactSupport fun u => (g u).im := hgc.comp_left Complex.zero_im
  have h1 := fullZeroForm_ge_of_support_le_curved hre hrec fun x hx => by simp [hzero x hx]
  have h2 := fullZeroForm_ge_of_support_le_curved him himc fun x hx => by simp [hzero x hx]
  have hsplit := GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im
    hg hgc
  have i1 : Integrable fun x => (g x).re ^ 2 :=
    (hre.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hrec)
  have i2 : Integrable fun x => (g x).im ^ 2 :=
    (him.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq himc)
  have hnorm : (∫ x, ‖g x‖ ^ 2) = (∫ x, (g x).re ^ 2) + ∫ x, (g x).im ^ 2 := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hsplit, hnorm]
  linarith

/-- **The curved-gauge floor**: `μ(A) ≥ 1/50` for every aperture `A ≤ 39/200`. -/
theorem one_div_fifty_le_ccmRestrictedWeilGroundEnergy {A : SuzukiPositiveAperture}
    (hA : A.1 ≤ 39 / 200) : 1 / 50 ≤ ccmRestrictedWeilGroundEnergy A := by
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  refine (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).2 ?_
  rintro r ⟨u, hu, rfl⟩
  have hnorm : ‖suzukiWeilIntervalFormEmbedding A u.toCCMFormVector‖ =
      ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ := by
    change ‖suzukiPhysicalToApertureCLM A (ccmArchimedeanFormToAperture A u.toCCMFormVector)‖ = _
    exact (suzukiApertureL2Equiv A).symm.norm_map _
  have hmass : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, ‖u x‖ ^ 2 := by
    unfold suzukiWeilIntervalFormMass
    rw [hnorm, norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector]
  have hpos : 0 < suzukiWeilIntervalFormMass A u.toCCMFormVector :=
    pow_pos (norm_pos_iff.mpr hu) 2
  unfold suzukiWeilIntervalFormRayleigh
  rw [le_div_iff₀ hpos, ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil, hmass]
  have hsupp : tsupport (u : ℝ → ℂ) ⊆ Icc (-(39 / 200)) (39 / 200) :=
    u.tsupport_subset.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact zetaZeroConfig_re_W_ge_of_support_le_curved
    (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hsupp

/-- **Contact apertures exceed `39/200`.** -/
theorem lt_of_ccmRestrictedWeilGroundEnergy_nonpos_curved {A : SuzukiPositiveAperture}
    (h : ccmRestrictedWeilGroundEnergy A ≤ 0) : 39 / 200 < A.1 := by
  by_contra hA
  have := one_div_fifty_le_ccmRestrictedWeilGroundEnergy (not_lt.mp hA)
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
