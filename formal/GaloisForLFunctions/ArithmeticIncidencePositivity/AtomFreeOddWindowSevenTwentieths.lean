import GaloisForLFunctions.ArithmeticIncidencePositivity.FirstPrimeMicroFold

/-!
# Odd-sector Weil positivity on `[−7/20, 7/20]`: the first prime window without a strip charge

The micro-fold (`FirstPrimeMicroFold`) pays the whole prime term `2Λ(2)/√2 ∫ F(x) F(x + log 2)` out of
the archimedean surplus of the pairs inside the edge strip `S = [log 2 − r, r]`, for every window
`r ≤ 2/5`. What remains is the ground-state potential `U_h^{off}` of the pairs off `S × S`; on `S` it
differs from the full potential `U_h` by the pairs inside `S`, whose weight
`h(x)(U_h − U_h^{off})(x) = ∫_S k(x, y)(h(x) − h(y)) dy` is at most `L |S| (½ + |S|/4)` since
`k(x, y)|x − y| ≤ ½ + |x − y|/4` (`mul_surplusPotential_le_off_add`). The strip charge per unit of gauge
thus drops from `Λ(2)/√2 ≈ 0.49` to `≈ 0.0023/h`.

With the plateau of radius `R = 701/2000` and the quartic gauge

    h(y) = 1/500 + (3/5) y − y² − (3/10) y³ − (49/20) y⁴,

the numerator of the potential (killing, quartic surplus, plateau potential, minus `397/20000`)
is nonnegative on `(0, 7/20]` and exceeds `0.0023` on `[0.343, 0.35] ⊇ S`
(`atomFreeNumerator_nonneg`, `atomFreeNumerator_strip`), by tangent lines at 7-smooth anchors.

**Theorem** (`fullZeroForm_ge_of_odd_support_le_sevenTwentieths`). Every odd `F ∈ C²_c` vanishing
outside `[−7/20, 7/20]` satisfies `Ẑ(F) ≥ (1/200) ∫ F²`. Equivalently, `J_M(u) + V_μ(u) ≥ 0` for every
even profile `u` with `M u` supported in `[−7/20, 7/20]`, in every odd gauge `M`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The loss of the strip pairs -/

/-- **The pairs inside the strip cost little.** For `x ∈ [p, r]` the potential with the pairs of
`[p, r]` removed loses at most `L (r − p)(½ + (r − p)/4)` per unit of gauge:
`k(x, y)(h(x) − h(y)) ≤ ω(|x − y|) L |x − y| ≤ L(½ + |x − y|/4)`. -/
theorem mul_surplusPotential_le_off_add {h : ℝ → ℝ} {p r x a₀ L : ℝ} (hp : 0 < p) (hpx : p ≤ x)
    (hxr : x ≤ r) (hr1 : r ≤ 1 / 2) (hh : Continuous h) (ha₀ : 0 < a₀) (hhx : a₀ ≤ h x)
    (hL0 : 0 ≤ L) (hhL : ∀ y, 0 < y → y ≤ r → |h x - h y| ≤ L * |x - y|) :
    h x * surplusPotential h r x ≤
      h x * surplusPotentialOff h p r x + L * (r - p) * (1 / 2 + (r - p) / 4) := by
  have hx0 : 0 < x := lt_of_lt_of_le hp hpx
  have hhx0 : 0 < h x := lt_of_lt_of_le ha₀ hhx
  have hint : IntegrableOn (fun y => surplusKernel x y * (1 - h y / h x)) (Ioc 0 r) := by
    refine Measure.integrableOn_of_bounded (M := 3 / 2 * |L| / a₀) (by simp)
      ((measurable_surplusKernel.comp (measurable_const.prodMk measurable_id)).mul
        (measurable_const.sub (hh.measurable.div measurable_const))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs]
    exact abs_surplusKernel_mul_le hx0 hy.1 (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2])
      ha₀ hhx (hhL y hy.1 hy.2)
  unfold surplusPotentialOff surplusPotential
  rw [if_neg (not_lt.mpr hpx)]
  have hsplit : Ioc 0 r = Ioo 0 p ∪ Icc p r := by
    ext y; simp only [mem_Ioc, mem_Ioo, mem_Icc, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hy : y < p
      · exact Or.inl ⟨h1, hy⟩
      · exact Or.inr ⟨not_lt.mp hy, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, h2⟩
  rw [hsplit, setIntegral_union (Set.disjoint_left.mpr fun y h1 h2 => by linarith [h1.2, h2.1])
    measurableSet_Icc (hint.mono_set (by rw [hsplit]; exact subset_union_left))
    (hint.mono_set (by rw [hsplit]; exact subset_union_right)), mul_add]
  have hpt : ∀ y ∈ Icc p r, h x * (surplusKernel x y * (1 - h y / h x)) ≤
      L * (1 / 2 + (r - p) / 4) := by
    intro y hy
    by_cases hxy : x = y
    · rw [← hxy, div_self hhx0.ne', sub_self, mul_zero, mul_zero]
      exact mul_nonneg hL0 (by linarith [hy.1, hy.2])
    have hy0 : 0 < y := lt_of_lt_of_le hp hy.1
    have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hdr : |x - y| ≤ r - p := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    have hk0 := surplusKernel_nonneg hx0 hy0 hxy
    have hk1 := (surplusKernel_le hx0 hy0).trans (archLevyDensity_le_inv hd)
    have e : h x * (surplusKernel x y * (1 - h y / h x)) = surplusKernel x y * (h x - h y) := by
      field_simp
    rw [e]
    have h1 : surplusKernel x y * (h x - h y) ≤ surplusKernel x y * (L * |x - y|) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hhL y hy0 hy.2)) hk0
    have h2 : surplusKernel x y * (L * |x - y|) ≤ (1 / (2 * |x - y|) + 1 / 4) * (L * |x - y|) :=
      mul_le_mul_of_nonneg_right hk1 (by positivity)
    have h3 : (1 / (2 * |x - y|) + 1 / 4) * (L * |x - y|) = L * (1 / 2 + |x - y| / 4) := by
      field_simp
    have h4 : L * (1 / 2 + |x - y| / 4) ≤ L * (1 / 2 + (r - p) / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hL0
    linarith
  have hmono := setIntegral_mono_on ((hint.mono_set (by rw [hsplit]; exact subset_union_right)).const_mul
    (h x)) (integrableOn_const (by simp)) measurableSet_Icc hpt
  rw [MeasureTheory.integral_const_mul, setIntegral_const, Real.volume_real_Icc_of_le (by linarith),
    smul_eq_mul] at hmono
  linarith

/-! ### The gauge and the numerator -/

theorem atomFreeGauge_ge {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 7 / 20) :
    1 / 500 ≤ quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x := by
  unfold quarticGauge
  have h : 0 ≤ 3 / 5 - x - 3 / 10 * x ^ 2 - 49 / 20 * x ^ 3 := by
    nlinarith [pow_le_pow_left₀ hx0 hxr 3]
  nlinarith [mul_nonneg hx0 h]

theorem atomFreeGauge_divDiff_le {u v : ℝ} (hu0 : 0 ≤ u) (hur : u ≤ 7 / 20) (hv0 : 0 ≤ v)
    (hvr : v ≤ 7 / 20) :
    |3 / 5 + -1 * (u + v) + -3 / 10 * (u ^ 2 + u * v + v ^ 2) +
      -49 / 20 * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3)| ≤ 16 / 25 := by
  have h1 := mul_nonneg hu0 hv0
  have h2 : u ^ 3 ≤ (7 / 20) ^ 3 := pow_le_pow_left₀ hu0 hur 3
  have h3 : v ^ 3 ≤ (7 / 20) ^ 3 := pow_le_pow_left₀ hv0 hvr 3
  have h4 : u ^ 2 * v ≤ (7 / 20) ^ 3 := by
    nlinarith [mul_le_mul (pow_le_pow_left₀ hu0 hur 2) hvr hv0 (by positivity)]
  have h5 : u * v ^ 2 ≤ (7 / 20) ^ 3 := by
    nlinarith [mul_le_mul hur (pow_le_pow_left₀ hv0 hvr 2) (by positivity) (by norm_num)]
  have h6 : 0 ≤ u ^ 2 * v := by positivity
  have h7 : 0 ≤ u * v ^ 2 := by positivity
  have h8 : 0 ≤ u ^ 3 := by positivity
  have h9 : 0 ≤ v ^ 3 := by positivity
  rw [abs_le]; constructor <;> nlinarith

/-- The polynomial part of the principal surplus of the gauge. -/
def atomFreePoly (x : ℝ) : ℝ :=
  3 / 5 * x + -1 * (3 / 2 * x ^ 2 - 7 / 20 * x) +
    -3 / 10 * (11 / 6 * x ^ 3 - (7 / 20) ^ 2 * x / 2) +
    -49 / 20 * (25 / 12 * x ^ 4 - 7 / 20 * x ^ 3 - (7 / 20) ^ 3 * x / 3)

/-- The numerator of the potential on `[−7/20, 7/20]` (`κ` stands for `log 2 + γ + log π`). -/
def atomFreeNumerator (κ x : ℝ) : ℝ :=
  (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 7 / 20) - Real.log x) +
    quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
      (-(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) - κ - 1 / 4000 -
        (x + 7 / 20) ^ 2 / 48 - 5 * (x + 7 / 20) ^ 3 / 192 - 397 / 20000) +
    atomFreePoly x - 16 / 25 * surplusRemainder (7 / 20) x

/-- **Tangent form of the numerator** on `[p, q] ⊆ [7/100, 7/20]`. -/
theorem atomFreeNumerator_ge_tangent {κ x p q v a b Lv La Lb : ℝ} (hp : 7 / 100 ≤ p)
    (hpx : p ≤ x) (hxq : x ≤ q) (hq : q ≤ 7 / 20) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b)
    (hLv : Real.log v ≤ Lv) (hLa : Real.log a ≤ La) (hLb : Real.log b ≤ Lb)
    (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + 1 / v - 1) +
        7 / 20 / v * (1 / (500 * q) - x - 49 / 20 * x ^ 3) +
        quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
          (-(1 / 2) * (La + (701 / 2000 - x) / a - 1) - 1 / 2 * (Lb + (701 / 2000 + x) / b - 1) -
            241517 / 100000 - 1 / 4000 - (q + 7 / 20) ^ 2 / 48 -
            5 * (q + 7 / 20) ^ 3 / 192 - 397 / 20000) +
        atomFreePoly x - 16 / 25 * surplusRemainder (7 / 20) x ≤
      atomFreeNumerator κ x := by
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 7 / 20 := le_trans hxq hq
  have hℓ : Real.log (x + 7 / 20) - Real.log x ≤ Lv + (1 + 7 / 20 / x) / v - 1 := by
    rw [← Real.log_div (by linarith) hx0.ne']
    have e : (x + 7 / 20) / x = 1 + 7 / 20 / x := by field_simp
    rw [e]
    have := log_le_tangent (show 0 < 1 + 7 / 20 / x by positivity) hv
    linarith
  have hc : 1 / 500 - x ^ 2 - 49 / 20 * x ^ 4 ≤ 0 := by nlinarith [pow_nonneg hx0.le 4]
  have h1 : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + (1 + 7 / 20 / x) / v - 1) ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 7 / 20) - Real.log x) :=
    mul_le_mul_of_nonpos_left hℓ hc
  have h1' : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + 1 / v - 1) +
      7 / 20 / v * (1 / (500 * q) - x - 49 / 20 * x ^ 3) ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + (1 + 7 / 20 / x) / v - 1) := by
    have e : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + (1 + 7 / 20 / x) / v - 1) =
        (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + 1 / v - 1) +
          7 / 20 / v * (1 / (500 * x) - x - 49 / 20 * x ^ 3) := by
      field_simp; ring
    rw [e]
    have hqx : 1 / (500 * q) ≤ 1 / (500 * x) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have hv' : 0 ≤ 7 / 20 / v := by positivity
    nlinarith
  have hla : -(1 / 2) * (La + (701 / 2000 - x) / a - 1) ≤ -(1 / 2) * Real.log (701 / 2000 - x) := by
    have := log_le_tangent (show (0 : ℝ) < 701 / 2000 - x by linarith) ha
    linarith
  have hlb : -(1 / 2) * (Lb + (701 / 2000 + x) / b - 1) ≤ -(1 / 2) * Real.log (701 / 2000 + x) := by
    have := log_le_tangent (show (0 : ℝ) < 701 / 2000 + x by linarith) hb
    linarith
  have hp2 : (x + 7 / 20) ^ 2 ≤ (q + 7 / 20) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 7 / 20) ^ 3 ≤ (q + 7 / 20) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := atomFreeGauge_ge hx0.le hxr
  have h2 : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (-(1 / 2) * (La + (701 / 2000 - x) / a - 1) - 1 / 2 * (Lb + (701 / 2000 + x) / b - 1) -
          241517 / 100000 - 1 / 4000 - (q + 7 / 20) ^ 2 / 48 -
          5 * (q + 7 / 20) ^ 3 / 192 - 397 / 20000) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (-(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) - κ - 1 / 4000 -
          (x + 7 / 20) ^ 2 / 48 - 5 * (x + 7 / 20) ^ 3 / 192 - 397 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold atomFreeNumerator
  linarith

/-- **Monotone form of the numerator** on `[p, q] ⊆ [7/100, 7/20]`: the window ratio and the plateau
logarithm frozen at `p`. -/
theorem atomFreeNumerator_ge_monotone {κ x p q Lℓ Llam : ℝ} (hp : 7 / 100 ≤ p) (hpx : p ≤ x)
    (hxq : x ≤ q) (hq : q ≤ 7 / 20)
    (hLℓ : Real.log (p + 7 / 20) - Real.log p ≤ Lℓ)
    (hLlam : Llam ≤ -(1 / 2) * Real.log ((701 / 2000) ^ 2 - p ^ 2)) (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * Lℓ +
        quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
          (Llam - 241517 / 100000 - 1 / 4000 - (q + 7 / 20) ^ 2 / 48 -
            5 * (q + 7 / 20) ^ 3 / 192 - 397 / 20000) +
        atomFreePoly x - 16 / 25 * surplusRemainder (7 / 20) x ≤
      atomFreeNumerator κ x := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 7 / 20 := le_trans hxq hq
  have hℓ : Real.log (x + 7 / 20) - Real.log x ≤ Lℓ := by
    rw [← Real.log_div (by linarith) hx0.ne']
    rw [← Real.log_div (by linarith) hp0.ne'] at hLℓ
    refine le_trans (Real.log_le_log (by positivity) ?_) hLℓ
    rw [div_le_div_iff₀ hx0 hp0]; nlinarith
  have hc : 1 / 500 - x ^ 2 - 49 / 20 * x ^ 4 ≤ 0 := by nlinarith [pow_nonneg hx0.le 4]
  have h1 := mul_le_mul_of_nonpos_left hℓ hc
  have hlam : Llam ≤ -(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) := by
    have e : -(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) =
        -(1 / 2) * Real.log ((701 / 2000) ^ 2 - x ^ 2) := by
      rw [show (701 / 2000 : ℝ) ^ 2 - x ^ 2 = (701 / 2000 - x) * (701 / 2000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hmono : Real.log ((701 / 2000) ^ 2 - x ^ 2) ≤ Real.log ((701 / 2000) ^ 2 - p ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    linarith
  have hp2 : (x + 7 / 20) ^ 2 ≤ (q + 7 / 20) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 7 / 20) ^ 3 ≤ (q + 7 / 20) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := atomFreeGauge_ge hx0.le hxr
  have h2 : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (Llam - 241517 / 100000 - 1 / 4000 - (q + 7 / 20) ^ 2 / 48 -
          5 * (q + 7 / 20) ^ 3 / 192 - 397 / 20000) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (-(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) - κ - 1 / 4000 -
          (x + 7 / 20) ^ 2 / 48 - 5 * (x + 7 / 20) ^ 3 / 192 - 397 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold atomFreeNumerator
  nlinarith

theorem atomFreeNumerator_nonneg_one {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/100 ≤ x)
    (h2 : x ≤ 1/10) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 2 0 0 0 0 1 1 0
  have eb := log_smooth_div 0 0 0 1 4 0 0 0
  norm_num at ea eb
  have hv : Real.log (5) ≤ 1.609438 := by linarith [l5.2]
  have ha : Real.log (4/15) ≤ -1.321755 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (7/16) ≤ -0.826678 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 7/100) (q := 1/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 17/200)),
    sq_nonneg (x - 17/200), mul_nonneg (sq_nonneg (x - 17/200)) (sq_nonneg (x - 17/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_two {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 1/10 ≤ x)
    (h2 : x ≤ 13/100) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 0 0 0 0 0 0 0
  have ea := log_smooth_div 0 1 1 0 6 0 0 0
  have eb := log_smooth_div 0 0 2 0 1 3 0 0
  norm_num at ev ea eb
  have hv : Real.log (4) ≤ 1.386295 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (15/64) ≤ -1.450832 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (25/54) ≤ -0.770107 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 1/10) (q := 13/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 23/200)),
    sq_nonneg (x - 23/200), mul_nonneg (sq_nonneg (x - 23/200)) (sq_nonneg (x - 23/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_three {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/100 ≤ x)
    (h2 : x ≤ 4/25) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 3 0 0 3 0 0 0
  have ea := log_smooth_div 1 0 2 0 0 5 0 0
  have eb := log_smooth_div 0 0 0 2 2 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (27/8) ≤ 1.216396 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (50/243) ≤ -1.581037 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (49/100) ≤ -0.713349 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 13/100) (q := 4/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 29/200)),
    sq_nonneg (x - 29/200), mul_nonneg (sq_nonneg (x - 29/200)) (sq_nonneg (x - 29/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_four {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 4/25 ≤ x)
    (h2 : x ≤ 9/50) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 0 2 0 0 1 0 2 0
  have eb := log_smooth_div 1 0 0 1 0 3 0 0
  norm_num at ea eb
  have hv : Real.log (3) ≤ 1.098613 := by linarith [l3.2]
  have ha : Real.log (9/50) ≤ -1.714798 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (14/27) ≤ -0.656779 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 4/25) (q := 9/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 17/100)),
    sq_nonneg (x - 17/100), mul_nonneg (sq_nonneg (x - 17/100)) (sq_nonneg (x - 17/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_five {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 9/50 ≤ x)
    (h2 : x ≤ 1/5) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 1 0 0 1 0 0 1 0
  have ea := log_smooth_div 2 0 0 0 0 0 2 0
  have eb := log_smooth_div 0 3 0 0 1 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (14/5) ≤ 1.029620 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (4/25) ≤ -1.832581 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (27/50) ≤ -0.616186 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 9/50) (q := 1/5) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 19/100)),
    sq_nonneg (x - 19/100), mul_nonneg (sq_nonneg (x - 19/100)) (sq_nonneg (x - 19/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_six {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 1/5 ≤ x)
    (h2 : x ≤ 11/50) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 3 0 0 0 0 1 0 0
  have ea := log_smooth_div 0 0 0 1 1 0 2 0
  have eb := log_smooth_div 0 0 1 0 0 2 0 0
  norm_num at ev ea eb
  have hv : Real.log (8/3) ≤ 0.980830 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/50) ≤ -1.966112 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (5/9) ≤ -0.587786 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 1/5) (q := 11/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 21/100)),
    sq_nonneg (x - 21/100), mul_nonneg (sq_nonneg (x - 21/100)) (sq_nonneg (x - 21/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_seven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 11/50 ≤ x)
    (h2 : x ≤ 6/25) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 1 0 1 0 0 0
  have ea := log_smooth_div 0 1 0 0 0 0 2 0
  have eb := log_smooth_div 3 2 0 0 0 0 3 0
  norm_num at ev ea eb
  have hv : Real.log (5/2) ≤ 0.916291 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/25) ≤ -2.120263 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (72/125) ≤ -0.551647 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 11/50) (q := 6/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 23/100)),
    sq_nonneg (x - 23/100), mul_nonneg (sq_nonneg (x - 23/100)) (sq_nonneg (x - 23/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_eight {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 6/25 ≤ x)
    (h2 : x ≤ 13/50) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 1 0 0 0 0 1 0
  have ea := log_smooth_div 0 0 0 0 1 0 1 0
  have eb := log_smooth_div 0 1 0 0 0 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (12/5) ≤ 0.875469 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/10) ≤ -2.302585 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (3/5) ≤ -0.510825 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 6/25) (q := 13/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 1/4)),
    sq_nonneg (x - 1/4), mul_nonneg (sq_nonneg (x - 1/4)) (sq_nonneg (x - 1/4)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_nine {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/50 ≤ x)
    (h2 : x ≤ 7/25) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 4 0 0 0 0 0 0 1
  have ea := log_smooth_div 1 0 0 0 0 0 2 0
  have eb := log_smooth_div 0 0 1 0 3 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (16/7) ≤ 0.826679 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (2/25) ≤ -2.525728 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (5/8) ≤ -0.470003 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 13/50) (q := 7/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 27/100)),
    sq_nonneg (x - 27/100), mul_nonneg (sq_nonneg (x - 27/100)) (sq_nonneg (x - 27/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_ten {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/25 ≤ x)
    (h2 : x ≤ 3/10) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 1 1 4 0 0 0
  have ea := log_smooth_div 0 1 0 0 1 0 2 0
  have eb := log_smooth_div 4 0 0 0 0 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (35/16) ≤ 0.782760 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/50) ≤ -2.813410 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (16/25) ≤ -0.446287 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 7/25) (q := 3/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 29/100)),
    sq_nonneg (x - 29/100), mul_nonneg (sq_nonneg (x - 29/100)) (sq_nonneg (x - 29/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_eleven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 3/10 ≤ x)
    (h2 : x ≤ 63/200) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 5 0 0 0 0 1 1 0
  have ea := log_smooth_div 0 1 0 0 1 0 1 1
  have eb := log_smooth_div 0 1 0 1 5 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (32/15) ≤ 0.757686 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/70) ≤ -3.149882 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (21/32) ≤ -0.421213 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 3/10) (q := 63/200) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 123/400)),
    sq_nonneg (x - 123/400), mul_nonneg (sq_nonneg (x - 123/400)) (sq_nonneg (x - 123/400)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_twelve {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 63/200 ≤ x)
    (h2 : x ≤ 13/40) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 2 0 2 1 0 0
  have ea := log_smooth_div 0 1 0 0 2 0 2 0
  have eb := log_smooth_div 1 0 0 0 0 1 0 0
  norm_num at ev ea eb
  have hv : Real.log (25/12) ≤ 0.733970 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/100) ≤ -3.506557 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (2/3) ≤ -0.405465 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 63/200) (q := 13/40) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 8/25)),
    sq_nonneg (x - 8/25), mul_nonneg (sq_nonneg (x - 8/25)) (sq_nonneg (x - 8/25)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_thirteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/40 ≤ x)
    (h2 : x ≤ 333/1000) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 3 2 0 0 0 0 1 1
  have ea := log_smooth_div 0 1 0 0 2 0 1 1
  have eb := log_smooth_div 0 3 0 0 3 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (72/35) ≤ 0.721319 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/140) ≤ -3.843030 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (27/40) ≤ -0.393042 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 13/40) (q := 333/1000) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 329/1000)),
    sq_nonneg (x - 329/1000), mul_nonneg (sq_nonneg (x - 329/1000)) (sq_nonneg (x - 329/1000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_nonneg_fourteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 333/1000 ≤ x)
    (h2 : x ≤ 169/500) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 4 0 0 3 0 1 0
  have ea := log_smooth_div 0 1 0 0 3 0 2 0
  have eb := log_smooth_div 3 1 0 0 0 0 1 1
  norm_num at ev ea eb
  have hv : Real.log (81/40) ≤ 0.705570 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/200) ≤ -4.199705 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (24/35) ≤ -0.377294 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (atomFreeNumerator_ge_tangent (p := 333/1000) (q := 169/500) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 671/2000)),
    sq_nonneg (x - 671/2000), mul_nonneg (sq_nonneg (x - 671/2000)) (sq_nonneg (x - 671/2000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem atomFreeNumerator_edgeA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 169/500 ≤ x)
    (h2 : x ≤ 17/50) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (169/500 + 7 / 20) - Real.log (169/500) ≤ 710899 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (169/500 + 7 / 20) / (169/500) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2377629 / 1000000 ≤ -(1 / 2) * Real.log ((701 / 2000) ^ 2 - (169/500) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (701 / 2000) ^ 2 - (169/500) ^ 2 by norm_num)
      (show (0 : ℝ) < 27/3125 by norm_num)
    have e := log_smooth_div 0 3 0 0 0 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := atomFreeNumerator_ge_monotone (p := 169/500) (q := 17/50) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 339/1000)),
    sq_nonneg (x - 339/1000)]

theorem atomFreeNumerator_edgeB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 17/50 ≤ x)
    (h2 : x ≤ 343/1000) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (17/50 + 7 / 20) - Real.log (17/50) ≤ 707854 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (17/50 + 7 / 20) / (17/50) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2463350 / 1000000 ≤ -(1 / 2) * Real.log ((701 / 2000) ^ 2 - (17/50) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (701 / 2000) ^ 2 - (17/50) ^ 2 by norm_num)
      (show (0 : ℝ) < 729/100000 by norm_num)
    have e := log_smooth_div 0 6 0 0 5 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := atomFreeNumerator_ge_monotone (p := 17/50) (q := 343/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 683/2000)),
    sq_nonneg (x - 683/2000)]

theorem atomFreeNumerator_stripA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 343/1000 ≤ x)
    (h2 : x ≤ 69/200) : 23 / 10000 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (343/1000 + 7 / 20) - Real.log (343/1000) ≤ 703352 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (343/1000 + 7 / 20) / (343/1000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2629406 / 1000000 ≤ -(1 / 2) * Real.log ((701 / 2000) ^ 2 - (343/1000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (701 / 2000) ^ 2 - (343/1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 21/4000 by norm_num)
    have e := log_smooth_div 0 1 0 1 5 0 3 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := atomFreeNumerator_ge_monotone (p := 343/1000) (q := 69/200) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 344/1000)),
    sq_nonneg (x - 344/1000)]

theorem atomFreeNumerator_stripB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 69/200 ≤ x)
    (h2 : x ≤ 347/1000) : 23 / 10000 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (69/200 + 7 / 20) - Real.log (69/200) ≤ 700394 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (69/200 + 7 / 20) / (69/200) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2783061 / 1000000 ≤ -(1 / 2) * Real.log ((701 / 2000) ^ 2 - (69/200) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (701 / 2000) ^ 2 - (69/200) ^ 2 by norm_num)
      (show (0 : ℝ) < 12/3125 by norm_num)
    have e := log_smooth_div 2 1 0 0 0 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := atomFreeNumerator_ge_monotone (p := 69/200) (q := 347/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 346/1000)),
    sq_nonneg (x - 346/1000)]

theorem atomFreeNumerator_stripC {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 347/1000 ≤ x)
    (h2 : x ≤ 349/1000) : 23 / 10000 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (347/1000 + 7 / 20) - Real.log (347/1000) ≤ 697470 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (347/1000 + 7 / 20) / (347/1000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 3007617 / 1000000 ≤ -(1 / 2) * Real.log ((701 / 2000) ^ 2 - (347/1000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (701 / 2000) ^ 2 - (347/1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 243/100000 by norm_num)
    have e := log_smooth_div 0 5 0 0 5 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := atomFreeNumerator_ge_monotone (p := 347/1000) (q := 349/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 348/1000)),
    sq_nonneg (x - 348/1000)]

theorem atomFreeNumerator_stripD {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 349/1000 ≤ x)
    (h2 : x ≤ 7/20) : 23 / 10000 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (349/1000 + 7 / 20) - Real.log (349/1000) ≤ 694580 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (349/1000 + 7 / 20) / (349/1000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 3429839 / 1000000 ≤ -(1 / 2) * Real.log ((701 / 2000) ^ 2 - (349/1000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (701 / 2000) ^ 2 - (349/1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 21/20000 by norm_num)
    have e := log_smooth_div 0 1 0 1 5 0 4 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := atomFreeNumerator_ge_monotone (p := 349/1000) (q := 7/20) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 3495/10000)),
    sq_nonneg (x - 3495/10000)]
/-- The numerator near the origin, `0 < x ≤ 11/250`. -/
theorem atomFreeNumerator_nonneg_origin {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 0 < x)
    (h2 : x ≤ 11 / 250) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hxr : x ≤ 7 / 20 := by linarith
  have hℓ : 207 / 100 ≤ Real.log (x + 7 / 20) - Real.log x := by
    rw [← Real.log_div (by linarith) h1.ne']
    have h8 : Real.log 8 ≤ Real.log ((x + 7 / 20) / x) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ h1]; linarith)
    have e8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlam : 1048393 / 1000000 ≤
      -(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) := by
    have e : -(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) =
        -(1 / 2) * Real.log ((701 / 2000) ^ 2 - x ^ 2) := by
      rw [show (701 / 2000 : ℝ) ^ 2 - x ^ 2 = (701 / 2000 - x) * (701 / 2000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((701 / 2000) ^ 2 - x ^ 2) ≤ Real.log ((701 / 2000) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have hR : Real.log ((701 / 2000 : ℝ) ^ 2) = 2 * Real.log (701 / 2000) := by
      rw [Real.log_pow]; norm_num
    have ht := log_le_tangent (show (0 : ℝ) < 701 / 2000 by norm_num) (show (0 : ℝ) < 7 / 20 by norm_num)
    have e7 := log_smooth_div 0 0 0 1 2 0 1 0
    norm_num at e7 ht
    rw [e7] at ht
    linarith
  have hc : 0 ≤ 1 / 500 - x ^ 2 - 49 / 20 * x ^ 4 := by nlinarith [pow_le_pow_left₀ h1.le h2 4]
  have hp2 : (x + 7 / 20) ^ 2 ≤ (11 / 250 + 7 / 20) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 7 / 20) ^ 3 ≤ (11 / 250 + 7 / 20) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := atomFreeGauge_ge h1.le hxr
  have hA : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (207 / 100) ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 7 / 20) - Real.log x) :=
    mul_le_mul_of_nonneg_left hℓ hc
  have hB : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (1048393 / 1000000 - 241517 / 100000 - 1 / 4000 - (11 / 250 + 7 / 20) ^ 2 / 48 -
          5 * (11 / 250 + 7 / 20) ^ 3 / 192 - 397 / 20000) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (-(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) - κ - 1 / 4000 -
          (x + 7 / 20) ^ 2 / 48 - 5 * (x + 7 / 20) ^ 3 / 192 - 397 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hpoly : 0 ≤ (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (207 / 100) + quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (1048393 / 1000000 - 241517 / 100000 - 1 / 4000 - (11 / 250 + 7 / 20) ^ 2 / 48 -
          5 * (11 / 250 + 7 / 20) ^ 3 / 192 - 397 / 20000) +
      atomFreePoly x - 16 / 25 * surplusRemainder (7 / 20) x := by
    unfold quarticGauge atomFreePoly surplusRemainder
    nlinarith [mul_nonneg h1.le (sub_nonneg.2 h2), sq_nonneg x,
      mul_nonneg (mul_nonneg h1.le h1.le) (sub_nonneg.2 h2), pow_nonneg h1.le 3, pow_nonneg h1.le 4]
  unfold atomFreeNumerator
  linarith

/-- The numerator on a collar `[p, q] ⊆ [11/250, 7/100]`: `ℓ` between its endpoint values. -/
theorem atomFreeNumerator_ge_collar {κ x p q Llo Lhi Llam : ℝ} (hp : 11 / 250 ≤ p) (hpx : p ≤ x)
    (hxq : x ≤ q) (hq : q ≤ 7 / 100)
    (hlo : Llo ≤ Real.log (x + 7 / 20) - Real.log x)
    (hhi : Real.log (x + 7 / 20) - Real.log x ≤ Lhi)
    (hlam : Llam ≤ -(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x))
    (hκ : κ ≤ 241517 / 100000) :
    1 / 500 * Llo - (x ^ 2 + 49 / 20 * x ^ 4) * Lhi +
        quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (Llam - 241517 / 100000 - 1 / 4000 - (q + 7 / 20) ^ 2 / 48 -
          5 * (q + 7 / 20) ^ 3 / 192 - 397 / 20000) +
        atomFreePoly x - 16 / 25 * surplusRemainder (7 / 20) x ≤
      atomFreeNumerator κ x := by
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 7 / 20 := by linarith
  have hp2 : (x + 7 / 20) ^ 2 ≤ (q + 7 / 20) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 7 / 20) ^ 3 ≤ (q + 7 / 20) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := atomFreeGauge_ge hx0.le hxr
  have hw : 0 ≤ x ^ 2 + 49 / 20 * x ^ 4 := by positivity
  have hA : 1 / 500 * Llo - (x ^ 2 + 49 / 20 * x ^ 4) * Lhi ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 7 / 20) - Real.log x) := by
    nlinarith [mul_le_mul_of_nonneg_left hhi hw]
  have hB : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (Llam - 241517 / 100000 - 1 / 4000 - (q + 7 / 20) ^ 2 / 48 -
          5 * (q + 7 / 20) ^ 3 / 192 - 397 / 20000) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (-(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) - κ - 1 / 4000 -
          (x + 7 / 20) ^ 2 / 48 - 5 * (x + 7 / 20) ^ 3 / 192 - 397 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold atomFreeNumerator
  linarith

/-- The window ratio `log((x + 7/20)/x)` on a collar, from both endpoints. -/
theorem atomFreeWindowRatio_bounds {x p q : ℝ} (hp : 0 < p) (hpx : p ≤ x) (hxq : x ≤ q) :
    Real.log (q + 7 / 20) - Real.log q ≤ Real.log (x + 7 / 20) - Real.log x ∧
      Real.log (x + 7 / 20) - Real.log x ≤ Real.log (p + 7 / 20) - Real.log p := by
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  rw [← Real.log_div (by linarith) hx0.ne', ← Real.log_div (by linarith) hq0.ne',
    ← Real.log_div (by linarith) hp.ne']
  constructor
  · exact Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hq0 hx0]; nlinarith)
  · exact Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hx0 hp]; nlinarith)

theorem atomFreeNumerator_nonneg_collarA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000)
    (h1 : 11 / 250 ≤ x) (h2 : x ≤ 57 / 1000) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨hr1, hr2⟩ := atomFreeWindowRatio_bounds (by norm_num) h1 h2
  have hlo : 1965566 / 1000000 ≤ Real.log (x + 7 / 20) - Real.log x := by
    refine le_trans ?_ hr1
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_ge_tangent (show (0 : ℝ) < (57 / 1000 + 7 / 20) / (57 / 1000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hhi : Real.log (x + 7 / 20) - Real.log x ≤ 2192175 / 1000000 := by
    refine le_trans hr2 ?_
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (11 / 250 + 7 / 20) / (11 / 250) by norm_num)
      (show (0 : ℝ) < 9 by norm_num)
    have e9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    norm_num at ht ⊢
    linarith
  have hlam : 1056322 / 1000000 ≤
      -(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) := by
    have e : -(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) =
        -(1 / 2) * Real.log ((701 / 2000) ^ 2 - x ^ 2) := by
      rw [show (701 / 2000 : ℝ) ^ 2 - x ^ 2 = (701 / 2000 - x) * (701 / 2000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((701 / 2000) ^ 2 - x ^ 2) ≤ Real.log ((701 / 2000) ^ 2 - (11 / 250) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (701 / 2000) ^ 2 - (11 / 250) ^ 2 by norm_num)
      (show (0 : ℝ) < 3 / 25 by norm_num)
    have e := log_smooth_div 0 1 0 0 0 0 2 0
    norm_num at e ht
    rw [e] at ht
    linarith
  refine le_trans ?_ (atomFreeNumerator_ge_collar (p := 11 / 250) (q := 57 / 1000) le_rfl h1 h2
    (by norm_num) hlo hhi hlam hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 5 / 100)),
    sq_nonneg (x - 5 / 100)]

theorem atomFreeNumerator_nonneg_collarB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000)
    (h1 : 57 / 1000 ≤ x) (h2 : x ≤ 7 / 100) : 0 ≤ atomFreeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨hr1, hr2⟩ := atomFreeWindowRatio_bounds (by norm_num) h1 h2
  have hlo : 1791759 / 1000000 ≤ Real.log (x + 7 / 20) - Real.log x := by
    refine le_trans ?_ hr1
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    norm_num
    linarith
  have hhi : Real.log (x + 7 / 20) - Real.log x ≤ 1965961 / 1000000 := by
    refine le_trans hr2 ?_
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (57 / 1000 + 7 / 20) / (57 / 1000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hlam : 1061793 / 1000000 ≤
      -(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) := by
    have e : -(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x) =
        -(1 / 2) * Real.log ((701 / 2000) ^ 2 - x ^ 2) := by
      rw [show (701 / 2000 : ℝ) ^ 2 - x ^ 2 = (701 / 2000 - x) * (701 / 2000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((701 / 2000) ^ 2 - x ^ 2) ≤ Real.log ((701 / 2000) ^ 2 - (57 / 1000) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (701 / 2000) ^ 2 - (57 / 1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 3 / 25 by norm_num)
    have e := log_smooth_div 0 1 0 0 0 0 2 0
    norm_num at e ht
    rw [e] at ht
    linarith
  refine le_trans ?_ (atomFreeNumerator_ge_collar (p := 57 / 1000) (q := 7 / 100) (by norm_num) h1
    h2 le_rfl hlo hhi hlam hκ)
  unfold quarticGauge atomFreePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 635 / 10000)),
    sq_nonneg (x - 635 / 10000)]

/-- **The numerator exceeds the strip loss on `[0.343, 0.35]`.** -/
theorem atomFreeNumerator_strip {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 343 / 1000 ≤ x)
    (h2 : x ≤ 7 / 20) : 23 / 10000 ≤ atomFreeNumerator κ x := by
  rcases le_or_gt x (69 / 200) with ha | ha
  · exact atomFreeNumerator_stripA hκ h1 ha
  rcases le_or_gt x (347 / 1000) with hb | hb
  · exact atomFreeNumerator_stripB hκ ha.le hb
  rcases le_or_gt x (349 / 1000) with hc | hc
  · exact atomFreeNumerator_stripC hκ hb.le hc
  · exact atomFreeNumerator_stripD hκ hc.le h2

/-- **The numerator is nonnegative on `(0, 7/20]`.** -/
theorem atomFreeNumerator_nonneg {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (hx0 : 0 < x)
    (hxr : x ≤ 7 / 20) : 0 ≤ atomFreeNumerator κ x := by
  rcases le_or_gt x (11 / 250) with h | h
  · exact atomFreeNumerator_nonneg_origin hκ hx0 h
  rcases le_or_gt x (57 / 1000) with h' | h'
  · exact atomFreeNumerator_nonneg_collarA hκ h.le h'
  rcases le_or_gt x (7 / 100) with h0 | h0
  · exact atomFreeNumerator_nonneg_collarB hκ h'.le h0
  rcases le_or_gt x (1 / 10) with h1 | h1
  · exact atomFreeNumerator_nonneg_one hκ h0.le h1
  rcases le_or_gt x (13 / 100) with h2 | h2
  · exact atomFreeNumerator_nonneg_two hκ h1.le h2
  rcases le_or_gt x (4 / 25) with h3 | h3
  · exact atomFreeNumerator_nonneg_three hκ h2.le h3
  rcases le_or_gt x (9 / 50) with h4 | h4
  · exact atomFreeNumerator_nonneg_four hκ h3.le h4
  rcases le_or_gt x (1 / 5) with h5 | h5
  · exact atomFreeNumerator_nonneg_five hκ h4.le h5
  rcases le_or_gt x (11 / 50) with h6 | h6
  · exact atomFreeNumerator_nonneg_six hκ h5.le h6
  rcases le_or_gt x (6 / 25) with h7 | h7
  · exact atomFreeNumerator_nonneg_seven hκ h6.le h7
  rcases le_or_gt x (13 / 50) with h8 | h8
  · exact atomFreeNumerator_nonneg_eight hκ h7.le h8
  rcases le_or_gt x (7 / 25) with h9 | h9
  · exact atomFreeNumerator_nonneg_nine hκ h8.le h9
  rcases le_or_gt x (3 / 10) with h10 | h10
  · exact atomFreeNumerator_nonneg_ten hκ h9.le h10
  rcases le_or_gt x (63 / 200) with h11 | h11
  · exact atomFreeNumerator_nonneg_eleven hκ h10.le h11
  rcases le_or_gt x (13 / 40) with h12 | h12
  · exact atomFreeNumerator_nonneg_twelve hκ h11.le h12
  rcases le_or_gt x (333 / 1000) with h13 | h13
  · exact atomFreeNumerator_nonneg_thirteen hκ h12.le h13
  rcases le_or_gt x (169 / 500) with h14 | h14
  · exact atomFreeNumerator_nonneg_fourteen hκ h13.le h14
  rcases le_or_gt x (17 / 50) with h15 | h15
  · exact atomFreeNumerator_edgeA hκ h14.le h15
  rcases le_or_gt x (343 / 1000) with h16 | h16
  · exact atomFreeNumerator_edgeB hκ h15.le h16
  · linarith [atomFreeNumerator_strip hκ h16.le hxr]

/-! ### The potential off the strip -/

/-- **The potential on `(0, 7/20]`.** The killing, the quartic surplus potential of the pairs off the
strip `S × S`, `S = [log 2 − 7/20, 7/20]`, and the plateau potential of radius `701/2000` exceed
`397/20000`. -/
theorem atomFree_potential_ge {x : ℝ} (hx0 : 0 < x) (hxr : x ≤ 7 / 20) :
    397 / 20000 ≤
      2 * (archLevyAntideriv x - archLevyAntideriv (x + 7 / 20)) +
        surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (Real.log 2 - 7 / 20) (7 / 20) x +
        (archLevyAntideriv (701 / 2000 - x) + archLevyAntideriv (701 / 2000 + x) -
          2 * windowEdgeFunction 0 - 2 * archConstantReal) := by
  have hh := atomFreeGauge_ge hx0.le hxr
  have hh0 : 0 < quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x := by linarith
  have hU := mul_surplusPotential_quarticGauge_ge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)
    hx0 hxr (by norm_num) hh0 fun u v hu0 hur hv0 hvr => atomFreeGauge_divDiff_le hu0 hur hv0 hvr
  have hΩx := archLevyAntideriv_ge hx0
  have hΩr := archLevyAntideriv_le_expansion (show 0 < x + 7 / 20 by linarith)
  have hΩa := archLevyAntideriv_ge (show 0 < 701 / 2000 - x by linarith)
  have hΩb := archLevyAntideriv_ge (show 0 < 701 / 2000 + x by linarith)
  have hγ := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hπ := log_pi_le_11448
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hκ : Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi ≤ 241517 / 100000 := by
    linarith
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e1 : Real.log (x / 4) = Real.log x - 2 * Real.log 2 := by
    rw [Real.log_div hx0.ne' (by norm_num), l4]
  have e2 : Real.log ((x + 7 / 20) / 4) = Real.log (x + 7 / 20) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e3 : Real.log ((701 / 2000 - x) / 4) = Real.log (701 / 2000 - x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e4 : Real.log ((701 / 2000 + x) / 4) = Real.log (701 / 2000 + x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  rw [e1] at hΩx
  rw [e2] at hΩr
  rw [e3] at hΩa
  rw [e4] at hΩb
  rw [windowEdgeFunction_zero]
  unfold archConstantReal
  set κ := Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi with hκdef
  set V : ℝ := (Real.log (x + 7 / 20) - Real.log x) +
    (-(1 / 2) * Real.log (701 / 2000 - x) - 1 / 2 * Real.log (701 / 2000 + x)) - κ - 1 / 4000 -
    (x + 7 / 20) ^ 2 / 48 - 5 * (x + 7 / 20) ^ 3 / 192 with hV
  set U := surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (7 / 20) x with hUdef
  set U' := surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (Real.log 2 - 7 / 20) (7 / 20) x with hU'def
  have hkey : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (V - 397 / 20000) +
      (quarticSurplusMain (3 / 5) (-1) (-3 / 10) (-49 / 20) (7 / 20) x -
        16 / 25 * surplusRemainder (7 / 20) x) = atomFreeNumerator κ x := by
    rw [hV]; unfold atomFreeNumerator quarticSurplusMain cubicSurplusMain atomFreePoly quarticGauge
    ring
  -- off the strip the two potentials agree; on the strip the loss is below `23/10000`
  have hoff : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * U ≤ quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * U' + 23 / 10000 ∧ 23 / 10000 ≤ atomFreeNumerator κ x ∨
      U' = U ∧ 0 ≤ atomFreeNumerator κ x := by
    by_cases hS : x < Real.log 2 - 7 / 20
    · right
      refine ⟨?_, atomFreeNumerator_nonneg hκ hx0 hxr⟩
      rw [hU'def, hUdef]; unfold surplusPotentialOff; rw [if_pos hS]
    · left
      have hpx : Real.log 2 - 7 / 20 ≤ x := not_lt.mp hS
      have hloss := mul_surplusPotential_le_off_add (h := quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (a₀ := 1 / 500) (L := 16 / 25)
        (by linarith) hpx hxr (by norm_num) (continuous_quarticGauge _ _ _ _ _) (by norm_num) hh
        (by norm_num) (fun y hy0 hyr => by
          rw [quarticGauge_sub, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (atomFreeGauge_divDiff_le hx0.le hxr hy0.le hyr)
            (abs_nonneg _))
      refine ⟨?_, atomFreeNumerator_strip hκ (by linarith) hxr⟩
      have hd0 : 0 ≤ 7 / 20 - (Real.log 2 - 7 / 20) := by linarith
      have hd1 : 7 / 20 - (Real.log 2 - 7 / 20) ≤ 686 / 100000 := by linarith
      have hd : 16 / 25 * (7 / 20 - (Real.log 2 - 7 / 20)) * (1 / 2 + (7 / 20 - (Real.log 2 - 7 / 20)) / 4)
          ≤ 23 / 10000 := by nlinarith [mul_nonneg hd0 (sub_nonneg.2 hd1)]
      rw [hU'def, hUdef]
      linarith
  clear_value V U U'
  have hVU : 397 / 20000 ≤ V + U' := by
    have h1 : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (397 / 20000) ≤ quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (V + U') := by
      have e : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (V + U') = quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (V - 397 / 20000) + quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * U' +
          397 / 20000 * quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x := by ring
      rw [e]
      rcases hoff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith only [hkey, hU, h1, h2]
      · rw [h1]; linarith only [hkey, hU, h2]
    exact le_of_mul_le_mul_left h1 hh0
  have hW : V + U' ≤ 2 * (archLevyAntideriv x - archLevyAntideriv (x + 7 / 20)) + U' +
      (archLevyAntideriv (701 / 2000 - x) + archLevyAntideriv (701 / 2000 + x) -
        2 * (3 / 2 * Real.log 2 + Real.pi / 4) -
        2 * ((Real.eulerMascheroniConstant + Real.log Real.pi) / 2)) := by
    rw [hV, hκdef]; linarith only [hΩx, hΩr, hΩa, hΩb]
  linarith only [hVU, hW]

/-! ### Odd-sector positivity on `[−7/20, 7/20]` -/

/-- **Weil positivity of every odd test supported in `[−7/20, 7/20]`.** The window crosses
`½ log 2`; the micro-fold pays the whole prime term, and the archimedean potential of the pairs off the
edge strip carries the rest: `Ẑ(F) ≥ (1/200) ∫ F²`. -/
theorem fullZeroForm_ge_of_odd_support_le_sevenTwentieths {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 7 / 20 < |x| → F x = 0) :
    1 / 200 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set r : ℝ := 7 / 20 with hrdef
  set R : ℝ := 701 / 2000 with hRdef
  set δ : ℝ := R - r with hδdef
  have hδ : 0 < δ := by rw [hδdef, hRdef, hrdef]; norm_num
  set P := plateauGauge R δ with hPdef
  have hPd : ContDiff ℝ 2 P := contDiff_plateauGauge R δ
  have hPcs : HasCompactSupport P := hasCompactSupport_plateauGauge hδ
  have hP0 : ∀ y, 0 ≤ P y := plateauGauge_nonneg R δ
  have hP1 : ∀ y, P y ≤ 1 := plateauGauge_le_one R δ
  have hPB : ∀ y, R ≤ |y| → P y = 0 := fun y hy => plateauGauge_eq_zero hδ hy
  have hPr : ∀ y, |y| ≤ r → P y = 1 := fun y hy =>
    plateauGauge_eq_one hδ (by rw [hδdef]; linarith)
  have hPe : ∀ y, P (-y) = P y := fun y => by
    simp only [hPdef, plateauGauge, sub_neg_eq_add, ← sub_eq_add_neg]
    ring
  have hFr : ∀ x, F x ≠ 0 → |x| ≤ r := fun x hx => by
    by_contra h
    exact hx (hsupp x (not_le.mp h))
  have hFM : ∀ x, F x ≠ 0 → P x = 1 := fun x hx => hPr x (hFr x hx)
  have hFB : ∀ x, R ≤ |x| → F x = 0 := fun x hx => hsupp x (by
    simp only [hrdef, hRdef] at hx ⊢; linarith)
  obtain ⟨KF, -, hKF⟩ := exists_lipschitz_bound_of_compactSupport (hF.of_le (by norm_num)) hFc
  have hFL : ∀ a b, |F a - F b| ≤ KF * |a - b| := fun a b => hKF b a
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hPd.of_le (by norm_num)) hPcs
  have hPL : ∀ a b, |P a - P b| ≤ KM * |a - b| := fun a b => hKM b a
  have hR0 : 0 < R := by rw [hRdef]; norm_num
  have hR1 : 2 * R ≤ 1 := by rw [hRdef]; norm_num
  have hR3 : 2 * R < Real.log 3 := by have := log_three_bounds.1; rw [hRdef]; linarith
  have hl0 := Real.log_two_gt_d9
  have hl1 := Real.log_two_lt_d9
  -- representation with the prime `2`; the micro-fold pays the whole prime term
  have hQ := markovEnergy_eq_gauge_window hF hFc hPd hPcs hP1 hP0 hPB hFM
  have hJ := signedJumpEnergy_eq_arch_add_two (F := F) hPB hR3
  obtain ⟨hIU, hfold⟩ := fourKilling_add_potentialOff_le_archJump_sub_prime hPd.continuous
    hF.continuous hPe hodd hP0 hP1 hPB hFB hFL hR0 hR1 (r := r) hFc (by rw [hrdef]; linarith)
    (by rw [hrdef]; norm_num) (by rw [hrdef, hRdef]; norm_num) hPr hFr hPcs
    (continuous_quarticGauge _ _ _ _ _) (a₀ := 1 / 500) (by norm_num)
    (fun x hx0 hxr => atomFreeGauge_ge hx0 hxr) (L := 16 / 25)
    (fun x y hx0 hxr hy0 hyr => by
      rw [quarticGauge_sub, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (atomFreeGauge_divDiff_le hx0 hxr hy0 hyr) (abs_nonneg _))
  have hZ : fullZeroForm F = markovEnergy (fun x => (F x : ℂ)) - 2 * oddPoleMoment F ^ 2 := by
    unfold fullZeroForm
    rw [evenPoleMoment_eq_zero_of_odd hodd]
    ring
  have hdec8 : ∀ y, |P y| ≤ Real.exp (8 * R) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hP0 y), ← Real.exp_add]
      exact (hP1 y).trans (Real.one_le_exp (by nlinarith))
    · rw [hPB y (not_lt.mp hy), abs_zero]
      positivity
  have hW : Continuous fun x => -poleFreeWeilOperator P x :=
    (continuous_poleFreeWeilOperator hPd.continuous hPL hdec8).neg
  set G : ℝ → ℝ := fun x => F x ^ 2 * P x * -poleFreeWeilOperator P x with hGdef
  have hGi : Integrable G :=
    (((hF.continuous.pow 2).mul hPd.continuous).mul hW).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  obtain ⟨hΛ0, hΛ1⟩ := vonMangoldtAtom_two_bounds
  set L : ℝ := Real.log 2 with hLdef
  set Λ₂ : ℝ := vonMangoldtAtom 2 with hΛdef
  set Pr : ℝ → ℝ := fun x => F x ^ 2 * P x * (P (x + L) + P (x - L)) with hPrdef
  have hPri : Integrable Pr :=
    ((((hF.continuous.pow 2).mul hPd.continuous).mul
      ((hPd.continuous.comp (continuous_id.add continuous_const)).add
        (hPd.continuous.comp (continuous_id.sub continuous_const))))).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  set G₁ : ℝ → ℝ := fun x => F x ^ 2 * P x * (-poleFreeWeilOperator P x + profilePrimeSum P x)
    with hG₁def
  have hG₁eq : ∀ x, G₁ x = G x + Λ₂ * Pr x := fun x => by
    simp only [hG₁def, hGdef, hPrdef]
    by_cases h : F x = 0
    · rw [h]; ring
    · have hx : |x| < R := by have := hFr x h; rw [hrdef] at this; rw [hRdef]; linarith
      rw [profilePrimeSum_eq_two hPB hR3 hx]
      ring
  have hG₁i : Integrable G₁ := by
    have : G₁ = fun x => G x + Λ₂ * Pr x := funext hG₁eq
    rw [this]; exact hGi.add (hPri.const_mul Λ₂)
  have hG₁e : ∀ x, G₁ (-x) = G₁ x := fun x => by
    simp only [hG₁def, hodd, hPe, poleFreeWeilOperator_neg hPe, profilePrimeSum_neg hPe, neg_sq]
  have hG₁int := integral_eq_two_mul_Ioi_of_even hG₁i hG₁e
  have hGsplit : (∫ x, G x) = (∫ x, G₁ x) - Λ₂ * ∫ x, Pr x := by
    have : (fun x => G₁ x) = fun x => G x + Λ₂ * Pr x := funext hG₁eq
    rw [this, integral_add hGi (hPri.const_mul Λ₂), MeasureTheory.integral_const_mul]
    ring
  have hprime : gaugeJumpProfile P F L - ∫ x, Pr x = -2 * ∫ x, F x * F (x + L) :=
    gaugeJumpProfile_sub_primePotential_eq hPd.continuous hF.continuous hFc hFM L
  have hprimeΛ : Λ₂ * gaugeJumpProfile P F L - Λ₂ * ∫ x, Pr x = -2 * (Λ₂ * ∫ x, F x * F (x + L)) := by
    rw [← mul_sub, hprime]; ring
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hF2e : ∀ x, (fun x => F x ^ 2) (-x) = F x ^ 2 := fun x => by simp only [hodd, neg_sq]
  have hF2int := integral_eq_two_mul_Ioi_of_even hF2 hF2e
  have hHi := integrableOn_sq_mul_antideriv_sub hF.continuous hodd hFB hFL hR1
    (r := r) (by rw [hrdef]; norm_num) (by rw [hrdef, hRdef]; norm_num)
  -- pointwise potential on the half line
  set c₀ : ℝ := 397 / 20000 with hc₀
  set U' : ℝ → ℝ := surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (L - r) r with hU'def
  have hpt : ∀ x ∈ Ioi (0 : ℝ), c₀ * F x ^ 2 ≤
      2 * (F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
        F x ^ 2 * U' x + G₁ x := by
    intro x hx
    have hx0 : 0 < x := hx
    by_cases h : F x = 0
    · have h0 : F x ^ 2 = 0 := by rw [h]; ring
      simp only [hG₁def, h0, mul_zero, zero_mul, add_zero, le_refl]
    · have hxr : x ≤ r := by
        have := hFr x h; rwa [abs_of_pos hx0] at this
      have hxR : |x| < R := by rw [abs_of_pos hx0, hRdef]; rw [hrdef] at hxr; linarith
      have hW' := neg_poleFreeWeilOperator_add_primeSum_ge hPd.continuous hPL hP1 hPB hxR (hFM x h)
      have hV : 397 / 20000 ≤ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r)) + U' x +
          (archLevyAntideriv (R - x) + archLevyAntideriv (R + x) - 2 * windowEdgeFunction 0 -
            2 * archConstantReal) := atomFree_potential_ge hx0 (by rw [hrdef] at hxr; exact hxr)
      simp only [hG₁def, hFM x h, mul_one]
      have hF0 := sq_nonneg (F x)
      have k1 := mul_le_mul_of_nonneg_left hW' hF0
      have k2 := mul_le_mul_of_nonneg_left hV hF0
      rw [hc₀]
      linarith
  have hsum : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * U' x + G₁ x) (Ioi 0) :=
    ((hHi.const_mul 2).add hIU).add hG₁i.integrableOn
  have hH2 : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r)))) (Ioi 0) := hHi.const_mul 2
  have hH2U : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * U' x) (Ioi 0) := hH2.add hIU
  have hmono := setIntegral_mono_on (hF2.integrableOn.const_mul c₀) hsum measurableSet_Ioi hpt
  rw [integral_add hH2U hG₁i.integrableOn, integral_add hH2 hIU, integral_const_mul,
    integral_const_mul] at hmono
  -- the odd pole moment
  have hS := sq_oddPoleMoment_le_cosh hR0.le hF.continuous hFc hPd.continuous hPcs hP0 hP1 hPB hFM
  have hcosh : Real.cosh (R / 2) ^ 2 ≤ 1031302 / 1000000 := by
    have h1 := Real.cosh_le_exp_half_sq (R / 2)
    have h2 : (R / 2) ^ 2 / 2 ≤ 154 / 10000 := by rw [hRdef]; norm_num
    have h3 : Real.exp ((R / 2) ^ 2 / 2) ≤ Real.exp (154 / 10000) := Real.exp_le_exp.mpr h2
    have h4 : Real.exp (154 / 10000) ≤ 101553 / 100000 := by
      have := Real.exp_bound' (show (0 : ℝ) ≤ 154 / 10000 by norm_num)
        (show (154 / 10000 : ℝ) ≤ 1 by norm_num) (show 0 < 3 by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
      norm_num at this ⊢
      linarith
    have h5 : Real.cosh (R / 2) ≤ 101553 / 100000 := by linarith
    have h6 := Real.cosh_pos (R / 2)
    nlinarith
  have hpole : 2 * oddPoleMoment F ^ 2 ≤ 297 / 20000 * ∫ x, F x ^ 2 := by
    have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hR3' : R ^ 3 / 6 * Real.cosh (R / 2) ^ 2 ≤ 297 / 40000 := by
      have : R ^ 3 / 6 = (701 / 2000) ^ 3 / 6 := by rw [hRdef]
      rw [this]
      have := mul_le_mul_of_nonneg_left hcosh (show (0 : ℝ) ≤ (701 / 2000) ^ 3 / 6 by norm_num)
      linarith
    have h2 := mul_le_mul_of_nonneg_right hR3' hI0
    linarith
  rw [hc₀] at hmono
  rw [hZ, hQ, hJ, hGsplit]
  linarith [hfold, hmono, hG₁int, hF2int, hpole, hprimeΛ]

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
