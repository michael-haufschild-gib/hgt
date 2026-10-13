import GaloisForLFunctions.RHTower.DilationAutocorrelationPeriodizationBounded
import GaloisForLFunctions.RHTower.PiecewiseLinearCoreBlindnessRigidity

/-!
# Step-function cores with support ratio below 11 are never blind

Let `0 < y_1, …, y_m` be distinct with `y_j < 11 y_l` for all `j, l`, and let `d_1, …, d_m` be real with
`Σ d_j = 0`.  The step function

`f(x) = Σ_j d_j 1_{x ≥ y_j}`   (`stepCore`)

is the general compactly supported step function with jumps `d_j` at the `y_j`.  If the
cosine–dilation kernel `Ψ_f = Cf ⋆ f` vanishes at every integer `n ≥ 2`, then every `d_j` vanishes
(`stepCore_coeff_eq_zero_of_cosDilationKernel_blind`).

**Proof.**
* *Closed form* (`dilationAutocorr_stepCore`): `A_f(r) = −Σ_{j,l} d_j d_l (y_l/r − y_j)_+`, since
  `∫_0^Y 1_{t ≥ y_j} 1_{rt ≥ y_l} dt = Y − max(y_j, y_l/r)` and `Σ d_j = 0`.
* *Periodization* (`tsum_dilationAutocorr_abs_eq_of_bounded`): `P(x) = Σ_k A_f(|x+k|)` equals
  `Ψ_f(0) + 2Ψ_f(1) cos 2πx`.  Near `x = 0`, `P(x) = R(x) + |x| V(|x|)` with `R, V` analytic and
  `V(v) = −Σ_{k y_j = y_l} d_j d_l y_j/(k − v)`.  The analytic function `P − R − x V(x)` vanishes on
  `(0, ε)`, hence near `0`.  So `V(x) + V(−x) = 0` for small `x < 0`, and therefore `V(0) = 0`.
* *Arithmetic positivity* (`stepCornerForm_ge`): with `D_j = d_j √y_j`,
  `−V(0) = Σ_j D_j² + Σ_{k≥2} k^{−3/2} Σ_{k y_j = y_l} D_j D_l ≥ (1 − Σ_{k=2}^{10} k^{−3/2}) Σ_j D_j²`, and
  `Σ_{k=2}^{10} k^{−3/2} < 0.996`.
-/

open MeasureTheory Set Real Filter Topology

namespace RHTower

noncomputable section

variable {m : ℕ}

/-- The step core `f(x) = Σ_j d_j 1_{x ≥ y_j}`. -/
def stepCore (y d : Fin m → ℝ) (x : ℝ) : ℝ := ∑ j, d j * (Ici (y j)).indicator 1 x

theorem measurable_stepCore (y d : Fin m → ℝ) : Measurable (stepCore y d) := by
  unfold stepCore
  exact Finset.measurable_sum _ fun j _ =>
    measurable_const.mul (measurable_const.indicator measurableSet_Ici)

theorem abs_stepCore_le (y d : Fin m → ℝ) (x : ℝ) : |stepCore y d x| ≤ ∑ j, |d j| := by
  unfold stepCore
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  have : |(Ici (y j)).indicator (1 : ℝ → ℝ) x| ≤ 1 := by
    by_cases h : x ∈ Ici (y j)
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  calc |d j| * |(Ici (y j)).indicator (1 : ℝ → ℝ) x| ≤ |d j| * 1 :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |d j| := mul_one _

theorem stepCore_eq_zero_of_lt (y d : Fin m → ℝ) {x : ℝ} (hx : ∀ j, x < y j) :
    stepCore y d x = 0 := by
  unfold stepCore
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [indicator_of_notMem (by simpa using hx j), mul_zero]

theorem stepCore_eq_zero_of_ge (y d : Fin m → ℝ) (hd0 : ∑ j, d j = 0) {x : ℝ}
    (hx : ∀ j, y j ≤ x) : stepCore y d x = 0 := by
  unfold stepCore
  have h : ∀ j, d j * (Ici (y j)).indicator (1 : ℝ → ℝ) x = d j := fun j => by
    rw [indicator_of_mem (by simpa using hx j)]; simp
  simp only [h, hd0]

theorem stepCore_supp (y d : Fin m → ℝ) (hd0 : ∑ j, d j = 0) {α β : ℝ}
    (hyα : ∀ j, α ≤ y j) (hyβ : ∀ j, y j ≤ β) (x : ℝ) (hx : stepCore y d x ≠ 0) :
    α ≤ x ∧ x ≤ β := by
  constructor
  · by_contra h
    exact hx (stepCore_eq_zero_of_lt y d fun j => by linarith [hyα j])
  · by_contra h
    exact hx (stepCore_eq_zero_of_ge y d hd0 fun j => by linarith [hyβ j])

/-! ### The closed form -/

theorem indicator_Ici_mul_indicator_Ici (a b t : ℝ) :
    (Ici a).indicator (1 : ℝ → ℝ) t * (Ici b).indicator (1 : ℝ → ℝ) t =
      (Ici (max a b)).indicator (1 : ℝ → ℝ) t := by
  by_cases ha : a ≤ t <;> by_cases hb : b ≤ t
  · rw [indicator_of_mem (show t ∈ Ici a from ha), indicator_of_mem (show t ∈ Ici b from hb),
      indicator_of_mem (show t ∈ Ici (max a b) from max_le ha hb)]
    simp
  · rw [indicator_of_notMem (show t ∉ Ici b from hb), mul_zero,
      indicator_of_notMem (show t ∉ Ici (max a b) from fun h => hb (le_trans (le_max_right _ _) h))]
  · rw [indicator_of_notMem (show t ∉ Ici a from ha), zero_mul,
      indicator_of_notMem (show t ∉ Ici (max a b) from fun h => ha (le_trans (le_max_left _ _) h))]
  · rw [indicator_of_notMem (show t ∉ Ici a from ha), zero_mul,
      indicator_of_notMem (show t ∉ Ici (max a b) from fun h => ha (le_trans (le_max_left _ _) h))]

theorem setIntegral_Ioc_indicator_Ici {a Y : ℝ} (ha : 0 < a) (haY : a ≤ Y) :
    ∫ t in Ioc (0 : ℝ) Y, (Ici a).indicator (1 : ℝ → ℝ) t = Y - a := by
  rw [setIntegral_indicator measurableSet_Ici]
  have hset : Ioc (0 : ℝ) Y ∩ Ici a = Icc a Y := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le ha h1, h2⟩, h1⟩
  rw [hset]
  simp only [Pi.one_apply, integral_const, smul_eq_mul, mul_one]
  rw [Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]

/-- **The closed form** `A_f(r) = −Σ_{j,l} d_j d_l (y_l/r − y_j)_+` for `r > 0`. -/
theorem dilationAutocorr_stepCore (y d : Fin m → ℝ) (hy : ∀ j, 0 < y j) {β : ℝ}
    (hyβ : ∀ j, y j ≤ β) (hd0 : ∑ j, d j = 0) {r : ℝ} (hr : 0 < r) :
    dilationAutocorr (stepCore y d) r = -∑ j, ∑ l, d j * d l * max (y l / r - y j) 0 := by
  set Y := |β| + |β| / r with hY
  have habs : 0 ≤ |β| / r := div_nonneg (abs_nonneg _) hr.le
  have hβY : β ≤ Y := by linarith [le_abs_self β]
  have hyY : ∀ j, y j ≤ Y := fun j => le_trans (hyβ j) hβY
  have hyrY : ∀ l, y l / r ≤ Y := fun l => by
    have : y l / r ≤ |β| / r := div_le_div_of_nonneg_right (le_trans (hyβ l) (le_abs_self β)) hr.le
    linarith [abs_nonneg β]
  -- the half-line integral is the integral over `(0, Y]`
  have h1 : dilationAutocorr (stepCore y d) r =
      ∫ t in Ioc (0 : ℝ) Y, stepCore y d t * stepCore y d (r * t) := by
    unfold dilationAutocorr
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun t ht => ?_
    have htY : Y < t := by
      by_contra h
      exact ht.2 ⟨ht.1, le_of_not_gt h⟩
    rw [stepCore_eq_zero_of_ge y d hd0 (fun j => by linarith [hyY j]), zero_mul]
  have h2 : ∀ t, stepCore y d t * stepCore y d (r * t) =
      ∑ j, ∑ l, d j * d l * (Ici (max (y j) (y l / r))).indicator (1 : ℝ → ℝ) t := by
    intro t
    have hr' : ∀ l, (Ici (y l)).indicator (1 : ℝ → ℝ) (r * t) =
        (Ici (y l / r)).indicator (1 : ℝ → ℝ) t := fun l => by
      by_cases h : y l / r ≤ t
      · rw [indicator_of_mem (show t ∈ Ici (y l / r) from h), indicator_of_mem
          (show r * t ∈ Ici (y l) by
            show y l ≤ r * t
            rw [div_le_iff₀ hr] at h; linarith)]
        rfl
      · rw [indicator_of_notMem (show t ∉ Ici (y l / r) from h), indicator_of_notMem
          (show r * t ∉ Ici (y l) by
            intro h'
            exact h (by rw [div_le_iff₀ hr]; have : y l ≤ r * t := h'; linarith))]
    unfold stepCore
    simp only [hr', Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← indicator_Ici_mul_indicator_Ici]
    ring
  have hint : ∀ j l, IntegrableOn (fun t => d j * d l *
      (Ici (max (y j) (y l / r))).indicator (1 : ℝ → ℝ) t) (Ioc (0 : ℝ) Y) := by
    intro j l
    have h0 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) Y) :=
      integrableOn_const measure_Ioc_lt_top.ne
    exact (h0.indicator measurableSet_Ici).const_mul (d j * d l)
  have hpair : ∀ j l, ∫ t in Ioc (0 : ℝ) Y,
      (Ici (max (y j) (y l / r))).indicator (1 : ℝ → ℝ) t = Y - max (y j) (y l / r) := fun j l =>
    setIntegral_Ioc_indicator_Ici (lt_of_lt_of_le (hy j) (le_max_left _ _))
      (max_le (hyY j) (hyrY l))
  have hmax : ∀ j l, d j * d l * (Y - max (y j) (y l / r)) =
      Y * d j * d l - d j * y j * d l - d j * d l * max (y l / r - y j) 0 := fun j l => by
    have : max (y j) (y l / r) = y j + max (y l / r - y j) 0 := by
      rcases le_total (y j) (y l / r) with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    rw [this]; ring
  have hterm : ∀ j, ∫ t in Ioc (0 : ℝ) Y,
      ∑ l, d j * d l * (Ici (max (y j) (y l / r))).indicator (1 : ℝ → ℝ) t =
      -∑ l, d j * d l * max (y l / r - y j) 0 := by
    intro j
    rw [integral_finsetSum _ fun l _ => hint j l]
    have hl : ∀ l, ∫ t in Ioc (0 : ℝ) Y, d j * d l *
        (Ici (max (y j) (y l / r))).indicator (1 : ℝ → ℝ) t =
        Y * d j * d l - d j * y j * d l - d j * d l * max (y l / r - y j) 0 := fun l => by
      rw [integral_const_mul, hpair, hmax]
    rw [Finset.sum_congr rfl fun l _ => hl l, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hd0]
    ring
  rw [h1, setIntegral_congr_fun measurableSet_Ioc fun t _ => h2 t,
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hint j l,
    Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_neg_distrib]

theorem continuous_dilationAutocorr_stepCore (y d : Fin m → ℝ) (hy : ∀ j, 0 < y j)
    (hd0 : ∑ j, d j = 0) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hyα : ∀ j, α ≤ y j)
    (hyβ : ∀ j, y j ≤ β) : Continuous (dilationAutocorr (stepCore y d)) := by
  rw [continuous_iff_continuousAt]
  intro r₀
  rcases lt_or_ge 0 r₀ with h | h
  · have h' : r₀ ≠ 0 := h.ne'
    have hg : ContinuousAt (fun r : ℝ => -∑ j, ∑ l, d j * d l * max (y l * r⁻¹ - y j) 0) r₀ := by
      fun_prop (disch := assumption)
    refine hg.congr ?_
    filter_upwards [Ioi_mem_nhds h] with r hr
    rw [dilationAutocorr_stepCore y d hy hyβ hd0 hr]
    simp only [div_eq_mul_inv]
  · have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds (lt_of_le_of_lt h (div_pos hα hβ0))] with r hr
    exact (dilationAutocorr_eq_zero_of_not_mem hα hαβ (stepCore_supp y d hd0 hyα hyβ)
      fun hm => by linarith [hm.1, mem_Iio.mp hr]).symm

/-! ### Corners of the periodization -/

/-- The smooth coefficient of `(k, j, l)`. -/
def stepSmoothCoeff (y d : Fin m → ℝ) (k : ℝ) (j l : Fin m) : ℝ :=
  if k * y j = y l then 0 else if 0 < y l - k * y j then -(d j * d l) else 0

/-- The corner coefficient of `(k, j, l)`: `−d_j d_l y_j` if `k y_j = y_l`. -/
def stepKinkCoeff (y d : Fin m → ℝ) (k : ℝ) (j l : Fin m) : ℝ :=
  if k * y j = y l then -(d j * d l * y j) else 0

/-- `(b − (k+x)a)/(k+x) + (b − (k−x)a)/(k−x)`. -/
def stepRat (a b k x : ℝ) : ℝ := (b - (k + x) * a) / (k + x) + (b - (k - x) * a) / (k - x)

def stepSmooth (y d : Fin m → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ j, ∑ l, stepSmoothCoeff y d ((n : ℝ) + 1) j l * stepRat (y j) (y l) ((n : ℝ) + 1) x

def stepKink (y d : Fin m → ℝ) (N : ℕ) (v : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ j, ∑ l, stepKinkCoeff y d ((n : ℝ) + 1) j l / ((n : ℝ) + 1 - v)

theorem eventually_stepTerm (y d : Fin m → ℝ) (hy : ∀ j, 0 < y j) {k : ℝ} (hk : 1 ≤ k)
    (j l : Fin m) :
    ∀ᶠ x in 𝓝 (0 : ℝ), -(d j * d l * (max (y l - (k + x) * y j) 0 / (k + x) +
      max (y l - (k - x) * y j) 0 / (k - x))) =
      stepSmoothCoeff y d k j l * stepRat (y j) (y l) k x +
        |x| * (stepKinkCoeff y d k j l / (k - |x|)) := by
  unfold stepSmoothCoeff stepKinkCoeff stepRat
  by_cases hkink : k * y j = y l
  · rw [if_pos hkink, if_pos hkink]
    have hsmall : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < 1 / 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
      simpa [Real.dist_eq] using hx
    filter_upwards [hsmall] with x hx
    have hxl := abs_lt.mp hx
    have h1 : y l - (k + x) * y j = -x * y j := by rw [← hkink]; ring
    have h2 : y l - (k - x) * y j = x * y j := by rw [← hkink]; ring
    rw [h1, h2]
    have hyj := hy j
    rcases le_total 0 x with hx0 | hx0
    · rw [max_eq_right (by nlinarith), max_eq_left (by positivity), abs_of_nonneg hx0]
      have : k - x ≠ 0 := by linarith
      field_simp
      ring
    · rw [max_eq_left (by nlinarith), max_eq_right (by nlinarith), abs_of_nonpos hx0]
      have : k + x ≠ 0 := by linarith
      have : k - -x ≠ 0 := by linarith
      field_simp
      ring
  · rw [if_neg hkink, if_neg hkink]
    simp only [zero_div, mul_zero, add_zero]
    have hc1 : ContinuousAt (fun x : ℝ => y l - (k + x) * y j) 0 := by fun_prop
    have hc2 : ContinuousAt (fun x : ℝ => y l - (k - x) * y j) 0 := by fun_prop
    by_cases hpos : 0 < y l - k * y j
    · rw [if_pos hpos]
      have h0 : 0 < y l - (k + 0) * y j := by simpa using hpos
      have h0' : 0 < y l - (k - 0) * y j := by simpa using hpos
      filter_upwards [hc1.eventually (lt_mem_nhds h0), hc2.eventually (lt_mem_nhds h0')]
        with x hx1 hx2
      rw [max_eq_left hx1.le, max_eq_left hx2.le]
      ring
    · rw [if_neg hpos]
      simp only [zero_mul]
      have hneg : y l - k * y j < 0 := lt_of_le_of_ne (not_lt.mp hpos)
        (fun h => hkink (by linarith))
      have h0 : y l - (k + 0) * y j < 0 := by simpa using hneg
      have h0' : y l - (k - 0) * y j < 0 := by simpa using hneg
      filter_upwards [hc1.eventually (gt_mem_nhds h0), hc2.eventually (gt_mem_nhds h0')]
        with x hx1 hx2
      rw [max_eq_right hx1.le, max_eq_right hx2.le]
      simp

theorem analyticAt_stepSmooth (y d : Fin m → ℝ) (N : ℕ) {x : ℝ} (hx : |x| < 1 / 2) :
    AnalyticAt ℝ (stepSmooth y d N) x := by
  unfold stepSmooth
  refine analyticAt_fun_finsetSum _ fun n _ => analyticAt_fun_finsetSum _ fun j _ =>
    analyticAt_fun_finsetSum _ fun l _ => ?_
  have hk := one_le_natCast_add_one n
  have h1 : (n : ℝ) + 1 + x ≠ 0 := by linarith [abs_lt.mp hx]
  have h2 : (n : ℝ) + 1 - x ≠ 0 := by linarith [abs_lt.mp hx]
  unfold stepRat
  fun_prop (disch := assumption)

theorem analyticAt_stepKink (y d : Fin m → ℝ) (N : ℕ) {x : ℝ} (hx : |x| < 1 / 2) :
    AnalyticAt ℝ (stepKink y d N) x := by
  unfold stepKink
  refine analyticAt_fun_finsetSum _ fun n _ => analyticAt_fun_finsetSum _ fun j _ =>
    analyticAt_fun_finsetSum _ fun l _ => ?_
  have hk := one_le_natCast_add_one n
  have h1 : (n : ℝ) + 1 - x ≠ 0 := by linarith [abs_lt.mp hx]
  fun_prop (disch := assumption)

/-! ### The corner form and its positivity -/

/-- The corner form `Σ_{k ≤ N} Σ_{k y_j = y_l} d_j d_l y_j / k`. -/
def stepCornerForm (y d : Fin m → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ j, ∑ l,
    if ((n : ℝ) + 1) * y j = y l then d j * d l * y j / ((n : ℝ) + 1) else 0

theorem stepKink_zero (y d : Fin m → ℝ) (N : ℕ) : stepKink y d N 0 = -stepCornerForm y d N := by
  unfold stepKink stepCornerForm stepKinkCoeff
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [neg_div]

/-- The weights `1/(k√k)`, `2 ≤ k ≤ 10`, sum to less than `1`. -/
theorem sum_inv_mul_sqrt_lt_one :
    ∑ n ∈ Finset.range 9, 1 / (((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2)) < 0.996 := by
  have hs : ∀ (k s : ℝ), 0 < s → s ^ 2 ≤ k → 1 / (k * Real.sqrt k) ≤ 1 / (k * s) := by
    intro k s hs hsk
    have hk : 0 < k := lt_of_lt_of_le (by positivity) hsk
    have : s ≤ Real.sqrt k := Real.le_sqrt_of_sq_le hsk
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left this hk.le)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast
  have b2 := hs 2 1.414 (by norm_num) (by norm_num)
  have b3 := hs 3 1.732 (by norm_num) (by norm_num)
  have b4 := hs 4 2 (by norm_num) (by norm_num)
  have b5 := hs 5 2.236 (by norm_num) (by norm_num)
  have b6 := hs 6 2.449 (by norm_num) (by norm_num)
  have b7 := hs 7 2.645 (by norm_num) (by norm_num)
  have b8 := hs 8 2.828 (by norm_num) (by norm_num)
  have b9 := hs 9 3 (by norm_num) (by norm_num)
  have b10 := hs 10 3.162 (by norm_num) (by norm_num)
  norm_num at b2 b3 b4 b5 b6 b7 b8 b9 b10 ⊢
  linarith

/-- **Positivity of the corner form** for support ratio below `11`. -/
theorem stepCornerForm_ge (y d : Fin m → ℝ) (hy : ∀ j, 0 < y j) (hinj : Function.Injective y)
    (hratio : ∀ j l, y l < 11 * y j) (N : ℕ) :
    (1 - 0.996) * ∑ j, d j ^ 2 * y j ≤ stepCornerForm y d (N + 1) := by
  set E := ∑ j, d j ^ 2 * y j with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun j _ => by have := hy j; positivity
  unfold stepCornerForm
  rw [Finset.sum_range_succ']
  have hdiag : ∑ j, ∑ l, (if (((0 : ℕ) : ℝ) + 1) * y j = y l then
      d j * d l * y j / (((0 : ℕ) : ℝ) + 1) else 0) = E := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ l, (if (((0 : ℕ) : ℝ) + 1) * y j = y l then
        d j * d l * y j / (((0 : ℕ) : ℝ) + 1) else 0) =
        if j = l then d j ^ 2 * y j else 0 := fun l => by
      by_cases h : j = l
      · subst h; rw [if_pos (by norm_num), if_pos rfl]; push_cast; ring
      · have : ¬ (((0 : ℕ) : ℝ) + 1) * y j = y l := by
          simp only [Nat.cast_zero, zero_add, one_mul]; exact fun h' => h (hinj h')
        rw [if_neg this, if_neg h]
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hdiag]
  -- the weight of the block `k = n + 2`
  set w : ℕ → ℝ := fun n => if n < 9 then 1 / (((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2)) else 0
    with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => by
    simp only [hw]; split_ifs
    · positivity
    · exact le_rfl
  have hblock : ∀ n ∈ Finset.range N, -(w n) * E ≤ ∑ j, ∑ l,
      (if (((n + 1 : ℕ) : ℝ) + 1) * y j = y l then
        d j * d l * y j / (((n + 1 : ℕ) : ℝ) + 1) else 0) := by
    intro n _
    set k : ℝ := ((n + 1 : ℕ) : ℝ) + 1 with hk
    have hkn : k = (n : ℝ) + 2 := by simp only [hk]; push_cast; ring
    have hk2 : 2 ≤ k := by rw [hkn]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hk0 : 0 < k := by linarith
    by_cases hn9 : n < 9
    · have hwn : w n = 1 / (k * Real.sqrt k) := by simp only [hw, if_pos hn9, hkn]
      have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
      have hterm : ∀ j l, -(if k * y j = y l then d j ^ 2 * y j / (2 * (k * Real.sqrt k)) else 0) -
          (if k * y j = y l then d l ^ 2 * y l / (2 * (k * Real.sqrt k)) else 0) ≤
          (if k * y j = y l then d j * d l * y j / k else 0) := by
        intro j l
        by_cases h : k * y j = y l
        · simp only [if_pos h]
          rw [← h]
          have hyj := hy j
          have hs2 : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk0.le
          have hamgm : -(d j ^ 2 + k * d l ^ 2) ≤ 2 * Real.sqrt k * (d j * d l) := by
            nlinarith [sq_nonneg (d j + Real.sqrt k * d l)]
          have key : -(d j ^ 2 * y j / (2 * (k * Real.sqrt k))) -
              d l ^ 2 * (k * y j) / (2 * (k * Real.sqrt k)) =
              -(d j ^ 2 + k * d l ^ 2) * y j / (2 * (k * Real.sqrt k)) := by ring
          rw [key]
          have hden : 0 < 2 * (k * Real.sqrt k) := by positivity
          rw [div_le_iff₀ hden]
          have : d j * d l * y j / k * (2 * (k * Real.sqrt k)) =
              2 * Real.sqrt k * (d j * d l) * y j := by field_simp
          rw [this]
          exact mul_le_mul_of_nonneg_right hamgm hyj.le
        · simp [if_neg h]
      have hL := sum_sum_ite_le_left (p := fun j l => k * y j = y l)
        (fun j => d j ^ 2 * y j / (2 * (k * Real.sqrt k))) (fun j => by have := hy j; positivity)
        fun j l l' h h' => hinj (h.symm.trans h')
      have hR := sum_sum_ite_le_right (p := fun j l => k * y j = y l)
        (fun l => d l ^ 2 * y l / (2 * (k * Real.sqrt k))) (fun j => by have := hy j; positivity)
        fun j j' l h h' => hinj (mul_left_cancel₀ hk0.ne' (h.trans h'.symm))
      have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
        Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hterm j l
      simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsum
      rw [← Finset.sum_div] at hL hR
      have : -(w n) * E = -(E / (2 * (k * Real.sqrt k))) - E / (2 * (k * Real.sqrt k)) := by
        rw [hwn]; field_simp; ring
      rw [this]
      linarith
    · -- no corner with `k ≥ 11`
      have hw9 : w n = 0 := by simp only [hw, if_neg hn9]
      have hk11 : 11 ≤ k := by
        rw [hkn]; have : (9 : ℝ) ≤ n := by exact_mod_cast not_lt.mp hn9
        linarith
      rw [hw9, neg_zero, zero_mul]
      refine le_of_eq (Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_).symm
      rw [if_neg]
      intro h
      have := hratio j l
      have hyj := hy j
      nlinarith
  have htot := Finset.sum_le_sum hblock
  rw [← Finset.sum_mul, Finset.sum_neg_distrib] at htot
  have hwsum : ∑ n ∈ Finset.range N, w n ≤ 0.996 := by
    have h9 : ∑ n ∈ Finset.range N, w n ≤ ∑ n ∈ Finset.range 9, w n := by
      calc ∑ n ∈ Finset.range N, w n ≤ ∑ n ∈ Finset.range (max N 9), w n :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (le_max_left _ _)) fun n _ _ => hw0 n
        _ = ∑ n ∈ Finset.range 9, w n := by
            rw [← Finset.sum_range_add_sum_Ico _ (le_max_right N 9)]
            rw [Finset.sum_eq_zero (s := Finset.Ico 9 (max N 9)) fun n hn => by
              simp only [hw]; rw [if_neg (by have := (Finset.mem_Ico.mp hn).1; omega)]]
            ring
    have heq : ∑ n ∈ Finset.range 9, w n =
        ∑ n ∈ Finset.range 9, 1 / (((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2)) :=
      Finset.sum_congr rfl fun n hn => by
        simp only [hw]; rw [if_pos (Finset.mem_range.mp hn)]
    linarith [sum_inv_mul_sqrt_lt_one]
  nlinarith [mul_le_mul_of_nonneg_right hwsum hE0]

/-! ### The rigidity theorem -/

theorem dilationAutocorr_stepCore' (y d : Fin m → ℝ) (hy : ∀ j, 0 < y j) {β : ℝ}
    (hyβ : ∀ j, y j ≤ β) (hd0 : ∑ j, d j = 0) {t : ℝ} (ht : 0 < t) :
    dilationAutocorr (stepCore y d) t = -∑ j, ∑ l, d j * d l * (max (y l - t * y j) 0 / t) := by
  rw [dilationAutocorr_stepCore y d hy hyβ hd0 ht]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  congr 1
  have : y l / t - y j = (y l - t * y j) / t := by field_simp
  rw [this]
  rcases le_total (y l - t * y j) 0 with h | h
  · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg h ht.le), max_eq_right h, zero_div]
  · rw [max_eq_left (div_nonneg h ht.le), max_eq_left h]

/-- **Step cores with support ratio below `11` are never blind.**  If `0 < y_j` are distinct
with `y_l < 11 y_j` for all `j, l`, `Σ d_j = 0`, and the cosine–dilation kernel of
`f = Σ_j d_j 1_{· ≥ y_j}` vanishes at every integer `n ≥ 2`, then every `d_j` vanishes. -/
theorem stepCore_coeff_eq_zero_of_cosDilationKernel_blind (y d : Fin m → ℝ) (hy : ∀ j, 0 < y j)
    (hinj : Function.Injective y) (hratio : ∀ j l, y l < 11 * y j) (hd0 : ∑ j, d j = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel (stepCore y d) n = 0) (j : Fin m) :
    d j = 0 := by
  set f := stepCore y d with hfdef
  set A := dilationAutocorr f with hA
  set S := ∑ i, 1 / y i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => (one_div_pos.mpr (hy i)).le
  set α : ℝ := 1 / (1 + S) with hαdef
  set β : ℝ := 1 + ∑ i, y i with hβdef
  have hα : 0 < α := by positivity
  have hyα : ∀ i, α ≤ y i := fun i => by
    rw [hαdef, div_le_iff₀ (by positivity)]
    have h1 : 1 / y i ≤ S := Finset.single_le_sum (f := fun i => 1 / y i)
      (fun i _ => (one_div_pos.mpr (hy i)).le) (Finset.mem_univ i)
    have h2 : y i * (1 / y i) = 1 := mul_one_div_cancel (hy i).ne'
    nlinarith [hy i]
  have hyβ : ∀ i, y i ≤ β := fun i => by
    have := Finset.single_le_sum (f := y) (fun i _ => (hy i).le) (Finset.mem_univ i)
    linarith
  have hα1 : α ≤ 1 := by rw [hαdef, div_le_one (by positivity)]; linarith
  have hαβ : α ≤ β := by
    have : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => (hy i).le
    linarith
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hsupp := stepCore_supp y d hd0 hyα hyβ
  have hfm := measurable_stepCore y d
  have hfb := abs_stepCore_le y d
  have hAc := continuous_dilationAutocorr_stepCore y d hy hd0 hα hαβ hyα hyβ
  have hblindℤ : ∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0 := by
    intro n hn
    have hm : 2 ≤ n.natAbs := by
      rw [Int.abs_eq_natAbs] at hn
      exact_mod_cast hn
    rcases Int.natAbs_eq n with h | h
    · rw [h, Int.cast_natCast]
      exact hblind _ hm
    · rw [h, Int.cast_neg, Int.cast_natCast, cosDilationKernel_neg_of_bounded hfm hfb hα hαβ hsupp]
      exact hblind _ hm
  set K : ℕ := ⌈β / α⌉₊ with hK
  set N : ℕ := K + 1 with hN
  have hKge : β / α ≤ K := Nat.le_ceil _
  have hA0 : ∀ t, t ∉ Icc (α / β) (β / α) → A t = 0 := fun t ht =>
    dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp ht
  set δ₀ : ℝ := min (1 / 2) (α / β) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min (by norm_num) (div_pos hα hβ0)
  -- the periodization near `0` is a finite sum
  have hper : ∀ x, |x| < δ₀ →
      ∑ n ∈ Finset.range N, (A ((n : ℝ) + 1 + x) + A ((n : ℝ) + 1 - x)) =
        cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) := by
    intro x hx
    have hx12 : |x| < 1 / 2 := lt_of_lt_of_le hx (min_le_left _ _)
    have hxab : |x| < α / β := lt_of_lt_of_le hx (min_le_right _ _)
    have hxl := abs_lt.mp hx12
    have h := tsum_dilationAutocorr_abs_eq_of_bounded hfm hfb hα hαβ hsupp hAc hblindℤ x
    set g : ℤ → ℂ := fun k => ((A |x + k| : ℝ) : ℂ) with hg
    have hNc : (N : ℝ) = K + 1 := by rw [hN]; push_cast; ring
    have hbig : ∀ n : ℕ, N ≤ n → A ((n : ℝ) + 1 + x) = 0 ∧ A ((n : ℝ) + 1 - x) = 0 := by
      intro n hn
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      constructor
      · exact hA0 _ fun hmem => by linarith [hmem.2]
      · exact hA0 _ fun hmem => by linarith [hmem.2]
    have hpos : ∀ n : ℕ, g ((n : ℤ) + 1) = ((A ((n : ℝ) + 1 + x) : ℝ) : ℂ) := by
      intro n
      simp only [hg]
      congr 2
      rw [abs_of_pos (by push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
      push_cast; ring
    have hneg : ∀ n : ℕ, g (-((n : ℤ) + 1)) = ((A ((n : ℝ) + 1 - x) : ℝ) : ℂ) := by
      intro n
      simp only [hg]
      congr 2
      rw [abs_of_neg (by push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
      push_cast; ring
    have hz : g 0 = 0 := by
      simp only [hg, Int.cast_zero, add_zero]
      rw [hA0 _ fun hmem => by linarith [hmem.1], Complex.ofReal_zero]
    have hv1 : ∀ n ∉ Finset.range N, g ((n : ℤ) + 1) = 0 := fun n hn => by
      rw [hpos, (hbig n (by simpa using hn)).1, Complex.ofReal_zero]
    have hv2 : ∀ n ∉ Finset.range N, g (-((n : ℤ) + 1)) = 0 := fun n hn => by
      rw [hneg, (hbig n (by simpa using hn)).2, Complex.ofReal_zero]
    rw [tsum_of_add_one_of_neg_add_one (summable_of_ne_finset_zero hv1)
      (summable_of_ne_finset_zero hv2), hz, add_zero, tsum_eq_sum hv1, tsum_eq_sum hv2] at h
    simp only [hpos, hneg] at h
    rw [← Finset.sum_add_distrib] at h
    have h' : ((∑ n ∈ Finset.range N, (A ((n : ℝ) + 1 + x) + A ((n : ℝ) + 1 - x)) : ℝ) : ℂ) =
        ((cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) : ℝ) : ℂ) := by
      rw [← h]; push_cast; rfl
    exact Complex.ofReal_injective h'
  -- the corner decomposition near `0`
  have hdec : ∀ᶠ x in 𝓝 (0 : ℝ),
      ∑ n ∈ Finset.range N, (A ((n : ℝ) + 1 + x) + A ((n : ℝ) + 1 - x)) =
        stepSmooth y d N x + |x| * stepKink y d N |x| := by
    have hall : ∀ᶠ x in 𝓝 (0 : ℝ), ∀ n ∈ Finset.range N, ∀ i l,
        -(d i * d l * (max (y l - ((n : ℝ) + 1 + x) * y i) 0 / ((n : ℝ) + 1 + x) +
          max (y l - ((n : ℝ) + 1 - x) * y i) 0 / ((n : ℝ) + 1 - x))) =
        stepSmoothCoeff y d ((n : ℝ) + 1) i l * stepRat (y i) (y l) ((n : ℝ) + 1) x +
          |x| * (stepKinkCoeff y d ((n : ℝ) + 1) i l / ((n : ℝ) + 1 - |x|)) :=
      (eventually_all_finset _).mpr fun n _ => eventually_all.mpr fun i =>
        eventually_all.mpr fun l => eventually_stepTerm y d hy (one_le_natCast_add_one n) i l
    have hsmall : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < 1 / 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
      simpa [Real.dist_eq] using hx
    filter_upwards [hall, hsmall] with x hx hx12
    have hxl := abs_lt.mp hx12
    unfold stepSmooth stepKink
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hk1 : 0 < (n : ℝ) + 1 + x := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hk2 : 0 < (n : ℝ) + 1 - x := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have e1 := dilationAutocorr_stepCore' y d hy hyβ hd0 hk1
    have e2 := dilationAutocorr_stepCore' y d hy hyβ hd0 hk2
    rw [← hfdef, ← hA] at e1 e2
    rw [e1, e2, ← neg_add, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hx n hn i l]
    ring
  have hident : ∀ᶠ x in 𝓝 (0 : ℝ),
      cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) =
        stepSmooth y d N x + |x| * stepKink y d N |x| := by
    have hball : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < δ₀ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ₀pos] with x hx
      simpa [Real.dist_eq] using hx
    filter_upwards [hdec, hball] with x hx hxδ
    rw [← hper x hxδ]
    exact hx
  obtain ⟨ε, hε, hεid⟩ := Metric.eventually_nhds_iff.mp hident
  set ε' := min ε (1 / 2) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'12 : ε' ≤ 1 / 2 := min_le_right _ _
  set F : ℝ → ℝ := fun x =>
    cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) -
      stepSmooth y d N x - x * stepKink y d N x with hF
  have hFan : AnalyticOnNhd ℝ F (Ioo (-ε') ε') := by
    intro x hx
    have hx12 : |x| < 1 / 2 := abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h1 := analyticAt_stepSmooth y d N hx12
    have h2 := analyticAt_stepKink y d N hx12
    have h3 : AnalyticAt ℝ (fun x : ℝ =>
        cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x)) x := by
      fun_prop
    exact (h3.sub h1).sub (analyticAt_id.mul h2)
  have hdist : ∀ x, |x| < ε' → dist x 0 < ε := fun x hx => by
    rw [Real.dist_eq, sub_zero]; linarith
  have hFpos : ∀ x ∈ Ioo 0 ε', F x = 0 := by
    intro x hx
    have := hεid (hdist x (by rw [abs_of_pos hx.1]; exact hx.2))
    simp only [hF]
    rw [this, abs_of_pos hx.1]
    ring
  have hFzero : EqOn F (fun _ => 0) (Ioo (-ε') ε') := by
    refine hFan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_Ioo
      (z₀ := ε' / 2) ⟨by linarith, by linarith⟩ ?_
    filter_upwards [Ioo_mem_nhds (by linarith : (0 : ℝ) < ε' / 2)
      (by linarith : ε' / 2 < ε')] with x hx
    exact hFpos x hx
  -- `V(x) + V(−x) = 0` on `(−ε', 0)`
  set G : ℝ → ℝ := fun x => stepKink y d N x + stepKink y d N (-x) with hG
  have hGneg : ∀ x ∈ Ioo (-ε') 0, G x = 0 := by
    intro x hx
    have h0 := hFzero ⟨hx.1, by linarith [hx.2]⟩
    have := hεid (hdist x (by rw [abs_of_neg hx.2]; linarith [hx.1]))
    simp only [hF] at h0
    rw [this, abs_of_neg hx.2] at h0
    have h2 : -x * (stepKink y d N x + stepKink y d N (-x)) = 0 := by linear_combination h0
    have hx0 : -x ≠ 0 := by linarith [hx.2]
    exact (mul_eq_zero.mp h2).resolve_left hx0
  have hG0 : G 0 = 0 := by
    have hc : ContinuousAt G 0 := by
      have h1 := (analyticAt_stepKink y d N (x := 0) (by norm_num)).continuousAt
      have h2 : ContinuousAt (fun x => stepKink y d N (-x)) 0 := by
        have := (analyticAt_stepKink y d N (x := -0) (by norm_num)).continuousAt
        exact this.comp continuous_neg.continuousAt
      exact h1.add h2
    have hlim : Tendsto G (𝓝[<] 0) (𝓝 (G 0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[<] 0] G := by
      filter_upwards [Ioo_mem_nhdsLT (by linarith : -ε' < 0)] with x hx
      exact (hGneg x hx).symm
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev)
  have hform : stepCornerForm y d (K + 1) = 0 := by
    have h := stepKink_zero y d N
    simp only [hG, neg_zero] at hG0
    show stepCornerForm y d N = 0
    linarith
  have hge := stepCornerForm_ge y d hy hinj hratio K
  rw [hform] at hge
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ d i ^ 2 * y i := fun i _ => by
    have := hy i; positivity
  have hsum0 : ∑ i, d i ^ 2 * y i ≤ 0 := by
    by_contra hneg
    have : 0 < (1 - 0.996 : ℝ) * ∑ i, d i ^ 2 * y i := mul_pos (by norm_num) (lt_of_not_ge hneg)
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp
    (le_antisymm hsum0 (Finset.sum_nonneg hnn)) j (Finset.mem_univ j)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    ((mul_eq_zero.mp hterm).resolve_right (hy j).ne')

end

end RHTower
