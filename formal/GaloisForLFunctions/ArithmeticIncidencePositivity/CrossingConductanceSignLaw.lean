import GaloisForLFunctions.RHTower.WeilPhiDoobReflectedKillingPotentialAndDisjointSupportDiagonal
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateKernelBounds

/-!
# The sign law of the archimedean crossing conductance

In an odd gauge `M`, positive on `(0, ∞)`, the zero form is a jump form: the conductance of a
pair of points `(x, y)` is `M(x) M(y) k(x, y)` with the gauge-free kernel
`k(x, y) = dm(|x − y|) + sinh(x/2) sinh(y/2)`, where `dm` is the jump measure, the archimedean
density `ω = archLevyDensity` plus the prime atoms. Same-side pairs (`xy > 0`) have `M(x)M(y) > 0`
and crossing pairs (`x < 0 < y`) have `M(x)M(y) < 0`: a crossing pair carries negative conductance
exactly where the kernel is positive.

This module determines the sign of the archimedean part `k_arch(x, y) = ω(|x − y|) + sinh(x/2) sinh(y/2)`
exactly, in the coordinates `s = y − x = |x| + y` (sum of the distances to the origin) and
`e = x + y` (imbalance) of a crossing pair.

* On same-side pairs `k_arch > 0`.
* On a crossing pair `k_arch > 0 ⟺ cosh(e/2) > S(s)`, with the **crossing symbol**
  `S(s) = cosh(s/2) − 2 ω(s)`.
* `S` is strictly increasing on `(0, ∞)` with `S(2 log 3) = 119/120 < 1 < 3311/2040 = S(4 log 2)`,
  so it has a unique root, the **crossing threshold** `s₀ ∈ (2 log 3, 4 log 2)`. Below the threshold
  every crossing pair has negative conductance; at the threshold only the balanced pair `x = −y` is
  neutral; above it the negative pairs are those with `cosh(e/2) > S(s)`, a collar along the axes.
* On the lattice the reflected pair `(−log a, log a)` has negative archimedean conductance exactly
  for `a ∈ {2, 3}`.
* **Collar bound.** For `s ≥ 4 log 2` a negative crossing pair satisfies `min(|x|, y) < 6 e^{−3s/4}`.
-/

open RHTower Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The archimedean part of the gauge-free pair kernel, `ω(|x − y|) + sinh(x/2) sinh(y/2)`. -/
def archPairKernel (x y : ℝ) : ℝ :=
  archLevyDensity |x - y| + Real.sinh (x / 2) * Real.sinh (y / 2)

/-- The crossing symbol `S(s) = cosh(s/2) − 2 ω(s)`. -/
def crossingSymbol (s : ℝ) : ℝ := Real.cosh (s / 2) - 2 * archLevyDensity s

theorem archPairKernel_comm (x y : ℝ) : archPairKernel x y = archPairKernel y x := by
  unfold archPairKernel
  rw [abs_sub_comm, mul_comm]

/-- Reflection symmetry `(x, y) ↦ (−y, −x)` of the kernel. -/
theorem archPairKernel_neg_neg (x y : ℝ) : archPairKernel (-y) (-x) = archPairKernel x y := by
  unfold archPairKernel
  have h1 : |-y - -x| = |x - y| := by
    rw [show -y - -x = -(y - x) by ring, abs_neg, abs_sub_comm]
  rw [h1, neg_div, neg_div, Real.sinh_neg, Real.sinh_neg, neg_mul_neg, mul_comm]

/-! ### Hyperbolic product-to-sum identities -/

theorem sinh_mul_sinh (A B : ℝ) :
    Real.sinh A * Real.sinh B = (Real.cosh (A + B) - Real.cosh (A - B)) / 2 := by
  rw [Real.cosh_add, Real.cosh_sub]
  ring

theorem cosh_sub_cosh (u v : ℝ) :
    Real.cosh u - Real.cosh v = 2 * Real.sinh ((u + v) / 2) * Real.sinh ((u - v) / 2) := by
  have h := sinh_mul_sinh ((u + v) / 2) ((u - v) / 2)
  rw [show (u + v) / 2 + (u - v) / 2 = u by ring, show (u + v) / 2 - (u - v) / 2 = v by ring] at h
  linarith

/-! ### Same-side pairs -/

/-- Same-side pairs have positive archimedean kernel: both terms are positive. -/
theorem archPairKernel_pos_of_sameSide {x y : ℝ} (hxy : 0 < x * y) (hne : x ≠ y) :
    0 < archPairKernel x y := by
  unfold archPairKernel
  have h1 : 0 < archLevyDensity |x - y| :=
    archLevyDensity_pos (abs_pos.mpr (sub_ne_zero.mpr hne))
  have h2 : 0 < Real.sinh (x / 2) * Real.sinh (y / 2) := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact mul_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.sinh_pos_iff.mpr (by linarith))
    · exact mul_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr (by linarith))
        (Real.sinh_neg_iff.mpr (by linarith))
  linarith

/-! ### Crossing pairs: the symbol form -/

/-- For `x < y`, `k_arch(x, y) = ω(y − x) + (cosh((x+y)/2) − cosh((y−x)/2))/2`. -/
theorem archPairKernel_eq_of_lt {x y : ℝ} (hxy : x < y) :
    archPairKernel x y =
      archLevyDensity (y - x) + (Real.cosh ((x + y) / 2) - Real.cosh ((y - x) / 2)) / 2 := by
  unfold archPairKernel
  rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hxy), sinh_mul_sinh,
    show x / 2 + y / 2 = (x + y) / 2 by ring, show x / 2 - y / 2 = -((y - x) / 2) by ring,
    Real.cosh_neg]

/-- **Sign law.** For `x < y` the kernel is positive iff `cosh((x+y)/2)` exceeds the symbol at
`s = y − x`. On a crossing pair this is the condition for negative conductance. -/
theorem archPairKernel_pos_iff {x y : ℝ} (hxy : x < y) :
    0 < archPairKernel x y ↔ crossingSymbol (y - x) < Real.cosh ((x + y) / 2) := by
  rw [archPairKernel_eq_of_lt hxy]
  unfold crossingSymbol
  constructor <;> intro h <;> linarith

theorem archPairKernel_eq_zero_iff {x y : ℝ} (hxy : x < y) :
    archPairKernel x y = 0 ↔ crossingSymbol (y - x) = Real.cosh ((x + y) / 2) := by
  rw [archPairKernel_eq_of_lt hxy]
  unfold crossingSymbol
  constructor <;> intro h <;> linarith

theorem archPairKernel_neg_iff {x y : ℝ} (hxy : x < y) :
    archPairKernel x y < 0 ↔ Real.cosh ((x + y) / 2) < crossingSymbol (y - x) := by
  rw [archPairKernel_eq_of_lt hxy]
  unfold crossingSymbol
  constructor <;> intro h <;> linarith

/-! ### The crossing symbol -/

theorem crossingSymbol_strictMonoOn : StrictMonoOn crossingSymbol (Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  unfold crossingSymbol
  have h1 : Real.cosh (a / 2) < Real.cosh (b / 2) :=
    Real.cosh_strictMonoOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) (by linarith)
  have h2 : archLevyDensity b < archLevyDensity a := strictAntiOn_archLevyDensity ha hb hab
  linarith

theorem continuousOn_archLevyDensity_Ioi : ContinuousOn archLevyDensity (Ioi 0) := by
  unfold archLevyDensity
  apply ContinuousOn.div
  · exact (Real.continuous_exp.comp (continuous_id.neg.div_const 2)).continuousOn
  · exact (continuous_const.sub
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
  · intro s hs
    have : Real.exp (-2 * s) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith [mem_Ioi.mp hs])
    linarith

theorem continuousOn_crossingSymbol : ContinuousOn crossingSymbol (Ioi 0) := by
  unfold crossingSymbol
  exact (Real.continuous_cosh.comp (continuous_id.div_const 2)).continuousOn.sub
    (continuousOn_const.mul continuousOn_archLevyDensity_Ioi)

/-- `S(2 log 3) = 119/120`. -/
theorem crossingSymbol_two_log_three : crossingSymbol (2 * Real.log 3) = 119 / 120 := by
  unfold crossingSymbol archLevyDensity
  have h3 : (0 : ℝ) < 3 := by norm_num
  have e1 : 2 * Real.log 3 / 2 = Real.log 3 := by ring
  have e2 : -(2 * Real.log 3) / 2 = -Real.log 3 := by ring
  have e3 : -2 * (2 * Real.log 3) = -Real.log ((3 : ℝ) ^ 4) := by
    rw [Real.log_pow]; push_cast; ring
  rw [e1, e2, e3, Real.cosh_eq, Real.exp_neg, Real.exp_neg, Real.exp_log h3,
    Real.exp_log (by norm_num)]
  norm_num

/-- `S(4 log 2) = 3311/2040`. -/
theorem crossingSymbol_four_log_two : crossingSymbol (4 * Real.log 2) = 3311 / 2040 := by
  unfold crossingSymbol archLevyDensity
  have e1 : 4 * Real.log 2 / 2 = Real.log ((2 : ℝ) ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  have e2 : -(4 * Real.log 2) / 2 = -Real.log ((2 : ℝ) ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  have e3 : -2 * (4 * Real.log 2) = -Real.log ((2 : ℝ) ^ 8) := by
    rw [Real.log_pow]; push_cast; ring
  rw [e1, e2, e3, Real.cosh_eq, Real.exp_neg, Real.exp_neg, Real.exp_log (by norm_num),
    Real.exp_log (by norm_num)]
  norm_num

theorem two_mul_log_three_pos : 0 < 2 * Real.log 3 := by
  have : 0 < Real.log 3 := Real.log_pos (by norm_num)
  linarith

theorem log_four_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

theorem two_mul_log_three_lt_four_mul_log_two : 2 * Real.log 3 < 4 * Real.log 2 := by
  have : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [log_four_eq] at this
  linarith

/-- The symbol crosses `1` in `(2 log 3, 4 log 2)`. -/
theorem exists_crossingThreshold :
    ∃ s, s ∈ Ioo (2 * Real.log 3) (4 * Real.log 2) ∧ crossingSymbol s = 1 := by
  have hlt := two_mul_log_three_lt_four_mul_log_two
  have hcont : ContinuousOn crossingSymbol (Icc (2 * Real.log 3) (4 * Real.log 2)) :=
    continuousOn_crossingSymbol.mono fun s hs =>
      mem_Ioi.mpr (lt_of_lt_of_le two_mul_log_three_pos hs.1)
  have hmem : (1 : ℝ) ∈ Ioo (crossingSymbol (2 * Real.log 3)) (crossingSymbol (4 * Real.log 2)) := by
    rw [crossingSymbol_two_log_three, crossingSymbol_four_log_two]
    constructor <;> norm_num
  obtain ⟨s, hs, hs1⟩ := intermediate_value_Ioo hlt.le hcont hmem
  exact ⟨s, hs, hs1⟩

/-- The crossing threshold `s₀`: the unique positive root of the crossing symbol. -/
def crossingThreshold : ℝ := Classical.choose exists_crossingThreshold

theorem crossingThreshold_mem : crossingThreshold ∈ Ioo (2 * Real.log 3) (4 * Real.log 2) :=
  (Classical.choose_spec exists_crossingThreshold).1

theorem crossingSymbol_crossingThreshold : crossingSymbol crossingThreshold = 1 :=
  (Classical.choose_spec exists_crossingThreshold).2

theorem crossingThreshold_pos : 0 < crossingThreshold :=
  lt_trans two_mul_log_three_pos crossingThreshold_mem.1

theorem crossingSymbol_lt_one_iff {s : ℝ} (hs : 0 < s) :
    crossingSymbol s < 1 ↔ s < crossingThreshold := by
  rw [← crossingSymbol_crossingThreshold]
  exact crossingSymbol_strictMonoOn.lt_iff_lt hs crossingThreshold_pos

theorem one_lt_crossingSymbol_iff {s : ℝ} (hs : 0 < s) :
    1 < crossingSymbol s ↔ crossingThreshold < s := by
  rw [← crossingSymbol_crossingThreshold]
  exact crossingSymbol_strictMonoOn.lt_iff_lt crossingThreshold_pos hs

/-- Uniqueness of the root. -/
theorem eq_crossingThreshold_of_crossingSymbol_eq_one {s : ℝ} (hs : 0 < s)
    (h : crossingSymbol s = 1) : s = crossingThreshold :=
  crossingSymbol_strictMonoOn.injOn hs crossingThreshold_pos
    (h.trans crossingSymbol_crossingThreshold.symm)

/-! ### The sign law in threshold form -/

/-- Below the threshold every pair `x < y` with `y − x < s₀` has positive kernel; on crossing
pairs this is negative conductance. -/
theorem archPairKernel_pos_of_lt_threshold {x y : ℝ} (hxy : x < y)
    (hs : y - x < crossingThreshold) : 0 < archPairKernel x y := by
  rw [archPairKernel_pos_iff hxy]
  have h1 : crossingSymbol (y - x) < 1 := (crossingSymbol_lt_one_iff (sub_pos.mpr hxy)).mpr hs
  exact lt_of_lt_of_le h1 (Real.one_le_cosh _)

/-- At the threshold the kernel is positive exactly off the balanced pair `x + y = 0`. -/
theorem archPairKernel_pos_iff_of_eq_threshold {x y : ℝ} (hxy : x < y)
    (hs : y - x = crossingThreshold) : 0 < archPairKernel x y ↔ x + y ≠ 0 := by
  rw [archPairKernel_pos_iff hxy, hs, crossingSymbol_crossingThreshold]
  constructor
  · intro h hxy0
    rw [hxy0, zero_div, Real.cosh_zero] at h
    exact lt_irrefl _ h
  · intro h
    rw [← Real.cosh_zero]
    exact Real.cosh_lt_cosh.mpr (by rw [abs_zero]; exact abs_pos.mpr (div_ne_zero h two_ne_zero))

/-- The balanced pair `(−s/2, s/2)` is neutral at the threshold and has negative kernel beyond it. -/
theorem archPairKernel_balanced_neg_iff {s : ℝ} (hs : 0 < s) :
    archPairKernel (-(s / 2)) (s / 2) < 0 ↔ crossingThreshold < s := by
  rw [archPairKernel_neg_iff (by linarith), show -(s / 2) + s / 2 = 0 by ring, zero_div,
    Real.cosh_zero, show s / 2 - -(s / 2) = s by ring]
  exact one_lt_crossingSymbol_iff hs

/-! ### The reflected lattice pair -/

/-- **Reflection law.** The reflected lattice pair `(−log a, log a)`, `a ≥ 2`, has positive
archimedean kernel, that is negative conductance, exactly for `a ∈ {2, 3}`. -/
theorem archPairKernel_reflection_pos_iff {a : ℕ} (ha : 2 ≤ a) :
    0 < archPairKernel (-Real.log a) (Real.log a) ↔ a ≤ 3 := by
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (by omega : 1 < a)
  have hla : 0 < Real.log a := Real.log_pos ha1
  have hxy : -Real.log a < Real.log a := by linarith
  rw [archPairKernel_pos_iff hxy, show -Real.log a + Real.log a = 0 by ring, zero_div,
    Real.cosh_zero, show Real.log a - -Real.log a = 2 * Real.log a by ring,
    crossingSymbol_lt_one_iff (by linarith)]
  constructor
  · intro h
    by_contra h4
    have h4' : (4 : ℝ) ≤ a := by exact_mod_cast (by omega : 4 ≤ a)
    have : Real.log (4 : ℝ) ≤ Real.log a := Real.log_le_log (by norm_num) h4'
    rw [log_four_eq] at this
    linarith [crossingThreshold_mem.2]
  · intro h
    have h3 : (a : ℝ) ≤ 3 := by exact_mod_cast h
    have : Real.log a ≤ Real.log 3 := Real.log_le_log (by linarith) h3
    linarith [crossingThreshold_mem.1]

/-! ### The collar bound -/

/-- Sharper archimedean bound beyond `4 log 2`: `ω(s) ≤ (256/255) e^{−s/2}`. -/
theorem archLevyDensity_le_of_four_log_two_le {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    archLevyDensity s ≤ 256 / 255 * Real.exp (-s / 2) := by
  have hexp : Real.exp (-2 * s) ≤ 1 / 256 := by
    have h := Real.exp_le_exp.mpr (show -2 * s ≤ -Real.log ((2 : ℝ) ^ 8) by
      rw [Real.log_pow]; push_cast; linarith)
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at h
    norm_num at h ⊢
    linarith
  unfold archLevyDensity
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Real.exp_pos (-s / 2)]

/-- `e^{−s/2} ≤ 1/4` for `s ≥ 4 log 2`. -/
theorem exp_neg_half_le_of_four_log_two_le {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    Real.exp (-s / 2) ≤ 1 / 4 := by
  have h := Real.exp_le_exp.mpr (show -s / 2 ≤ -Real.log ((2 : ℝ) ^ 2) by
    rw [Real.log_pow]; push_cast; linarith)
  rw [Real.exp_neg, Real.exp_log (by norm_num)] at h
  norm_num at h ⊢
  linarith

/-- **Collar bound.** Beyond `4 log 2`, a crossing pair with negative conductance lies within
`6 e^{−3s/4}` of an axis: `min(|x|, y) < 6 e^{−3(y−x)/4}`. -/
theorem min_lt_of_archPairKernel_pos {x y : ℝ} (hx : x < 0) (hy : 0 < y)
    (hs : 4 * Real.log 2 ≤ y - x) (hk : 0 < archPairKernel x y) :
    min (-x) y < 6 * Real.exp (-(3 * (y - x)) / 4) := by
  set s := y - x with hs_def
  set c := min (-x) y with hc_def
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hs0 : 0 < s := by linarith
  have hc0 : 0 ≤ c := le_min (by linarith) hy.le
  have hcs : 2 * c ≤ s := by
    rcases le_total (-x) y with h | h
    · rw [hc_def, min_eq_left h]; linarith
    · rw [hc_def, min_eq_right h]; linarith
  have habs : |x + y| = s - 2 * c := by
    rcases le_total (-x) y with h | h
    · rw [hc_def, min_eq_left h, abs_of_nonneg (by linarith)]; ring
    · rw [hc_def, min_eq_right h, abs_of_nonpos (by linarith)]; ring
  have hkey : Real.cosh (s / 2) - Real.cosh ((s - 2 * c) / 2) < 2 * archLevyDensity s := by
    have h := (archPairKernel_pos_iff (by linarith : x < y)).mp hk
    unfold crossingSymbol at h
    have hc' : Real.cosh ((x + y) / 2) = Real.cosh ((s - 2 * c) / 2) := by
      rw [← Real.cosh_abs ((x + y) / 2), abs_div, habs, abs_two]
    rw [hc'] at h
    linarith
  have hω : archLevyDensity s ≤ 256 / 255 * Real.exp (-s / 2) :=
    archLevyDensity_le_of_four_log_two_le hs
  have hexp : Real.exp (-s / 2) ≤ 1 / 4 := exp_neg_half_le_of_four_log_two_le hs
  rcases le_or_gt c (s / 4) with hc | hc
  · -- the pair is close to an axis: `c sinh(s/4) ≤ cosh(s/2) − cosh(s/2 − c) < 2ω(s)`
    have hdiff : Real.cosh (s / 2) - Real.cosh ((s - 2 * c) / 2) =
        2 * Real.sinh ((s - c) / 2) * Real.sinh (c / 2) := by
      rw [cosh_sub_cosh, show (s / 2 + (s - 2 * c) / 2) / 2 = (s - c) / 2 by ring,
        show (s / 2 - (s - 2 * c) / 2) / 2 = c / 2 by ring]
    have hsinh4 : 0 < Real.sinh (s / 4) := Real.sinh_pos_iff.mpr (by linarith)
    have h1 : Real.sinh (s / 4) ≤ Real.sinh ((s - c) / 2) :=
      Real.sinh_strictMono.monotone (by linarith)
    have h2 : c / 2 ≤ Real.sinh (c / 2) := Real.self_le_sinh_iff.mpr (by linarith)
    have h3 : c * Real.sinh (s / 4) ≤ Real.cosh (s / 2) - Real.cosh ((s - 2 * c) / 2) := by
      rw [hdiff]
      calc c * Real.sinh (s / 4) = 2 * Real.sinh (s / 4) * (c / 2) := by ring
        _ ≤ 2 * Real.sinh ((s - c) / 2) * Real.sinh (c / 2) :=
          mul_le_mul (by linarith) h2 (by linarith) (by linarith)
    -- `sinh(s/4) ≥ (3/8) e^{s/4}`
    have hE := Real.exp_pos (s / 4)
    have hF := Real.exp_pos (-(3 * s) / 4)
    have hEF : Real.exp (-s / 2) = Real.exp (-(3 * s) / 4) * Real.exp (s / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    have hsinh_lower : 3 / 8 * Real.exp (s / 4) ≤ Real.sinh (s / 4) := by
      rw [Real.sinh_eq]
      have e : Real.exp (-(s / 4)) = Real.exp (s / 4) * Real.exp (-s / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e]
      nlinarith [hE, hexp]
    have hmain : c * (3 / 8) * Real.exp (s / 4) <
        512 / 255 * Real.exp (-(3 * s) / 4) * Real.exp (s / 4) := by
      calc c * (3 / 8) * Real.exp (s / 4) = c * (3 / 8 * Real.exp (s / 4)) := by ring
        _ ≤ c * Real.sinh (s / 4) := mul_le_mul_of_nonneg_left hsinh_lower hc0
        _ < 2 * archLevyDensity s := lt_of_le_of_lt h3 hkey
        _ ≤ 512 / 255 * Real.exp (-s / 2) := by linarith
        _ = 512 / 255 * Real.exp (-(3 * s) / 4) * Real.exp (s / 4) := by rw [hEF]; ring
    have hdiv : c * (3 / 8) < 512 / 255 * Real.exp (-(3 * s) / 4) :=
      lt_of_mul_lt_mul_right hmain hE.le
    nlinarith [hF]
  · -- a balanced pair far out: `cosh(s/2) − cosh(s/4) ≥ 3s²/32` beats `2ω(s) ≤ 128/255`
    exfalso
    have hle : Real.cosh ((s - 2 * c) / 2) ≤ Real.cosh (s / 4) :=
      Real.cosh_strictMonoOn.monotoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith))
        (by linarith)
    have hdiff : Real.cosh (s / 2) - Real.cosh (s / 4) =
        2 * Real.sinh (3 * s / 8) * Real.sinh (s / 8) := by
      rw [cosh_sub_cosh, show (s / 2 + s / 4) / 2 = 3 * s / 8 by ring,
        show (s / 2 - s / 4) / 2 = s / 8 by ring]
    have h1 : 3 * s / 8 ≤ Real.sinh (3 * s / 8) := Real.self_le_sinh_iff.mpr (by linarith)
    have h2 : s / 8 ≤ Real.sinh (s / 8) := Real.self_le_sinh_iff.mpr (by linarith)
    have h3 : 3 * s ^ 2 / 32 ≤ Real.cosh (s / 2) - Real.cosh (s / 4) := by
      rw [hdiff]
      nlinarith [mul_le_mul h1 h2 (by linarith) (by linarith)]
    nlinarith [hkey, hω, hexp, hle, h3, hs0]

end GaloisForLFunctions.ArithmeticIncidencePositivity
