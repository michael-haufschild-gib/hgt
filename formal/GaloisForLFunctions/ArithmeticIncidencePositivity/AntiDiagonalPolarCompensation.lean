import GaloisForLFunctions.ArithmeticIncidencePositivity.CrossingConductanceSignLaw
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms

/-!
# Polar compensation on the anti-diagonals

The continuum part of the incidence picture. A crossing pair `(x, y)`, `x < 0 < y`, lies on the
**anti-diagonal of sum** `s = |x| + y`; parametrize it as `(−a, s − a)`, `0 < a < s`. In an odd gauge
`M`, positive on `(0, ∞)`, the pair carries three conductances per unit `|M(−a) M(s − a)|`:

* the **prime atom** `Λ(n)/√n` when `s = log n` (a Dirac mass along the whole segment), negative;
* the **archimedean density** `ω(s)`, negative;
* the **polar weight** `sinh(a/2) sinh((s − a)/2)` from the variance term of the pole, positive.

The pole is the only positive source on crossing pairs. This module measures what it pays.

* The polar weight equals `(cosh(s/2) − cosh(s/2 − a))/2`; it vanishes at both axes `a = 0`, `a = s`,
  is symmetric under `a ↦ s − a`, and attains its maximum `sinh²(s/4)` at the midpoint.
* **Pointwise payment of the archimedean density.** Off the collar, that is where
  `k_arch(x, y) ≤ 0`, the polar weight is at least `ω(|x| + y)`, so the variance density dominates
  the archimedean crossing density pair by pair, and integrated over any profile
  (`lintegral_archCrossingDensity_offCollar_le`). The archimedean negativity that survives the pole
  lives on the collar only.
* **The anti-diagonal of a small prime power is unpaid throughout.** For `n ≤ 9` the whole segment
  `|x| + y = log n` has negative archimedean conductance (`log 9 = 2 log 3 < s₀`); for `n ≥ 16` only
  the two end collars of length `< 6 n^{−3/4}` do.
* **The prime atom is never paid at the axes.** The ratio of the polar weight to the atom tends to
  zero at both ends of every anti-diagonal; the best the pole can do is at the midpoint, where the
  ratio of atom to polar weight is the **payment scale** `4Λ(n)/(√n − 1)²`, which decays like
  `16 log n / n`. The prime obstruction is an axis phenomenon of small `n`.
-/

open RHTower Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The polar weight along an anti-diagonal -/

/-- The polar weight of the crossing pair `(−a, s − a)`: `sinh(a/2) sinh((s − a)/2)`. The variance
density of the pair in an odd gauge is `|M(−a) M(s − a)|` times this weight. -/
def crossingPolarWeight (s a : ℝ) : ℝ := Real.sinh (a / 2) * Real.sinh ((s - a) / 2)

theorem crossingPolarWeight_eq (s a : ℝ) :
    crossingPolarWeight s a = (Real.cosh (s / 2) - Real.cosh (s / 2 - a)) / 2 := by
  unfold crossingPolarWeight
  rw [sinh_mul_sinh, show a / 2 + (s - a) / 2 = s / 2 by ring,
    show a / 2 - (s - a) / 2 = -(s / 2 - a) by ring, Real.cosh_neg]

theorem crossingPolarWeight_symm (s a : ℝ) :
    crossingPolarWeight s (s - a) = crossingPolarWeight s a := by
  unfold crossingPolarWeight
  rw [show s - (s - a) = a by ring, mul_comm]

theorem crossingPolarWeight_zero_left (s : ℝ) : crossingPolarWeight s 0 = 0 := by
  unfold crossingPolarWeight; simp

theorem crossingPolarWeight_zero_right (s : ℝ) : crossingPolarWeight s s = 0 := by
  unfold crossingPolarWeight; simp

theorem crossingPolarWeight_nonneg {s a : ℝ} (ha : 0 ≤ a) (has : a ≤ s) :
    0 ≤ crossingPolarWeight s a :=
  mul_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (Real.sinh_nonneg_iff.mpr (by linarith))

theorem crossingPolarWeight_pos {s a : ℝ} (ha : 0 < a) (has : a < s) :
    0 < crossingPolarWeight s a :=
  mul_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.sinh_pos_iff.mpr (by linarith))

/-- `cosh(s/2) − 1 = 2 sinh²(s/4)`. -/
theorem cosh_half_sub_one (s : ℝ) : Real.cosh (s / 2) - 1 = 2 * Real.sinh (s / 4) ^ 2 := by
  have h := Real.cosh_two_mul (s / 4)
  rw [show 2 * (s / 4) = s / 2 by ring, Real.cosh_sq] at h
  linarith

/-- At the midpoint the polar weight is `sinh²(s/4)`. -/
theorem crossingPolarWeight_midpoint (s : ℝ) :
    crossingPolarWeight s (s / 2) = Real.sinh (s / 4) ^ 2 := by
  rw [crossingPolarWeight_eq, show s / 2 - s / 2 = 0 by ring, Real.cosh_zero, cosh_half_sub_one]
  ring

/-- The midpoint is the maximum of the polar weight along the anti-diagonal. -/
theorem crossingPolarWeight_le_midpoint (s a : ℝ) :
    crossingPolarWeight s a ≤ Real.sinh (s / 4) ^ 2 := by
  rw [crossingPolarWeight_eq, ← crossingPolarWeight_midpoint, crossingPolarWeight_eq,
    show s / 2 - s / 2 = 0 by ring, Real.cosh_zero]
  linarith [Real.one_le_cosh (s / 2 - a)]

/-- Strictly below the midpoint value away from the midpoint. -/
theorem crossingPolarWeight_lt_midpoint {s a : ℝ} (ha : a ≠ s / 2) :
    crossingPolarWeight s a < Real.sinh (s / 4) ^ 2 := by
  rw [crossingPolarWeight_eq, ← crossingPolarWeight_midpoint, crossingPolarWeight_eq,
    show s / 2 - s / 2 = 0 by ring, Real.cosh_zero]
  have : 1 < Real.cosh (s / 2 - a) := by
    rw [← Real.cosh_zero]
    exact Real.cosh_lt_cosh.mpr (by rw [abs_zero]; exact abs_pos.mpr (sub_ne_zero.mpr
      (by intro h; exact ha h.symm)))
  linarith

/-- **Axis law.** The polar weight vanishes at the negative axis: no pole mass is available to pay
the prime atom near the ends of an anti-diagonal. -/
theorem tendsto_crossingPolarWeight_zero (s : ℝ) :
    Filter.Tendsto (fun a => crossingPolarWeight s a) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hc : Continuous fun a => crossingPolarWeight s a := by
    unfold crossingPolarWeight
    exact (Real.continuous_sinh.comp (continuous_id.div_const 2)).mul
      (Real.continuous_sinh.comp ((continuous_const.sub continuous_id).div_const 2))
  have h := hc.tendsto 0
  rw [crossingPolarWeight_zero_left] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

/-! ### The archimedean kernel along an anti-diagonal -/

/-- At the point `(−a, s − a)` of the anti-diagonal of sum `s`, `k_arch > 0 ⟺ S(s) < cosh(s/2 − a)`. -/
theorem archPairKernel_antiDiagonal_pos_iff {s : ℝ} (hs : 0 < s) (a : ℝ) :
    0 < archPairKernel (-a) (s - a) ↔ crossingSymbol s < Real.cosh (s / 2 - a) := by
  rw [archPairKernel_pos_iff (by linarith), show s - a - -a = s by ring,
    show (-a + (s - a)) / 2 = s / 2 - a by ring]

/-- Below the threshold the whole anti-diagonal has negative conductance. -/
theorem archPairKernel_antiDiagonal_pos_of_lt_threshold {s : ℝ} (hs0 : 0 < s)
    (hs : s < crossingThreshold) (a : ℝ) : 0 < archPairKernel (-a) (s - a) :=
  archPairKernel_pos_of_lt_threshold (by linarith) (by rw [show s - a - -a = s by ring]; exact hs)

/-- `log 9 = 2 log 3`. -/
theorem log_nine_eq : Real.log (9 : ℝ) = 2 * Real.log 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

/-- **Small prime powers are unpaid throughout.** For `2 ≤ n ≤ 9` every point of the anti-diagonal
`|x| + y = log n` has negative archimedean conductance. -/
theorem archPairKernel_antiDiagonal_pos_of_le_nine {n : ℕ} (hn2 : 2 ≤ n) (hn9 : n ≤ 9) (a : ℝ) :
    0 < archPairKernel (-a) (Real.log n - a) := by
  apply archPairKernel_antiDiagonal_pos_of_lt_threshold
    (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
  have h1 : Real.log (n : ℝ) ≤ Real.log 9 :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hn9)
  rw [log_nine_eq] at h1
  linarith [crossingThreshold_mem.1]

/-- **Large prime powers: collar only.** For `n ≥ 16` a point of the anti-diagonal of `n` with
negative archimedean conductance lies within `6 n^{−3/4}` of an axis. -/
theorem antiDiagonal_collar_of_sixteen_le {n : ℕ} (hn : 16 ≤ n) {a : ℝ} (ha : 0 < a)
    (has : a < Real.log n) (hk : 0 < archPairKernel (-a) (Real.log n - a)) :
    min a (Real.log n - a) < 6 * Real.exp (-(3 * Real.log n) / 4) := by
  have h16 : 4 * Real.log 2 ≤ (Real.log n - a) - -a := by
    have : Real.log (16 : ℝ) ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
    push_cast at this
    linarith
  have h := min_lt_of_archPairKernel_pos (by linarith) (by linarith) h16 hk
  have e : Real.log n - a - -a = Real.log n := by ring
  rw [e] at h
  simpa only [neg_neg] using h

/-! ### Pointwise polar payment of the archimedean crossing density -/

/-- Off the collar (`k_arch ≤ 0`) the polar weight of a crossing pair dominates the archimedean
density: `ω(y − x) ≤ sinh(−x/2) sinh(y/2)`. -/
theorem archLevyDensity_le_polar_of_kernel_nonpos {x y : ℝ} (hxy : x < y)
    (hk : archPairKernel x y ≤ 0) :
    archLevyDensity (y - x) ≤ Real.sinh (-x / 2) * Real.sinh (y / 2) := by
  unfold archPairKernel at hk
  rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hxy)] at hk
  rw [neg_div, Real.sinh_neg]
  linarith

/-- In a gauge with `M(x)M(y) ≤ 0` on the pair, the archimedean crossing conductance
`ω(y − x)|M(x)M(y)|` is at most the variance conductance `μ(x)μ(y)`, `μ = M sinh(·/2)`,
whenever `k_arch(x, y) ≤ 0`. -/
theorem archCrossing_le_variance_of_kernel_nonpos {M : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hM : M x * M y ≤ 0) (hk : archPairKernel x y ≤ 0) :
    archLevyDensity (y - x) * |M x * M y| ≤
      (M x * Real.sinh (x / 2)) * (M y * Real.sinh (y / 2)) := by
  have h := archLevyDensity_le_polar_of_kernel_nonpos hxy hk
  rw [neg_div, Real.sinh_neg] at h
  rw [abs_of_nonpos hM]
  calc archLevyDensity (y - x) * -(M x * M y)
      ≤ (-Real.sinh (x / 2) * Real.sinh (y / 2)) * -(M x * M y) :=
        mul_le_mul_of_nonneg_right h (by linarith)
    _ = (M x * Real.sinh (x / 2)) * (M y * Real.sinh (y / 2)) := by ring

/-- The off-collar crossing region: pairs `x < 0 < y` with `k_arch(x, y) ≤ 0`. -/
def offCollar : Set (ℝ × ℝ) := {p | p.1 < 0 ∧ 0 < p.2 ∧ archPairKernel p.1 p.2 ≤ 0}

theorem measurable_archPairKernel : Measurable fun p : ℝ × ℝ => archPairKernel p.1 p.2 := by
  unfold archPairKernel
  exact (measurable_archLevyDensity.comp
      (continuous_abs.measurable.comp (measurable_fst.sub measurable_snd))).add
    ((Real.continuous_sinh.measurable.comp (measurable_fst.div_const 2)).mul
      (Real.continuous_sinh.measurable.comp (measurable_snd.div_const 2)))

theorem measurableSet_offCollar : MeasurableSet offCollar := by
  unfold offCollar
  have h1 : MeasurableSet {p : ℝ × ℝ | p.1 < 0} :=
    measurableSet_lt measurable_fst measurable_const
  have h2 : MeasurableSet {p : ℝ × ℝ | 0 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  have h3 : MeasurableSet {p : ℝ × ℝ | archPairKernel p.1 p.2 ≤ 0} :=
    measurableSet_le measurable_archPairKernel measurable_const
  have e : {p : ℝ × ℝ | p.1 < 0 ∧ 0 < p.2 ∧ archPairKernel p.1 p.2 ≤ 0} =
      {p : ℝ × ℝ | p.1 < 0} ∩ ({p | 0 < p.2} ∩ {p | archPairKernel p.1 p.2 ≤ 0}) := by
    ext p; simp only [mem_setOf_eq, mem_inter_iff]
  rw [e]
  exact h1.inter (h2.inter h3)

/-- Archimedean crossing energy density of a profile `u` in a gauge `M` on the pair `p`:
`ω(|x − y|) |M(x)M(y)| (u(x) − u(y))²`. -/
def archCrossingDensity (M u : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  archLevyDensity |p.1 - p.2| * |M p.1 * M p.2| * (u p.1 - u p.2) ^ 2

/-- Variance (polar) energy density on the pair `p`: `μ(x)μ(y)(u(x) − u(y))²`, `μ = M sinh(·/2)`. -/
def varianceDensity (M u : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (M p.1 * Real.sinh (p.1 / 2)) * (M p.2 * Real.sinh (p.2 / 2)) * (u p.1 - u p.2) ^ 2

/-- **Polar payment off the collar.** In a gauge that is odd-type on crossing pairs
(`M(x)M(y) ≤ 0` for `x < 0 < y`), the archimedean crossing energy over the off-collar region is
dominated by the variance energy over the same region, for every profile `u`. -/
theorem lintegral_archCrossingDensity_offCollar_le {M u : ℝ → ℝ}
    (hM : ∀ x y : ℝ, x < 0 → 0 < y → M x * M y ≤ 0) :
    ∫⁻ p in offCollar, ENNReal.ofReal (archCrossingDensity M u p) ≤
      ∫⁻ p in offCollar, ENNReal.ofReal (varianceDensity M u p) := by
  refine setLIntegral_mono' measurableSet_offCollar fun p hp => ?_
  obtain ⟨h1, h2, h3⟩ := hp
  apply ENNReal.ofReal_le_ofReal
  unfold archCrossingDensity varianceDensity
  have hxy : p.1 < p.2 := by linarith
  have h := archCrossing_le_variance_of_kernel_nonpos hxy (hM _ _ h1 h2) h3
  rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hxy)]
  exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

/-! ### The prime atom against the pole -/

/-- The polar payment scale of the prime atom `n`: the ratio of the atom `Λ(n)/√n` to the maximal
polar weight `sinh²(log n / 4)` on its anti-diagonal. -/
def polarPaymentScale (n : ℕ) : ℝ := vonMangoldtAtom n / Real.sinh (Real.log n / 4) ^ 2

/-- `sinh²(log n / 4) = (√n − 1)² / (4√n)` for `n ≥ 1`. -/
theorem sinh_log_div_four_sq {n : ℕ} (hn : 1 ≤ n) :
    Real.sinh (Real.log n / 4) ^ 2 = (Real.sqrt n - 1) ^ 2 / (4 * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set r := Real.sqrt (Real.sqrt n) with hr_def
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hr : 0 < r := Real.sqrt_pos.mpr hsn
  have hr2 : r ^ 2 = Real.sqrt n := Real.sq_sqrt hsn.le
  have hr4 : r ^ 4 = n := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2, Real.sq_sqrt hn0.le]
  have hlog : Real.log n / 4 = Real.log r := by
    rw [← hr4, Real.log_pow]; push_cast; ring
  rw [hlog, Real.sinh_eq, Real.exp_neg, Real.exp_log hr, ← hr2]
  field_simp
  ring

/-- **Payment scale.** `polarPaymentScale n = 4 Λ(n) / (√n − 1)²` for `n ≥ 2`. -/
theorem polarPaymentScale_eq {n : ℕ} (hn : 2 ≤ n) :
    polarPaymentScale n =
      4 * (ArithmeticFunction.vonMangoldt n : ℝ) / (Real.sqrt n - 1) ^ 2 := by
  unfold polarPaymentScale vonMangoldtAtom
  rw [if_pos hn, sinh_log_div_four_sq (by omega)]
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hs : 1 < Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hn1
  have hne : Real.sqrt n - 1 ≠ 0 := by linarith
  field_simp

/-- The payment scale decays: `polarPaymentScale n ≤ 16 log n / n` for `n ≥ 4`. -/
theorem polarPaymentScale_le {n : ℕ} (hn : 4 ≤ n) :
    polarPaymentScale n ≤ 16 * Real.log n / n := by
  rw [polarPaymentScale_eq (by omega)]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs2 : 2 ≤ Real.sqrt n := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hsq : (n : ℝ) / 4 ≤ (Real.sqrt n - 1) ^ 2 := by
    have h : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
    nlinarith
  have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hpos : 0 < (Real.sqrt n - 1) ^ 2 := pow_pos (by linarith) 2
  calc 4 * (ArithmeticFunction.vonMangoldt n : ℝ) / (Real.sqrt n - 1) ^ 2
      ≤ 4 * Real.log n / (Real.sqrt n - 1) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) hpos.le
    _ ≤ 4 * Real.log n / ((n : ℝ) / 4) := by
        apply div_le_div_of_nonneg_left _ (by positivity) hsq
        have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
        linarith
    _ = 16 * Real.log n / n := by field_simp; ring

end GaloisForLFunctions.ArithmeticIncidencePositivity
