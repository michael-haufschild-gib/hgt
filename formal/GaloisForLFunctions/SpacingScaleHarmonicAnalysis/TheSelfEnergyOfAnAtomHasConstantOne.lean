import GaloisForLFunctions.ArithmeticElectrostatics.TheWeilFormAtAtomicResolution

/-!
# The self-energy of an atom has constant one

The archimedean form is the Lévy form `archForm f = 2θ′(0)‖f‖² + ∫_0^∞ ω(y)‖f − f(· + y)‖² dy` with
the Lévy density `ω(y) = e^{−y/2}/(1 − e^{−2y})`, and `ω(y) ∼ 1/(2y)` at `0`. A bump of width `w`
therefore costs `log(1/w)` per unit mass, with **constant one** — the constant of the covariant
counterterm `log N + O(1)` of the prime place (RAPT). This file proves the two density bounds and
the resulting self-energy.

* **Sharp lower density bound** (`archLevyDensity_ge_inv_two_mul`): `ω(y) ≥ 1/(2y)` on `(0, 1]`,
  equivalently `sinh y ≤ y e^{y/2}`, from the cubic Taylor bounds of `e^{±y}`.
* **Upper density bound** (`archLevyDensity_le_exp_div`): `ω(y) ≤ e^{y/2}/(2y)` for `y > 0`,
  equivalently `y ≤ sinh y`.
* **The window integral** (`log_div_le_two_mul_setIntegral_archLevyDensity`):
  `log(s/w) ≤ 2 ∫_{(w, s]} ω` for `0 < w ≤ s ≤ 1`.
* **Lévy gain with constant one** (`levyEnergy_ge_log_of_disjoint_shifts`): if every shift by
  `y ∈ (w, s]` moves the support of `f` off itself, the Lévy energy is at least `log(s/w)‖f‖²`.
* **The self-energy of an atom** (`levyEnergy_atom_ge`, `archForm_atom_ge`): a bump supported in
  `[0, w]`, `w ≤ 1`, has `levyEnergy ≥ log(1/w)‖g‖²` and `archForm ≥ (2θ′(0) + log(1/w))‖g‖²`.

The corpus bound `ω(y) ≥ e^{−1/2}/(2y)` gives `e^{−1/2} log(1/w)`, which falls short of the prime
counterterm `log N` at every width `w ≥ N^{−e^{1/2}}`; constant one is what reaches the spacing.
-/

noncomputable section

open MeasureTheory Set RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

/-! ### The Lévy density -/

/-- `sinh y ≤ y e^{y/2}` on `[0, 1]`, in exponential form: `e^y − e^{−y} ≤ 2y e^{y/2}`. -/
theorem exp_sub_exp_neg_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp y - Real.exp (-y) ≤ 2 * y * Real.exp (y / 2) := by
  -- cubic Taylor bounds: `e^y ≤ 1 + y + y²/2 + (2/9)y³`, `e^{−y} ≥ 1 − y + y²/2 − (2/9)y³`
  have hup := Real.exp_bound' hy0 hy1 (n := 3) (by norm_num)
  have hlo := Real.exp_bound (x := -y) (by rw [abs_neg, abs_of_nonneg hy0]; exact hy1)
    (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one,
    Nat.cast_ofNat] at hup hlo
  rw [abs_neg, abs_of_nonneg hy0, abs_le] at hlo
  norm_num at hup hlo
  have hhalf := Real.add_one_le_exp (y / 2)
  nlinarith [hlo.1, sq_nonneg y, mul_nonneg hy0 (sq_nonneg y)]

/-- **Sharp lower density bound**: `ω(y) ≥ 1/(2y)` on `(0, 1]`. -/
theorem archLevyDensity_ge_inv_two_mul {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    1 / (2 * y) ≤ archLevyDensity y := by
  unfold archLevyDensity
  have hd : 0 < 1 - Real.exp (-2 * y) := by
    have : Real.exp (-2 * y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [div_le_div_iff₀ (by positivity) hd, one_mul]
  -- multiply `e^y − e^{−y} ≤ 2y e^{y/2}` by `e^{−y}`
  have key := exp_sub_exp_neg_le hy0.le hy1
  have e1 : Real.exp (-2 * y) = Real.exp (-y) * Real.exp (-y) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-y / 2) = Real.exp (-y) * Real.exp (y / 2) := by
    rw [← Real.exp_add]; ring_nf
  have e3 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-y) := Real.exp_pos _
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left key hpos.le]

/-- **Upper density bound**: `ω(y) ≤ e^{y/2}/(2y)` for `y > 0`. -/
theorem archLevyDensity_le_exp_div {y : ℝ} (hy0 : 0 < y) :
    archLevyDensity y ≤ Real.exp (y / 2) / (2 * y) := by
  unfold archLevyDensity
  have hd : 0 < 1 - Real.exp (-2 * y) := by
    have : Real.exp (-2 * y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [div_le_div_iff₀ hd (by positivity)]
  -- `2y ≤ e^y − e^{−y}`, multiplied by `e^{−y/2}`
  have hs : 2 * y ≤ Real.exp y - Real.exp (-y) := by
    have := Real.self_le_sinh_iff.mpr hy0.le
    rw [Real.sinh_eq] at this
    linarith
  have e1 : Real.exp (y / 2) * Real.exp (-2 * y) = Real.exp (-y / 2) * Real.exp (-y) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (-y / 2) * Real.exp y = Real.exp (y / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hpos : 0 < Real.exp (-y / 2) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left hs hpos.le]

/-- `ω(y) ≤ e^{1/2}/(2y)` on `(0, 1]`. -/
theorem archLevyDensity_le_sqrt_e_div {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    archLevyDensity y ≤ Real.exp (1 / 2) / (2 * y) :=
  (archLevyDensity_le_exp_div hy0).trans
    (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity))

/-! ### The window integral -/

theorem integrableOn_archLevyDensity_Ioc {w s : ℝ} (hw : 0 < w) :
    IntegrableOn archLevyDensity (Ioc w s) := by
  have hc : ContinuousOn archLevyDensity (Icc w s) := fun y hy => by
    have hy0 : 0 < y := lt_of_lt_of_le hw hy.1
    have h2 : 1 - Real.exp (-2 * y) ≠ 0 := by
      have : Real.exp (-2 * y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    unfold archLevyDensity
    exact (ContinuousAt.div (f := fun x : ℝ => Real.exp (-x / 2))
      (g := fun x : ℝ => 1 - Real.exp (-2 * x)) (by fun_prop) (by fun_prop) h2).continuousWithinAt
  exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

/-- **The window integral**: `log(s/w) ≤ 2 ∫_{(w, s]} ω` for `0 < w ≤ s ≤ 1`. -/
theorem log_div_le_two_mul_setIntegral_archLevyDensity {w s : ℝ} (hw : 0 < w) (hws : w ≤ s)
    (hs1 : s ≤ 1) : Real.log (s / w) ≤ 2 * ∫ y in Ioc w s, archLevyDensity y := by
  have hinv : IntegrableOn (fun y : ℝ => y⁻¹) (Ioc w s) := by
    have hc : ContinuousOn (fun y : ℝ => y⁻¹) (Icc w s) :=
      continuousOn_inv₀.mono fun y hy => ne_of_gt (lt_of_lt_of_le hw hy.1)
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hmono : ∫ y in Ioc w s, (1 / 2 : ℝ) * y⁻¹ ≤ ∫ y in Ioc w s, archLevyDensity y :=
    setIntegral_mono_on (hinv.const_mul _) (integrableOn_archLevyDensity_Ioc hw)
      measurableSet_Ioc fun y hy => by
        have := archLevyDensity_ge_inv_two_mul (lt_trans hw hy.1) (hy.2.trans hs1)
        rw [one_div, mul_inv] at this
        linarith
  have hval : ∫ y in Ioc w s, (1 / 2 : ℝ) * y⁻¹ = Real.log (s / w) / 2 := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hws,
      integral_inv_of_pos hw (lt_of_lt_of_le hw hws)]
    ring
  linarith

/-! ### The Lévy gain with constant one -/

/-- **Lévy gain with constant one**: `levyEnergy f ≥ log(s/w) ∫ f²` when every shift by
`y ∈ (w, s]`, `s ≤ 1`, moves the support of `f` off itself. -/
theorem levyEnergy_ge_log_of_disjoint_shifts {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w s : ℝ} (hw0 : 0 < w) (hws : w ≤ s) (hs1 : s ≤ 1)
    (hdisj : ∀ y ∈ Ioc w s, ∀ u, f u * f (u + y) = 0) :
    Real.log (s / w) * ∫ u, f u ^ 2 ≤ levyEnergy f := by
  set M : ℝ := ∫ u, f u ^ 2
  set L : ℝ → ℝ := fun y => archLevyDensity y * ∫ u, (f u - f (u + y)) ^ 2
  have hLint : IntegrableOn L (Ioi 0) := integrableOn_levyIntegrand hf hfc
  have hsub : Ioc w s ⊆ Ioi 0 := fun y hy => lt_trans hw0 hy.1
  have hstep1 : ∫ y in Ioc w s, L y ≤ ∫ y in Ioi 0, L y :=
    setIntegral_mono_set hLint (levyIntegrand_nonneg f) (Filter.Eventually.of_forall hsub)
  have hM : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  have hpt : ∀ y ∈ Ioc w s, L y = 2 * M * archLevyDensity y := fun y hy => by
    simp only [L]
    rw [ArithmeticElectrostatics.integral_sq_sub_shift_of_disjoint hf.continuous hfc (hdisj y hy)]
    ring
  have hstep2 : ∫ y in Ioc w s, L y = 2 * M * ∫ y in Ioc w s, archLevyDensity y := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc hpt
  have hwin := log_div_le_two_mul_setIntegral_archLevyDensity hw0 hws hs1
  unfold levyEnergy
  nlinarith

/-! ### The self-energy of an atom -/

variable {g : ℝ → ℝ} {w : ℝ}

/-- A bump supported in `[0, w]` is moved off itself by every shift `y > w`. -/
theorem bump_mul_shift_eq_zero (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) {y : ℝ} (hy : w < y)
    (u : ℝ) : g u * g (u + y) = 0 := by
  by_cases hu : u ∈ Icc 0 w
  · rw [hgsupp (u + y) fun h => by linarith [hu.1, h.2], mul_zero]
  · rw [hgsupp u hu, zero_mul]

/-- **The Lévy self-energy of an atom**: `levyEnergy g ≥ log(1/w) ‖g‖²` for a bump of width
`w ≤ 1`. -/
theorem levyEnergy_atom_ge (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    Real.log (1 / w) * ∫ u, g u ^ 2 ≤ levyEnergy g :=
  levyEnergy_ge_log_of_disjoint_shifts hg hgc hw0 hw1 le_rfl fun _ hy u =>
    bump_mul_shift_eq_zero hgsupp hy.1 u

/-- **The archimedean self-energy of an atom**: `archForm g ≥ (2θ′(0) + log(1/w)) ‖g‖²`. -/
theorem archForm_atom_ge (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    (2 * gammaHardyPhaseRate 0 + Real.log (1 / w)) * ∫ u, g u ^ 2 ≤ archForm g := by
  rw [archForm_eq_levyEnergy hg hgc]
  have := levyEnergy_atom_ge hg hgc hgsupp hw0 hw1
  linarith

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
