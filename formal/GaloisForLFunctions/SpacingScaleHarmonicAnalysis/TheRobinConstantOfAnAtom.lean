import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomIsExactlyLogarithmic

/-!
# The Robin constant of an atom

`TheSelfEnergyOfAnAtomIsExactlyLogarithmic` sandwiches the self-energy of an atom of width `w`
between `log(1/w)‖g‖²` and `(log(1/w) + C₀)‖g‖² + O(w)`. This file computes the constant: the
self-energy is `log(1/w)` plus a universal archimedean constant plus a shape term, up to `O(w)`.

Write `ω` for the archimedean Lévy density and `Q(y) = ‖g − g(· + y)‖²`. Then:

* **The archimedean Robin constant** (`archRobinConstant`):
  `2c_∞ = 2∫_0^1 (ω(y) − 1/(2y)) dy + 2∫_1^∞ ω(y) dy`, a constant of the Γ-factor alone; the
  integrand of the first integral lies in `[0, e^{1/2}/4]`.
* **The shape term** (`bumpRobin`): `β(g) = ∫_0^w Q(y)/(2y) dy`, finite for a Lipschitz bump. For a
  dilated profile `g = φ(·/w)` both `β(g)` and `‖g‖²` scale by `w`, so `β/‖g‖²` depends only on `φ`.
* **The exact self-energy** (`levyEnergy_atom_eq`, `abs_levyEnergy_atom_sub_le`): for a `C²` bump
  supported in `[0, w]`, `w ≤ 1`,
  `levyEnergy g = (log(1/w) + 2c_∞)‖g‖² + β(g) + R`, `|R| ≤ (e^{1/2}/2) w ‖g‖²`.

So the archimedean counterterm of an atom is `log(1/w) + 2c_∞ + β(g)/‖g‖²` to `O(w)`: with
`2θ′(0)` this is the constant `κ₀(g) = 2θ′(0) + 2c_∞ + β(g)/‖g‖²` of the spacing-scale law, which
together with the sharp prime counterterm `log N − γ` (RAPT) decides the stability width of the
Markov form on the pole vector, `log(1/(wN)) + κ₀(g) + γ`.
-/

noncomputable section

open MeasureTheory Set RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### The archimedean Robin constant -/

/-- The regular part `r(y) = ω(y) − 1/(2y)` of the Lévy density. -/
def levyRegularPart (y : ℝ) : ℝ := archLevyDensity y - 1 / (2 * y)

theorem levyRegularPart_nonneg {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) : 0 ≤ levyRegularPart y := by
  unfold levyRegularPart; linarith [archLevyDensity_ge_inv_two_mul hy0 hy1]

theorem levyRegularPart_le {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    levyRegularPart y ≤ Real.exp (1 / 2) / 4 := by
  unfold levyRegularPart; linarith [archLevyDensity_le_inv_two_mul_add hy0 hy1]

theorem measurable_levyRegularPart : Measurable levyRegularPart :=
  RHTower.measurable_archLevyDensity.sub (measurable_const.div (measurable_const.mul measurable_id))

theorem integrableOn_levyRegularPart {a : ℝ} (ha : a ≤ 1) :
    IntegrableOn levyRegularPart (Ioc 0 a) := by
  refine Measure.integrableOn_of_bounded (M := Real.exp (1 / 2) / 4) ?_
    measurable_levyRegularPart.aestronglyMeasurable ?_
  · exact (measure_Ioc_lt_top).ne
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (levyRegularPart_nonneg hy.1 (hy.2.trans ha))]
    exact levyRegularPart_le hy.1 (hy.2.trans ha)

theorem integrableOn_archLevyDensity_Ioi_one : IntegrableOn archLevyDensity (Ioi 1) := by
  have h2 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hexp0 : IntegrableOn (fun y : ℝ => Real.exp (-(1 / 2) * y)) (Ioi 1) :=
    integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0) 1
  have hexp : IntegrableOn (fun y : ℝ => Real.exp (-(1 / 2) * y) / (1 - Real.exp (-2))) (Ioi 1) :=
    hexp0.div_const _
  refine hexp.mono' RHTower.measurable_archLevyDensity.aestronglyMeasurable ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    have hy1 : (1 : ℝ) ≤ y := le_of_lt hy
    rw [Real.norm_eq_abs, abs_of_pos (archLevyDensity_pos (by linarith))]
    have := archLevyDensity_le_exp_tail hy1
    rwa [show -y / 2 = -(1 / 2) * y by ring] at this

/-- The **archimedean Robin constant** `2c_∞ = 2∫_0^1 (ω − 1/(2y)) + 2∫_1^∞ ω`. -/
def archRobinConstant : ℝ :=
  2 * (∫ y in Ioc 0 1, levyRegularPart y) + 2 * ∫ y in Ioi 1, archLevyDensity y

/-! ### The shape term -/

/-- The **shape term** `β(g) = ∫_0^w ‖g − g(· + y)‖²/(2y) dy`. -/
def bumpRobin (g : ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ y in Ioc 0 w, (∫ u, (g u - g (u + y)) ^ 2) / (2 * y)

theorem integral_sub_shift_sq_le_four (hg : Continuous g) (hgc : HasCompactSupport g) (y : ℝ) :
    ∫ u, (g u - g (u + y)) ^ 2 ≤ 4 * ∫ u, g u ^ 2 := by
  have h1 : Integrable fun u => g u ^ 2 := by
    have h0 : Integrable (fun t => g t * g t) :=
      (hg.mul hg).integrable_of_hasCompactSupport hgc.mul_right
    simpa [pow_two] using h0
  have h2 : Integrable fun u => g (u + y) ^ 2 := h1.comp_add_right y
  have hsq : Integrable fun u => (g u - g (u + y)) ^ 2 :=
    RHTower.WeilMarkovPole.integrable_sub_shift_sq hg hgc y
  have hpt : ∀ u, (g u - g (u + y)) ^ 2 ≤ 2 * g u ^ 2 + 2 * g (u + y) ^ 2 := fun u => by
    nlinarith [sq_nonneg (g u + g (u + y))]
  calc ∫ u, (g u - g (u + y)) ^ 2 ≤ ∫ u, (2 * g u ^ 2 + 2 * g (u + y) ^ 2) :=
        integral_mono hsq ((h1.const_mul 2).add (h2.const_mul 2)) hpt
    _ = 4 * ∫ u, g u ^ 2 := by
        rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul, integral_const_mul,
          integral_add_right_eq_self (fun u => g u ^ 2) y]
        ring

theorem integral_sub_shift_sq_nonneg (y : ℝ) : 0 ≤ ∫ u, (g u - g (u + y)) ^ 2 :=
  integral_nonneg fun _ => sq_nonneg _

/-! ### The exact self-energy -/

/-- **The exact self-energy of an atom.** For a `K`-Lipschitz `C²` bump supported in `[0, w]`,
`0 < w ≤ 1`: `levyEnergy g = (log(1/w) + 2c_∞)‖g‖² + β(g) + R` with `|R| ≤ (e^{1/2}/2) w ‖g‖²`. -/
theorem abs_levyEnergy_atom_sub_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hw0 : 0 < w) (hw1 : w ≤ 1) {K : ℝ}
    (hK : ∀ u v, |g u - g v| ≤ K * |u - v|) :
    |levyEnergy g - ((Real.log (1 / w) + archRobinConstant) * (∫ u, g u ^ 2) + bumpRobin g w)| ≤
      Real.exp (1 / 2) / 2 * w * ∫ u, g u ^ 2 := by
  set M := ∫ u, g u ^ 2 with hMdef
  set A := ∫ u, |g u|
  have hM : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  have hA : 0 ≤ A := integral_nonneg fun u => abs_nonneg _
  set Q : ℝ → ℝ := fun y => ∫ u, (g u - g (u + y)) ^ 2 with hQdef
  set L : ℝ → ℝ := fun y => archLevyDensity y * Q y
  have hLint : IntegrableOn L (Ioi 0) := integrableOn_levyIntegrand hg hgc
  have hQ0 : ∀ y, 0 ≤ Q y := fun y => integral_sub_shift_sq_nonneg y
  have hQ4 : ∀ y, Q y ≤ 4 * M := fun y => integral_sub_shift_sq_le_four hg.continuous hgc y
  have hfar : ∀ y, w < y → L y = 2 * M * archLevyDensity y := fun y hy => by
    simp only [L, Q]
    rw [ArithmeticElectrostatics.integral_sq_sub_shift_of_disjoint hg.continuous hgc
      (bump_mul_shift_eq_zero hgsupp hy)]
    ring
  -- measurability of `Q`
  have hQm : StronglyMeasurable Q := by
    have hc : Continuous fun p : ℝ × ℝ => (g p.2 - g (p.2 + p.1)) ^ 2 := by
      have := hg.continuous; fun_prop
    exact hc.stronglyMeasurable.integral_prod_right'
  -- the near range: `L = Q/(2y) + r Q` on `(0, w]`
  have hQdiv_le : ∀ y ∈ Ioc 0 w, Q y / (2 * y) ≤ K * A := by
    intro y hy
    have hinc := integral_sub_shift_sq_le_lipschitz hg.continuous hgc hK y
    rw [abs_of_pos hy.1] at hinc
    rw [div_le_iff₀ (by linarith [hy.1])]
    nlinarith
  have hQdiv_int : IntegrableOn (fun y => Q y / (2 * y)) (Ioc 0 w) := by
    refine Measure.integrableOn_of_bounded (M := K * A) (measure_Ioc_lt_top).ne
      ((hQm.measurable.div (measurable_const.mul measurable_id)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hQ0 y) (by linarith [hy.1]))]
    exact hQdiv_le y hy
  have hr_int : IntegrableOn levyRegularPart (Ioc 0 w) := integrableOn_levyRegularPart hw1
  have hrQ_int : IntegrableOn (fun y => levyRegularPart y * (Q y - 2 * M)) (Ioc 0 w) := by
    refine Measure.integrableOn_of_bounded (M := Real.exp (1 / 2) / 4 * (2 * M))
      (measure_Ioc_lt_top).ne ?_ ?_
    · exact (measurable_levyRegularPart.mul (hQm.measurable.sub measurable_const)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun y hy => ?_)
      have hr0 := levyRegularPart_nonneg hy.1 (hy.2.trans hw1)
      have hr1 := levyRegularPart_le hy.1 (hy.2.trans hw1)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hr0]
      have : |Q y - 2 * M| ≤ 2 * M := abs_le.mpr ⟨by linarith [hQ0 y], by linarith [hQ4 y]⟩
      exact mul_le_mul hr1 this (abs_nonneg _) (by positivity)
  -- splitting `(0, ∞) = (0, w] ∪ (w, 1] ∪ (1, ∞)`
  have hsplit1 : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hsplit2 : Ioc (0 : ℝ) 1 = Ioc 0 w ∪ Ioc w 1 := (Ioc_union_Ioc_eq_Ioc hw0.le hw1).symm
  have hI1 : IntegrableOn L (Ioc 0 1) := hLint.mono_set fun y hy => hy.1
  have hI2 : IntegrableOn L (Ioi 1) :=
    hLint.mono_set fun y hy => mem_Ioi.mpr (lt_trans one_pos (mem_Ioi.mp hy))
  have hI3 : IntegrableOn L (Ioc 0 w) := hI1.mono_set fun y hy => ⟨hy.1, hy.2.trans hw1⟩
  have hI4 : IntegrableOn L (Ioc w 1) := hI1.mono_set fun y hy => ⟨lt_trans hw0 hy.1, hy.2⟩
  have hunion : ∫ y in Ioi 0, L y =
      (∫ y in Ioc 0 w, L y) + (∫ y in Ioc w 1, L y) + ∫ y in Ioi 1, L y := by
    rw [hsplit1, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2, hsplit2,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hI3 hI4]
  -- near: `∫_0^w L = β + ∫_0^w r (Q − 2M) + 2M ∫_0^w r`
  have hnear : ∫ y in Ioc 0 w, L y = bumpRobin g w +
      (∫ y in Ioc 0 w, levyRegularPart y * (Q y - 2 * M)) +
        2 * M * ∫ y in Ioc 0 w, levyRegularPart y := by
    have hpt : ∀ y ∈ Ioc 0 w, L y = Q y / (2 * y) + levyRegularPart y * (Q y - 2 * M) +
        2 * M * levyRegularPart y := by
      intro y hy
      simp only [L, levyRegularPart]
      have : (y : ℝ) ≠ 0 := ne_of_gt hy.1
      field_simp
      ring
    have hsum : IntegrableOn (fun x => Q x / (2 * x) + levyRegularPart x * (Q x - 2 * M))
        (Ioc 0 w) := hQdiv_int.add hrQ_int
    have hc : IntegrableOn (fun x => 2 * M * levyRegularPart x) (Ioc 0 w) := hr_int.const_mul _
    rw [setIntegral_congr_fun measurableSet_Ioc hpt,
      integral_add (f := fun x => Q x / (2 * x) + levyRegularPart x * (Q x - 2 * M))
        (g := fun x => 2 * M * levyRegularPart x) hsum hc,
      integral_add (f := fun x => Q x / (2 * x)) (g := fun x => levyRegularPart x * (Q x - 2 * M))
        hQdiv_int hrQ_int, integral_const_mul]
    rfl
  -- middle: `∫_w^1 L = M log(1/w) + 2M ∫_w^1 r`
  have hmid : ∫ y in Ioc w 1, L y = M * Real.log (1 / w) +
      2 * M * ∫ y in Ioc w 1, levyRegularPart y := by
    have hinv : IntegrableOn (fun y : ℝ => y⁻¹) (Ioc w 1) := by
      have hc : ContinuousOn (fun y : ℝ => y⁻¹) (Icc w 1) :=
        continuousOn_inv₀.mono fun y hy => ne_of_gt (lt_of_lt_of_le hw0 hy.1)
      exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hr_mid : IntegrableOn levyRegularPart (Ioc w 1) :=
      (integrableOn_levyRegularPart le_rfl).mono_set fun y hy => ⟨lt_trans hw0 hy.1, hy.2⟩
    have hpt : ∀ y ∈ Ioc w 1, L y = M * y⁻¹ + 2 * M * levyRegularPart y := by
      intro y hy
      rw [hfar y hy.1]
      simp only [levyRegularPart]
      have : (y : ℝ) ≠ 0 := ne_of_gt (lt_trans hw0 hy.1)
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add (hinv.const_mul M)
      (hr_mid.const_mul _), integral_const_mul, integral_const_mul,
      ← intervalIntegral.integral_of_le hw1, integral_inv_of_pos hw0 one_pos, one_div]
  -- tail: `∫_1^∞ L = 2M ∫_1^∞ ω`
  have htail : ∫ y in Ioi 1, L y = 2 * M * ∫ y in Ioi 1, archLevyDensity y := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun y hy => hfar y (lt_of_le_of_lt hw1 hy),
      integral_const_mul]
  -- `∫_0^1 r = ∫_0^w r + ∫_w^1 r`
  have hrsplit : ∫ y in Ioc 0 1, levyRegularPart y =
      (∫ y in Ioc 0 w, levyRegularPart y) + ∫ y in Ioc w 1, levyRegularPart y := by
    rw [hsplit2, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hr_int
      ((integrableOn_levyRegularPart le_rfl).mono_set fun y hy => ⟨lt_trans hw0 hy.1, hy.2⟩)]
  -- the error term
  have herr : |∫ y in Ioc 0 w, levyRegularPart y * (Q y - 2 * M)| ≤
      Real.exp (1 / 2) / 2 * w * M := by
    have hb : ∀ y ∈ Ioc 0 w, |levyRegularPart y * (Q y - 2 * M)| ≤
        Real.exp (1 / 2) / 4 * (2 * M) := by
      intro y hy
      have hr0 := levyRegularPart_nonneg hy.1 (hy.2.trans hw1)
      have hr1 := levyRegularPart_le hy.1 (hy.2.trans hw1)
      rw [abs_mul, abs_of_nonneg hr0]
      have : |Q y - 2 * M| ≤ 2 * M := abs_le.mpr ⟨by linarith [hQ0 y], by linarith [hQ4 y]⟩
      exact mul_le_mul hr1 this (abs_nonneg _) (by positivity)
    calc |∫ y in Ioc 0 w, levyRegularPart y * (Q y - 2 * M)|
        ≤ ∫ y in Ioc 0 w, |levyRegularPart y * (Q y - 2 * M)| := abs_integral_le_integral_abs
      _ ≤ ∫ y in Ioc 0 w, Real.exp (1 / 2) / 4 * (2 * M) :=
          setIntegral_mono_on hrQ_int.abs (integrableOn_const (by simp)) measurableSet_Ioc hb
      _ = Real.exp (1 / 2) / 2 * w * M := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hw0.le, sub_zero]; ring
  have hlevy : levyEnergy g = ∫ y in Ioi 0, L y := rfl
  rw [hlevy, hunion, hnear, hmid, htail]
  unfold archRobinConstant
  rw [hrsplit]
  have e : bumpRobin g w + (∫ y in Ioc 0 w, levyRegularPart y * (Q y - 2 * M)) +
      2 * M * (∫ y in Ioc 0 w, levyRegularPart y) +
      (M * Real.log (1 / w) + 2 * M * ∫ y in Ioc w 1, levyRegularPart y) +
      2 * M * (∫ y in Ioi 1, archLevyDensity y) -
      ((Real.log (1 / w) + (2 * ((∫ y in Ioc 0 w, levyRegularPart y) +
        ∫ y in Ioc w 1, levyRegularPart y) + 2 * ∫ y in Ioi 1, archLevyDensity y)) * M +
        bumpRobin g w) = ∫ y in Ioc 0 w, levyRegularPart y * (Q y - 2 * M) := by ring
  rw [e]
  exact herr

/-! ### Dilated profiles: the Robin constant of a shape -/

/-- The atom of width `w` with profile `φ`: `u ↦ φ(u/w)`. -/
def atomDilate (φ : ℝ → ℝ) (w : ℝ) : ℝ → ℝ := fun u => φ (u / w)

/-- The **Robin constant of a profile** `κ_L(φ) = 2c_∞ + β(φ)/‖φ‖²`, `β(φ)` at width one. -/
def profileRobin (φ : ℝ → ℝ) : ℝ := archRobinConstant + bumpRobin φ 1 / ∫ u, φ u ^ 2

variable {φ : ℝ → ℝ}

theorem integral_atomDilate_sq (hw : 0 < w) :
    ∫ u, atomDilate φ w u ^ 2 = w * ∫ u, φ u ^ 2 := by
  have h := MeasureTheory.Measure.integral_comp_div (fun x => φ x ^ 2) w
  simp only [smul_eq_mul, abs_of_pos hw] at h
  exact h

theorem integral_sub_shift_atomDilate (hw : 0 < w) (y : ℝ) :
    ∫ u, (atomDilate φ w u - atomDilate φ w (u + y)) ^ 2 =
      w * ∫ v, (φ v - φ (v + y / w)) ^ 2 := by
  have h := MeasureTheory.Measure.integral_comp_div (fun x => (φ x - φ (x + y / w)) ^ 2) w
  simp only [smul_eq_mul, abs_of_pos hw] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [atomDilate, add_div]

/-- **The shape term scales with the width**: `β(φ(·/w)) = w β(φ)`. -/
theorem bumpRobin_atomDilate (hw : 0 < w) : bumpRobin (atomDilate φ w) w = w * bumpRobin φ 1 := by
  set h : ℝ → ℝ := fun t => (∫ v, (φ v - φ (v + t)) ^ 2) / (2 * t)
  have hpt : ∀ y ∈ Ioc (0 : ℝ) w, (∫ u, (atomDilate φ w u - atomDilate φ w (u + y)) ^ 2) /
      (2 * y) = h (y / w) := by
    intro y hy
    rw [integral_sub_shift_atomDilate hw]
    simp only [h]
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    field_simp
  unfold bumpRobin
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, ← intervalIntegral.integral_of_le hw.le,
    intervalIntegral.integral_comp_div (fun t => h t) hw.ne', zero_div, div_self hw.ne',
    intervalIntegral.integral_of_le zero_le_one, smul_eq_mul]

/-- **The Robin constant of a profile.** For a `K`-Lipschitz `C²` profile `φ` supported in `[0, 1]`
and `0 < w ≤ 1`, the atom `φ(·/w)` has
`|levyEnergy(φ(·/w)) − (log(1/w) + κ_L(φ))‖φ(·/w)‖²| ≤ (e^{1/2}/2) w ‖φ(·/w)‖²`, with
`κ_L(φ) = 2c_∞ + β(φ)/‖φ‖²` independent of `w`. -/
theorem abs_levyEnergy_atomDilate_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0)
    (hφ0 : 0 < ∫ u, φ u ^ 2) (hw0 : 0 < w) (hw1 : w ≤ 1) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) :
    |levyEnergy (atomDilate φ w) -
        (Real.log (1 / w) + profileRobin φ) * ∫ u, atomDilate φ w u ^ 2| ≤
      Real.exp (1 / 2) / 2 * w * ∫ u, atomDilate φ w u ^ 2 := by
  have hcd : ContDiff ℝ 2 (atomDilate φ w) := hφ.comp (contDiff_id.div_const w)
  have hsupp : ∀ u, u ∉ Icc 0 w → atomDilate φ w u = 0 := by
    intro u hu
    refine hφsupp (u / w) fun h => hu ⟨?_, ?_⟩
    · have := h.1; rw [le_div_iff₀ hw0] at this; linarith
    · have := h.2; rw [div_le_iff₀ hw0] at this; linarith
  have hcs : HasCompactSupport (atomDilate φ w) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := w)) fun u hu => hsupp u hu
  have hLip : ∀ u v, |atomDilate φ w u - atomDilate φ w v| ≤ K / w * |u - v| := by
    intro u v
    have := hK (u / w) (v / w)
    simp only [atomDilate]
    rw [show u / w - v / w = (u - v) / w by ring, abs_div, abs_of_pos hw0] at this
    calc |φ (u / w) - φ (v / w)| ≤ K * (|u - v| / w) := this
      _ = K / w * |u - v| := by ring
  have h := abs_levyEnergy_atom_sub_le hcd hcs hsupp hw0 hw1 hLip
  have hβ := bumpRobin_atomDilate (φ := φ) hw0
  have hM := integral_atomDilate_sq (φ := φ) hw0
  rw [hβ] at h
  have e : (Real.log (1 / w) + archRobinConstant) * (∫ u, atomDilate φ w u ^ 2) + w * bumpRobin φ 1 =
      (Real.log (1 / w) + profileRobin φ) * ∫ u, atomDilate φ w u ^ 2 := by
    unfold profileRobin
    rw [hM]
    field_simp
    ring
  rwa [e] at h

/-- **The Robin constant is the finite part of the self-energy**:
`levyEnergy(φ(·/w))/‖φ(·/w)‖² − log(1/w) → κ_L(φ)` as `w → 0⁺`. -/
theorem tendsto_levyEnergy_atomDilate_sub_log (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) :
    Filter.Tendsto (fun w => levyEnergy (atomDilate φ w) / (∫ u, atomDilate φ w u ^ 2) -
      Real.log (1 / w)) (nhdsWithin 0 (Ioi 0)) (nhds (profileRobin φ)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min 1 (ε / Real.exp (1 / 2)), by positivity, fun w hw hdist => ?_⟩
  have hw0 : 0 < w := hw
  rw [Real.dist_eq, sub_zero, abs_of_pos hw0] at hdist
  have hw1 : w ≤ 1 := (lt_of_lt_of_le hdist (min_le_left _ _)).le
  have hwε : w < ε / Real.exp (1 / 2) := lt_of_lt_of_le hdist (min_le_right _ _)
  have hMpos : 0 < ∫ u, atomDilate φ w u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; positivity
  have h := abs_levyEnergy_atomDilate_sub_le hφ hφsupp hφ0 hw0 hw1 hK
  rw [Real.dist_eq]
  have e : levyEnergy (atomDilate φ w) / (∫ u, atomDilate φ w u ^ 2) - Real.log (1 / w) -
      profileRobin φ = (levyEnergy (atomDilate φ w) - (Real.log (1 / w) + profileRobin φ) *
        ∫ u, atomDilate φ w u ^ 2) / ∫ u, atomDilate φ w u ^ 2 := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hMpos, div_lt_iff₀ hMpos]
  have hexp : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have : Real.exp (1 / 2) / 2 * w < ε := by
    rw [lt_div_iff₀ hexp] at hwε; nlinarith
  nlinarith

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
