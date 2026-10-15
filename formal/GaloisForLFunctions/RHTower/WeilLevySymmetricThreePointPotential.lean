import GaloisForLFunctions.RHTower.WeilLevyQuarterWindowCoercivity

/-!
# Symmetric Three-Point Lévy–Cosh Potential and Unconditional Window Positivity on `(0, 1 / 3)`

In `WeilLevyQuarterWindowCoercivity.lean`, we established the universal quarter-window coercivity
`(1 / 3) * ∫ u, h u ^ 2 ≤ ∫ u, (h u - h (u + x)) ^ 2` for all shifts `x ≥ L / 4`.
However, when `sub_levyCoshPotential_half_le_setIntegral_Ioo` paired `L - y ∈ (L - b, L / 2)` with
`y ∈ (L / 2, b)`, it bounded
`(-K(L - y)) D_h(L - y) + (-K(y)) D_h(y) ≥ (-K(y)) (D_h(L - y) + D_h(y)) ≥ 2 (-K(y)) ∫ h²`,
discarding the nonnegative kernel excess `((-K(L - y)) - (-K(y))) D_h(L - y) ≥ 0`.

In this file we retain that excess using the quarter-window lower bound `D_h(L - y) ≥ (1 / 3) ∫ h²`
for `y ∈ (L / 2, b)` (`L / 2 ≤ b ≤ 3 * L / 4`), obtaining the sharp pointwise bound
`((1 / 3) * (-K(L - y)) + (5 / 3) * (-K(y))) * ∫ h² ≤ (-K(L - y)) D_h(L - y) + (-K(y)) D_h(y)`.

## Main Results

1. **Excess-Preserving Reflected Midpoint Bound (`L / 2 ≤ b ≤ 3 * L / 4`)**:
   - `excess_reflected_levyCoshPotential_le_setIntegral_Ioo`:
     `((1 / 6) * Φ(L - b) + (2 / 3) * Φ(L / 2) - (5 / 6) * Φ(b)) * ∫ h² ≤ ∫_{Ioo (L - b) b} (-K(x)) D_h(x) dx`.
   - `three_point_sub_levyCoshPotential_le_setIntegral_Ioo`:
     combining `Ioo (L / 4) (L - b)` with `Ioo (L - b) b` cancels `Φ(L - b)` identically, giving
     `((1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) - (5 / 6) * Φ(b)) * ∫ h² ≤ ∫_{Ioo (L / 4) b} (-K(x)) D_h(x) dx`.
   - `excess_quarter_add_half_window_levyCosh_crossover_le_weilArchRe`:
     `(A(0) + (1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (1 / 6) * Φ(c)) * ∫ f² + pair_c(f) ≤ W_∞(f ⋆ f̃)`.

2. **Symmetric Three-Point Potential Floor (`3 * L / 4 ≤ c < L`)**:
   - `symmetric_three_point_sub_levyCoshPotential_le_setIntegral_Ioo`:
     for `3 * L / 4 ≤ c < L` and `c ≤ screwSignThreshold`, splitting `Ioo (L - c) c` into the inner
     shell `Ioo (L / 4) (3 * L / 4)` and the outer reflected shell gives
     `((1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (1 / 6) * Φ(3 * L / 4) - Φ(c)) * ∫ h² ≤ ∫_{Ioo (L - c) c} (-K(x)) D_h(x) dx`.
   - `symmetric_three_point_levyCosh_crossover_le_weilArchRe` & `symmetric_three_point_potential_le_weilArchRe`:
     `(A(0) + (1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (1 / 6) * Φ(3 * L / 4)) * ∫ f² ≤ W_∞(f ⋆ f̃)`
     for all nonnegative `f ∈ C²_c(ℝ)` on `(0, L)` whenever `0 < L ≤ (4 / 3) * screwSignThreshold ≈ 0.3750`.

3. **Osculating Lower Bound and Unconditional Window Positivity on `(0, 1 / 3)`**:
   - `osculating_le_symmetric_three_point_potential`:
     `log(1 / (π L)) + (1 / 6) * log(4 / 3) + (7 / 4) * L - γ ≤ A(0) + (1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (1 / 6) * Φ(3 * L / 4)`.
   - `neg_gammaBracket_zero_le_symmetric_three_point_of_le_one_third`:
     at `L = 1 / 3`, the logarithmic arguments combine into `(1 / 6) * log(972 / π⁶) > 0` (since
     `π < 3.1416 ⟹ π⁶ < 961.44 < 972`) while `(7 / 4) * (1 / 3) = 7 / 12 > 0.577216 > γ`, proving
     `0 ≤ A(0) + (1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (1 / 6) * Φ(3 * L / 4)` for all `0 < L ≤ 1 / 3`.
   - `weilArchRe_nonneg_of_support_Ioo_le_one_third` & `windowPositive_one_third`:
     unconditional window positivity on `(0, 1 / 3)` (covering **48.1% of `(0, log 2)`**).
-/

open Complex MeasureTheory Set Filter Topology Real
open scoped ENNReal FourierTransform ComplexConjugate
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevySymmetricThreePoint

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor
open RHTower.WeilLevyQuarterWindow

/-! ## Section 1: Excess-Preserving Reflected Midpoint Bound (`L / 2 ≤ b ≤ 3 * L / 4`) -/

/-- Helper evaluation of the kernel integral on `Ioo a b` (`0 < a ≤ b`):
`∫ x in Ioo a b, -screwRegularKernel x = (1 / 2) * (levyCoshPotential a - levyCoshPotential b)`. -/
theorem setIntegral_Ioo_neg_screwRegularKernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in Ioo a b, -screwRegularKernel x) =
      (1 / 2 : ℝ) * (levyCoshPotential a - levyCoshPotential b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  have hFTC := integral_two_mul_screwRegularKernel ha hb
  have hneg : (∫ x in a..b, -screwRegularKernel x) =
      -(1 / 2) * ∫ x in a..b, 2 * screwRegularKernel x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [hneg, hFTC]
  ring

/-- Helper evaluation of the reflected kernel integral on `Ioo (L / 2) b`:
`∫ y in Ioo (L / 2) b, (-screwRegularKernel (L - y)) = (1 / 2) * (levyCoshPotential (L - b) - levyCoshPotential (L / 2))`. -/
theorem setIntegral_Ioo_reflect_neg_screwRegularKernel {L b : ℝ}
    (_hL0 : 0 < L) (hL2b : L / 2 ≤ b) (hbL : b < L) :
    (∫ y in Ioo (L / 2) b, -screwRegularKernel (L - y)) =
      (1 / 2 : ℝ) * (levyCoshPotential (L - b) - levyCoshPotential (L / 2)) := by
  have hLb0 : 0 < L - b := by linarith
  have hLb_L2 : L - b ≤ L / 2 := by linarith
  rw [← setIntegral_Ioo_reflect_half (fun x => -screwRegularKernel x) L b,
    setIntegral_Ioo_neg_screwRegularKernel hLb0 hLb_L2]

/-- **Excess-Preserving Reflected Midpoint Bound (`L / 2 ≤ b ≤ 3 * L / 4`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`) and any `b` with
`L / 2 ≤ b ≤ 3 * L / 4` and `b ≤ screwSignThreshold`, retaining the quarter-window lower bound
`D_h(L - y) ≥ (1 / 3) * ∫ h²` on the positive kernel excess `(-K(L - y)) - (-K(y)) ≥ 0` proves:
`((1 / 6) * levyCoshPotential (L - b) + (2 / 3) * levyCoshPotential (L / 2) - (5 / 6) * levyCoshPotential b) * ∫ u, h u ^ 2`
`≤ ∫ x in Ioo (L - b) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem excess_reflected_levyCoshPotential_le_setIntegral_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L b : ℝ} (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0)
    (hL0 : 0 < L) (hL2b : L / 2 ≤ b) (hb3L4 : b ≤ 3 * L / 4) (hbt : b ≤ screwSignThreshold) :
    ((1 / 6 : ℝ) * levyCoshPotential (L - b) + (2 / 3 : ℝ) * levyCoshPotential (L / 2) -
        (5 / 6 : ℝ) * levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L - b) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hbL : b < L := by linarith
  have hLb0 : 0 < L - b := by linarith
  have hL2 : 0 < L / 2 := by linarith
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L - b) b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hLb0 hx.1).neg
  have hIF : IntegrableOn F (Ioo (L - b) b) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hLb0 hx.1) (hx.2.le.trans hbt))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_left : IntegrableOn F (Ioo (L - b) (L / 2)) :=
    hIF.mono_set (Ioo_subset_Ioo le_rfl hL2b)
  have hIF_right : IntegrableOn F (Ioo (L / 2) b) :=
    hIF.mono_set (Ioo_subset_Ioo (by linarith) le_rfl)
  have hIF_left_Ioc : IntegrableOn F (Ioc (L - b) (L / 2)) := by
    rwa [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hIF_Ioc : IntegrableOn F (Ioc (L / 2) b) := by
    rwa [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hdisj_Ioc : Disjoint (Ioc (L - b) (L / 2)) (Ioc (L / 2) b) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L - b) b, F x) =
      (∫ y in Ioo (L / 2) b, F (L - y)) + ∫ y in Ioo (L / 2) b, F y := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (by linarith) hL2b,
      setIntegral_union hdisj_Ioc measurableSet_Ioc hIF_left_Ioc hIF_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
      setIntegral_Ioo_reflect_half]
  have hIF_refl : IntegrableOn (fun y => F (L - y)) (Ioo (L / 2) b) := by
    have hpre : (fun y : ℝ => -y + L) ⁻¹' Ioo (L - b) (L / 2) = Ioo (L / 2) b := by
      ext y; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith
    have h1 : Integrable (fun y : ℝ => (Ioo (L - b) (L / 2)).indicator F (-y + L)) :=
      (((integrable_indicator_iff measurableSet_Ioo).mpr hIF_left).comp_add_right L).comp_neg
    rw [← integrable_indicator_iff measurableSet_Ioo]
    refine h1.congr (ae_of_all _ fun y => ?_)
    dsimp only
    rw [← Set.indicator_comp_right (fun y : ℝ => -y + L), hpre]
    exact congrArg (fun g => (Ioo (L / 2) b).indicator g y) (funext fun z => congrArg F (by ring))
  rw [hsplit, ← integral_add hIF_refl hIF_right]
  have hIK_right : IntegrableOn (fun y => -screwRegularKernel y) (Ioo (L / 2) b) :=
    (hcont_K.mono (Icc_subset_Icc (by linarith) le_rfl)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hIK_refl : IntegrableOn (fun y => -screwRegularKernel (L - y)) (Ioo (L / 2) b) := by
    have hcont_refl : ContinuousOn (fun y => -screwRegularKernel (L - y)) (Icc (L / 2) b) :=
      (hcont_K.comp (continuousOn_const.sub continuousOn_id)
        fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    exact hcont_refl.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  let G : ℝ → ℝ := fun y =>
    ((1 / 3 : ℝ) * (-screwRegularKernel (L - y)) + (5 / 3 : ℝ) * (-screwRegularKernel y)) *
      ∫ u, h u ^ 2
  have hIG : IntegrableOn G (Ioo (L / 2) b) :=
    ((hIK_refl.const_mul (1 / 3)).add (hIK_right.const_mul (5 / 3))).mul_const _
  have hval : (∫ y in Ioo (L / 2) b, G y) =
      ((1 / 6 : ℝ) * levyCoshPotential (L - b) + (2 / 3 : ℝ) * levyCoshPotential (L / 2) -
        (5 / 6 : ℝ) * levyCoshPotential b) * ∫ u, h u ^ 2 := by
    dsimp only [G]
    rw [integral_mul_const,
      integral_add (hIK_refl.const_mul (1 / 3)) (hIK_right.const_mul (5 / 3)),
      integral_const_mul, integral_const_mul,
      setIntegral_Ioo_reflect_neg_screwRegularKernel hL0 hL2b hbL,
      setIntegral_Ioo_neg_screwRegularKernel hL2 hL2b]
    ring
  rw [← hval]
  refine setIntegral_mono_on hIG (hIF_refl.add hIF_right) measurableSet_Ioo fun y hy => ?_
  dsimp only [G, F, Pi.add_apply]
  have hy0 : 0 < y := lt_trans hL2 hy.1
  have hLy0 : 0 < L - y := by linarith [hy.2]
  have hLy_le : L - y ≤ y := by linarith [hy.1]
  have hLy_quarter : L / 4 ≤ L - y := by linarith [hy.2]
  have hK_le : -screwRegularKernel y ≤ -screwRegularKernel (L - y) :=
    neg_le_neg (monotoneOn_screwRegularKernel hLy0 hy0 hLy_le)
  have hK0 : 0 ≤ -screwRegularKernel y :=
    neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold hy0 (hy.2.le.trans hbt))
  have hsum := two_mul_integral_sq_le_integral_jump_sq_add_sub hh hsupp hy0.le
    (le_trans hy.2.le hbL.le)
  have hq := one_third_mul_integral_sq_le_integral_jump_sq_of_quarter_le
    hh hsupp hL0.le hLy_quarter
  have hstep1 : (-screwRegularKernel y) * (2 * ∫ u, h u ^ 2) ≤
      (-screwRegularKernel y) *
        ((∫ u, (h u - h (u + y)) ^ 2) + ∫ u, (h u - h (u + (L - y))) ^ 2) :=
    mul_le_mul_of_nonneg_left hsum hK0
  have hstep2 : (-screwRegularKernel (L - y) - -screwRegularKernel y) *
        ((1 / 3 : ℝ) * ∫ u, h u ^ 2) ≤
      (-screwRegularKernel (L - y) - -screwRegularKernel y) *
        ∫ u, (h u - h (u + (L - y))) ^ 2 :=
    mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hK_le)
  linarith

/-- **Three-Point Potential Lower Bound on `Ioo (L / 4) b` (`L / 2 ≤ b ≤ 3 * L / 4`)**:
combining `one_sixth_mul_sub_levyCoshPotential_quarter_le_setIntegral_Ioo` on `Ioo (L / 4) (L - b)`
with `excess_reflected_levyCoshPotential_le_setIntegral_Ioo` on `Ioo (L - b) b` cancels
`levyCoshPotential (L - b)` identically, proving:
`((1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) - (5 / 6) * Φ(b)) * ∫ h² ≤ ∫_{Ioo (L / 4) b} (-K(x)) D_h(x) dx`. -/
theorem three_point_sub_levyCoshPotential_le_setIntegral_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L b : ℝ} (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0)
    (hL0 : 0 < L) (hL2b : L / 2 ≤ b) (hb3L4 : b ≤ 3 * L / 4) (hbt : b ≤ screwSignThreshold) :
    ((1 / 6 : ℝ) * levyCoshPotential (L / 4) + (2 / 3 : ℝ) * levyCoshPotential (L / 2) -
        (5 / 6 : ℝ) * levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 4) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL4 : 0 < L / 4 := by linarith
  have hL4_Lb : L / 4 ≤ L - b := by linarith
  have hLb_b : L - b ≤ b := by linarith
  have hLbt : L - b ≤ screwSignThreshold := hLb_b.trans hbt
  let G : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hh
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 4) b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL4 hx.1).neg
  have hIG : IntegrableOn G (Ioo (L / 4) b) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL4 hx.1) (hx.2.le.trans hbt))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIG_left_Ioc : IntegrableOn G (Ioc (L / 4) (L - b)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIG.mono_set (Ioo_subset_Ioo le_rfl hLb_b)
  have hIG_right_Ioc : IntegrableOn G (Ioc (L - b) b) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIG.mono_set (Ioo_subset_Ioo hL4_Lb le_rfl)
  have hdisj : Disjoint (Ioc (L / 4) (L - b)) (Ioc (L - b) b) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 4) b, G x) =
      (∫ x in Ioo (L / 4) (L - b), G x) + ∫ x in Ioo (L - b) b, G x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL4_Lb hLb_b,
      setIntegral_union hdisj measurableSet_Ioc hIG_left_Ioc hIG_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have hq := one_sixth_mul_sub_levyCoshPotential_quarter_le_setIntegral_Ioo
    hh hsupp hL0 hL4_Lb hLbt
  have hrefl := excess_reflected_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL2b hb3L4 hbt
  dsimp only [G] at hsplit
  linarith

/-- **Excess-Preserving Quarter-Plus-Half Window Lévy–Cosh Crossover (`L / 2 ≤ c ≤ 3 * L / 4`)**:
for every signed `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and every `c` with
`L / 2 ≤ c ≤ 3 * L / 4` and `c ≤ screwSignThreshold`,
`(A(0) + (1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (1 / 6) * Φ(c)) * ∫ f² + pair_c(f) ≤ W_∞(f ⋆ f̃)`. -/
theorem excess_quarter_add_half_window_levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL0 : 0 < L)
    (hL2c : L / 2 ≤ c) (hc3L4 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 6) * levyCoshPotential (L / 4) +
        (2 / 3) * levyCoshPotential (L / 2) + (1 / 6) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL4 : 0 < L / 4 := by linarith
  have hL4c : L / 4 ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL4 hL4c hct
  have h3 := three_point_sub_levyCoshPotential_le_setIntegral_Ioo hB hsupp hL0 hL2c hc3L4 hct
  linarith

/-! ## Section 2: Symmetric Three-Point Potential Floor (`3 * L / 4 ≤ c < L`) -/

/-- **Symmetric Three-Point Potential Lower Bound on `Ioo (L - c) c` (`3 * L / 4 ≤ c < L`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`) and any `c` with
`3 * L / 4 ≤ c < L` and `c ≤ screwSignThreshold`, splitting the reflected integral over `Ioo (L / 2) c`
at `3 * L / 4` combines the excess-preserving quarter-plus-half bound on `Ioo (L / 2) (3 * L / 4)`
with the midpoint reflection bound on `Ioo (3 * L / 4) c`, proving:
`((1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (1 / 6) * Φ(3 * L / 4) - Φ(c)) * ∫ h² ≤ ∫_{Ioo (L - c) c} (-K(x)) D_h(x) dx`. -/
theorem symmetric_three_point_sub_levyCoshPotential_le_setIntegral_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L c : ℝ} (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0)
    (hL0 : 0 < L) (h3L4c : 3 * L / 4 ≤ c) (hcL : c < L) (hct : c ≤ screwSignThreshold) :
    ((1 / 6 : ℝ) * levyCoshPotential (L / 4) + (2 / 3 : ℝ) * levyCoshPotential (L / 2) +
        (1 / 6 : ℝ) * levyCoshPotential (3 * L / 4) - levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L - c) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hLc0 : 0 < L - c := by linarith
  have hL2 : 0 < L / 2 := by linarith
  have h3L4_pos : 0 < 3 * L / 4 := by linarith
  have hL2_3L4 : L / 2 ≤ 3 * L / 4 := by linarith
  have hL2c : L / 2 ≤ c := by linarith
  have h3L4_t : 3 * L / 4 ≤ screwSignThreshold := h3L4c.trans hct
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L - c) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hLc0 hx.1).neg
  have hIF : IntegrableOn F (Ioo (L - c) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hLc0 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_left : IntegrableOn F (Ioo (L - c) (L / 2)) :=
    hIF.mono_set (Ioo_subset_Ioo le_rfl hL2c)
  have hIF_right : IntegrableOn F (Ioo (L / 2) c) :=
    hIF.mono_set (Ioo_subset_Ioo (by linarith) le_rfl)
  have hIF_left_Ioc : IntegrableOn F (Ioc (L - c) (L / 2)) := by
    rwa [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hIF_Ioc : IntegrableOn F (Ioc (L / 2) c) := by
    rwa [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hdisj_Ioc : Disjoint (Ioc (L - c) (L / 2)) (Ioc (L / 2) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L - c) c, F x) =
      (∫ y in Ioo (L / 2) c, F (L - y)) + ∫ y in Ioo (L / 2) c, F y := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (by linarith) hL2c,
      setIntegral_union hdisj_Ioc measurableSet_Ioc hIF_left_Ioc hIF_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
      setIntegral_Ioo_reflect_half]
  have hIF_refl : IntegrableOn (fun y => F (L - y)) (Ioo (L / 2) c) := by
    have hpre : (fun y : ℝ => -y + L) ⁻¹' Ioo (L - c) (L / 2) = Ioo (L / 2) c := by
      ext y; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith
    have h1 : Integrable (fun y : ℝ => (Ioo (L - c) (L / 2)).indicator F (-y + L)) :=
      (((integrable_indicator_iff measurableSet_Ioo).mpr hIF_left).comp_add_right L).comp_neg
    rw [← integrable_indicator_iff measurableSet_Ioo]
    refine h1.congr (ae_of_all _ fun y => ?_)
    dsimp only
    rw [← Set.indicator_comp_right (fun y : ℝ => -y + L), hpre]
    exact congrArg (fun g => (Ioo (L / 2) c).indicator g y) (funext fun z => congrArg F (by ring))
  have hIF_pair : IntegrableOn (fun y => F (L - y) + F y) (Ioo (L / 2) c) :=
    hIF_refl.add hIF_right
  have hIF_pair_1_Ioc : IntegrableOn (fun y => F (L - y) + F y) (Ioc (L / 2) (3 * L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF_pair.mono_set (Ioo_subset_Ioo le_rfl h3L4c)
  have hIF_pair_2_Ioc : IntegrableOn (fun y => F (L - y) + F y) (Ioc (3 * L / 4) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF_pair.mono_set (Ioo_subset_Ioo hL2_3L4 le_rfl)
  have hdisj_pair : Disjoint (Ioc (L / 2) (3 * L / 4)) (Ioc (3 * L / 4) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit_pair : (∫ x in Ioo (L - c) c, F x) =
      (∫ y in Ioo (L / 2) (3 * L / 4), (F (L - y) + F y)) +
        ∫ y in Ioo (3 * L / 4) c, (F (L - y) + F y) := by
    rw [hsplit, ← integral_add hIF_refl hIF_right,
      ← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL2_3L4 h3L4c,
      setIntegral_union hdisj_pair measurableSet_Ioc hIF_pair_1_Ioc hIF_pair_2_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  -- On `Ioo (L / 2) (3 * L / 4)`, apply `excess_reflected_levyCoshPotential_le_setIntegral_Ioo`
  -- with `b = 3 * L / 4` (noting `L - 3 * L / 4 = L / 4`).
  have h1 : ((1 / 6 : ℝ) * levyCoshPotential (L / 4) + (2 / 3 : ℝ) * levyCoshPotential (L / 2) -
      (5 / 6 : ℝ) * levyCoshPotential (3 * L / 4)) * (∫ u, h u ^ 2) ≤
      ∫ y in Ioo (L / 2) (3 * L / 4), (F (L - y) + F y) := by
    have hex := excess_reflected_levyCoshPotential_le_setIntegral_Ioo
      hh hsupp hL0 hL2_3L4 le_rfl h3L4_t
    rw [show L - 3 * L / 4 = L / 4 by ring] at hex
    have hIF_1_left : IntegrableOn F (Ioo (L / 4) (L / 2)) :=
      hIF_left.mono_set (Ioo_subset_Ioo (by linarith) le_rfl)
    have hIF_1_right : IntegrableOn F (Ioo (L / 2) (3 * L / 4)) :=
      hIF_right.mono_set (Ioo_subset_Ioo le_rfl h3L4c)
    have hIF_1_left_Ioc : IntegrableOn F (Ioc (L / 4) (L / 2)) := by
      rwa [integrableOn_Ioc_iff_integrableOn_Ioo]
    have hIF_1_right_Ioc : IntegrableOn F (Ioc (L / 2) (3 * L / 4)) := by
      rwa [integrableOn_Ioc_iff_integrableOn_Ioo]
    have hdisj_1 : Disjoint (Ioc (L / 4) (L / 2)) (Ioc (L / 2) (3 * L / 4)) :=
      disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
    have hIF_1_refl : IntegrableOn (fun y => F (L - y)) (Ioo (L / 2) (3 * L / 4)) :=
      hIF_refl.mono_set (Ioo_subset_Ioo le_rfl h3L4c)
    have hsplit_1 : (∫ x in Ioo (L / 4) (3 * L / 4), F x) =
        ∫ y in Ioo (L / 2) (3 * L / 4), (F (L - y) + F y) := by
      have hrefl_1 := setIntegral_Ioo_reflect_half F L (3 * L / 4)
      rw [show L - 3 * L / 4 = L / 4 by ring] at hrefl_1
      rw [← integral_Ioc_eq_integral_Ioo,
        ← Ioc_union_Ioc_eq_Ioc (by linarith) hL2_3L4,
        setIntegral_union hdisj_1 measurableSet_Ioc hIF_1_left_Ioc hIF_1_right_Ioc,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
        hrefl_1, ← integral_add hIF_1_refl hIF_1_right]
    rw [← hsplit_1]
    exact hex
  -- On `Ioo (3 * L / 4) c`, use the standard reflection lower bound `2 * (-K(y)) * ∫ h²`.
  have h2 : (levyCoshPotential (3 * L / 4) - levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ y in Ioo (3 * L / 4) c, (F (L - y) + F y) := by
    have hI_low : IntegrableOn (fun y => (-screwRegularKernel y) * (2 * ∫ u, h u ^ 2))
        (Ioo (3 * L / 4) c) :=
      ((hcont_K.mono (Icc_subset_Icc (by linarith) le_rfl)).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self).mul_const _
    have hval2 : (∫ y in Ioo (3 * L / 4) c, (-screwRegularKernel y) * (2 * ∫ u, h u ^ 2)) =
        (levyCoshPotential (3 * L / 4) - levyCoshPotential c) * ∫ u, h u ^ 2 := by
      rw [integral_mul_const, setIntegral_Ioo_neg_screwRegularKernel h3L4_pos h3L4c]
      ring
    rw [← hval2]
    refine setIntegral_mono_on hI_low
      (hIF_pair.mono_set (Ioo_subset_Ioo hL2_3L4 le_rfl)) measurableSet_Ioo fun y hy => ?_
    dsimp only [F, Pi.add_apply]
    have hy0 : 0 < y := lt_trans h3L4_pos hy.1
    have hLy0 : 0 < L - y := by linarith [hy.2]
    have hLy_le : L - y ≤ y := by linarith [hy.1]
    have hK_le : -screwRegularKernel y ≤ -screwRegularKernel (L - y) :=
      neg_le_neg (monotoneOn_screwRegularKernel hLy0 hy0 hLy_le)
    have hK0 : 0 ≤ -screwRegularKernel y :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold hy0 (hy.2.le.trans hct))
    have hsum := two_mul_integral_sq_le_integral_jump_sq_add_sub hh hsupp hy0.le
      (le_trans hy.2.le hcL.le)
    have hstep1 : (-screwRegularKernel y) * (2 * ∫ u, h u ^ 2) ≤
        (-screwRegularKernel y) *
          ((∫ u, (h u - h (u + y)) ^ 2) + ∫ u, (h u - h (u + (L - y))) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hK0
    have hstep2 : (-screwRegularKernel y) * (∫ u, (h u - h (u + (L - y))) ^ 2) ≤
        (-screwRegularKernel (L - y)) * ∫ u, (h u - h (u + (L - y))) ^ 2 :=
      mul_le_mul_of_nonneg_right hK_le (hD0 (L - y))
    linarith
  dsimp only [F] at hsplit_pair h1 h2
  linarith

/-- **Symmetric Three-Point Lévy–Cosh Crossover on `(0, L)` (`3 * L / 4 ≤ c < L`)**:
for every signed `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and every `c` with
`3 * L / 4 ≤ c < L` and `c ≤ screwSignThreshold`,
`(A(0) + (1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (1 / 6) * Φ(3 * L / 4)) * ∫ f² + pair_c(f) ≤ W_∞(f ⋆ f̃)`. -/
theorem symmetric_three_point_levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL0 : 0 < L)
    (h3L4c : 3 * L / 4 ≤ c) (hcL : c < L) (hct : c ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 6) * levyCoshPotential (L / 4) +
        (2 / 3) * levyCoshPotential (L / 2) +
        (1 / 6) * levyCoshPotential (3 * L / 4)) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hLc0 : 0 < L - c := by linarith
  have hLcc : L - c ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hLc0 hLcc hct
  have h3 := symmetric_three_point_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL0 h3L4c hcL hct
  linarith

/-- **Symmetric Three-Point Potential Floor on the Nonnegative Cone
(`screwSignThreshold < L ≤ (4 / 3) * screwSignThreshold ≈ 0.3750`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with
`3 * L / 4 ≤ screwSignThreshold < L`,
`(A(0) + (1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (1 / 6) * Φ(3 * L / 4)) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem symmetric_three_point_potential_le_weilArchRe {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL0 : 0 < L) (h3L4t : 3 * L / 4 ≤ screwSignThreshold)
    (htL : screwSignThreshold < L) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 6) * levyCoshPotential (L / 4) +
        (2 / 3) * levyCoshPotential (L / 2) +
        (1 / 6) * levyCoshPotential (3 * L / 4)) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := symmetric_three_point_levyCosh_crossover_le_weilArchRe
    hf hfc hL0 h3L4t htL le_rfl hsupp
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-! ## Section 3: Osculating Lower Bound and Unconditional Window Positivity on `(0, 1 / 3)` -/

/-- **Osculating Lower Bound for the Symmetric Three-Point Potential**:
for every `L > 0`,
`Real.log (1 / (Real.pi * L)) + (1 / 6) * Real.log (4 / 3) + (7 / 4) * L - eulerMascheroniConstant`
`≤ EF.gammaBracket 0 + (1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (1 / 6) * Φ(3 * L / 4)`. -/
theorem osculating_le_symmetric_three_point_potential {L : ℝ} (hL0 : 0 < L) :
    Real.log (1 / (Real.pi * L)) + (1 / 6 : ℝ) * Real.log (4 / 3) + (7 / 4 : ℝ) * L -
        eulerMascheroniConstant ≤
      EF.gammaBracket 0 + (1 / 6) * levyCoshPotential (L / 4) +
        (2 / 3) * levyCoshPotential (L / 2) +
        (1 / 6) * levyCoshPotential (3 * L / 4) := by
  have h1 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 4 by linarith)
  have h2 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 2 by linarith)
  have h3 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < 3 * L / 4 by linarith)
  have hlog1 : Real.log (1 / (2 * Real.pi * (L / 4))) =
      Real.log (1 / (Real.pi * L)) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; norm_num
  have hlog2 : Real.log (1 / (2 * Real.pi * (L / 2))) =
      Real.log (1 / (Real.pi * L)) := by
    congr 1; field_simp
  have hlog3 : Real.log (1 / (2 * Real.pi * (3 * L / 4))) =
      Real.log (1 / (Real.pi * L)) + Real.log (4 / 3) - Real.log 2 := by
    rw [eq_sub_iff_add_eq, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  linarith

/-- At `L = 1 / 3`, `Real.log (3 / Real.pi) + (1 / 6) * Real.log (4 / 3) > 0` because
`(3 / π)⁶ * (4 / 3) = 972 / π⁶ > 1` (`π < 3.1416 ⟹ π⁶ < 961.44 < 972`). -/
theorem zero_lt_log_three_div_pi_add_one_sixth_log_four_thirds :
    0 < Real.log (3 / Real.pi) + (1 / 6 : ℝ) * Real.log (4 / 3) := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have h3pi_pos : 0 < 3 / Real.pi := by positivity
  have hpow : (1 : ℝ) < (3 / Real.pi) ^ (6 : ℕ) * (4 / 3) := by
    rw [div_pow, div_mul_eq_mul_div, one_lt_div (by positivity)]
    have h6 : Real.pi ^ (6 : ℕ) < (3.1416 : ℝ) ^ (6 : ℕ) :=
      pow_lt_pow_left₀ hpi_lt hpi_pos.le (by decide)
    linarith [show (3.1416 : ℝ) ^ (6 : ℕ) < 3 ^ (6 : ℕ) * (4 / 3) by norm_num]
  have hlog_pos : 0 < Real.log ((3 / Real.pi) ^ (6 : ℕ) * (4 / 3)) :=
    Real.log_pos hpow
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow, Nat.cast_ofNat] at hlog_pos
  linarith

/-- **Nonnegativity of the Symmetric Three-Point Potential for all `0 < L ≤ 1 / 3`**:
`0 ≤ EF.gammaBracket 0 + (1 / 6) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (1 / 6) * Φ(3 * L / 4)`. -/
theorem neg_gammaBracket_zero_le_symmetric_three_point_of_le_one_third {L : ℝ}
    (hL0 : 0 < L) (hL : L ≤ 1 / 3) :
    0 ≤ EF.gammaBracket 0 + (1 / 6) * levyCoshPotential (L / 4) +
        (2 / 3) * levyCoshPotential (L / 2) +
        (1 / 6) * levyCoshPotential (3 * L / 4) := by
  have h13 : 0 ≤ EF.gammaBracket 0 + (1 / 6) * levyCoshPotential ((1 / 3 : ℝ) / 4) +
      (2 / 3) * levyCoshPotential ((1 / 3 : ℝ) / 2) +
      (1 / 6) * levyCoshPotential (3 * (1 / 3 : ℝ) / 4) := by
    have hosc := osculating_le_symmetric_three_point_potential (by norm_num : (0 : ℝ) < 1 / 3)
    have harg : (1 : ℝ) / (Real.pi * (1 / 3)) = 3 / Real.pi := by ring
    rw [harg] at hosc
    have hlog := zero_lt_log_three_div_pi_add_one_sixth_log_four_thirds
    have hγ :=
      RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
    linarith
  have hmono1 : levyCoshPotential ((1 / 3 : ℝ) / 4) ≤ levyCoshPotential (L / 4) :=
    antitoneOn_levyCoshPotential_Ioc
      ⟨by linarith, by linarith [screwSignThreshold_gt]⟩
      ⟨by norm_num, by linarith [screwSignThreshold_gt]⟩ (by linarith)
  have hmono2 : levyCoshPotential ((1 / 3 : ℝ) / 2) ≤ levyCoshPotential (L / 2) :=
    antitoneOn_levyCoshPotential_Ioc
      ⟨by linarith, by linarith [screwSignThreshold_gt]⟩
      ⟨by norm_num, by linarith [screwSignThreshold_gt]⟩ (by linarith)
  have hmono3 : levyCoshPotential (3 * (1 / 3 : ℝ) / 4) ≤ levyCoshPotential (3 * L / 4) :=
    antitoneOn_levyCoshPotential_Ioc
      ⟨by linarith, by linarith [screwSignThreshold_gt]⟩
      ⟨by norm_num, by linarith [screwSignThreshold_gt]⟩ (by linarith)
  linarith

/-- **Unconditional nonnegativity of `weilArchRe` on `(0, L)` for all `L ≤ 1 / 3`**:
every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with `L ≤ 1 / 3` (covering **48.1%**
of `(0, log 2)`) satisfies `0 ≤ W_∞(f ⋆ f̃)` unconditionally without `WindowPositive`! -/
theorem weilArchRe_nonneg_of_support_Ioo_le_one_third {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL : L ≤ 1 / 3)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_13 : ∀ u ∉ Ioo (0 : ℝ) (1 / 3), f u = 0 :=
    fun u hu => hsupp u fun h => hu ⟨h.1, lt_of_lt_of_le h.2 hL⟩
  have hmain := symmetric_three_point_potential_le_weilArchRe hf hfc hf0
    (by norm_num : (0 : ℝ) < 1 / 3) (by linarith [screwSignThreshold_gt])
    (by linarith [screwSignThreshold_lt]) hsupp_13
  have hpot := neg_gammaBracket_zero_le_symmetric_three_point_of_le_one_third
    (by norm_num : (0 : ℝ) < 1 / 3) le_rfl
  have hE0 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact le_trans (mul_nonneg hpot hE0) hmain

/-- **Unconditional `WindowPositive` on `(0, 1 / 3)`**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (1 / 3)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_one_third (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (1 / 3)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_one_third hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

end

end RHTower.WeilLevySymmetricThreePoint
