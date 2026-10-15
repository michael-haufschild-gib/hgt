import GaloisForLFunctions.RHTower.WeilLevyBoundaryEscapeCollarPotential

/-!
# Full Half-Window Reflection Crossover, Collar-Core Decomposition, and Core-to-Collar Transport on `(0, L)`

In `WeilLevyBoundaryEscapeCollarPotential.lean`, we proved:
1. The exact pointwise and integral boundary-escape + interior-Dirichlet decomposition on `(0, L)`:
   `D_h(x) = (∫ u in Iic x, h u ^ 2) + (∫ u in Ioi (L - x), h u ^ 2) + ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`.
2. The complementary shift reflection inequality `2 * ∫ h² ≤ D_h(x) + D_h(L - x)` for `x ∈ [0, L]`.
3. Global monotonicity of `screwRegularKernel` and antitonicity of `archLevyDensity` on `(0, ∞)`.
4. Half-window lower bounds using `D_h(x) ≥ ∫ h²` on `(L / 2, c)`, which retained a factor of `1 / 2`
   on `levyCoshPotential (L / 2)` and `archLevyAntideriv (L / 2)`.

In this module we exploit the **complementary reflection pairing `x ↔ L - x` across the midpoint
`L / 2`** together with the antitonicity of `archLevyDensity` and `-screwRegularKernel` to remove
the factor of `1 / 2`, and we establish the **collar-core decomposition and core-to-collar shift
transport inequality** valid for arbitrary window lengths `L > 0` (including `L = log 2`):

1. **Full Half-Window Jump Energy Bound (`2 * Ω(L / 2) * ∫ h² ≤ jumpEnergy h`)**:
   For every `y ∈ (L / 2, b)` (`L / 2 ≤ b < L`), pairing `L - y ∈ (L - b, L / 2)` with `y` gives
   `ω(L - y) D_h(L - y) + ω(y) D_h(y) ≥ ω(y) (D_h(L - y) + D_h(y)) ≥ 2 ω(y) ∫ h²`.
   Integrating over `y ∈ (L / 2, b)`, adding the `(L, ∞)` tail `2 Ω(L) ∫ h²`, and passing `b → L⁻`
   cancels `-2 Ω(L) + 2 Ω(L) = 0` and proves
   `ENNReal.ofReal (2 * archLevyAntideriv (L / 2) * ∫ u, h u ^ 2) ≤ jumpEnergy h`
   (`ofReal_two_mul_archLevyAntideriv_half_le_jumpEnergy_of_support_Ioo`), and by quantile
   rearrangement for all nonnegative measurable `g` with `volume {x | 0 < g x} ≤ ENNReal.ofReal L`
   (`ofReal_two_mul_archLevyAntideriv_half_le_jumpEnergy_of_volume_pos_le`). This immediately
   doubles the unconditional disconnected-measure positivity threshold from `1 / 130` to `1 / 65`
   (`weilEnergyNonneg_of_volume_pos_le_inv_65`, `weilArchRe_nonneg_of_volume_pos_le_inv_65`).

2. **Full Half-Window Lévy–Cosh Crossover (`(A(0) + Φ(L / 2)) ∫ f² ≤ W_∞(f ⋆ f̃)`)**:
   Pairing `L - y ∈ (L - c, L / 2)` with `y ∈ (L / 2, c)` (`0 < L - c ≤ L / 2 ≤ c ≤ screwSignThreshold`)
   gives `∫_{x ∈ (L - c, c)} (-screwRegularKernel x) D_f(x) ≥ (Φ(L / 2) - Φ(c)) ∫ f²`.
   Combined with `levyCosh_crossover_add_jump_le_weilArchRe` at `δ = L - c > 0`, `Φ(c)` cancels
   algebraically, and choosing `c = min (3 * L / 4) screwSignThreshold` yields the limit-free theorem
   `(EF.gammaBracket 0 + levyCoshPotential (L / 2)) * ∫ f² ≤ weilArchRe` for all nonnegative
   `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` whenever `0 < L ≤ 2 * screwSignThreshold`
   (`full_half_window_levyCoshPotential_le_weilArchRe`).

3. **Collar-Core Decomposition on `(0, L)` for Arbitrary `L > 0` (Including `L = log 2`)**:
   Decomposing `∫ f² = collarMass f L a + coreMass f L a` into the outer collars
   `Iic a ∪ Ioi (L - a)` and the interior core `Ioc a (L - a)` (`0 < a ≤ min (L / 2) c`),
   the collar mass receives the boosted potential `(1 / 2) Φ(a) + (1 / 2) Φ(c)` while the
   interior Dirichlet energy `∫_{x ∈ (a, c)} (-screwRegularKernel x) ∫_{u ∈ Ioc 0 (L - x)} (f(u) - f(u + x))²`
   is retained in full (`collar_core_levyCosh_crossover_le_weilArchRe`). At `a = 1 / 36` and
   `c = screwSignThreshold`, the collar coefficient is strictly positive (`> 1 / 5`), so any
   nonnegative `f` supported on `(0, L)` (for any `L ≥ 1 / 18`, including `L = log 2`) with
   `2 * coreMass f L (1 / 36) ≤ collarMass f L (1 / 36)` satisfies `0 ≤ weilArchRe` unconditionally
   (`weilArchRe_nonneg_of_two_mul_coreMass_le_collarMass`).

4. **Core-to-Collar Shift Transport Inequality on `(0, L)`**:
   For any shift `x` with `a ≤ x` and `a + x ≤ L - a`, shifting `Ioc 0 a` by `+x` transports it into
   the core slice `Ioc x (a + x)` and shifting the core slice `Ioc (L - x - a) (L - x)` by `+x`
   transports it into the right collar `Ioc (L - a) L`, proving
   `(1 / 2) * ((∫ u in Ioc x (a + x), h u ^ 2) + ∫ u in Ioc (L - x - a) (L - x), h u ^ 2) - collarMass h L a ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`
   (`core_slice_sub_collarMass_le_interior_jump_sq`).
-/

open Complex MeasureTheory Set Filter Topology Real
open scoped ENNReal FourierTransform ComplexConjugate
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyCollarCoupling

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape

/-! ## Section 1: Full Half-Window Reflection Pairing for `jumpEnergy` (`2 * Ω(L / 2) * ∫ h² ≤ jumpEnergy h`) -/

/-- Reflection identity for set integrals across the midpoint `L / 2`:
for any `f : ℝ → ℝ` and `b ∈ ℝ`,
`∫ x in Ioo (L - b) (L / 2), f x = ∫ y in Ioo (L / 2) b, f (L - y)`. -/
theorem setIntegral_Ioo_reflect_half (f : ℝ → ℝ) (L b : ℝ) :
    (∫ x in Ioo (L - b) (L / 2), f x) = ∫ y in Ioo (L / 2) b, f (L - y) := by
  have hpre : (fun y : ℝ => -y + L) ⁻¹' Ioo (L - b) (L / 2) = Ioo (L / 2) b := by
    ext y
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith
  have hmeas : MeasurableSet (Ioo (L - b) (L / 2)) := measurableSet_Ioo
  have h1 := integral_add_right_eq_self (μ := volume)
    (fun z : ℝ => (Ioo (L - b) (L / 2)).indicator f z) L
  have h2 := integral_neg_eq_self (μ := volume)
    (fun y : ℝ => (Ioo (L - b) (L / 2)).indicator f (y + L))
  rw [← integral_indicator hmeas, ← h1, ← h2, ← integral_indicator measurableSet_Ioo]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  rw [← Set.indicator_comp_right (fun y : ℝ => -y + L), hpre]
  exact congrArg (fun g => (Ioo (L / 2) b).indicator g y) (funext fun z => congrArg f (by ring))

/-- **Reflected midpoint integral lower bound for `archLevyDensity`**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`) and any `b` with `L / 2 ≤ b < L`,
`2 * (archLevyAntideriv (L / 2) - archLevyAntideriv b) * ∫ u, h u ^ 2 ≤ ∫ x in Ioo (L - b) b, archLevyDensity x * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem two_mul_sub_archLevyAntideriv_half_le_setIntegral_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L b : ℝ} (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0)
    (_hL : 0 < L) (hL2b : L / 2 ≤ b) (hbL : b < L) :
    2 * (archLevyAntideriv (L / 2) - archLevyAntideriv b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L - b) b, archLevyDensity x * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hLb0 : 0 < L - b := by linarith
  have hL2 : 0 < L / 2 := by linarith
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => archLevyDensity x * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold archLevyDensity; fun_prop
  have hcont_ω : ContinuousOn archLevyDensity (Icc (L - b) b) :=
    continuousOn_archLevyDensity.mono fun x hx => lt_of_lt_of_le hLb0 hx.1
  have hIF : IntegrableOn F (Ioo (L - b) b) := by
    refine ((hcont_ω.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hω0 : 0 ≤ archLevyDensity x := (archLevyDensity_pos (lt_trans hLb0 hx.1)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hω0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hω0
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
  have hI_low : IntegrableOn (fun y => archLevyDensity y * (2 * ∫ u, h u ^ 2)) (Ioo (L / 2) b) :=
    ((continuousOn_archLevyDensity.mono fun y hy => lt_of_lt_of_le hL2 hy.1).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self).mul_const _
  have hval : (∫ y in Ioo (L / 2) b, archLevyDensity y * (2 * ∫ u, h u ^ 2)) =
      2 * (archLevyAntideriv (L / 2) - archLevyAntideriv b) * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL2b, integral_archLevyDensity_Icc hL2 hL2b]
    ring
  rw [← hval]
  refine setIntegral_mono_on hI_low (hIF_refl.add hIF_right) measurableSet_Ioo fun y hy => ?_
  dsimp only [F, Pi.add_apply]
  have hy0 : 0 < y := lt_trans hL2 hy.1
  have hLy0 : 0 < L - y := by linarith [hy.2]
  have hLy_le : L - y ≤ y := by linarith [hy.1]
  have hω_le : archLevyDensity y ≤ archLevyDensity (L - y) :=
    WeilLevyBoundaryEscape.antitoneOn_archLevyDensity hLy0 hy0 hLy_le
  have hω0 : 0 ≤ archLevyDensity y := (archLevyDensity_pos hy0).le
  have hsum := two_mul_integral_sq_le_integral_jump_sq_add_sub hh hsupp hy0.le
    (le_trans hy.2.le hbL.le)
  have hstep1 : archLevyDensity y * (2 * ∫ u, h u ^ 2) ≤
      archLevyDensity y * ((∫ u, (h u - h (u + y)) ^ 2) + ∫ u, (h u - h (u + (L - y))) ^ 2) :=
    mul_le_mul_of_nonneg_left hsum hω0
  have hstep2 : archLevyDensity y * (∫ u, (h u - h (u + (L - y))) ^ 2) ≤
      archLevyDensity (L - y) * ∫ u, (h u - h (u + (L - y))) ^ 2 :=
    mul_le_mul_of_nonneg_right hω_le (hD0 (L - y))
  linarith

/-- **Full Half-Window Jump Energy Bound on `(0, L)`**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`),
`ENNReal.ofReal (2 * archLevyAntideriv (L / 2) * ∫ u, h u ^ 2) ≤ jumpEnergy h`. -/
theorem ofReal_two_mul_archLevyAntideriv_half_le_jumpEnergy_of_support_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L : ℝ} (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) :
    ENNReal.ofReal (2 * archLevyAntideriv (L / 2) * ∫ u, h u ^ 2) ≤ jumpEnergy h := by
  have hL2 : 0 < L / 2 := by linarith
  have hE0 : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  have hint2 : IntegrableOn (fun x => archLevyDensity x * (2 * ∫ u, h u ^ 2)) (Ioi L) :=
    (integrableOn_archLevyDensity_Ioi hL).mul_const _
  have hval2 : (∫ x in Ioi L, archLevyDensity x * (2 * ∫ u, h u ^ 2)) =
      2 * archLevyAntideriv L * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, integral_archLevyDensity_Ioi hL]; ring
  have hle2 : ENNReal.ofReal (2 * archLevyAntideriv L * ∫ u, h u ^ 2) ≤
      ∫⁻ x in Ioi L,
        ENNReal.ofReal (archLevyDensity x * ∫ u, (h u - h (u + x)) ^ 2) := by
    rw [← hval2, ofReal_integral_eq_lintegral_ofReal hint2
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx =>
        mul_nonneg (archLevyDensity_pos (lt_trans hL hx)).le (by positivity)))]
    refine setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal ?_
    rw [integral_jump_sq_eq_two_mul_of_support_Ioo hh hsupp (mem_Ioi.mp hx).le]
  let b : ℕ → ℝ := fun n => L - L / (2 * ((n : ℝ) + 1))
  have hseq : ∀ n : ℕ,
      ENNReal.ofReal (2 * (archLevyAntideriv (L / 2) - archLevyAntideriv (b n) +
        archLevyAntideriv L) * ∫ u, h u ^ 2) ≤ jumpEnergy h := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hdiv_pos : 0 < L / (2 * ((n : ℝ) + 1)) := by positivity
    have hdiv_le : L / (2 * ((n : ℝ) + 1)) ≤ L / 2 :=
      div_le_div_of_nonneg_left hL.le (by positivity) (by linarith)
    have hL2b : L / 2 ≤ b n := by dsimp [b]; linarith
    have hbL : b n < L := by dsimp [b]; linarith
    have hLb0 : 0 < L - b n := by linarith
    let F : ℝ → ℝ := fun x => archLevyDensity x * ∫ u, (h u - h (u + x)) ^ 2
    have hFm : Measurable F := by
      refine Measurable.mul ?_ (measurable_jump hh)
      unfold archLevyDensity; fun_prop
    have hcont_ω : ContinuousOn archLevyDensity (Icc (L - b n) (b n)) :=
      continuousOn_archLevyDensity.mono fun x hx => lt_of_lt_of_le hLb0 hx.1
    have hIF : IntegrableOn F (Ioo (L - b n) (b n)) := by
      refine ((hcont_ω.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
        (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
      have hω0 : 0 ≤ archLevyDensity x := (archLevyDensity_pos (lt_trans hLb0 hx.1)).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hω0 (hD0 x))]
      exact mul_le_mul_of_nonneg_left (jump_le hh x) hω0
    have hle1 : ENNReal.ofReal (2 * (archLevyAntideriv (L / 2) - archLevyAntideriv (b n)) *
        ∫ u, h u ^ 2) ≤
        ∫⁻ x in Ioo (L - b n) (b n), ENNReal.ofReal (F x) := by
      calc ENNReal.ofReal (2 * (archLevyAntideriv (L / 2) - archLevyAntideriv (b n)) *
            ∫ u, h u ^ 2)
          ≤ ENNReal.ofReal (∫ x in Ioo (L - b n) (b n), F x) :=
            ENNReal.ofReal_le_ofReal
              (two_mul_sub_archLevyAntideriv_half_le_setIntegral_Ioo hh hsupp hL hL2b hbL)
        _ = ∫⁻ x in Ioo (L - b n) (b n), ENNReal.ofReal (F x) :=
            ofReal_integral_eq_lintegral_ofReal hIF
              ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx =>
                mul_nonneg (archLevyDensity_pos (lt_trans hLb0 hx.1)).le (hD0 x)))
    have hbn0 : 0 < b n := lt_of_lt_of_le hL2 hL2b
    have hpos1 : 0 ≤ 2 * (archLevyAntideriv (L / 2) - archLevyAntideriv (b n)) * ∫ u, h u ^ 2 :=
      mul_nonneg (mul_nonneg zero_le_two
        (sub_nonneg.mpr (antitoneOn_archLevyAntideriv hL2 hbn0 hL2b))) hE0
    have hpos2 : 0 ≤ 2 * archLevyAntideriv L * ∫ u, h u ^ 2 :=
      mul_nonneg (mul_nonneg zero_le_two (archLevyAntideriv_pos hL).le) hE0
    have hsplit_sum : 2 * (archLevyAntideriv (L / 2) - archLevyAntideriv (b n) +
        archLevyAntideriv L) * ∫ u, h u ^ 2 =
        2 * (archLevyAntideriv (L / 2) - archLevyAntideriv (b n)) * (∫ u, h u ^ 2) +
          2 * archLevyAntideriv L * ∫ u, h u ^ 2 := by ring
    have hdisj : Disjoint (Ioo (L - b n) (b n)) (Ioi L) :=
      disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge (hx1.2.le.trans hbL.le) (mem_Ioi.mp hx2)
    rw [hsplit_sum, ENNReal.ofReal_add hpos1 hpos2]
    calc ENNReal.ofReal (2 * (archLevyAntideriv (L / 2) - archLevyAntideriv (b n)) * ∫ u, h u ^ 2) +
          ENNReal.ofReal (2 * archLevyAntideriv L * ∫ u, h u ^ 2)
        ≤ (∫⁻ x in Ioo (L - b n) (b n), ENNReal.ofReal (F x)) +
            ∫⁻ x in Ioi L, ENNReal.ofReal (F x) := add_le_add hle1 hle2
      _ = ∫⁻ x in Ioo (L - b n) (b n) ∪ Ioi L, ENNReal.ofReal (F x) := by
          rw [lintegral_union measurableSet_Ioi hdisj]
      _ ≤ jumpEnergy h := by
          refine lintegral_mono_set fun x hx => ?_
          rcases hx with hx1 | hx2
          · exact lt_trans hLb0 hx1.1
          · exact lt_trans hL hx2
  have hb_lim : Tendsto b atTop (𝓝 L) := by
    have h0 : Tendsto (fun n : ℕ => L / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (Tendsto.const_mul_atTop zero_lt_two
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
    simpa using tendsto_const_nhds.sub h0
  have hΩ_lim : Tendsto (fun n : ℕ => archLevyAntideriv (b n)) atTop (𝓝 (archLevyAntideriv L)) :=
    (hasDerivAt_archLevyAntideriv hL).continuousAt.tendsto.comp hb_lim
  have h_sum : Tendsto (fun n : ℕ => archLevyAntideriv (L / 2) - archLevyAntideriv (b n) +
      archLevyAntideriv L) atTop
      (𝓝 (archLevyAntideriv (L / 2) - archLevyAntideriv L + archLevyAntideriv L)) :=
    (tendsto_const_nhds.sub hΩ_lim).add tendsto_const_nhds
  rw [sub_add_cancel] at h_sum
  have hlim : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (2 * (archLevyAntideriv (L / 2) - archLevyAntideriv (b n) +
        archLevyAntideriv L) * ∫ u, h u ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (2 * archLevyAntideriv (L / 2) * ∫ u, h u ^ 2))) :=
    ENNReal.tendsto_ofReal (Tendsto.mul_const _ (Tendsto.const_mul 2 h_sum))
  exact le_of_tendsto hlim (Eventually.of_forall hseq)

/-- **Quantile-rearranged Full Half-Window Jump Energy Bound**:
for any bounded measurable `g ≥ 0` with `volume {x | 0 < g x} ≤ ENNReal.ofReal L` (`L > 0`),
`ENNReal.ofReal (2 * archLevyAntideriv (L / 2) * ∫ u, g u ^ 2) ≤ jumpEnergy g`. -/
theorem ofReal_two_mul_archLevyAntideriv_half_le_jumpEnergy_of_volume_pos_le {g : ℝ → ℝ}
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) {C L : ℝ} (hgC : ∀ x, g x ≤ C) (hL0 : 0 < L)
    (hvol : volume {x | 0 < g x} ≤ ENNReal.ofReal L) :
    ENNReal.ofReal (2 * archLevyAntideriv (L / 2) * ∫ u, g u ^ 2) ≤ jumpEnergy g := by
  set S := {x | 0 < g x}
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hg
  have hS : volume S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
  have hgB : BddSupp S g C :=
    { meas := hg
      bound := fun x => by rw [abs_of_nonneg (hg0 x)]; exact hgC x
      supp := fun x hx => le_antisymm (not_lt.mp hx) (hg0 x)
      setm := hSm
      fin := hS }
  have hSL : (volume S).toReal ≤ L := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rwa [ENNReal.toReal_ofReal hL0.le] at this
  have hTB := transport_bddSupp hSm hS hgB
  have hTB_L : BddSupp (Ioo 0 L) (transport hSm hS g) C :=
    { meas := hTB.meas
      bound := hTB.bound
      supp := fun x hx => Set.indicator_of_notMem (fun hx' => hx ⟨hx'.1, hx'.2.trans_le hSL⟩) _
      setm := measurableSet_Ioo
      fin := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top }
  have h1 := ofReal_two_mul_archLevyAntideriv_half_le_jumpEnergy_of_support_Ioo hTB_L hTB_L.supp hL0
  rw [integral_sq_transport hSm hS hgB] at h1
  refine h1.trans ?_
  rw [jumpEnergy_eq, jumpEnergy_eq]
  exact lintegral_jump_transport_le hSm hS hgB hg0 measurable_jumpKernel jumpKernel_nonneg
    antitoneOn_jumpKernel integrableOn_min_jumpKernel

/-- **Unconditional `WeilEnergyNonneg` for any nonnegative `g` with `|{g > 0}| ≤ L` and
`-A(0) ≤ 2 Ω(L / 2)`.** -/
theorem weilEnergyNonneg_of_volume_pos_le_half {g : ℝ → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) {C L : ℝ} (hgC : ∀ x, g x ≤ C) (hL0 : 0 < L)
    (hvol : volume {x | 0 < g x} ≤ ENNReal.ofReal L)
    (hΩ : -EF.gammaBracket 0 ≤ 2 * archLevyAntideriv (L / 2)) :
    WeilEnergyNonneg g := by
  unfold WeilEnergyNonneg
  have hE0 : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 : ENNReal.ofReal (-EF.gammaBracket 0 * ∫ u, g u ^ 2) ≤
      ENNReal.ofReal (2 * archLevyAntideriv (L / 2) * ∫ u, g u ^ 2) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hΩ hE0)
  have h2 := ofReal_two_mul_archLevyAntideriv_half_le_jumpEnergy_of_volume_pos_le
    hg hg0 hgC hL0 hvol
  exact (h1.trans h2).trans le_self_add

/-- **Unconditional `WeilEnergyNonneg` for any nonnegative `g` with `|{g > 0}| ≤ 1 / 65`**
(doubling the `1 / 130` disconnected-measure threshold from `WeilLevyPoleGaussModeCancellation`). -/
theorem weilEnergyNonneg_of_volume_pos_le_inv_65 {g : ℝ → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) {C : ℝ} (hgC : ∀ x, g x ≤ C)
    (hvol : volume {x | 0 < g x} ≤ ENNReal.ofReal (1 / 65)) :
    WeilEnergyNonneg g := by
  refine weilEnergyNonneg_of_volume_pos_le_half hg hg0 hgC (by norm_num) hvol ?_
  rw [show (1 / 65 : ℝ) / 2 = 1 / 130 by norm_num]
  exact neg_gammaBracket_zero_le_two_mul_archLevyAntideriv (by norm_num) le_rfl

/-- **Unconditional nonnegativity of `weilArchRe` for any nonnegative `f ∈ C²_c(ℝ)` with
`|{f > 0}| ≤ L` and `-A(0) ≤ 2 Ω(L / 2)`.** -/
theorem weilArchRe_nonneg_of_volume_pos_le_half {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) {L : ℝ} (hL0 : 0 < L)
    (hvol : volume {x | 0 < f x} ≤ ENNReal.ofReal L)
    (hΩ : -EF.gammaBracket 0 ≤ 2 * archLevyAntideriv (L / 2)) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hc := hf.continuous
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, f x ≤ C := by
    obtain ⟨C, hC⟩ := hc.bddAbove_range_of_hasCompactSupport hfc
    exact ⟨C, fun x => hC ⟨x, rfl⟩⟩
  have hE := weilEnergyNonneg_of_volume_pos_le_half hc.measurable hf0 hC hL0 hvol hΩ
  rw [WeilLevyPole.weilArchRe_eq_levy_pole hf hfc]
  unfold WeilEnergyNonneg at hE
  have hJ := jumpEnergy_ne_top_of_smooth hf hfc
  rw [poleEnergy_eq_ofReal hc hfc hf0, ← ENNReal.ofReal_toReal hJ] at hE
  set J := (jumpEnergy f).toReal
  set P := ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)
  have hP0 : 0 ≤ P :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _)) (Real.cosh_pos _).le
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  rw [show (2 : ENNReal) * ENNReal.ofReal P = ENNReal.ofReal (2 * P) by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_add hJ0 (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hE
  change 0 ≤ EF.gammaBracket 0 * (∫ u, f u ^ 2) + J + 2 * P
  linarith

/-- **Unconditional nonnegativity of `weilArchRe` for any nonnegative `f ∈ C²_c(ℝ)` with
`|{f > 0}| ≤ 1 / 65`** (even for disconnected support, without `WindowPositive`). -/
theorem weilArchRe_nonneg_of_volume_pos_le_inv_65 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x)
    (hvol : volume {x | 0 < f x} ≤ ENNReal.ofReal (1 / 65)) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  refine weilArchRe_nonneg_of_volume_pos_le_half hf hfc hf0 (by norm_num) hvol ?_
  rw [show (1 / 65 : ℝ) / 2 = 1 / 130 by norm_num]
  exact neg_gammaBracket_zero_le_two_mul_archLevyAntideriv (by norm_num) le_rfl

/-! ## Section 2: Full Half-Window Reflection Crossover for `levyCoshPotential` (`(A(0) + Φ(L / 2)) ∫ f² ≤ weilArchRe`) -/

/-- **Reflected midpoint integral lower bound for `-screwRegularKernel`**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`) and any `c` with
`L / 2 ≤ c < L` and `c ≤ screwSignThreshold`,
`(levyCoshPotential (L / 2) - levyCoshPotential c) * ∫ u, h u ^ 2 ≤ ∫ x in Ioo (L - c) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem sub_levyCoshPotential_half_le_setIntegral_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L c : ℝ} (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0)
    (_hL : 0 < L) (hL2c : L / 2 ≤ c) (hcL : c < L) (hct : c ≤ screwSignThreshold) :
    (levyCoshPotential (L / 2) - levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L - c) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hLc0 : 0 < L - c := by linarith
  have hL2 : 0 < L / 2 := by linarith
  have hc0 : 0 < c := by linarith
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let G : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hGm : Measurable G := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L - c) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hLc0 hx.1).neg
  have hIG : IntegrableOn G (Ioo (L - c) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hGm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hLc0 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIG_left : IntegrableOn G (Ioo (L - c) (L / 2)) :=
    hIG.mono_set (Ioo_subset_Ioo le_rfl hL2c)
  have hIG_right : IntegrableOn G (Ioo (L / 2) c) :=
    hIG.mono_set (Ioo_subset_Ioo (by linarith) le_rfl)
  have hIG_left_Ioc : IntegrableOn G (Ioc (L - c) (L / 2)) := by
    rwa [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hIG_Ioc : IntegrableOn G (Ioc (L / 2) c) := by
    rwa [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hdisj_Ioc : Disjoint (Ioc (L - c) (L / 2)) (Ioc (L / 2) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L - c) c, G x) =
      (∫ y in Ioo (L / 2) c, G (L - y)) + ∫ y in Ioo (L / 2) c, G y := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (by linarith) hL2c,
      setIntegral_union hdisj_Ioc measurableSet_Ioc hIG_left_Ioc hIG_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
      setIntegral_Ioo_reflect_half]
  have hIG_refl : IntegrableOn (fun y => G (L - y)) (Ioo (L / 2) c) := by
    have hpre : (fun y : ℝ => -y + L) ⁻¹' Ioo (L - c) (L / 2) = Ioo (L / 2) c := by
      ext y; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith
    have h1 : Integrable (fun y : ℝ => (Ioo (L - c) (L / 2)).indicator G (-y + L)) :=
      (((integrable_indicator_iff measurableSet_Ioo).mpr hIG_left).comp_add_right L).comp_neg
    rw [← integrable_indicator_iff measurableSet_Ioo]
    refine h1.congr (ae_of_all _ fun y => ?_)
    dsimp only
    rw [← Set.indicator_comp_right (fun y : ℝ => -y + L), hpre]
    exact congrArg (fun g => (Ioo (L / 2) c).indicator g y) (funext fun z => congrArg G (by ring))
  rw [hsplit, ← integral_add hIG_refl hIG_right]
  have hI_low : IntegrableOn
      (fun y => (-screwRegularKernel y) * (2 * ∫ u, h u ^ 2)) (Ioo (L / 2) c) :=
    (((WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun y hy => lt_of_lt_of_le hL2 hy.1).neg).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self).mul_const _
  have hval : (∫ y in Ioo (L / 2) c, (-screwRegularKernel y) * (2 * ∫ u, h u ^ 2)) =
      (levyCoshPotential (L / 2) - levyCoshPotential c) * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL2c]
    have hFTC := integral_two_mul_screwRegularKernel hL2 hc0
    have hneg : (∫ y in (L / 2)..c, -screwRegularKernel y) =
        -(1 / 2) * ∫ y in (L / 2)..c, 2 * screwRegularKernel y := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun y _ => by ring
    rw [hneg, hFTC]
    ring
  rw [← hval]
  refine setIntegral_mono_on hI_low (hIG_refl.add hIG_right) measurableSet_Ioo fun y hy => ?_
  dsimp only [G, Pi.add_apply]
  have hy0 : 0 < y := lt_trans hL2 hy.1
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

/-- **Full Half-Window Lévy–Cosh Crossover on `(0, L)` (all signed `f ∈ C²_c(ℝ)`)**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and every `c` with
`L / 2 ≤ c < L` and `c ≤ screwSignThreshold`,
`(A(0) + levyCoshPotential (L / 2)) ∫ f² + ∫∫ f(u) f(v) (2 cosh((u - v)/2) - levyCoshKernel c |u - v|) du dv ≤ W_∞(f ⋆ f̃)`. -/
theorem full_half_window_levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {L c : ℝ} (hL0 : 0 < L) (hL2c : L / 2 ≤ c)
    (hcL : c < L) (hct : c ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + levyCoshPotential (L / 2)) * (∫ u, f u ^ 2) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hLc0 : 0 < L - c := by linarith
  have hLcc : L - c ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hLc0 hLcc hct
  have hrefl := sub_levyCoshPotential_half_le_setIntegral_Ioo hB hsupp hL0 hL2c hcL hct
  linarith

/-- **Full Half-Window Signed Short-Support Floor (`0 < L ≤ screwSignThreshold`)**:
for **every signed** `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with `0 < L ≤ screwSignThreshold`,
`(EF.gammaBracket 0 + levyCoshPotential (L / 2)) * ∫ u, f u ^ 2 ≤ W_∞(f ⋆ f̃)`. -/
theorem full_half_window_signed_short_support_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {L : ℝ} (hL0 : 0 < L) (hLt : L ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + levyCoshPotential (L / 2)) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hD0 : ∀ x, 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hB
  have hpair0 : (∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel L |p.1 - p.2|)) = 0 := by
    have hzero : ∀ p : ℝ × ℝ,
        f p.1 * f p.2 * (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel L |p.1 - p.2|) = 0 := by
      intro p
      by_cases hp1 : p.1 ∈ Ioo 0 L
      · by_cases hp2 : p.2 ∈ Ioo 0 L
        · have habs : |p.1 - p.2| ≤ L := abs_le.mpr ⟨by linarith [hp1.1, hp2.2],
            by linarith [hp1.2, hp2.1]⟩
          rw [two_mul_cosh_sub_levyCoshKernel_eq hL0, if_pos habs, mul_zero]
        · rw [hsupp p.2 hp2, mul_zero, zero_mul]
      · rw [hsupp p.1 hp1, zero_mul, zero_mul]
    simp_rw [hzero, integral_zero]
  let b : ℕ → ℝ := fun n => L - L / (2 * ((n : ℝ) + 1))
  have hseq : ∀ n : ℕ,
      (EF.gammaBracket 0 + levyCoshPotential L +
        (levyCoshPotential (L / 2) - levyCoshPotential (b n))) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hdiv_pos : 0 < L / (2 * ((n : ℝ) + 1)) := by positivity
    have hdiv_le : L / (2 * ((n : ℝ) + 1)) ≤ L / 2 :=
      div_le_div_of_nonneg_left hL0.le (by positivity) (by linarith)
    have hL2b : L / 2 ≤ b n := by dsimp [b]; linarith
    have hbL : b n < L := by dsimp [b]; linarith
    have hLb0 : 0 < L - b n := by linarith
    have hLbL : L - b n ≤ L := by linarith
    have hbt : b n ≤ screwSignThreshold := hbL.le.trans hLt
    have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hLb0 hLbL hLt
    rw [hpair0, add_zero] at hmain
    have hrefl := sub_levyCoshPotential_half_le_setIntegral_Ioo hB hsupp hL0 hL2b hbL hbt
    have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L - b n) L) :=
      (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
        fun x hx => lt_of_lt_of_le hLb0 hx.1).neg
    have hIG_full : IntegrableOn
        (fun x => (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2) (Ioo (L - b n) L) := by
      refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
        (4 * ∫ u, f u ^ 2)).mono' (hKm.mul hDm).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
      have hK0 : 0 ≤ -screwRegularKernel x :=
        neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
          (lt_trans hLb0 hx.1) (hx.2.le.trans hLt))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
      exact mul_le_mul_of_nonneg_left (jump_le hB x) hK0
    have hmono : (∫ x in Ioo (L - b n) (b n),
        (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2) ≤
        ∫ x in Ioo (L - b n) L, (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2 := by
      refine setIntegral_mono_set hIG_full ?_
        (Eventually.of_forall (Ioo_subset_Ioo le_rfl hbL.le))
      refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_)
      exact mul_nonneg (neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hLb0 hx.1) (hx.2.le.trans hLt))) (hD0 x)
    linarith
  have hb_lim : Tendsto b atTop (𝓝 L) := by
    have h0 : Tendsto (fun n : ℕ => L / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (Tendsto.const_mul_atTop zero_lt_two
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
    simpa using tendsto_const_nhds.sub h0
  have hΦ_lim : Tendsto (fun n : ℕ => levyCoshPotential (b n)) atTop (𝓝 (levyCoshPotential L)) :=
    (hasDerivAt_levyCoshPotential hL0).continuousAt.tendsto.comp hb_lim
  have hcoeff_lim : Tendsto (fun n : ℕ =>
      EF.gammaBracket 0 + levyCoshPotential L +
        (levyCoshPotential (L / 2) - levyCoshPotential (b n))) atTop
      (𝓝 (EF.gammaBracket 0 + levyCoshPotential L +
        (levyCoshPotential (L / 2) - levyCoshPotential L))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.sub hΦ_lim)
  rw [show EF.gammaBracket 0 + levyCoshPotential L +
      (levyCoshPotential (L / 2) - levyCoshPotential L) =
      EF.gammaBracket 0 + levyCoshPotential (L / 2) by ring] at hcoeff_lim
  exact le_of_tendsto (hcoeff_lim.mul_const _) (Eventually.of_forall hseq)

/-- **Full Half-Window Potential Floor on the Nonnegative Cone
(`0 < L ≤ 2 * screwSignThreshold`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with
`0 < L / 2 ≤ screwSignThreshold` (i.e. all `0 < L ≤ 2 * screwSignThreshold ≈ 0.5624`),
`(EF.gammaBracket 0 + levyCoshPotential (L / 2)) * ∫ u, f u ^ 2 ≤ W_∞(f ⋆ f̃)`. -/
theorem full_half_window_levyCoshPotential_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL0 : 0 < L)
    (hLt : L / 2 ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + levyCoshPotential (L / 2)) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  rcases le_or_gt L screwSignThreshold with hle | hgt
  · exact full_half_window_signed_short_support_le_weilArchRe hf hfc hL0 hle hsupp
  · have hmain := full_half_window_levyCosh_crossover_le_weilArchRe
      hf hfc hL0 hLt hgt le_rfl hsupp
    have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
      integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
        (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
    linarith

/-- **Unconditional positivity on `(0, L)` whenever `-A(0) ≤ levyCoshPotential (L / 2)`**:
for any nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with
`0 < L / 2 ≤ screwSignThreshold` and `-EF.gammaBracket 0 ≤ levyCoshPotential (L / 2)`,
`0 ≤ W_∞(f ⋆ f̃)` holds unconditionally without `WindowPositive`. -/
theorem weilArchRe_nonneg_of_support_Ioo_of_full_half_window {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL0 : 0 < L)
    (hLt : L / 2 ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0)
    (hΦ : -EF.gammaBracket 0 ≤ levyCoshPotential (L / 2)) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := full_half_window_levyCoshPotential_le_weilArchRe hf hfc hf0 hL0 hLt hsupp
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-! ## Section 3: Collar-Core Decomposition and Collar-Boosted Lévy–Cosh Inequality on `(0, L)` (Valid for Arbitrary `L > 0`, Including `L = log 2`) -/

/-- The `L²` mass of `h` in the outer collars `Iic a ∪ Ioi (L - a)` of width `a` inside `(0, L)`. -/
def collarMass (h : ℝ → ℝ) (L a : ℝ) : ℝ :=
  (∫ u in Iic a, h u ^ 2) + ∫ u in Ioi (L - a), h u ^ 2

/-- The `L²` mass of `h` in the interior core `Ioc a (L - a)` inside `(0, L)`. -/
def coreMass (h : ℝ → ℝ) (L a : ℝ) : ℝ :=
  ∫ u in Ioc a (L - a), h u ^ 2

/-- Both `collarMass` and `coreMass` are nonnegative. -/
theorem collarMass_nonneg (h : ℝ → ℝ) (L a : ℝ) : 0 ≤ collarMass h L a :=
  add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)

theorem coreMass_nonneg (h : ℝ → ℝ) (L a : ℝ) : 0 ≤ coreMass h L a :=
  integral_nonneg fun _ => sq_nonneg _

/-- **Exact `L²` conservation between collar and core (`a ≤ L / 2`)**:
for any `BddSupp A h C` and any `a ≤ L / 2`,
`collarMass h L a + coreMass h L a = ∫ u, h u ^ 2`. -/
theorem collarMass_add_coreMass_eq {A : Set ℝ} {h : ℝ → ℝ} {C L a : ℝ}
    (hh : BddSupp A h C) (haL : a ≤ L / 2) :
    collarMass h L a + coreMass h L a = ∫ u, h u ^ 2 := by
  unfold collarMass coreMass
  have ha_le : a ≤ L - a := by linarith
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hsplit : (∫ u in Ioi a, h u ^ 2) =
      (∫ u in Ioc a (L - a), h u ^ 2) + ∫ u in Ioi (L - a), h u ^ 2 := by
    rw [← Ioc_union_Ioi_eq_Ioi ha_le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hsq.integrableOn hsq.integrableOn]
  have hp := setIntegral_Iic_add_Ioi_sq hh a
  linarith

/-- `collarMass h L a` is monotone in the collar width `a`. -/
theorem collarMass_mono {A : Set ℝ} {h : ℝ → ℝ} {C L a b : ℝ}
    (hh : BddSupp A h C) (hab : a ≤ b) :
    collarMass h L a ≤ collarMass h L b := by
  unfold collarMass
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have h1 : (∫ u in Iic a, h u ^ 2) ≤ ∫ u in Iic b, h u ^ 2 :=
    setIntegral_mono_set hsq.integrableOn
      (ae_of_all _ fun _ => sq_nonneg _) (Eventually.of_forall (Iic_subset_Iic.mpr hab))
  have h2 : (∫ u in Ioi (L - a), h u ^ 2) ≤ ∫ u in Ioi (L - b), h u ^ 2 :=
    setIntegral_mono_set hsq.integrableOn
      (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall (Ioi_subset_Ioi (by linarith)))
  linarith

/-- For any `BddSupp A h C` vanishing outside `Ioo 0 L` and any `0 ≤ a ≤ x`,
`collarMass h L a + ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem collarMass_add_interior_le_integral_jump_sq {A : Set ℝ} {h : ℝ → ℝ} {C L a x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (ha0 : 0 ≤ a) (hax : a ≤ x) :
    collarMass h L a + (∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2) ≤
      ∫ u, (h u - h (u + x)) ^ 2 := by
  have hx0 : 0 ≤ x := le_trans ha0 hax
  rw [integral_jump_sq_eq_boundary_escape_add_interior hh hsupp hx0]
  have hmono := collarMass_mono (L := L) hh hax
  unfold collarMass at hmono ⊢
  linarith

/-- **Collar-Core Lévy–Cosh Crossover Inequality on `(0, L)` (Valid for All `L > 0`, Including `L = log 2`)**:
for every signed `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L`, and every `a, c` with
`0 < a ≤ c ≤ screwSignThreshold` and `a ≤ L / 2`,
`(A(0) + (1 / 2) Φ(a) + (1 / 2) Φ(c)) collarMass f L a + (A(0) + Φ(c)) coreMass f L a`
`+ ∫_{x ∈ Ioo a c} (-screwRegularKernel x) (∫_{u ∈ Ioc 0 (L - x)} (f u - f (u + x))²) dx`
`+ ∫∫ f(u) f(v) (2 cosh((u - v)/2) - levyCoshKernel c |u - v|) du dv ≤ W_∞(f ⋆ f̃)`. -/
theorem collar_core_levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {L a c : ℝ} (ha0 : 0 < a) (hac : a ≤ c)
    (hct : c ≤ screwSignThreshold) (haL : a ≤ L / 2) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 2) * levyCoshPotential a + (1 / 2) * levyCoshPotential c) *
        collarMass f L a +
      (EF.gammaBracket 0 + levyCoshPotential c) * coreMass f L a +
      (∫ x in Ioo a c,
        (-screwRegularKernel x) * (∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2)) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hc0 : 0 < c := lt_of_lt_of_le ha0 hac
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc ha0 hac hct
  have hcons := collarMass_add_coreMass_eq hB haL
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc a c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le ha0 hx.1).neg
  have hI_K_Ioo : IntegrableOn (fun x => -screwRegularKernel x) (Ioo a c) :=
    hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hB
  have hD0 : ∀ x, 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  have hI_jump : IntegrableOn
      (fun x : ℝ => (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2) (Ioo a c) := by
    refine (hI_K_Ioo.mul_const (4 * ∫ u, f u ^ 2)).mono'
      (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans ha0 hx.1)
        (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hB x) hK0
  -- Measurability & integrability of the interior Dirichlet energy on `Ioo a c` (`0 < a`)
  have hm_left : Monotone fun x : ℝ => ∫ u in Iic x, f u ^ 2 := fun x y hxy =>
    setIntegral_mono_set hB.integrable_sq.integrableOn
      (ae_of_all _ fun _ => sq_nonneg _) (Eventually.of_forall (Iic_subset_Iic.mpr hxy))
  have hm_right : Monotone fun x : ℝ => ∫ u in Ioi (L - x), f u ^ 2 := fun x y hxy =>
    setIntegral_mono_set hB.integrable_sq.integrableOn
      (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall (Ioi_subset_Ioi (by linarith)))
  let intJ : ℝ → ℝ := fun x =>
    if 0 ≤ x then
      (∫ u, (f u - f (u + x)) ^ 2) - ((∫ u in Iic x, f u ^ 2) + ∫ u in Ioi (L - x), f u ^ 2)
    else 0
  have hintJ_m : Measurable intJ :=
    Measurable.ite measurableSet_Ici
      (hDm.sub (hm_left.measurable.add hm_right.measurable)) measurable_const
  have hintJ_eq : ∀ x ∈ Ioo a c,
      intJ x = ∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := (lt_trans ha0 hx.1).le
    dsimp [intJ]
    rw [if_pos hx0, integral_jump_sq_eq_boundary_escape_add_interior hB hsupp hx0]
    ring
  have hI_int : IntegrableOn
      (fun x : ℝ => (-screwRegularKernel x) * ∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2)
      (Ioo a c) := by
    have hmeas_ae : AEStronglyMeasurable
        (fun x : ℝ => (-screwRegularKernel x) * ∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2)
        (volume.restrict (Ioo a c)) := by
      refine (hKm.mul hintJ_m).aestronglyMeasurable.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      dsimp only [Pi.mul_apply]
      rw [hintJ_eq x hx]
    refine hI_jump.mono' hmeas_ae
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hx0 : 0 ≤ x := (lt_trans ha0 hx.1).le
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans ha0 hx.1)
        (hx.2.le.trans hct))
    have hint0 : 0 ≤ ∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hint_le : (∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2) ≤
        ∫ u, (f u - f (u + x)) ^ 2 := by
      rw [integral_jump_sq_eq_boundary_escape_add_interior hB hsupp hx0]
      have h1 : 0 ≤ ∫ u in Iic x, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
      have h2 : 0 ≤ ∫ u in Ioi (L - x), f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 hint0)]
    exact mul_le_mul_of_nonneg_left hint_le hK0
  have hval : (∫ x in Ioo a c, (-screwRegularKernel x) * collarMass f L a) =
      (1 / 2) * (levyCoshPotential a - levyCoshPotential c) * collarMass f L a := by
    rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hac]
    have hFTC := integral_two_mul_screwRegularKernel ha0 hc0
    have hneg : (∫ x in a..c, -screwRegularKernel x) =
        -(1 / 2) * ∫ x in a..c, 2 * screwRegularKernel x := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => by ring
    rw [hneg, hFTC]
    ring
  have hmono : (∫ x in Ioo a c, (-screwRegularKernel x) * collarMass f L a) +
      (∫ x in Ioo a c,
        (-screwRegularKernel x) * (∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2)) ≤
      ∫ x in Ioo a c, (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2 := by
    rw [← integral_add (hI_K_Ioo.mul_const _) hI_int]
    refine setIntegral_mono_on ((hI_K_Ioo.mul_const _).add hI_int) hI_jump measurableSet_Ioo
      fun x hx => ?_
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans ha0 hx.1)
        (hx.2.le.trans hct))
    have hcol := collarMass_add_interior_le_integral_jump_sq hB hsupp ha0.le hx.1.le
    calc (-screwRegularKernel x) * collarMass f L a +
          (-screwRegularKernel x) * (∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2)
        = (-screwRegularKernel x) *
            (collarMass f L a + ∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2) := by ring
      _ ≤ (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2 :=
          mul_le_mul_of_nonneg_left hcol hK0
  rw [← hcons] at hmain
  linarith

/-- **Collar-Core Plastic-Number Floor on the Nonnegative Cone (All `L > 0`, Including `L = log 2`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` and every collar width
`0 < a ≤ min (L / 2) screwSignThreshold`,
`(A(0) + (1 / 2) Φ(a) + (1 / 2) Φ(t_*)) collarMass f L a + (A(0) + Φ(t_*)) coreMass f L a`
`+ ∫_{x ∈ Ioo a t_*} (-screwRegularKernel x) (∫_{u ∈ Ioc 0 (L - x)} (f u - f (u + x))²) dx ≤ W_∞(f ⋆ f̃)`. -/
theorem collar_core_plastic_floor_add_interior_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L a : ℝ} (ha0 : 0 < a)
    (hat : a ≤ screwSignThreshold) (haL : a ≤ L / 2) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 2) * levyCoshPotential a +
        (1 / 2) * levyCoshPotential screwSignThreshold) * collarMass f L a +
      (EF.gammaBracket 0 + levyCoshPotential screwSignThreshold) * coreMass f L a +
      (∫ x in Ioo a screwSignThreshold,
        (-screwRegularKernel x) * (∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := collar_core_levyCosh_crossover_le_weilArchRe hf hfc ha0 hat le_rfl haL hsupp
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-- Dropping the nonnegative interior Dirichlet energy gives the pure collar-core potential bound
on the nonnegative cone. -/
theorem collar_core_plastic_floor_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L a : ℝ} (ha0 : 0 < a)
    (hat : a ≤ screwSignThreshold) (haL : a ≤ L / 2) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 2) * levyCoshPotential a +
        (1 / 2) * levyCoshPotential screwSignThreshold) * collarMass f L a +
      (EF.gammaBracket 0 + levyCoshPotential screwSignThreshold) * coreMass f L a ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := collar_core_plastic_floor_add_interior_le_weilArchRe hf hfc hf0 ha0 hat haL hsupp
  have hint_nn : 0 ≤ ∫ x in Ioo a screwSignThreshold,
      (-screwRegularKernel x) * (∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2) := by
    refine setIntegral_nonneg measurableSet_Ioo fun x hx => ?_
    exact mul_nonneg
      (neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans ha0 hx.1) hx.2.le))
      (integral_nonneg fun _ => sq_nonneg _)
  linarith

/-- Elementary upper bound `log π ≤ 2 * log 2 + π / 4 - 1` from `π = 4 * (π / 4)` and
`log x ≤ x - 1`. -/
theorem log_pi_le_quarter : Real.log Real.pi ≤ 2 * Real.log 2 + Real.pi / 4 - 1 := by
  have hpi : Real.pi = 4 * (Real.pi / 4) := by ring
  have hpos : 0 < Real.pi / 4 := by positivity
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]; ring
  have h1 : Real.log Real.pi = 2 * Real.log 2 + Real.log (Real.pi / 4) := by
    conv_lhs => rw [hpi]
    rw [Real.log_mul (by norm_num) hpos.ne', h4]
  have h2 : Real.log (Real.pi / 4) ≤ Real.pi / 4 - 1 := Real.log_le_sub_one_of_pos hpos
  linarith

/-- **Sharpened rational upper bound**: `-EF.gammaBracket 0 < 11 / 2` (`= 5.5`). -/
theorem neg_gammaBracket_zero_lt_eleven_halves : -EF.gammaBracket 0 < 11 / 2 := by
  rw [neg_gammaBracket_zero_eq]
  have h1 := log_pi_le_quarter
  have h2 := Real.log_two_lt_d9
  have h3 := Real.eulerMascheroniConstant_lt_two_thirds
  have h4 := Real.pi_lt_d4
  linarith

/-- **Concrete rational collar-core lower bound at collar width `a = 1 / 36` (valid for all
`L ≥ 1 / 18`, including `L = log 2`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`1 / 18 ≤ L`),
`(1 / 10) * collarMass f L (1 / 36) - (3 / 10) * coreMass f L (1 / 36)`
`+ ∫_{x ∈ Ioo (1/36) t_*} (-screwRegularKernel x) (∫_{u ∈ Ioc 0 (L - x)} (f u - f (u + x))²) dx ≤ W_∞(f ⋆ f̃)`. -/
theorem rational_collar_core_add_interior_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL : 1 / 18 ≤ L)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (1 / 10 : ℝ) * collarMass f L (1 / 36) - (3 / 10 : ℝ) * coreMass f L (1 / 36) +
      (∫ x in Ioo (1 / 36) screwSignThreshold,
        (-screwRegularKernel x) * (∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hat : (1 : ℝ) / 36 ≤ screwSignThreshold := by linarith [screwSignThreshold_gt]
  have haL : (1 : ℝ) / 36 ≤ L / 2 := by linarith
  have hmain := collar_core_plastic_floor_add_interior_le_weilArchRe
    hf hfc hf0 (by norm_num : (0 : ℝ) < 1 / 36) hat haL hsupp
  have h6 : (6 : ℝ) ≤ levyCoshPotential (1 / 36) :=
    six_le_levyCoshPotential_of_le_inv_36 (by norm_num) le_rfl
  have h26 := twenty_six_fifths_lt_levyCoshPotential_screwSignThreshold
  have hA := neg_gammaBracket_zero_lt_eleven_halves
  have hcol_nn := collarMass_nonneg f L (1 / 36)
  have hcor_nn := coreMass_nonneg f L (1 / 36)
  have hcoeff1 : (1 / 10 : ℝ) ≤ EF.gammaBracket 0 + (1 / 2) * levyCoshPotential (1 / 36) +
      (1 / 2) * levyCoshPotential screwSignThreshold := by linarith
  have hcoeff2 : -(3 / 10 : ℝ) ≤ EF.gammaBracket 0 + levyCoshPotential screwSignThreshold := by
    linarith
  nlinarith

/-- **Unconditional positivity on `(0, L)` (for any `L ≥ 1 / 18`, including `L = log 2`) whenever
`3 * coreMass f L (1 / 36) ≤ collarMass f L (1 / 36)`**:
every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`1 / 18 ≤ L`) whose collar mass
in `Iic (1 / 36) ∪ Ioi (L - 1 / 36)` is at least three times its core mass in
`Ioc (1 / 36) (L - 1 / 36)` satisfies `0 ≤ W_∞(f ⋆ f̃)` unconditionally (without `WindowPositive`). -/
theorem weilArchRe_nonneg_of_three_mul_coreMass_le_collarMass {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL : 1 / 18 ≤ L)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0)
    (hdom : 3 * coreMass f L (1 / 36) ≤ collarMass f L (1 / 36)) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := rational_collar_core_add_interior_le_weilArchRe hf hfc hf0 hL hsupp
  have hint_nn : 0 ≤ ∫ x in Ioo (1 / 36) screwSignThreshold,
      (-screwRegularKernel x) * (∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2) := by
    refine setIntegral_nonneg measurableSet_Ioo fun x hx => ?_
    exact mul_nonneg
      (neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans (by norm_num) hx.1) hx.2.le))
      (integral_nonneg fun _ => sq_nonneg _)
  linarith

/-! ## Section 4: Core-to-Collar Shift Transport Inequality on `(0, L)` -/

/-- Elementary quadratic transport inequality `(1 / 2) p² - q² ≤ (p - q)²`,
with exact identity `(p - q)² - ((1 / 2) p² - q²) = (1 / 2) (p - 2 q)²`. -/
theorem half_sq_sub_sq_le_sub_sq (p q : ℝ) :
    (1 / 2 : ℝ) * p ^ 2 - q ^ 2 ≤ (p - q) ^ 2 := by
  have : (p - q) ^ 2 - ((1 / 2 : ℝ) * p ^ 2 - q ^ 2) = (1 / 2 : ℝ) * (p - 2 * q) ^ 2 := by ring
  have hnn : 0 ≤ (1 / 2 : ℝ) * (p - 2 * q) ^ 2 := by positivity
  linarith

/-- Translation identity for set integrals over `Ioc`:
`∫ u in Ioc c d, g (u + x) = ∫ v in Ioc (c + x) (d + x), g v`. -/
theorem setIntegral_Ioc_add_right (g : ℝ → ℝ) (c d x : ℝ) :
    (∫ u in Ioc c d, g (u + x)) = ∫ v in Ioc (c + x) (d + x), g v := by
  have hpre : (fun u : ℝ => u + x) ⁻¹' Ioc (c + x) (d + x) = Ioc c d := by
    ext u; simp only [mem_preimage, mem_Ioc]; constructor <;> intro h <;> constructor <;> linarith
  have h1 := integral_add_right_eq_self (μ := volume)
    (fun v : ℝ => (Ioc (c + x) (d + x)).indicator g v) x
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc, ← h1]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  dsimp only
  rw [← Set.indicator_comp_right (fun u : ℝ => u + x), hpre]
  rfl

/-- **Core-to-Collar Shift Transport Inequality on `(0, L)`**:
for any `BddSupp A h C` and any collar width `0 ≤ a` and shift `x` with `a ≤ x` and
`2 * a + x ≤ L` (so `a ≤ L - x - a`), shifting `Ioc 0 a` by `+x` transports it into the core slice
`Ioc x (a + x)` and shifting the core slice `Ioc (L - x - a) (L - x)` by `+x` transports it into
the right collar `Ioc (L - a) L`, yielding:
`(1 / 2) * ((∫ v in Ioc x (a + x), h v ^ 2) + ∫ u in Ioc (L - x - a) (L - x), h u ^ 2) - collarMass h L a ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`. -/
theorem core_slice_sub_collarMass_le_interior_jump_sq {A : Set ℝ} {h : ℝ → ℝ} {C L a x : ℝ}
    (hh : BddSupp A h C) (ha0 : 0 ≤ a) (_hax : a ≤ x) (h2axL : 2 * a + x ≤ L) :
    (1 / 2 : ℝ) *
        ((∫ v in Ioc x (a + x), h v ^ 2) + ∫ u in Ioc (L - x - a) (L - x), h u ^ 2) -
      collarMass h L a ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  -- Left transport: on `Ioc 0 a`, `(1/2) h(u + x)² - h(u)² ≤ (h(u) - h(u + x))²`
  have hleft_pt : ∀ u : ℝ, (1 / 2 : ℝ) * h (u + x) ^ 2 - h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := half_sq_sub_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have hleft_int : (1 / 2 : ℝ) * (∫ v in Ioc x (a + x), h v ^ 2) - (∫ u in Iic a, h u ^ 2) ≤
      ∫ u in Ioc 0 a, (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc 0 a)
      ((hshift.const_mul (1 / 2)).integrableOn.sub hsq.integrableOn)
      hjump.integrableOn hleft_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (1 / 2)).integrableOn hsq.integrableOn,
      integral_const_mul, setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 a x, zero_add] at h1
    have hIoc_le_Iic : (∫ u in Ioc 0 a, h u ^ 2) ≤ ∫ u in Iic a, h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Iic_self)
    linarith
  -- Right transport: on `Ioc (L - x - a) (L - x)`, `(1/2) h(u)² - h(u + x)² ≤ (h(u) - h(u + x))²`
  have hright_pt : ∀ u : ℝ, (1 / 2 : ℝ) * h u ^ 2 - h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => half_sq_sub_sq_le_sub_sq (h u) (h (u + x))
  have hright_int : (1 / 2 : ℝ) * (∫ u in Ioc (L - x - a) (L - x), h u ^ 2) -
      (∫ v in Ioi (L - a), h v ^ 2) ≤
      ∫ u in Ioc (L - x - a) (L - x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - x - a) (L - x))
      ((hsq.const_mul (1 / 2)).integrableOn.sub hshift.integrableOn)
      hjump.integrableOn hright_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (1 / 2)).integrableOn hshift.integrableOn,
      integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - x - a) (L - x) x,
      show L - x - a + x = L - a by ring, show L - x + x = L by ring] at h1
    have hIoc_le_Ioi : (∫ v in Ioc (L - a) L, h v ^ 2) ≤ ∫ v in Ioi (L - a), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Ioi_self)
    linarith
  -- Disjoint union `Ioc 0 a ∪ Ioc (L - x - a) (L - x) ⊆ Ioc 0 (L - x)` since `a ≤ L - x - a`
  have hdisj : Disjoint (Ioc 0 a) (Ioc (L - x - a) (L - x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hsub : Ioc 0 a ∪ Ioc (L - x - a) (L - x) ⊆ Ioc 0 (L - x) := by
    intro u hu
    rcases hu with hu1 | hu2
    · exact ⟨hu1.1, by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], hu2.2⟩
  have hunion_le : (∫ u in Ioc 0 a, (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (L - x - a) (L - x), (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj measurableSet_Ioc hjump.integrableOn hjump.integrableOn]
    exact setIntegral_mono_set hjump.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall hsub)
  unfold collarMass
  linarith

end

end RHTower.WeilLevyCollarCoupling

