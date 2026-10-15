import GaloisForLFunctions.RHTower.WeilLevyOsculatingPotentialFloor

/-!
# Quarter-Window Jump Coercivity (`x ≥ L / 4`), Quarter-Window Lévy–Cosh Crossover on `(0, log 2)`, and Hybrid Quarter-Half Window Bounds

In `WeilLevyBoundaryEscapeCollarPotential.lean` and `WeilLevyCollarInteriorCoupling.lean`,
the half-window bound `∫ u, h u ^ 2 ≤ ∫ u, (h u - h (u + x)) ^ 2` required shifts `x ≥ L / 2`.
For the prime-blind window `L = log 2 ≈ 0.69315`, however, `L / 2 ≈ 0.34657` lies **above**
Suzuki's plastic-number sign threshold `screwSignThreshold ≈ 0.2812`, so the half-window bound
could not be applied directly inside `(0, screwSignThreshold)` at `L = log 2`.

In this module we combine the collar-cancelled core-slice inequality
`half_core_slice_le_integral_jump_sq` from `WeilLevyOsculatingPotentialFloor.lean` with the
collar bound `collarMass h L x ≤ D_h(x)` and `L²` conservation `collarMass + coreMass = ∫ h²`
to break the `L / 2` barrier down to `L / 4`:

1. **Quarter-Window Core-Mass Coercivity (`half_coreMass_le_integral_jump_sq_of_quarter_le`)**:
   For any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and any shift `x ∈ [L / 4, L / 2]`,
   choosing `a = min x ((L - x) / 2)` in `half_core_slice_le_integral_jump_sq` covers the entire
   core `Ioc x (L - x)` by the two core slices `Ioc x (a + x)` and `Ioc (L - x - a) (L - x)`
   (since `L / 4 ≤ x` implies `L - x - a ≤ a + x`), proving:
   `(1 / 2) * coreMass h L x ≤ ∫ u, (h u - h (u + x)) ^ 2`.

2. **Universal Quarter-Window Jump Coercivity (`one_third_mul_integral_sq_le_integral_jump_sq_of_quarter_le`)**:
   Taking `(1 / 3) * collarMass h L x + (2 / 3) * ((1 / 2) * coreMass h L x)` for `x ∈ [L / 4, L / 2]`
   and `integral_sq_le_integral_jump_sq_of_half_le` for `x ≥ L / 2` proves that for **every**
   signed `BddSupp A h C` vanishing outside `Ioo 0 L` and **every shift `x ≥ L / 4`**,
   `(1 / 3) * ∫ u, h u ^ 2 ≤ ∫ u, (h u - h (u + x)) ^ 2`,
   or equivalently `2 * autocorr h x ≤ (5 / 3) * ∫ u, h u ^ 2`
   (`two_mul_autocorr_le_five_thirds_mul_integral_sq_of_quarter_le`).

3. **Quarter-Window Lévy–Cosh Crossover on `(0, L)` (`L ≤ 4 * screwSignThreshold ≈ 1.1248`,
   Including `L = log 2 ≈ 0.69315`)**:
   Because `(log 2) / 4 ≈ 0.17329 < 7 / 40 = 0.175 < screwSignThreshold ≈ 0.2812`, the
   quarter-window shift zone `(L / 4, screwSignThreshold)` is non-empty for `L = log 2`.
   Integrating `(-screwRegularKernel x) * D_f(x)` over `Ioo (L / 4) c` yields:
   - `quarter_window_levyCosh_crossover_le_weilArchRe` (all signed `f ∈ C²_c(ℝ)` on `(0, L)`):
     `(A(0) + (1 / 6) Φ(L / 4) + (5 / 6) Φ(c)) ∫ f² + pair_c(f) ≤ W_∞(f ⋆ f̃)`.
   - `quarter_window_plastic_floor_le_weilArchRe` (all nonnegative `f ∈ C²_c(ℝ)` on `(0, L)`
     with `0 < L / 4 ≤ screwSignThreshold`):
     `(A(0) + (1 / 6) Φ(L / 4) + (5 / 6) Φ(t_*)) ∫ f² ≤ W_∞(f ⋆ f̃)`.
   - `quarter_window_log_two_plastic_floor_le_weilArchRe`: unconditional lower bound on the
     full prime-blind window `(0, log 2)` boosting the plastic-number floor by
     `(1 / 6) (Φ((log 2) / 4) - Φ(t_*)) > 0`.

4. **Hybrid Quarter-Plus-Half Window Crossover (`quarter_add_half_window_levyCosh_crossover_le_weilArchRe`)**:
   For `L / 2 ≤ c < L` with `L / 4 ≤ L - c` (i.e. `L / 2 ≤ c ≤ 3 * L / 4`), splitting `Ioo (L / 4) c`
   at `L - c` combines the quarter-window bound on `Ioo (L / 4) (L - c)` with the reflected
   half-window bound on `Ioo (L - c) c`, proving:
   `(A(0) + Φ(L / 2) + (1 / 6) (Φ(L / 4) - Φ(L - c))) ∫ f² + pair_c(f) ≤ W_∞(f ⋆ f̃)`.
-/

open Complex MeasureTheory Set Filter Topology Real
open scoped ENNReal FourierTransform ComplexConjugate
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyQuarterWindow

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor

/-! ## Section 1: Quarter-Window Core-Mass and Full-Norm Coercivity (`x ≥ L / 4`) -/

/-- Set-integral union cover inequality: if `g` is integrable and nonnegative and `s ⊆ t₁ ∪ t₂`
for measurable sets `s, t₁, t₂`, then `∫ u in s, g u ≤ (∫ u in t₁, g u) + ∫ u in t₂, g u`. -/
theorem setIntegral_le_add_of_subset_union {g : ℝ → ℝ} (hg : Integrable g)
    (hg0 : ∀ u, 0 ≤ g u) {s t₁ t₂ : Set ℝ} (hs : MeasurableSet s)
    (ht₁ : MeasurableSet t₁) (ht₂ : MeasurableSet t₂) (hsub : s ⊆ t₁ ∪ t₂) :
    (∫ u in s, g u) ≤ (∫ u in t₁, g u) + ∫ u in t₂, g u := by
  have hIs : Integrable (s.indicator g) := (integrable_indicator_iff hs).mpr hg.integrableOn
  have hIt₁ : Integrable (t₁.indicator g) := (integrable_indicator_iff ht₁).mpr hg.integrableOn
  have hIt₂ : Integrable (t₂.indicator g) := (integrable_indicator_iff ht₂).mpr hg.integrableOn
  rw [← integral_indicator hs, ← integral_indicator ht₁, ← integral_indicator ht₂,
    ← integral_add hIt₁ hIt₂]
  refine integral_mono hIs (hIt₁.add hIt₂) fun u => ?_
  dsimp only [Pi.add_apply]
  by_cases hu : u ∈ s
  · rw [Set.indicator_of_mem hu]
    rcases hsub hu with hu1 | hu2
    · rw [Set.indicator_of_mem hu1]
      linarith [Set.indicator_apply_nonneg (s := t₂) (fun _ => hg0 u)]
    · rw [Set.indicator_of_mem hu2]
      linarith [Set.indicator_apply_nonneg (s := t₁) (fun _ => hg0 u)]
  · rw [Set.indicator_of_notMem hu]
    linarith [Set.indicator_apply_nonneg (s := t₁) (fun _ => hg0 u),
      Set.indicator_apply_nonneg (s := t₂) (fun _ => hg0 u)]

/-- For any `BddSupp A h C` and any shift `x ∈ [L / 4, L / 2]`, setting `a = min x ((L - x) / 2)`
covers the core `Ioc x (L - x)` by the two core slices `Ioc x (a + x)` and `Ioc (L - x - a) (L - x)`. -/
theorem coreMass_le_core_slice_of_quarter_le {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hx_low : L / 4 ≤ x) (_hx_high : x ≤ L / 2) :
    coreMass h L x ≤
      (∫ v in Ioc x (min x ((L - x) / 2) + x), h v ^ 2) +
        ∫ u in Ioc (L - x - min x ((L - x) / 2)) (L - x), h u ^ 2 := by
  unfold coreMass
  set a := min x ((L - x) / 2)
  have hgap : L - x - a ≤ a + x := by
    have h1 : (L - 2 * x) / 2 ≤ a := le_min (by linarith) (by linarith)
    linarith
  refine setIntegral_le_add_of_subset_union hh.integrable_sq (fun _ => sq_nonneg _)
    measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
  rcases le_or_gt u (a + x) with hle | hgt
  · exact Or.inl ⟨hu.1, hle⟩
  · exact Or.inr ⟨lt_of_le_of_lt hgap hgt, hu.2⟩

/-- **Quarter-Window Core-Mass Coercivity (`x ∈ [L / 4, L / 2]`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and any shift `x ∈ [L / 4, L / 2]`,
`(1 / 2) * coreMass h L x ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem half_coreMass_le_integral_jump_sq_of_quarter_le {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx_low : L / 4 ≤ x) (hx_high : x ≤ L / 2) :
    (1 / 2 : ℝ) * coreMass h L x ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  set a := min x ((L - x) / 2)
  have ha0 : 0 ≤ a := le_min (by linarith) (by linarith)
  have hax : a ≤ x := min_le_left _ _
  have h2axL : 2 * a + x ≤ L := by
    have : a ≤ (L - x) / 2 := min_le_right _ _
    linarith
  have hcov := coreMass_le_core_slice_of_quarter_le hh hx_low hx_high
  have hslice := half_core_slice_le_integral_jump_sq hh hsupp ha0 hax h2axL
  linarith

/-- Convex combination of collar and core bounds on `[L / 4, L / 2]`:
for any `θ ∈ [0, 1]` and `x ∈ [L / 4, L / 2]`,
`θ * collarMass h L x + ((1 - θ) / 2) * coreMass h L x ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem convex_collar_core_le_integral_jump_sq_of_quarter_le {A : Set ℝ} {h : ℝ → ℝ}
    {C L x θ : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx_low : L / 4 ≤ x) (hx_high : x ≤ L / 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * collarMass h L x + ((1 - θ) / 2) * coreMass h L x ≤
      ∫ u, (h u - h (u + x)) ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hcol : collarMass h L x ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
    have h1 := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
    have h2 : 0 ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    linarith
  have hcor := half_coreMass_le_integral_jump_sq_of_quarter_le hh hsupp hL0 hx_low hx_high
  nlinarith

/-- **Universal Quarter-Window Jump Coercivity (`x ≥ L / 4`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and **every shift `x ≥ L / 4`**,
`(1 / 3) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem one_third_mul_integral_sq_le_integral_jump_sq_of_quarter_le {A : Set ℝ} {h : ℝ → ℝ}
    {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 4 ≤ x) :
    (1 / 3 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  rcases le_or_gt x (L / 2) with hle | hgt
  · have hconv := convex_collar_core_le_integral_jump_sq_of_quarter_le
      (θ := 1 / 3) hh hsupp hL0 hx hle (by norm_num) (by norm_num)
    have hsum := collarMass_add_coreMass_eq hh hle
    linarith
  · have h1 := integral_sq_le_integral_jump_sq_of_half_le hh hsupp hL0 hgt.le
    have hsq : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith

/-- **Quarter-Window Autocorrelation Upper Bound (`x ≥ L / 4`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and every shift `x ≥ L / 4`,
`2 * autocorr h x ≤ (5 / 3) * ∫ u, h u ^ 2`. -/
theorem two_mul_autocorr_le_five_thirds_mul_integral_sq_of_quarter_le {A : Set ℝ} {h : ℝ → ℝ}
    {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 4 ≤ x) :
    2 * autocorr h x ≤ (5 / 3 : ℝ) * ∫ u, h u ^ 2 := by
  have h1 := one_third_mul_integral_sq_le_integral_jump_sq_of_quarter_le hh hsupp hL0 hx
  have h2 := integral_jump_sq hh x
  linarith

/-! ## Section 2: Quarter-Window Lévy–Cosh Crossover Inequality on `(0, L)` (Valid up to `L ≤ 4 * screwSignThreshold ≈ 1.1248`, Including `L = log 2`) -/

/-- For any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`) and any `c` with
`L / 4 ≤ c ≤ screwSignThreshold`,
`(1 / 6) * (levyCoshPotential (L / 4) - levyCoshPotential c) * ∫ u, h u ^ 2 ≤ ∫ x in Ioo (L / 4) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem one_sixth_mul_sub_levyCoshPotential_quarter_le_setIntegral_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L c : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 < L) (hL4c : L / 4 ≤ c) (hct : c ≤ screwSignThreshold) :
    (1 / 6 : ℝ) * (levyCoshPotential (L / 4) - levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 4) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL4 : 0 < L / 4 := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le hL4 hL4c
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 4) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL4 hx.1).neg
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hh
  have hI_rhs : IntegrableOn
      (fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) (Ioo (L / 4) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL4 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hI_lhs : IntegrableOn
      (fun x => (-screwRegularKernel x) * ((1 / 3 : ℝ) * ∫ u, h u ^ 2)) (Ioo (L / 4) c) :=
    (hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const _
  have hval : (∫ x in Ioo (L / 4) c, (-screwRegularKernel x) * ((1 / 3 : ℝ) * ∫ u, h u ^ 2)) =
      (1 / 6 : ℝ) * (levyCoshPotential (L / 4) - levyCoshPotential c) * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL4c]
    have hFTC := integral_two_mul_screwRegularKernel hL4 hc0
    have hneg : (∫ x in (L / 4)..c, -screwRegularKernel x) =
        -(1 / 2) * ∫ x in (L / 4)..c, 2 * screwRegularKernel x := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => by ring
    rw [hneg, hFTC]
    ring
  rw [← hval]
  refine setIntegral_mono_on hI_lhs hI_rhs measurableSet_Ioo fun x hx => ?_
  have hK0 : 0 ≤ -screwRegularKernel x :=
    neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
      (lt_trans hL4 hx.1) (hx.2.le.trans hct))
  exact mul_le_mul_of_nonneg_left
    (one_third_mul_integral_sq_le_integral_jump_sq_of_quarter_le hh hsupp hL0.le hx.1.le) hK0

/-- **Quarter-Window Lévy–Cosh Crossover Inequality on `(0, L)` (all signed `f ∈ C²_c(ℝ)`)**:
for every signed `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and every `c` with
`L / 4 ≤ c ≤ screwSignThreshold`,
`(A(0) + (1 / 6) * levyCoshPotential (L / 4) + (5 / 6) * levyCoshPotential c) * ∫ f²`
`+ ∫∫ f(u) f(v) (2 cosh((u - v)/2) - levyCoshKernel c |u - v|) du dv ≤ W_∞(f ⋆ f̃)`. -/
theorem quarter_window_levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {L c : ℝ} (hL0 : 0 < L) (hL4c : L / 4 ≤ c)
    (hct : c ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 6) * levyCoshPotential (L / 4) +
        (5 / 6) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL4 : 0 < L / 4 := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL4 hL4c hct
  have hq := one_sixth_mul_sub_levyCoshPotential_quarter_le_setIntegral_Ioo hB hsupp hL0 hL4c hct
  linarith

/-- **Quarter-Window Plastic-Number Potential Floor on the Nonnegative Cone
(`0 < L ≤ 4 * screwSignThreshold ≈ 1.1248`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with
`0 < L / 4 ≤ screwSignThreshold`,
`(A(0) + (1 / 6) * levyCoshPotential (L / 4) + (5 / 6) * levyCoshPotential screwSignThreshold) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem quarter_window_plastic_floor_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL0 : 0 < L)
    (hL4t : L / 4 ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 6) * levyCoshPotential (L / 4) +
        (5 / 6) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := quarter_window_levyCosh_crossover_le_weilArchRe hf hfc hL0 hL4t le_rfl hsupp
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-- **Unconditional Quarter-Window Boosted Floor on the Prime-Blind Window `(0, log 2)`**:
every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 (Real.log 2)` satisfies
`(EF.gammaBracket 0 + (1 / 6) * levyCoshPotential (Real.log 2 / 4) + (5 / 6) * levyCoshPotential screwSignThreshold) * ∫ u, f u ^ 2 ≤ W_∞(f ⋆ f̃)`. -/
theorem quarter_window_log_two_plastic_floor_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hsupp : ∀ u ∉ Ioo 0 (Real.log 2), f u = 0) :
    (EF.gammaBracket 0 + (1 / 6) * levyCoshPotential (Real.log 2 / 4) +
        (5 / 6) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL4t : Real.log 2 / 4 ≤ screwSignThreshold := by
    linarith [Real.log_two_lt_d9, screwSignThreshold_gt]
  exact quarter_window_plastic_floor_le_weilArchRe hf hfc hf0 hL0 hL4t hsupp

/-! ## Section 3: Hybrid Quarter-Plus-Half Window Crossover on `(0, L)` (`L / 2 ≤ c ≤ 3 * L / 4`) -/

/-- **Hybrid Quarter-Plus-Half Window Lévy–Cosh Crossover on `(0, L)`**:
for every signed `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and every `c` with
`L / 2 ≤ c ≤ 3 * L / 4` and `c ≤ screwSignThreshold`, splitting `Ioo (L / 4) c` at `L - c`
combines the quarter-window bound on `Ioo (L / 4) (L - c)` with the reflected midpoint bound
on `Ioo (L - c) c`, proving:
`(A(0) + levyCoshPotential (L / 2) + (1 / 6) * (levyCoshPotential (L / 4) - levyCoshPotential (L - c))) * ∫ f²`
`+ ∫∫ f(u) f(v) (2 cosh((u - v)/2) - levyCoshKernel c |u - v|) du dv ≤ W_∞(f ⋆ f̃)`. -/
theorem quarter_add_half_window_levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL0 : 0 < L)
    (hL2c : L / 2 ≤ c) (hc3L4 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + levyCoshPotential (L / 2) +
        (1 / 6) * (levyCoshPotential (L / 4) - levyCoshPotential (L - c))) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL4 : 0 < L / 4 := by linarith
  have hL4_Lc : L / 4 ≤ L - c := by linarith
  have hLc_c : L - c ≤ c := by linarith
  have hL4c : L / 4 ≤ c := by linarith
  have hcL : c < L := by linarith
  have hLct : L - c ≤ screwSignThreshold := hLc_c.trans hct
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  let G : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2
  have hD0 : ∀ x, 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hB
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 4) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL4 hx.1).neg
  have hIG : IntegrableOn G (Ioo (L / 4) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, f u ^ 2)).mono' (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL4 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hB x) hK0
  have hIG_left_Ioc : IntegrableOn G (Ioc (L / 4) (L - c)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIG.mono_set (Ioo_subset_Ioo le_rfl hLc_c)
  have hIG_right_Ioc : IntegrableOn G (Ioc (L - c) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIG.mono_set (Ioo_subset_Ioo hL4_Lc le_rfl)
  have hdisj : Disjoint (Ioc (L / 4) (L - c)) (Ioc (L - c) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 4) c, G x) =
      (∫ x in Ioo (L / 4) (L - c), G x) + ∫ x in Ioo (L - c) c, G x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL4_Lc hLc_c,
      setIntegral_union hdisj measurableSet_Ioc hIG_left_Ioc hIG_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL4 hL4c hct
  have hq := one_sixth_mul_sub_levyCoshPotential_quarter_le_setIntegral_Ioo
    hB hsupp hL0 hL4_Lc hLct
  have hrefl := sub_levyCoshPotential_half_le_setIntegral_Ioo hB hsupp hL0 hL2c hcL hct
  dsimp only [G] at hsplit
  linarith

end

end RHTower.WeilLevyQuarterWindow
