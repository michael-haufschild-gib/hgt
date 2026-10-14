import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover

/-!
# Boundary-escape decomposition, midpoint convexity, and half-window collar positivity on `(0, L)`

For a test function `h` supported on an open interval `(0, L)` (`0 < L`), the jump energy
`D_h(x) = ∫_ℝ (h(u) - h(u + x))² du` splits at every shift `x ≥ 0` into left boundary escape,
right boundary escape, and interior Dirichlet jump energy:

`∫_ℝ (h(u) - h(u + x))² du = ∫_{u ≤ x} h(u)² du + ∫_{u > L - x} h(u)² du + ∫_{u ∈ (0, L - x]} (h(u) - h(u + x))² du`.

This module establishes four unconditional producer results from this decomposition:

1. **Pointwise and integral boundary-escape + interior-Dirichlet decomposition (`pointwise_jump_sq_eq_boundary_escape_add_interior`, `integral_jump_sq_eq_boundary_escape_add_interior`)**,
   **complementary shift reflection (`integral_jump_sq_add_sub_eq`)**, and **half-window overlap decomposition (`integral_jump_sq_eq_sq_add_overlap_add_interior`)**:
   * For every `x ∈ [0, L]`, `D_h(x) + D_h(L - x) ≥ 2 ∫_ℝ h(u)² du`.
   * For every `x ≥ L / 2`, the intervals `(0, L - x)` and `(x, L)` are disjoint, so every point
     `u ∈ (0, L)` escapes in at least one direction and every point in the central overlap
     `(L - x, x]` escapes in both directions:
     `D_h(x) = ∫_ℝ h(u)² du + ∫_{u ∈ (L - x, x]} h(u)² du + ∫_{u ∈ (0, L - x]} (h(u) - h(u + x))² du ≥ ∫_ℝ h(u)² du`,
     and equivalently `2 * autocorr h x ≤ ∫_ℝ h(u)² du`.

2. **Global monotonicity of `screwRegularKernel` and midpoint convexity of `archLevyAntideriv` and `levyCoshPotential` (`monotoneOn_screwRegularKernel`, `two_mul_archLevyAntideriv_midpoint_le_add`, `two_mul_levyCoshPotential_midpoint_le_add`)**:
   Since `archLevyDensity` is antitone on `(0, ∞)` and `2 cosh(x / 2)` is monotone on `(0, ∞)`,
   `screwRegularKernel x = 2 cosh(x / 2) - archLevyDensity x` is monotone on `(0, ∞)`. Both
   `archLevyAntideriv` (`Ω' = -ω`) and `levyCoshPotential` (`Φ' = 2 K`) are therefore midpoint-convex
   on `(0, ∞)`.

3. **Half-window + full-window jump energy bound (`ofReal_archLevyAntideriv_half_add_le_jumpEnergy_of_support_Ioo`, `ofReal_archLevyAntideriv_half_add_le_jumpEnergy_of_volume_pos_le`)**:
   Integrating `D_h(x) ≥ ∫ h²` on `(L / 2, L)` and `D_h(x) = 2 ∫ h²` on `(L, ∞)` yields
   `(Ω(L / 2) + Ω(L)) ∫ h² ≤ jumpEnergy h` for every `h` supported on `(0, L)` (and by quantile
   rearrangement for every nonnegative `g` with `|{g > 0}| ≤ L`).

4. **Half-window Lévy–cosh crossover bounds on `(0, L)` (`half_window_levyCosh_crossover_le_weilArchRe`, `half_window_plastic_floor_le_weilArchRe`, `half_window_signed_short_support_le_weilArchRe`, `weilArchRe_nonneg_of_support_Ioo_le_inv_18`)**:
   Combining `D_f(x) ≥ ∫ f²` on `(L / 2, c)` with `levyCosh_crossover_add_jump_le_weilArchRe`
   replaces `Φ(c)` by `(1 / 2) Φ(L / 2) + (1 / 2) Φ(c)`:
   * For every nonnegative `f ∈ C²_c(ℝ)` supported on `(0, L)` with `0 < L ≤ 2 * screwSignThreshold`
     (`2 t_* ≈ 0.5624`, covering `81.1%` of `(0, log 2)`),
     `(A(0) + (1 / 2) Φ(L / 2) + (1 / 2) Φ(t_*)) ∫ f² ≤ W_∞(f ⋆ f̃)`.
   * Whenever `(1 / 2) Φ(L / 2) + (1 / 2) Φ(t_*) ≥ -A(0)` — which we prove unconditionally for all
     `0 < L ≤ 1 / 18` (`weilArchRe_nonneg_of_support_Ioo_le_inv_18`) — `0 ≤ W_∞(f ⋆ f̃)` holds
     without `WindowPositive`, expanding the unconditional window on `(0, log 2)` by more than
     `7×` (from `1 / 130` to `1 / 18`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform ComplexConjugate
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyBoundaryEscape

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss RHTower.WeilLevyCoshCrossover

/-! ## Section 1: Pointwise and Integral Boundary-Escape + Interior-Dirichlet Decomposition on `(0, L)` -/

/-- **Exact pointwise jump decomposition on `(0, L)`**:
if `h` vanishes outside `Ioo 0 L`, then for every shift `x ≥ 0` and every `u ∈ ℝ`,
`(h u - h (u + x))²` decomposes into left boundary escape (`u + x ≤ x`, i.e. `u ≤ 0`),
right boundary escape (`u > L - x`, so `u + x > L`), and interior jump (`u ∈ (0, L - x]`). -/
theorem pointwise_jump_sq_eq_boundary_escape_add_interior {h : ℝ → ℝ} {L x : ℝ}
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (_hx : 0 ≤ x) (u : ℝ) :
    Set.indicator (Iic x) (fun v => h v ^ 2) (u + x) +
        Set.indicator (Ioi (L - x)) (fun v => h v ^ 2) u +
        Set.indicator (Ioc 0 (L - x)) (fun v => (h v - h (v + x)) ^ 2) u =
      (h u - h (u + x)) ^ 2 := by
  rcases le_or_gt u 0 with hu0 | hu0
  · have hux : u + x ≤ x := by linarith
    have hu_not_Ioo : u ∉ Ioo 0 L := fun h' => not_lt_of_ge hu0 h'.1
    have hu_zero : h u = 0 := hsupp u hu_not_Ioo
    have hu_not_Ioc : u ∉ Ioc 0 (L - x) := fun h' => not_lt_of_ge hu0 h'.1
    rw [Set.indicator_of_mem (mem_Iic.mpr hux), Set.indicator_of_notMem hu_not_Ioc, hu_zero]
    by_cases huL : u ∈ Ioi (L - x)
    · rw [Set.indicator_of_mem huL, hu_zero]; ring
    · rw [Set.indicator_of_notMem huL]; ring
  · have hux : u + x ∉ Iic x := by rw [mem_Iic, not_le]; linarith
    rw [Set.indicator_of_notMem hux]
    rcases le_or_gt u (L - x) with huLx | huLx
    · have hu_Ioc : u ∈ Ioc 0 (L - x) := ⟨hu0, huLx⟩
      have hu_not_Ioi : u ∉ Ioi (L - x) := not_lt_of_ge huLx
      rw [Set.indicator_of_notMem hu_not_Ioi, Set.indicator_of_mem hu_Ioc]; ring
    · have hu_Ioi : u ∈ Ioi (L - x) := huLx
      have hu_not_Ioc : u ∉ Ioc 0 (L - x) := fun h' => not_le_of_gt huLx h'.2
      have hux_not_Ioo : u + x ∉ Ioo 0 L := fun h' => by linarith [h'.2]
      rw [Set.indicator_of_mem hu_Ioi, Set.indicator_of_notMem hu_not_Ioc,
        hsupp (u + x) hux_not_Ioo]
      ring

/-- **Exact integral jump decomposition on `(0, L)`**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` and any shift `x ≥ 0`,
`∫ u, (h u - h (u + x)) ^ 2 = (∫ u in Iic x, h u ^ 2) + (∫ u in Ioi (L - x), h u ^ 2) + ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`. -/
theorem integral_jump_sq_eq_boundary_escape_add_interior {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hx : 0 ≤ x) :
    ∫ u, (h u - h (u + x)) ^ 2 =
      (∫ u in Iic x, h u ^ 2) + (∫ u in Ioi (L - x), h u ^ 2) +
        ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
  have hsq : Integrable (fun v : ℝ => h v ^ 2) := hh.integrable_sq
  have hjump : Integrable (fun v : ℝ => (h v - h (v + x)) ^ 2) := by
    have hshift : Integrable (fun v : ℝ => h (v + x) ^ 2) := hsq.comp_add_right x
    have hmul : Integrable (fun v : ℝ => h v * h (v + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift).sub (hmul.const_mul 2)).congr (ae_of_all _ fun v => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hI1 : Integrable (fun u : ℝ => Set.indicator (Iic x) (fun v => h v ^ 2) (u + x)) :=
    ((integrable_indicator_iff measurableSet_Iic).mpr hsq.integrableOn).comp_add_right x
  have hI2 : Integrable (fun u : ℝ => Set.indicator (Ioi (L - x)) (fun v => h v ^ 2) u) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hsq.integrableOn
  have hI3 : Integrable (fun u : ℝ =>
      Set.indicator (Ioc 0 (L - x)) (fun v => (h v - h (v + x)) ^ 2) u) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hjump.integrableOn
  have hcongr : (∫ u, (h u - h (u + x)) ^ 2) =
      ∫ u, ((Set.indicator (Iic x) (fun v => h v ^ 2) (u + x) +
          Set.indicator (Ioi (L - x)) (fun v => h v ^ 2) u) +
        Set.indicator (Ioc 0 (L - x)) (fun v => (h v - h (v + x)) ^ 2) u) :=
    integral_congr_ae (ae_of_all _ fun u =>
      (pointwise_jump_sq_eq_boundary_escape_add_interior hsupp hx u).symm)
  have hadd1 := integral_add (hI1.add hI2) hI3
  have hadd2 := integral_add hI1 hI2
  dsimp only [Pi.add_apply] at hadd1 hadd2
  rw [hcongr, hadd1, hadd2,
    integral_add_right_eq_self (fun v : ℝ => Set.indicator (Iic x) (fun w => h w ^ 2) v) x,
    integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ioi,
    integral_indicator measurableSet_Ioc]

/-- Dropping the nonnegative interior Dirichlet energy gives the boundary-escape lower bound
`(∫ u in Iic x, h u ^ 2) + (∫ u in Ioi (L - x), h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2` for `x ≥ 0`. -/
theorem boundary_escape_le_integral_jump_sq {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hx : 0 ≤ x) :
    (∫ u in Iic x, h u ^ 2) + (∫ u in Ioi (L - x), h u ^ 2) ≤
      ∫ u, (h u - h (u + x)) ^ 2 := by
  rw [integral_jump_sq_eq_boundary_escape_add_interior hh hsupp hx]
  have hint_nn : 0 ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  linarith

/-- Partition of `∫ u, h u ^ 2` at any threshold `t ∈ ℝ`:
`(∫ u in Iic t, h u ^ 2) + (∫ u in Ioi t, h u ^ 2) = ∫ u, h u ^ 2`. -/
theorem setIntegral_Iic_add_Ioi_sq {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ}
    (hh : BddSupp A h C) (t : ℝ) :
    (∫ u in Iic t, h u ^ 2) + (∫ u in Ioi t, h u ^ 2) = ∫ u, h u ^ 2 := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
    hsq.integrableOn hsq.integrableOn, Iic_union_Ioi, setIntegral_univ]

/-- **Complementary shift reflection identity on `[0, L]`**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` and any `x ∈ [0, L]`,
`D_h(x) + D_h(L - x) = 2 ∫ h² + ∫_{Ioc 0 (L - x)} (h(u) - h(u + x))² + ∫_{Ioc 0 x} (h(u) - h(u + (L - x)))²`. -/
theorem integral_jump_sq_add_sub_eq {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    (∫ u, (h u - h (u + x)) ^ 2) + (∫ u, (h u - h (u + (L - x))) ^ 2) =
      2 * (∫ u, h u ^ 2) +
        (∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2) +
        ∫ u in Ioc 0 x, (h u - h (u + (L - x))) ^ 2 := by
  have hLx0 : 0 ≤ L - x := by linarith
  have h1 := integral_jump_sq_eq_boundary_escape_add_interior hh hsupp hx0
  have h2 := integral_jump_sq_eq_boundary_escape_add_interior hh hsupp hLx0
  rw [show L - (L - x) = x by ring] at h2
  have hp1 := setIntegral_Iic_add_Ioi_sq hh x
  have hp2 := setIntegral_Iic_add_Ioi_sq hh (L - x)
  linarith

/-- **Complementary shift lower bound on `[0, L]`**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` and any `x ∈ [0, L]`,
`2 * (∫ u, h u ^ 2) ≤ (∫ u, (h u - h (u + x)) ^ 2) + ∫ u, (h u - h (u + (L - x))) ^ 2`. -/
theorem two_mul_integral_sq_le_integral_jump_sq_add_sub {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    2 * (∫ u, h u ^ 2) ≤
      (∫ u, (h u - h (u + x)) ^ 2) + ∫ u, (h u - h (u + (L - x))) ^ 2 := by
  rw [integral_jump_sq_add_sub_eq hh hsupp hx0 hxL]
  have h1 : 0 ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have h2 : 0 ≤ ∫ u in Ioc 0 x, (h u - h (u + (L - x))) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  linarith

/-- **Half-window central-overlap decomposition (`x ≥ L / 2`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and any shift `x ≥ L / 2`,
`∫ u, (h u - h (u + x)) ^ 2 = (∫ u, h u ^ 2) + (∫ u in Ioc (L - x) x, h u ^ 2) + ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`. -/
theorem integral_jump_sq_eq_sq_add_overlap_add_interior {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx : L / 2 ≤ x) :
    ∫ u, (h u - h (u + x)) ^ 2 =
      (∫ u, h u ^ 2) + (∫ u in Ioc (L - x) x, h u ^ 2) +
        ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hLx : L - x ≤ x := by linarith
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hsplit : (∫ u in Ioi (L - x), h u ^ 2) =
      (∫ u in Ioc (L - x) x, h u ^ 2) + ∫ u in Ioi x, h u ^ 2 := by
    rw [← Ioc_union_Ioi_eq_Ioi hLx,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hsq.integrableOn hsq.integrableOn]
  have hp := setIntegral_Iic_add_Ioi_sq hh x
  rw [integral_jump_sq_eq_boundary_escape_add_interior hh hsupp hx0, hsplit]
  linarith

/-- **Half-window jump energy lower bound (`x ≥ L / 2`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and any shift `x ≥ L / 2`,
`(∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem integral_sq_le_integral_jump_sq_of_half_le {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx : L / 2 ≤ x) :
    (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  rw [integral_jump_sq_eq_sq_add_overlap_add_interior hh hsupp hL0 hx]
  have h1 : 0 ≤ ∫ u in Ioc (L - x) x, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h2 : 0 ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  linarith

/-- **Half-window autocorrelation upper bound (`x ≥ L / 2`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and any shift `x ≥ L / 2`,
`2 * autocorr h x ≤ ∫ u, h u ^ 2`. -/
theorem two_mul_autocorr_le_integral_sq_of_half_le {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx : L / 2 ≤ x) :
    2 * autocorr h x ≤ ∫ u, h u ^ 2 := by
  have h1 := integral_sq_le_integral_jump_sq_of_half_le hh hsupp hL0 hx
  have h2 := integral_jump_sq hh x
  linarith

/-! ## Section 2: Global Monotonicity of `screwRegularKernel` and Midpoint Convexity of `archLevyAntideriv` and `levyCoshPotential` -/

/-- `archLevyDensity` is antitone on `(0, ∞)`. -/
theorem antitoneOn_archLevyDensity : AntitoneOn archLevyDensity (Ioi 0) := by
  intro a ha b hb hab
  have h := antitoneOn_jumpKernel ha hb hab
  simpa only [jumpKernel, if_pos (mem_Ioi.mp ha), if_pos (mem_Ioi.mp hb),
    max_eq_left (archLevyDensity_pos (mem_Ioi.mp ha)).le,
    max_eq_left (archLevyDensity_pos (mem_Ioi.mp hb)).le] using h

/-- `screwRegularKernel` is monotone on `(0, ∞)` because `2 cosh(x / 2)` is monotone and
`archLevyDensity` is antitone on `(0, ∞)`. -/
theorem monotoneOn_screwRegularKernel : MonotoneOn screwRegularKernel (Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  rw [screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity ha0,
    screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity hb0]
  have hcosh : Real.cosh (a / 2) ≤ Real.cosh (b / 2) :=
    Real.cosh_le_cosh.mpr (by
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith)
  have hω : archLevyDensity b ≤ archLevyDensity a :=
    antitoneOn_archLevyDensity ha hb hab
  linarith

/-- Helper: midpoint convexity from an antitone derivative on `[a, b]` (`a ≤ b`). -/
private theorem midpoint_convex_of_integral_antitone {F f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h1 : F a - F ((a + b) / 2) = ∫ x in a..((a + b) / 2), f x)
    (h2 : F ((a + b) / 2) - F b = ∫ x in ((a + b) / 2)..b, f x)
    (hcont1 : ContinuousOn f (Icc a ((a + b) / 2)))
    (hcont2 : ContinuousOn f (Icc ((a + b) / 2) b))
    (hanti1 : ∀ x ∈ Icc a ((a + b) / 2), f ((a + b) / 2) ≤ f x)
    (hanti2 : ∀ x ∈ Icc ((a + b) / 2) b, f x ≤ f ((a + b) / 2)) :
    2 * F ((a + b) / 2) ≤ F a + F b := by
  have ham : a ≤ (a + b) / 2 := by linarith
  have hmb : (a + b) / 2 ≤ b := by linarith
  have hlow : ((a + b) / 2 - a) * f ((a + b) / 2) ≤ ∫ x in a..((a + b) / 2), f x := by
    calc ((a + b) / 2 - a) * f ((a + b) / 2)
        = ∫ _x in a..((a + b) / 2), f ((a + b) / 2) := by simp
      _ ≤ ∫ x in a..((a + b) / 2), f x :=
          intervalIntegral.integral_mono_on ham intervalIntegrable_const
            (hcont1.intervalIntegrable_of_Icc ham) hanti1
  have hhigh : ∫ x in ((a + b) / 2)..b, f x ≤ (b - (a + b) / 2) * f ((a + b) / 2) := by
    calc ∫ x in ((a + b) / 2)..b, f x
        ≤ ∫ _x in ((a + b) / 2)..b, f ((a + b) / 2) :=
          intervalIntegral.integral_mono_on hmb (hcont2.intervalIntegrable_of_Icc hmb)
            intervalIntegrable_const hanti2
      _ = (b - (a + b) / 2) * f ((a + b) / 2) := by simp
  linarith

/-- **Midpoint convexity of `archLevyAntideriv` on `(0, ∞)`**:
for any `a > 0` and `b > 0`,
`2 * archLevyAntideriv ((a + b) / 2) ≤ archLevyAntideriv a + archLevyAntideriv b`. -/
theorem two_mul_archLevyAntideriv_midpoint_le_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * archLevyAntideriv ((a + b) / 2) ≤ archLevyAntideriv a + archLevyAntideriv b := by
  have hm : 0 < (a + b) / 2 := by linarith
  rcases le_total a b with hab | hba
  · have ham : a ≤ (a + b) / 2 := by linarith
    have hmb : (a + b) / 2 ≤ b := by linarith
    exact midpoint_convex_of_integral_antitone hab
      (integral_archLevyDensity_Icc ha ham).symm
      (integral_archLevyDensity_Icc hm hmb).symm
      (continuousOn_archLevyDensity.mono fun x hx => lt_of_lt_of_le ha hx.1)
      (continuousOn_archLevyDensity.mono fun x hx => lt_of_lt_of_le hm hx.1)
      (fun x hx => antitoneOn_archLevyDensity (lt_of_lt_of_le ha hx.1) hm hx.2)
      (fun x hx => antitoneOn_archLevyDensity hm (lt_of_lt_of_le hm hx.1) hx.1)
  · have hbm : b ≤ (a + b) / 2 := by linarith
    have hma : (a + b) / 2 ≤ a := by linarith
    have hsym := midpoint_convex_of_integral_antitone hba
      (show archLevyAntideriv b - archLevyAntideriv ((b + a) / 2) =
          ∫ x in b..((b + a) / 2), archLevyDensity x by
        rw [add_comm b a]; exact (integral_archLevyDensity_Icc hb hbm).symm)
      (show archLevyAntideriv ((b + a) / 2) - archLevyAntideriv a =
          ∫ x in ((b + a) / 2)..a, archLevyDensity x by
        rw [add_comm b a]; exact (integral_archLevyDensity_Icc hm hma).symm)
      (continuousOn_archLevyDensity.mono fun x hx => lt_of_lt_of_le hb hx.1)
      (continuousOn_archLevyDensity.mono fun x hx => by
        rw [add_comm b a] at hx; exact lt_of_lt_of_le hm hx.1)
      (fun x hx => by
        rw [add_comm b a] at hx ⊢
        exact antitoneOn_archLevyDensity (lt_of_lt_of_le hb hx.1) hm hx.2)
      (fun x hx => by
        rw [add_comm b a] at hx ⊢
        exact antitoneOn_archLevyDensity hm (lt_of_lt_of_le hm hx.1) hx.1)
    rw [add_comm b a] at hsym
    linarith

/-- **Midpoint convexity of `levyCoshPotential` on `(0, ∞)`**:
for any `a > 0` and `b > 0`,
`2 * levyCoshPotential ((a + b) / 2) ≤ levyCoshPotential a + levyCoshPotential b`. -/
theorem two_mul_levyCoshPotential_midpoint_le_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * levyCoshPotential ((a + b) / 2) ≤ levyCoshPotential a + levyCoshPotential b := by
  have hm : 0 < (a + b) / 2 := by linarith
  have h1 : levyCoshPotential a - levyCoshPotential ((a + b) / 2) =
      ∫ x in a..((a + b) / 2), (-2 * screwRegularKernel x) := by
    have h := integral_two_mul_screwRegularKernel ha hm
    have hneg : (∫ x in a..((a + b) / 2), -2 * screwRegularKernel x) =
        -∫ x in a..((a + b) / 2), 2 * screwRegularKernel x := by
      simp_rw [neg_mul, intervalIntegral.integral_neg]
    linarith
  have h2 : levyCoshPotential ((a + b) / 2) - levyCoshPotential b =
      ∫ x in ((a + b) / 2)..b, (-2 * screwRegularKernel x) := by
    have h := integral_two_mul_screwRegularKernel hm hb
    have hneg : (∫ x in ((a + b) / 2)..b, -2 * screwRegularKernel x) =
        -∫ x in ((a + b) / 2)..b, 2 * screwRegularKernel x := by
      simp_rw [neg_mul, intervalIntegral.integral_neg]
    linarith
  have hcont : ContinuousOn (fun x => -2 * screwRegularKernel x) (Ioi 0) :=
    continuousOn_const.mul WeilLevyCoshCrossover.continuousOn_screwRegularKernel
  rcases le_total a b with hab | hba
  · exact midpoint_convex_of_integral_antitone hab h1 h2
      (hcont.mono fun x hx => lt_of_lt_of_le ha hx.1)
      (hcont.mono fun x hx => lt_of_lt_of_le hm hx.1)
      (fun x hx => by
        have := monotoneOn_screwRegularKernel (lt_of_lt_of_le ha hx.1) hm hx.2
        linarith)
      (fun x hx => by
        have := monotoneOn_screwRegularKernel hm (lt_of_lt_of_le hm hx.1) hx.1
        linarith)
  · have hsym := midpoint_convex_of_integral_antitone hba
      (show levyCoshPotential b - levyCoshPotential ((b + a) / 2) =
          ∫ x in b..((b + a) / 2), (-2 * screwRegularKernel x) by
        rw [add_comm b a]
        have h := integral_two_mul_screwRegularKernel hb hm
        have hneg : (∫ x in b..((a + b) / 2), -2 * screwRegularKernel x) =
            -∫ x in b..((a + b) / 2), 2 * screwRegularKernel x := by
          simp_rw [neg_mul, intervalIntegral.integral_neg]
        linarith)
      (show levyCoshPotential ((b + a) / 2) - levyCoshPotential a =
          ∫ x in ((b + a) / 2)..a, (-2 * screwRegularKernel x) by
        rw [add_comm b a]
        have h := integral_two_mul_screwRegularKernel hm ha
        have hneg : (∫ x in ((a + b) / 2)..a, -2 * screwRegularKernel x) =
            -∫ x in ((a + b) / 2)..a, 2 * screwRegularKernel x := by
          simp_rw [neg_mul, intervalIntegral.integral_neg]
        linarith)
      (hcont.mono fun x hx => lt_of_lt_of_le hb hx.1)
      (hcont.mono fun x hx => by rw [add_comm b a] at hx; exact lt_of_lt_of_le hm hx.1)
      (fun x hx => by
        rw [add_comm b a] at hx ⊢
        have := monotoneOn_screwRegularKernel (lt_of_lt_of_le hb hx.1) hm hx.2
        linarith)
      (fun x hx => by
        rw [add_comm b a] at hx ⊢
        have := monotoneOn_screwRegularKernel hm (lt_of_lt_of_le hm hx.1) hx.1
        linarith)
    rw [add_comm b a] at hsym
    linarith

/-! ## Section 3: Half-Window + Full-Window Jump Energy Bound `(Ω(L/2) + Ω(L)) ∫ h² ≤ jumpEnergy h` -/

/-- Integrating `D_h(x) ≥ ∫ h²` on `(L / 2, L)` and `D_h(x) = 2 ∫ h²` on `(L, ∞)` yields
`ENNReal.ofReal ((archLevyAntideriv (L / 2) + archLevyAntideriv L) * ∫ u, h u ^ 2) ≤ jumpEnergy h`
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`). -/
theorem ofReal_archLevyAntideriv_half_add_le_jumpEnergy_of_support_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L : ℝ} (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) :
    ENNReal.ofReal ((archLevyAntideriv (L / 2) + archLevyAntideriv L) * ∫ u, h u ^ 2) ≤
      jumpEnergy h := by
  have hL2 : 0 < L / 2 := by linarith
  have hE0 : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  -- Part 1: On `Ioc (L / 2) L`, `archLevyDensity x * ∫ h² ≤ archLevyDensity x * D_h(x)`
  have hcont1 : ContinuousOn archLevyDensity (Icc (L / 2) L) :=
    continuousOn_archLevyDensity.mono fun x hx => lt_of_lt_of_le hL2 hx.1
  have hint1 : IntegrableOn (fun x => archLevyDensity x * ∫ u, h u ^ 2) (Ioc (L / 2) L) :=
    (hcont1.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mul_const _
  have hval1 : (∫ x in Ioc (L / 2) L, archLevyDensity x * ∫ u, h u ^ 2) =
      (archLevyAntideriv (L / 2) - archLevyAntideriv L) * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, ← intervalIntegral.integral_of_le (by linarith),
      integral_archLevyDensity_Icc hL2 (by linarith)]
  have hle1 : ENNReal.ofReal ((archLevyAntideriv (L / 2) - archLevyAntideriv L) * ∫ u, h u ^ 2) ≤
      ∫⁻ x in Ioc (L / 2) L,
        ENNReal.ofReal (archLevyDensity x * ∫ u, (h u - h (u + x)) ^ 2) := by
    rw [← hval1, ofReal_integral_eq_lintegral_ofReal hint1
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx =>
        mul_nonneg (archLevyDensity_pos (lt_trans hL2 hx.1)).le hE0))]
    refine setLIntegral_mono' measurableSet_Ioc fun x hx => ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_left
      (integral_sq_le_integral_jump_sq_of_half_le hh hsupp hL.le hx.1.le)
      (archLevyDensity_pos (lt_trans hL2 hx.1)).le
  -- Part 2: On `Ioi L`, `archLevyDensity x * (2 ∫ h²) = archLevyDensity x * D_h(x)`
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
  -- Combine on `Ioc (L / 2) L ∪ Ioi L = Ioi (L / 2) ⊆ Ioi 0`
  have hsub_pos : 0 ≤ (archLevyAntideriv (L / 2) - archLevyAntideriv L) * ∫ u, h u ^ 2 :=
    mul_nonneg (sub_nonneg.mpr (antitoneOn_archLevyAntideriv hL2 hL (by linarith))) hE0
  have h2_pos : 0 ≤ 2 * archLevyAntideriv L * ∫ u, h u ^ 2 :=
    mul_nonneg (mul_nonneg zero_le_two (archLevyAntideriv_pos hL).le) hE0
  have hsum_eq : (archLevyAntideriv (L / 2) + archLevyAntideriv L) * ∫ u, h u ^ 2 =
      (archLevyAntideriv (L / 2) - archLevyAntideriv L) * (∫ u, h u ^ 2) +
        2 * archLevyAntideriv L * ∫ u, h u ^ 2 := by ring
  rw [hsum_eq, ENNReal.ofReal_add hsub_pos h2_pos]
  calc ENNReal.ofReal ((archLevyAntideriv (L / 2) - archLevyAntideriv L) * ∫ u, h u ^ 2) +
        ENNReal.ofReal (2 * archLevyAntideriv L * ∫ u, h u ^ 2)
      ≤ (∫⁻ x in Ioc (L / 2) L,
          ENNReal.ofReal (archLevyDensity x * ∫ u, (h u - h (u + x)) ^ 2)) +
        ∫⁻ x in Ioi L,
          ENNReal.ofReal (archLevyDensity x * ∫ u, (h u - h (u + x)) ^ 2) :=
        add_le_add hle1 hle2
    _ = ∫⁻ x in Ioc (L / 2) L ∪ Ioi L,
          ENNReal.ofReal (archLevyDensity x * ∫ u, (h u - h (u + x)) ^ 2) := by
        rw [lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
    _ ≤ jumpEnergy h := by
        rw [Ioc_union_Ioi_eq_Ioi (by linarith)]
        exact lintegral_mono_set fun x hx => lt_trans hL2 hx

/-- **Quantile-rearranged half-window + full-window jump energy bound**:
for any bounded measurable `g ≥ 0` with `volume {x | 0 < g x} ≤ ENNReal.ofReal L` (`L > 0`),
`ENNReal.ofReal ((archLevyAntideriv (L / 2) + archLevyAntideriv L) * ∫ u, g u ^ 2) ≤ jumpEnergy g`. -/
theorem ofReal_archLevyAntideriv_half_add_le_jumpEnergy_of_volume_pos_le {g : ℝ → ℝ}
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) {C L : ℝ} (hgC : ∀ x, g x ≤ C) (hL0 : 0 < L)
    (hvol : volume {x | 0 < g x} ≤ ENNReal.ofReal L) :
    ENNReal.ofReal ((archLevyAntideriv (L / 2) + archLevyAntideriv L) * ∫ u, g u ^ 2) ≤
      jumpEnergy g := by
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
  have h1 := ofReal_archLevyAntideriv_half_add_le_jumpEnergy_of_support_Ioo hTB_L hTB_L.supp hL0
  rw [integral_sq_transport hSm hS hgB] at h1
  refine h1.trans ?_
  rw [jumpEnergy_eq, jumpEnergy_eq]
  exact lintegral_jump_transport_le hSm hS hgB hg0 measurable_jumpKernel jumpKernel_nonneg
    antitoneOn_jumpKernel integrableOn_min_jumpKernel

/-! ## Section 4: Half-Window Lévy–Cosh Crossover Lower Bounds on `(0, L)` -/

/-- **Half-window Lévy–cosh crossover lower bound on `(0, L)` (all signed `f ∈ C²_c(ℝ)`)**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` and every `c` with
`0 < L / 2 ≤ c ≤ screwSignThreshold`,
`(A(0) + (1 / 2) levyCoshPotential (L / 2) + (1 / 2) levyCoshPotential c) ∫ f² + ∫∫ f(u) f(v) (2 cosh((u - v)/2) - levyCoshKernel c |u - v|) du dv ≤ W_∞(f ⋆ f̃)`. -/
theorem half_window_levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {L c : ℝ} (hL0 : 0 < L) (hLc : L / 2 ≤ c)
    (hct : c ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 2) * levyCoshPotential (L / 2) + (1 / 2) * levyCoshPotential c) *
        (∫ u, f u ^ 2) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL2 : 0 < L / 2 := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le hL2 hLc
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL2 hLc hct
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 2) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono fun x hx =>
      lt_of_lt_of_le hL2 hx.1).neg
  have hI_K_Ioo : IntegrableOn (fun x => -screwRegularKernel x) (Ioo (L / 2) c) :=
    hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hB
  have hD0 : ∀ x, 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hI_jump : IntegrableOn
      (fun x : ℝ => (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2) (Ioo (L / 2) c) := by
    refine (hI_K_Ioo.mul_const (4 * ∫ u, f u ^ 2)).mono'
      (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans hL2 hx.1)
        (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hB x) hK0
  have hval : (∫ x in Ioo (L / 2) c, (-screwRegularKernel x) * ∫ u, f u ^ 2) =
      (1 / 2) * (levyCoshPotential (L / 2) - levyCoshPotential c) * ∫ u, f u ^ 2 := by
    rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hLc]
    have hFTC := integral_two_mul_screwRegularKernel hL2 hc0
    have hneg : (∫ x in (L / 2)..c, -screwRegularKernel x) =
        -(1 / 2) * ∫ x in (L / 2)..c, 2 * screwRegularKernel x := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => by ring
    rw [hneg, hFTC]
    ring
  have hmono : (∫ x in Ioo (L / 2) c, (-screwRegularKernel x) * ∫ u, f u ^ 2) ≤
      ∫ x in Ioo (L / 2) c, (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2 := by
    refine setIntegral_mono_on (hI_K_Ioo.mul_const _) hI_jump measurableSet_Ioo fun x hx => ?_
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans hL2 hx.1)
        (hx.2.le.trans hct))
    exact mul_le_mul_of_nonneg_left
      (integral_sq_le_integral_jump_sq_of_half_le hB hsupp hL0.le hx.1.le) hK0
  linarith

/-- **Half-window plastic-number floor on the nonnegative cone (`0 < L ≤ 2 * screwSignThreshold`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with
`0 < L / 2 ≤ screwSignThreshold` (in particular all `0 < L ≤ 13 / 25 = 0.52`),
`(A(0) + (1 / 2) levyCoshPotential (L / 2) + (1 / 2) levyCoshPotential screwSignThreshold) ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem half_window_plastic_floor_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL0 : 0 < L)
    (hLt : L / 2 ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 2) * levyCoshPotential (L / 2) +
        (1 / 2) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := half_window_levyCosh_crossover_le_weilArchRe hf hfc hL0 hLt le_rfl hsupp
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-- **Half-window signed short-support lower bound (`0 < L ≤ screwSignThreshold`)**:
for **every signed** `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with `0 < L ≤ screwSignThreshold`,
`(A(0) + (1 / 2) levyCoshPotential (L / 2) + (1 / 2) levyCoshPotential L) ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem half_window_signed_short_support_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {L : ℝ} (hL0 : 0 < L) (hLt : L ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 2) * levyCoshPotential (L / 2) +
        (1 / 2) * levyCoshPotential L) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := half_window_levyCosh_crossover_le_weilArchRe hf hfc hL0 (by linarith) hLt hsupp
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
  linarith

/-- **Unconditional positivity on `(0, L)` when `(1 / 2) Φ(L / 2) + (1 / 2) Φ(t_*) ≥ -A(0)`**:
for any nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with `0 < L / 2 ≤ screwSignThreshold`
and `-EF.gammaBracket 0 ≤ (1 / 2) * levyCoshPotential (L / 2) + (1 / 2) * levyCoshPotential screwSignThreshold`,
`0 ≤ W_∞(f ⋆ f̃)` holds unconditionally without `WindowPositive`. -/
theorem weilArchRe_nonneg_of_support_Ioo_of_half_window_plastic {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL0 : 0 < L)
    (hLt : L / 2 ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0)
    (hΦ : -EF.gammaBracket 0 ≤
      (1 / 2) * levyCoshPotential (L / 2) + (1 / 2) * levyCoshPotential screwSignThreshold) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := half_window_plastic_floor_le_weilArchRe hf hfc hf0 hL0 hLt hsupp
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- Concrete verification that `6 ≤ levyCoshPotential y` for all `0 < y ≤ 1 / 36`. -/
theorem six_le_levyCoshPotential_of_le_inv_36 {y : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 36) :
    (6 : ℝ) ≤ levyCoshPotential y := by
  have hlt := two_mul_archLevyAntideriv_lt_levyCoshPotential hy0
  rw [archLevyAntideriv_eq_log_div hy0] at hlt
  set t := Real.exp (-y / 2)
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hexp : 1 - y / 2 ≤ t := by
    have := Real.add_one_le_exp (-y / 2)
    linarith
  have h128 : (2 : ℝ) ^ (7 : ℕ) ≤ (1 + t) / (1 - t) := by
    rw [le_div_iff₀ (by linarith)]
    norm_num
    linarith
  have hlog7 : 7 * Real.log 2 ≤ Real.log ((1 + t) / (1 - t)) := by
    have := Real.log_le_log (by positivity) h128
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have harc_low := pi_div_four_sub_le_arctan ht0.le ht1.le
  have ht_ge : (71 : ℝ) / 72 ≤ t := by linarith
  have hrem : (1 - t) / (1 + t ^ 2) ≤ (1 - (71 : ℝ) / 72) / (1 + ((71 : ℝ) / 72) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hl2 := Real.log_two_gt_d9
  have hpi := Real.pi_gt_d4
  linarith

/-- **Unconditional positivity of `weilArchRe` for all nonnegative `f ∈ C²_c(ℝ)` supported on
`Ioo 0 L` with `0 < L ≤ 1 / 18`** (expanding the unconditional window from `1 / 130` to `1 / 18`,
more than `7×` larger, without `WindowPositive`). -/
theorem weilArchRe_nonneg_of_support_Ioo_le_inv_18 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL0 : 0 < L)
    (hL : L ≤ 1 / 18) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL2 : 0 < L / 2 := by linarith
  have hLt : L / 2 ≤ screwSignThreshold := by linarith [screwSignThreshold_gt]
  have h6 : (6 : ℝ) ≤ levyCoshPotential (L / 2) :=
    six_le_levyCoshPotential_of_le_inv_36 hL2 (by linarith)
  have hA := neg_gammaBracket_zero_lt
  have h26 := twenty_six_fifths_lt_levyCoshPotential_screwSignThreshold
  exact weilArchRe_nonneg_of_support_Ioo_of_half_window_plastic hf hfc hf0 hL0 hLt hsupp (by linarith)

end

end RHTower.WeilLevyBoundaryEscape
