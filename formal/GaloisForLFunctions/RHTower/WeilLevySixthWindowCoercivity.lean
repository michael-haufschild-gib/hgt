import GaloisForLFunctions.RHTower.WeilLevySymmetricThreePointPotential

/-!
# Sixth-Window Coercivity (`x ≥ L / 6`), Five-Point Lévy–Cosh Potential, and Unconditional Window Positivity Beyond `(log 2) / 2`

In `WeilLevyQuarterWindowCoercivity.lean` and `WeilLevySymmetricThreePointPotential.lean`, we broke
the half-window barrier `x ≥ L / 2` down to `x ≥ L / 4` (`(1 / 3) * ∫ h² ≤ D_h(x)`) and proved
unconditional window positivity on `(0, 1 / 3)` (`48.1%` of `(0, log 2)`).

In this file we extend the core-slice transport staircase by one more layer (`x ≥ L / 6`), breaking
the half-window threshold `(log 2) / 2 ≈ 0.34657` of the prime-blind window `(0, log 2)`!

## Main Results

1. **Second-Layer Core-Slice Transport and Sixth-Window Coercivity (`x ≥ L / 6`)**:
   - `second_layer_slice_sub_first_layer_le_interior_jump_sq`:
     for `0 ≤ a ≤ x` and `2 * a + 3 * x ≤ L`, shifting `Ioc x (a + x)` and `Ioc (L - 2*x - a) (L - 2*x)`
     by `+x` inside `Ioc 0 (L - x)` proves
     `(1 / 2) * (∫_{Ioc (2*x) (a + 2*x)} h² + ∫_{Ioc (L - 2*x - a) (L - 2*x)} h²) - (∫_{Ioc x (2*x)} h² + ∫_{Ioc (L - 2*x) (L - x)} h²) ≤ ∫_{Ioc 0 (L - x)} (h u - h (u + x))²`.
   - `quarter_collarMass_add_eighth_core_layers_le_integral_jump_sq`:
     combining `(1 / 4)` of the second-layer + boundary-escape bound with `(3 / 4)` of
     `half_double_slice_le_integral_jump_sq` proves
     `(1 / 4) * collarMass h L x + (1 / 8) * (first_layer + second_layer_slice) ≤ D_h(x)`.
   - `one_eighth_mul_integral_sq_le_integral_jump_sq_of_sixth_le`:
     for every shift `x ≥ L / 6`, `(1 / 8) * ∫ u, h u ^ 2 ≤ ∫ u, (h u - h (u + x)) ^ 2`.

2. **Boosted `(0, log 2)` Floor and Five-Point Lévy–Cosh Potential (`3 * L / 4 ≤ c ≤ 5 * L / 6`)**:
   - `sixth_window_log_two_plastic_floor_le_weilArchRe`:
     since `log 2 / 6 < log 2 / 4 < screwSignThreshold`, integrating over `Ioo (log 2 / 6) (log 2 / 4)`
     and `Ioo (log 2 / 4) screwSignThreshold` upgrades the unconditional floor on `(0, log 2)` to
     `(A(0) + (1 / 16) * Φ(log 2 / 6) + (5 / 48) * Φ(log 2 / 4) + (5 / 6) * Φ(t_*)) * ∫ f² ≤ W_∞(f ⋆ f̃)`.
   - `five_point_sub_levyCoshPotential_le_setIntegral_Ioo` &
     `five_point_levyCosh_crossover_le_weilArchRe`:
     for `3 * L / 4 ≤ c ≤ 5 * L / 6` and `c ≤ screwSignThreshold`, combining `Ioo (L / 6) (L - c)`
     with the excess-preserving reflected bound on `Ioo (L - c) c` cancels `Φ(L - c)` and proves
     `(A(0) + (1 / 16) * Φ(L / 6) + (5 / 48) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (5 / 48) * Φ(3*L / 4) + (1 / 16) * Φ(c)) * ∫ f² + pair_c(f) ≤ W_∞(f ⋆ f̃)`.

3. **Unconditional Window Positivity on `(0, 7 / 20)` (`0.35 > (log 2) / 2 ≈ 0.34657`)**:
   - `osculating_le_five_point_potential`: closed-form lower bound cancelling `log 2`, `log 3`, and `π / 2`.
   - `weilArchRe_nonneg_of_support_Ioo_le_seven_twentieths` & `windowPositive_seven_twentieths`:
     unconditional window positivity on `(0, 7 / 20)` (`= (0, 0.35)`, covering **50.5% of `(0, log 2)`**).
   - `weilArchRe_nonneg_of_support_Ioo_le_half_log_two` & `windowPositive_half_log_two`:
     unconditional window positivity on the exact half-window `(0, Real.log 2 / 2)`!
-/

open Complex MeasureTheory Set Filter Topology Real
open scoped ENNReal FourierTransform ComplexConjugate
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevySixthWindow

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor
open RHTower.WeilLevyQuarterWindow RHTower.WeilLevySymmetricThreePoint

/-! ## Section 1: Second-Layer Core-Slice Transport and Universal Sixth-Window Coercivity (`x ≥ L / 6`) -/

/-- **Second-Layer Core-Slice Shift Transport Inequality on `(0, L)`**:
for any `BddSupp A h C` and any `0 ≤ a ≤ x` with `2 * a + 3 * x ≤ L` (so `a + x ≤ L - 2 * x - a`),
shifting `Ioc x (a + x)` by `+x` transports it into `Ioc (2 * x) (a + 2 * x)` and shifting
`Ioc (L - 2 * x - a) (L - 2 * x)` by `+x` transports it into `Ioc (L - x - a) (L - x) ⊆ Ioc (L - 2 * x) (L - x)`,
yielding:
`(1 / 2) * ((∫ v in Ioc (2 * x) (a + 2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x - a) (L - 2 * x), h u ^ 2)`
`- ((∫ u in Ioc x (2 * x), h u ^ 2) + ∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2)`
`≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`. -/
theorem second_layer_slice_sub_first_layer_le_interior_jump_sq {A : Set ℝ} {h : ℝ → ℝ}
    {C L a x : ℝ} (hh : BddSupp A h C) (ha0 : 0 ≤ a) (hax : a ≤ x) (h2a3xL : 2 * a + 3 * x ≤ L) :
    (1 / 2 : ℝ) *
        ((∫ v in Ioc (2 * x) (a + 2 * x), h v ^ 2) +
          ∫ u in Ioc (L - 2 * x - a) (L - 2 * x), h u ^ 2) -
      ((∫ u in Ioc x (2 * x), h u ^ 2) + ∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2) ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
  have hx0 : 0 ≤ x := le_trans ha0 hax
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  have hleft_pt : ∀ u : ℝ, (1 / 2 : ℝ) * h (u + x) ^ 2 - h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := half_sq_sub_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have hleft_int : (1 / 2 : ℝ) * (∫ v in Ioc (2 * x) (a + 2 * x), h v ^ 2) -
      (∫ u in Ioc x (2 * x), h u ^ 2) ≤
      ∫ u in Ioc x (a + x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc x (a + x))
      ((hshift.const_mul (1 / 2)).integrableOn.sub hsq.integrableOn)
      hjump.integrableOn hleft_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (1 / 2)).integrableOn hsq.integrableOn,
      integral_const_mul, setIntegral_Ioc_add_right (fun v => h v ^ 2) x (a + x) x,
      show x + x = 2 * x by ring, show a + x + x = a + 2 * x by ring] at h1
    have hsub_left : (∫ u in Ioc x (a + x), h u ^ 2) ≤ ∫ u in Ioc x (2 * x), h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall (Ioc_subset_Ioc le_rfl (by linarith)))
    linarith
  have hright_pt : ∀ u : ℝ, (1 / 2 : ℝ) * h u ^ 2 - h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => half_sq_sub_sq_le_sub_sq (h u) (h (u + x))
  have hright_int : (1 / 2 : ℝ) * (∫ u in Ioc (L - 2 * x - a) (L - 2 * x), h u ^ 2) -
      (∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2) ≤
      ∫ u in Ioc (L - 2 * x - a) (L - 2 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - 2 * x - a) (L - 2 * x))
      ((hsq.const_mul (1 / 2)).integrableOn.sub hshift.integrableOn)
      hjump.integrableOn hright_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (1 / 2)).integrableOn hshift.integrableOn,
      integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - 2 * x - a) (L - 2 * x) x,
      show L - 2 * x - a + x = L - x - a by ring,
      show L - 2 * x + x = L - x by ring] at h1
    have hsub_right : (∫ v in Ioc (L - x - a) (L - x), h v ^ 2) ≤
        ∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall (Ioc_subset_Ioc (by linarith) le_rfl))
    linarith
  have hdisj : Disjoint (Ioc x (a + x)) (Ioc (L - 2 * x - a) (L - 2 * x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hsub : Ioc x (a + x) ∪ Ioc (L - 2 * x - a) (L - 2 * x) ⊆ Ioc 0 (L - x) := by
    intro u hu
    rcases hu with hu1 | hu2
    · exact ⟨by linarith [hu1.1], by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], by linarith [hu2.2]⟩
  have hunion_le : (∫ u in Ioc x (a + x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (L - 2 * x - a) (L - 2 * x), (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj measurableSet_Ioc hjump.integrableOn hjump.integrableOn]
    exact setIntegral_mono_set hjump.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall hsub)
  linarith

/-- Combining `(1 / 4)` of `second_layer_slice_sub_first_layer_le_interior_jump_sq` +
`collarMass_add_interior_le_integral_jump_sq` with `(3 / 4)` of `half_double_slice_le_integral_jump_sq`
cancels the negative first-layer term and yields:
`(1 / 4) * collarMass h L x + (1 / 8) * ((∫_{Ioc x (2*x)} h² + ∫_{Ioc (L - 2*x) (L - x)} h²) + (∫_{Ioc (2*x) (a + 2*x)} h² + ∫_{Ioc (L - 2*x - a) (L - 2*x)} h²)) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem quarter_collarMass_add_eighth_core_layers_le_integral_jump_sq {A : Set ℝ} {h : ℝ → ℝ}
    {C L a x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (ha0 : 0 ≤ a) (hax : a ≤ x) (h2a3xL : 2 * a + 3 * x ≤ L) :
    (1 / 4 : ℝ) * collarMass h L x +
      (1 / 8 : ℝ) *
        (((∫ u in Ioc x (2 * x), h u ^ 2) + ∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2) +
          ((∫ v in Ioc (2 * x) (a + 2 * x), h v ^ 2) +
            ∫ u in Ioc (L - 2 * x - a) (L - 2 * x), h u ^ 2)) ≤
      ∫ u, (h u - h (u + x)) ^ 2 := by
  have hx0 : 0 ≤ x := le_trans ha0 hax
  have h3xL : 3 * x ≤ L := by linarith
  have h1 := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
  have h2 := second_layer_slice_sub_first_layer_le_interior_jump_sq hh ha0 hax h2a3xL
  have h3 := half_double_slice_le_integral_jump_sq hh hsupp hx0 h3xL
  linarith

/-- For any `BddSupp A h C` and any shift `x ∈ [L / 6, L / 4]`, setting `a = min x ((L - 3 * x) / 2)`
covers the entire core `Ioc x (L - x)` by the first layer `Ioc x (2 * x) ∪ Ioc (L - 2 * x) (L - x)`
and the second-layer slices `Ioc (2 * x) (a + 2 * x) ∪ Ioc (L - 2 * x - a) (L - 2 * x)`. -/
theorem coreMass_le_two_layers_of_sixth_le {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hx_low : L / 6 ≤ x) (hx_high : x ≤ L / 4) :
    coreMass h L x ≤
      ((∫ u in Ioc x (2 * x), h u ^ 2) + ∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2) +
        ((∫ v in Ioc (2 * x) (min x ((L - 3 * x) / 2) + 2 * x), h v ^ 2) +
          ∫ u in Ioc (L - 2 * x - min x ((L - 3 * x) / 2)) (L - 2 * x), h u ^ 2) := by
  unfold coreMass
  set a := min x ((L - 3 * x) / 2)
  have hgap : L - 2 * x - a ≤ a + 2 * x := by
    have h1 : (L - 4 * x) / 2 ≤ a := le_min (by linarith) (by linarith)
    linarith
  have hinner : (∫ u in Ioc (2 * x) (L - 2 * x), h u ^ 2) ≤
      (∫ v in Ioc (2 * x) (a + 2 * x), h v ^ 2) +
        ∫ u in Ioc (L - 2 * x - a) (L - 2 * x), h u ^ 2 := by
    refine setIntegral_le_add_of_subset_union hh.integrable_sq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (a + 2 * x) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨lt_of_le_of_lt hgap hgt, hu.2⟩
  have houter1 : (∫ u in Ioc x (L - 2 * x), h u ^ 2) ≤
      (∫ u in Ioc x (2 * x), h u ^ 2) + ∫ u in Ioc (2 * x) (L - 2 * x), h u ^ 2 := by
    refine setIntegral_le_add_of_subset_union hh.integrable_sq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (2 * x) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨hgt, hu.2⟩
  have houter2 : (∫ u in Ioc x (L - x), h u ^ 2) ≤
      (∫ u in Ioc x (L - 2 * x), h u ^ 2) + ∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2 := by
    refine setIntegral_le_add_of_subset_union hh.integrable_sq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (L - 2 * x) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨hgt, hu.2⟩
  linarith

/-- **Universal Sixth-Window Jump Coercivity (`x ≥ L / 6`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and **every shift `x ≥ L / 6`**,
`(1 / 8) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem one_eighth_mul_integral_sq_le_integral_jump_sq_of_sixth_le {A : Set ℝ} {h : ℝ → ℝ}
    {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 6 ≤ x) :
    (1 / 8 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  rcases le_or_gt x (L / 4) with hle | hgt
  · set a := min x ((L - 3 * x) / 2)
    have ha0 : 0 ≤ a := le_min (by linarith) (by linarith)
    have hax : a ≤ x := min_le_left _ _
    have h2a3xL : 2 * a + 3 * x ≤ L := by
      have : a ≤ (L - 3 * x) / 2 := min_le_right _ _
      linarith
    have hcov := coreMass_le_two_layers_of_sixth_le hh hx hle
    have hlayers := quarter_collarMass_add_eighth_core_layers_le_integral_jump_sq
      hh hsupp ha0 hax h2a3xL
    have hsum := collarMass_add_coreMass_eq hh (by linarith : x ≤ L / 2)
    have hcol_nn := collarMass_nonneg h L x
    linarith
  · have hq := one_third_mul_integral_sq_le_integral_jump_sq_of_quarter_le hh hsupp hL0 hgt.le
    have hsq : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith

/-- **Sixth-Window Autocorrelation Upper Bound (`x ≥ L / 6`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and every shift `x ≥ L / 6`,
`2 * autocorr h x ≤ (15 / 8) * ∫ u, h u ^ 2`. -/
theorem two_mul_autocorr_le_fifteen_eighths_mul_integral_sq_of_sixth_le {A : Set ℝ} {h : ℝ → ℝ}
    {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 6 ≤ x) :
    2 * autocorr h x ≤ (15 / 8 : ℝ) * ∫ u, h u ^ 2 := by
  have h1 := one_eighth_mul_integral_sq_le_integral_jump_sq_of_sixth_le hh hsupp hL0 hx
  have h2 := integral_jump_sq hh x
  linarith

/-! ## Section 2: Sixth-Window Potential Integrals, Boosted `(0, log 2)` Floor, and Five-Point Crossover -/

/-- For any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`) and any `a, b` with
`L / 6 ≤ a ≤ b ≤ screwSignThreshold`,
`(1 / 16) * (levyCoshPotential a - levyCoshPotential b) * ∫ u, h u ^ 2 ≤ ∫ x in Ioo a b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem one_sixteenth_mul_sub_levyCoshPotential_le_setIntegral_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L a b : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 < L) (hL6a : L / 6 ≤ a) (hab : a ≤ b) (hbt : b ≤ screwSignThreshold) :
    (1 / 16 : ℝ) * (levyCoshPotential a - levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo a b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by linarith) hL6a
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc a b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le ha0 hx.1).neg
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hh
  have hI_rhs : IntegrableOn
      (fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) (Ioo a b) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hbt))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hI_lhs : IntegrableOn
      (fun x => (-screwRegularKernel x) * ((1 / 8 : ℝ) * ∫ u, h u ^ 2)) (Ioo a b) :=
    (hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const _
  have hval : (∫ x in Ioo a b, (-screwRegularKernel x) * ((1 / 8 : ℝ) * ∫ u, h u ^ 2)) =
      (1 / 16 : ℝ) * (levyCoshPotential a - levyCoshPotential b) * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, setIntegral_Ioo_neg_screwRegularKernel ha0 hab]
    ring
  rw [← hval]
  refine setIntegral_mono_on hI_lhs hI_rhs measurableSet_Ioo fun x hx => ?_
  have hK0 : 0 ≤ -screwRegularKernel x :=
    neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
      (lt_trans ha0 hx.1) (hx.2.le.trans hbt))
  exact mul_le_mul_of_nonneg_left
    (one_eighth_mul_integral_sq_le_integral_jump_sq_of_sixth_le hh hsupp hL0.le
      (hL6a.trans hx.1.le)) hK0

/-- **Sixth-Plus-Quarter Window Boosted Floor on `(0, L)` (`L / 4 ≤ c ≤ screwSignThreshold`)**:
for every signed `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and every `c` with
`L / 4 ≤ c ≤ screwSignThreshold`, splitting `Ioo (L / 6) c` at `L / 4` combines the `(1 / 8)`
sixth-window bound on `Ioo (L / 6) (L / 4)` with the `(1 / 3)` quarter-window bound on `Ioo (L / 4) c`:
`(A(0) + (1 / 16) * Φ(L / 6) + (5 / 48) * Φ(L / 4) + (5 / 6) * Φ(c)) * ∫ f² + pair_c(f) ≤ W_∞(f ⋆ f̃)`. -/
theorem sixth_add_quarter_window_levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL0 : 0 < L)
    (hL4c : L / 4 ≤ c) (hct : c ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 16) * levyCoshPotential (L / 6) +
        (5 / 48) * levyCoshPotential (L / 4) + (5 / 6) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL6 : 0 < L / 6 := by linarith
  have hL6_L4 : L / 6 ≤ L / 4 := by linarith
  have hL6c : L / 6 ≤ c := by linarith
  have hL4t : L / 4 ≤ screwSignThreshold := hL4c.trans hct
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  let G : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2
  have hD0 : ∀ x, 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hB
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 6) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL6 hx.1).neg
  have hIG : IntegrableOn G (Ioo (L / 6) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, f u ^ 2)).mono' (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL6 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hB x) hK0
  have hIG_left_Ioc : IntegrableOn G (Ioc (L / 6) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIG.mono_set (Ioo_subset_Ioo le_rfl hL4c)
  have hIG_right_Ioc : IntegrableOn G (Ioc (L / 4) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIG.mono_set (Ioo_subset_Ioo hL6_L4 le_rfl)
  have hdisj : Disjoint (Ioc (L / 6) (L / 4)) (Ioc (L / 4) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 6) c, G x) =
      (∫ x in Ioo (L / 6) (L / 4), G x) + ∫ x in Ioo (L / 4) c, G x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL6_L4 hL4c,
      setIntegral_union hdisj measurableSet_Ioc hIG_left_Ioc hIG_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL6 hL6c hct
  have hs := one_sixteenth_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL0 le_rfl hL6_L4 hL4t
  have hq := one_sixth_mul_sub_levyCoshPotential_quarter_le_setIntegral_Ioo
    hB hsupp hL0 hL4c hct
  dsimp only [G] at hsplit
  linarith

/-- **Unconditional Sixth-Plus-Quarter Window Boosted Floor on `(0, log 2)`**:
every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 (Real.log 2)` satisfies
`(EF.gammaBracket 0 + (1 / 16) * Φ(log 2 / 6) + (5 / 48) * Φ(log 2 / 4) + (5 / 6) * Φ(screwSignThreshold)) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem sixth_window_log_two_plastic_floor_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hsupp : ∀ u ∉ Ioo 0 (Real.log 2), f u = 0) :
    (EF.gammaBracket 0 + (1 / 16) * levyCoshPotential (Real.log 2 / 6) +
        (5 / 48) * levyCoshPotential (Real.log 2 / 4) +
        (5 / 6) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL4t : Real.log 2 / 4 ≤ screwSignThreshold := by
    linarith [Real.log_two_lt_d9, screwSignThreshold_gt]
  have hmain := sixth_add_quarter_window_levyCosh_crossover_le_weilArchRe
    hf hfc hL0 hL4t le_rfl hsupp
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-- **Excess-Preserving Outer Shell Reflection Bound (`3 * L / 4 ≤ c ≤ 5 * L / 6`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`) and any `c` with
`3 * L / 4 ≤ c ≤ 5 * L / 6` and `c ≤ screwSignThreshold`, retaining the sixth-window lower bound
`D_h(L - y) ≥ (1 / 8) * ∫ h²` on `y ∈ Ioo (3 * L / 4) c` (where `L - y ∈ Ioo (L - c) (L / 4) ⊆ Icc (L / 6) (L / 4)`)
and the quarter-window lower bound `D_h(L - y) ≥ (1 / 3) * ∫ h²` on `y ∈ Ioo (L / 2) (3 * L / 4)` proves:
`((1 / 16) * Φ(L - c) + (5 / 48) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (5 / 48) * Φ(3 * L / 4) - (15 / 16) * Φ(c)) * ∫ h²`
`≤ ∫ x in Ioo (L - c) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem excess_outer_shell_levyCoshPotential_le_setIntegral_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L c : ℝ} (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0)
    (hL0 : 0 < L) (h3L4c : 3 * L / 4 ≤ c) (hc5L6 : c ≤ 5 * L / 6)
    (hct : c ≤ screwSignThreshold) :
    ((1 / 16 : ℝ) * levyCoshPotential (L - c) + (5 / 48 : ℝ) * levyCoshPotential (L / 4) +
        (2 / 3 : ℝ) * levyCoshPotential (L / 2) +
        (5 / 48 : ℝ) * levyCoshPotential (3 * L / 4) -
        (15 / 16 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L - c) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hcL : c < L := by linarith
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
  -- On `Ioo (3 * L / 4) c`, retain the `(1 / 8)` sixth-window excess on `L - y ∈ Ioo (L - c) (L / 4)`.
  have h2 : (((1 / 16 : ℝ) * (levyCoshPotential (L - c) - levyCoshPotential (L / 4)) +
      (15 / 16 : ℝ) * (levyCoshPotential (3 * L / 4) - levyCoshPotential c)) * ∫ u, h u ^ 2) ≤
      ∫ y in Ioo (3 * L / 4) c, (F (L - y) + F y) := by
    have hIK_2_right : IntegrableOn (fun y => -screwRegularKernel y) (Ioo (3 * L / 4) c) :=
      (hcont_K.mono (Icc_subset_Icc (by linarith) le_rfl)).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
    have hIK_2_refl : IntegrableOn (fun y => -screwRegularKernel (L - y)) (Ioo (3 * L / 4) c) := by
      have hcont_refl : ContinuousOn (fun y => -screwRegularKernel (L - y)) (Icc (3 * L / 4) c) :=
        (hcont_K.comp (continuousOn_const.sub continuousOn_id)
          fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩)
      exact hcont_refl.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    let G₂ : ℝ → ℝ := fun y =>
      ((1 / 8 : ℝ) * (-screwRegularKernel (L - y)) + (15 / 8 : ℝ) * (-screwRegularKernel y)) *
        ∫ u, h u ^ 2
    have hIG₂ : IntegrableOn G₂ (Ioo (3 * L / 4) c) :=
      ((hIK_2_refl.const_mul (1 / 8)).add (hIK_2_right.const_mul (15 / 8))).mul_const _
    have hrefl_K2 : (∫ y in Ioo (3 * L / 4) c, -screwRegularKernel (L - y)) =
        (1 / 2 : ℝ) * (levyCoshPotential (L - c) - levyCoshPotential (L / 4)) := by
      have hIK_all_right : IntegrableOn (fun y => -screwRegularKernel (L - y)) (Ioo (L / 2) c) := by
        have hcont_refl : ContinuousOn (fun y => -screwRegularKernel (L - y)) (Icc (L / 2) c) :=
          (hcont_K.comp (continuousOn_const.sub continuousOn_id)
            fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩)
        exact hcont_refl.integrableOn_Icc.mono_set Ioo_subset_Icc_self
      have hIK_1_Ioc : IntegrableOn (fun y => -screwRegularKernel (L - y))
          (Ioc (L / 2) (3 * L / 4)) := by
        rw [integrableOn_Ioc_iff_integrableOn_Ioo]
        exact hIK_all_right.mono_set (Ioo_subset_Ioo le_rfl h3L4c)
      have hIK_2_Ioc : IntegrableOn (fun y => -screwRegularKernel (L - y))
          (Ioc (3 * L / 4) c) := by
        rw [integrableOn_Ioc_iff_integrableOn_Ioo]
        exact hIK_all_right.mono_set (Ioo_subset_Ioo hL2_3L4 le_rfl)
      have hsplit_K : (∫ y in Ioo (L / 2) c, -screwRegularKernel (L - y)) =
          (∫ y in Ioo (L / 2) (3 * L / 4), -screwRegularKernel (L - y)) +
            ∫ y in Ioo (3 * L / 4) c, -screwRegularKernel (L - y) := by
        rw [← integral_Ioc_eq_integral_Ioo,
          ← Ioc_union_Ioc_eq_Ioc hL2_3L4 h3L4c,
          setIntegral_union hdisj_pair measurableSet_Ioc hIK_1_Ioc hIK_2_Ioc,
          integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      have hall := setIntegral_Ioo_reflect_neg_screwRegularKernel hL0 hL2c hcL
      have hpart1 := setIntegral_Ioo_reflect_neg_screwRegularKernel hL0 hL2_3L4 (by linarith)
      rw [show L - 3 * L / 4 = L / 4 by ring] at hpart1
      linarith
    have hval2 : (∫ y in Ioo (3 * L / 4) c, G₂ y) =
        ((1 / 16 : ℝ) * (levyCoshPotential (L - c) - levyCoshPotential (L / 4)) +
          (15 / 16 : ℝ) * (levyCoshPotential (3 * L / 4) - levyCoshPotential c)) *
          ∫ u, h u ^ 2 := by
      dsimp only [G₂]
      rw [integral_mul_const,
        integral_add (hIK_2_refl.const_mul (1 / 8)) (hIK_2_right.const_mul (15 / 8)),
        integral_const_mul, integral_const_mul, hrefl_K2,
        setIntegral_Ioo_neg_screwRegularKernel h3L4_pos h3L4c]
      ring
    rw [← hval2]
    refine setIntegral_mono_on hIG₂
      (hIF_pair.mono_set (Ioo_subset_Ioo hL2_3L4 le_rfl)) measurableSet_Ioo fun y hy => ?_
    dsimp only [G₂, F, Pi.add_apply]
    have hy0 : 0 < y := lt_trans h3L4_pos hy.1
    have hLy0 : 0 < L - y := by linarith [hy.2]
    have hLy_le : L - y ≤ y := by linarith [hy.1]
    have hLy_sixth : L / 6 ≤ L - y := by linarith [hy.2]
    have hK_le : -screwRegularKernel y ≤ -screwRegularKernel (L - y) :=
      neg_le_neg (monotoneOn_screwRegularKernel hLy0 hy0 hLy_le)
    have hK0 : 0 ≤ -screwRegularKernel y :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold hy0 (hy.2.le.trans hct))
    have hsum := two_mul_integral_sq_le_integral_jump_sq_add_sub hh hsupp hy0.le
      (le_trans hy.2.le hcL.le)
    have hs := one_eighth_mul_integral_sq_le_integral_jump_sq_of_sixth_le
      hh hsupp hL0.le hLy_sixth
    have hstep1 : (-screwRegularKernel y) * (2 * ∫ u, h u ^ 2) ≤
        (-screwRegularKernel y) *
          ((∫ u, (h u - h (u + y)) ^ 2) + ∫ u, (h u - h (u + (L - y))) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hK0
    have hstep2 : (-screwRegularKernel (L - y) - -screwRegularKernel y) *
          ((1 / 8 : ℝ) * ∫ u, h u ^ 2) ≤
        (-screwRegularKernel (L - y) - -screwRegularKernel y) *
          ∫ u, (h u - h (u + (L - y))) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hK_le)
    linarith
  dsimp only [F] at hsplit_pair h1 h2
  linarith

/-- **Five-Point Potential Lower Bound on `Ioo (L / 6) c` (`3 * L / 4 ≤ c ≤ 5 * L / 6`)**:
combining `one_sixteenth_mul_sub_levyCoshPotential_le_setIntegral_Ioo` on `Ioo (L / 6) (L - c)`
with `excess_outer_shell_levyCoshPotential_le_setIntegral_Ioo` on `Ioo (L - c) c` cancels
`levyCoshPotential (L - c)` identically, proving:
`((1 / 16) * Φ(L / 6) + (5 / 48) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (5 / 48) * Φ(3 * L / 4) - (15 / 16) * Φ(c)) * ∫ h²`
`≤ ∫_{Ioo (L / 6) c} (-K(x)) D_h(x) dx`. -/
theorem five_point_sub_levyCoshPotential_le_setIntegral_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L c : ℝ} (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0)
    (hL0 : 0 < L) (h3L4c : 3 * L / 4 ≤ c) (hc5L6 : c ≤ 5 * L / 6)
    (hct : c ≤ screwSignThreshold) :
    ((1 / 16 : ℝ) * levyCoshPotential (L / 6) + (5 / 48 : ℝ) * levyCoshPotential (L / 4) +
        (2 / 3 : ℝ) * levyCoshPotential (L / 2) +
        (5 / 48 : ℝ) * levyCoshPotential (3 * L / 4) -
        (15 / 16 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 6) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL6 : 0 < L / 6 := by linarith
  have hL6_Lc : L / 6 ≤ L - c := by linarith
  have hLc_c : L - c ≤ c := by linarith
  have hLct : L - c ≤ screwSignThreshold := hLc_c.trans hct
  let G : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hh
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 6) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL6 hx.1).neg
  have hIG : IntegrableOn G (Ioo (L / 6) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL6 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIG_left_Ioc : IntegrableOn G (Ioc (L / 6) (L - c)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIG.mono_set (Ioo_subset_Ioo le_rfl hLc_c)
  have hIG_right_Ioc : IntegrableOn G (Ioc (L - c) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIG.mono_set (Ioo_subset_Ioo hL6_Lc le_rfl)
  have hdisj : Disjoint (Ioc (L / 6) (L - c)) (Ioc (L - c) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 6) c, G x) =
      (∫ x in Ioo (L / 6) (L - c), G x) + ∫ x in Ioo (L - c) c, G x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL6_Lc hLc_c,
      setIntegral_union hdisj measurableSet_Ioc hIG_left_Ioc hIG_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have hs := one_sixteenth_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL6_Lc hLct
  have hout := excess_outer_shell_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 h3L4c hc5L6 hct
  dsimp only [G] at hsplit
  linarith

/-- **Five-Point Lévy–Cosh Crossover on `(0, L)` (`3 * L / 4 ≤ c ≤ 5 * L / 6`)**:
for every signed `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and every `c` with
`3 * L / 4 ≤ c ≤ 5 * L / 6` and `c ≤ screwSignThreshold`,
`(A(0) + (1 / 16) * Φ(L / 6) + (5 / 48) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (5 / 48) * Φ(3 * L / 4) + (1 / 16) * Φ(c)) * ∫ f² + pair_c(f) ≤ W_∞(f ⋆ f̃)`. -/
theorem five_point_levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL0 : 0 < L)
    (h3L4c : 3 * L / 4 ≤ c) (hc5L6 : c ≤ 5 * L / 6) (hct : c ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 16) * levyCoshPotential (L / 6) +
        (5 / 48) * levyCoshPotential (L / 4) +
        (2 / 3) * levyCoshPotential (L / 2) +
        (5 / 48) * levyCoshPotential (3 * L / 4) +
        (1 / 16) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL6 : 0 < L / 6 := by linarith
  have hL6c : L / 6 ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL6 hL6c hct
  have h5 := five_point_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL0 h3L4c hc5L6 hct
  linarith

/-! ## Section 3: Osculating Five-Point Lower Bound and Unconditional Window Positivity on `(0, 7 / 20)` (`0.35 > (log 2) / 2`) -/

/-- **Osculating Lower Bound for the Five-Point Potential**:
for every `L > 0` and `0 < c ≤ 5 * L / 6`,
`Real.log (1 / (Real.pi * L)) + (5 / 48) * Real.log (4 / 3) + (1 / 16) * Real.log (9 / 5) + (7 / 2) * ((43 / 96) * L + (1 / 16) * c) - eulerMascheroniConstant`
`≤ EF.gammaBracket 0 + (1 / 16) * Φ(L / 6) + (5 / 48) * Φ(L / 4) + (2 / 3) * Φ(L / 2) + (5 / 48) * Φ(3 * L / 4) + (1 / 16) * Φ(c)`. -/
theorem osculating_le_five_point_potential {L c : ℝ} (hL0 : 0 < L)
    (hc0 : 0 < c) (hc5L6 : c ≤ 5 * L / 6) :
    Real.log (1 / (Real.pi * L)) + (5 / 48 : ℝ) * Real.log (4 / 3) +
        (1 / 16 : ℝ) * Real.log (9 / 5) +
        (7 / 2 : ℝ) * ((43 / 96 : ℝ) * L + (1 / 16 : ℝ) * c) -
        eulerMascheroniConstant ≤
      EF.gammaBracket 0 + (1 / 16) * levyCoshPotential (L / 6) +
        (5 / 48) * levyCoshPotential (L / 4) +
        (2 / 3) * levyCoshPotential (L / 2) +
        (5 / 48) * levyCoshPotential (3 * L / 4) +
        (1 / 16) * levyCoshPotential c := by
  have h1 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 6 by linarith)
  have h2 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 4 by linarith)
  have h3 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 2 by linarith)
  have h4 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < 3 * L / 4 by linarith)
  have h5 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential hc0
  have hlog1 : Real.log (1 / (2 * Real.pi * (L / 6))) =
      Real.log (1 / (Real.pi * L)) + Real.log 3 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; norm_num
  have hlog2 : Real.log (1 / (2 * Real.pi * (L / 4))) =
      Real.log (1 / (Real.pi * L)) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; norm_num
  have hlog3 : Real.log (1 / (2 * Real.pi * (L / 2))) =
      Real.log (1 / (Real.pi * L)) := by
    congr 1; field_simp
  have hlog4 : Real.log (1 / (2 * Real.pi * (3 * L / 4))) =
      Real.log (1 / (Real.pi * L)) + Real.log (4 / 3) - Real.log 2 := by
    rw [eq_sub_iff_add_eq, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  have hlog5_le : Real.log (1 / (Real.pi * L)) + Real.log (9 / 5) - Real.log 3 ≤
      Real.log (1 / (2 * Real.pi * c)) := by
    have hlog5_eq : Real.log (1 / (2 * Real.pi * (5 * L / 6))) =
        Real.log (1 / (Real.pi * L)) + Real.log (9 / 5) - Real.log 3 := by
      rw [eq_sub_iff_add_eq, ← Real.log_mul (by positivity) (by positivity),
        ← Real.log_mul (by positivity) (by positivity)]
      congr 1; field_simp; norm_num
    rw [← hlog5_eq]
    refine Real.log_le_log (by positivity) ?_
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left hc5L6 (by positivity))
  linarith

/-- For every `L > 0`, splitting `π * L = (π / 3) * (3 * L)` and applying `Real.log_le_sub_one_of_pos`
gives the tight rational-linear lower bound `2 - Real.pi / 3 - 3 * L ≤ Real.log (1 / (Real.pi * L))`. -/
theorem two_sub_pi_div_three_sub_three_mul_le_log_inv_pi_mul {L : ℝ} (hL0 : 0 < L) :
    2 - Real.pi / 3 - 3 * L ≤ Real.log (1 / (Real.pi * L)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.pi / 3 by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show 0 < 3 * L by positivity)
  have hlog : Real.log (1 / (Real.pi * L)) = -Real.log (Real.pi / 3) - Real.log (3 * L) := by
    rw [one_div, Real.log_inv, show Real.pi * L = (Real.pi / 3) * (3 * L) by ring,
      Real.log_mul (by positivity) (by positivity)]
    ring
  linarith

/-- Rational lower bounds `2 / 7 < Real.log (4 / 3)` and `32 / 55 < Real.log (9 / 5)`. -/
theorem two_sevenths_lt_log_four_thirds : (2 : ℝ) / 7 < Real.log (4 / 3) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 3)
  norm_num at h ⊢
  exact h

theorem thirty_two_fifty_fifths_lt_log_nine_fifths : (32 : ℝ) / 55 < Real.log (9 / 5) := by
  have h1 := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 5)
  have h2 := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  norm_num at h1 h2
  have hmul : Real.log (9 / 5 : ℝ) = Real.log (6 / 5) + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  linarith

/-- Tightened lower rational enclosure `(6036 : ℝ) / 21509 < screwSignThreshold` (`0.280626 < t_*`),
derived directly from `exp_half_screwSignThreshold_gt` via `Real.lt_log_one_add_of_pos`. -/
theorem screwSignThreshold_gt_6036_over_21509 :
    (6036 : ℝ) / 21509 < screwSignThreshold := by
  have hexp := exp_half_screwSignThreshold_gt
  have hlog := Real.log_lt_log (by norm_num) hexp
  rw [Real.log_exp] at hlog
  have hpade := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1509 / 10000)
  norm_num at hpade
  linarith

/-- Tightened upper rational enclosure `screwSignThreshold < (787 : ℝ) / 2700` (`t_* < 0.291481`),
derived directly from `exp_half_screwSignThreshold_lt` by factoring
`11510 / 10000 = (27 / 25) * (1151 / 1080)`. -/
theorem screwSignThreshold_lt_787_over_2700 :
    screwSignThreshold < (787 : ℝ) / 2700 := by
  have hexp := exp_half_screwSignThreshold_lt
  have hlog := Real.log_lt_log (Real.exp_pos _) hexp
  rw [Real.log_exp, show (1151 : ℝ) / 1000 = (27 / 25) * (1151 / 1080) by norm_num,
    Real.log_mul (by norm_num) (by norm_num)] at hlog
  have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 27 / 25)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1151 / 1080)
  linarith

/-- **Strict Positivity of the Five-Point Potential at `L = 7 / 20` (`= 0.35 > (log 2) / 2`)**:
`0 ≤ EF.gammaBracket 0 + (1 / 16) * Φ((7/20)/6) + (5 / 48) * Φ((7/20)/4) + (2 / 3) * Φ((7/20)/2) + (5 / 48) * Φ(3*(7/20)/4) + (1 / 16) * Φ(screwSignThreshold)`. -/
theorem zero_le_five_point_potential_seven_twentieths :
    0 ≤ EF.gammaBracket 0 + (1 / 16) * levyCoshPotential ((7 / 20 : ℝ) / 6) +
        (5 / 48) * levyCoshPotential ((7 / 20 : ℝ) / 4) +
        (2 / 3) * levyCoshPotential ((7 / 20 : ℝ) / 2) +
        (5 / 48) * levyCoshPotential (3 * (7 / 20 : ℝ) / 4) +
        (1 / 16) * levyCoshPotential screwSignThreshold := by
  have hc0 : 0 < screwSignThreshold := screwSignThreshold_pos
  have hc5L6 : screwSignThreshold ≤ 5 * (7 / 20 : ℝ) / 6 := by
    linarith [screwSignThreshold_lt_787_over_2700]
  have hosc := osculating_le_five_point_potential (by norm_num : (0 : ℝ) < 7 / 20) hc0 hc5L6
  have hlog_pi := two_sub_pi_div_three_sub_three_mul_le_log_inv_pi_mul
    (by norm_num : (0 : ℝ) < 7 / 20)
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hlog43 := two_sevenths_lt_log_four_thirds
  have hlog95 := thirty_two_fifty_fifths_lt_log_nine_fifths
  have ht_gt := screwSignThreshold_gt_6036_over_21509
  have hγ :=
    RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith

/-- **Unconditional nonnegativity of `weilArchRe` on `(0, L)` for all `L ≤ 7 / 20` (`= 0.35`)**:
every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with `L ≤ 7 / 20` (covering **50.5%**
of `(0, log 2)` and strictly exceeding `(log 2) / 2 ≈ 0.34657`) satisfies `0 ≤ W_∞(f ⋆ f̃)`
unconditionally without `WindowPositive`! -/
theorem weilArchRe_nonneg_of_support_Ioo_le_seven_twentieths {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL : L ≤ 7 / 20)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_7_20 : ∀ u ∉ Ioo (0 : ℝ) (7 / 20), f u = 0 :=
    fun u hu => hsupp u fun h => hu ⟨h.1, lt_of_lt_of_le h.2 hL⟩
  have hmain := five_point_levyCosh_crossover_le_weilArchRe hf hfc
    (by norm_num : (0 : ℝ) < 7 / 20)
    (by linarith [screwSignThreshold_gt_6036_over_21509])
    (by linarith [screwSignThreshold_lt_787_over_2700])
    le_rfl hsupp_7_20
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  have hpot := zero_le_five_point_potential_seven_twentieths
  have hE0 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hpot_E : 0 ≤ (EF.gammaBracket 0 + (1 / 16) * levyCoshPotential ((7 / 20 : ℝ) / 6) +
        (5 / 48) * levyCoshPotential ((7 / 20 : ℝ) / 4) +
        (2 / 3) * levyCoshPotential ((7 / 20 : ℝ) / 2) +
        (5 / 48) * levyCoshPotential (3 * (7 / 20 : ℝ) / 4) +
        (1 / 16) * levyCoshPotential screwSignThreshold) * ∫ u, f u ^ 2 :=
    mul_nonneg hpot hE0
  linarith

/-- **Unconditional nonnegativity of `weilArchRe` on the exact half-window `(0, (log 2) / 2)`**:
every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 (Real.log 2 / 2)` satisfies
`0 ≤ W_∞(f ⋆ f̃)` unconditionally! -/
theorem weilArchRe_nonneg_of_support_Ioo_le_half_log_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL : L ≤ Real.log 2 / 2)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_seven_twentieths hf hfc hf0
    (hL.trans (by linarith [Real.log_two_lt_d9])) hsupp

/-- **Unconditional `WindowPositive` on `(0, 7 / 20)` (`= (0, 0.35)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (7 / 20)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_seven_twentieths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (7 / 20)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_seven_twentieths hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on the exact half-window `(0, Real.log 2 / 2)`**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (Real.log 2 / 2)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_half_log_two (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (Real.log 2 / 2))
    (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_half_log_two hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

end

end RHTower.WeilLevySixthWindow
