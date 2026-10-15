import GaloisForLFunctions.RHTower.WeilLevySixthWindowCoercivity

/-!
# Cycle 70: Fibonacci & Disjoint Midpoint-Split Staircase Coercivity and Unconditional Window Positivity on `(0, 9 / 25)`

In `WeilLevyQuarterWindowCoercivity.lean` (Cycle 67) and `WeilLevySixthWindowCoercivity.lean`
(Cycle 69), we established the universal jump coercivity bounds
* `(1 / 3) * ∫ h² ≤ D_h(x)` for `x ≥ L / 4`, and
* `(1 / 8) * ∫ h² ≤ D_h(x)` for `x ≥ L / 6`,
which yielded the five-point potential floor and unconditional `WindowPositive` on
`(0, 7 / 20)` (`= (0, 0.35) > (log 2) / 2`).

In this module we sharpen both staircase coercivity constants by eliminating two sources of loss:
1. **Fibonacci Optimization on `[L / 4, L / 2]` (`8 / 21 ≈ 0.38095` vs. `1 / 3 ≈ 0.33333`)**:
   Instead of using `(1 / 2) p² - q² ≤ (p - q)²` first and taking a convex combination afterward,
   we use the Fibonacci-ratio sum-of-squares identity
   $$(p - q)^2 - \left(\frac{8}{21} p^2 - \frac{13}{21} q^2\right)
     = \frac{21}{34}\left(p - \frac{34}{21} q\right)^2 + \frac{1}{714} p^2 \ge 0,$$
   which equalizes the collar weight `1 - 13 / 21 = 8 / 21` and the core weight `8 / 21` in one step
   (within `0.00101` of the theoretical spectral limit `(3 - √5) / 2 ≈ 0.381966`), proving
   $$\frac{8}{21} \int_{\mathbb{R}} h(u)^2\,du \le \int_{\mathbb{R}} (h(u) - h(u + x))^2\,du
     \qquad \forall x \ge \frac{L}{4}.$$

2. **Disjoint Midpoint-Split Two-Step Coercivity on `[L / 6, L / 4]` (`7 / 36 ≈ 0.19444` vs. `1 / 8 = 0.125`)**:
   In Cycle 69, shifting both `Ioc x (2x)` and `Ioc (L - 3x) (L - 2x)` overlapped when `x > L / 5`.
   Here we split the second interior layer `Ioc (2x) (L - 2x)` at the midpoint `L / 2` into
   `Ioc (2x) (L / 2)` (reached by `+x` from `Ioc x (L / 2 - x) ⊆ Ioc x (2x)`) and
   `Ioc (L / 2) (L - 2x)` (whose `+x` image lies in `Ioc (L / 2 + x) (L - x) ⊆ Ioc (L - 2x) (L - x)`).
   Because `0 ≤ x ≤ L / 2 - x ≤ L / 2 ≤ L - 2x ≤ L - x` for all `x ∈ [L / 6, L / 4]`, the four jump
   intervals `Ioc 0 x`, `Ioc x (L / 2 - x)`, `Ioc (L / 2) (L - 2x)`, `Ioc (L - 2x) (L - x)` are
   pairwise disjoint! Combining the quadratic transport bounds with weights `(4 / 9, 4 / 5)` on the
   first step and `(1 / 5, 1 / 4)` on the second step equalizes `4 / 9 - 1 / 4 = 7 / 36` and
   `1 - 4 / 5 = 1 / 5 ≥ 7 / 36`, proving
   $$\frac{7}{36} \int_{\mathbb{R}} h(u)^2\,du \le \int_{\mathbb{R}} (h(u) - h(u + x))^2\,du
     \qquad \forall x \ge \frac{L}{6}$$
   (a `+55.6%` improvement over `1 / 8`, within `0.0036` of the spectral limit `4 sin²(π / 14) ≈ 0.19806`).

3. **Sharpened Five-Point Potential and Unconditional Window Positivity on `(0, 9 / 25)` (`= (0, 0.36)`)**:
   Combining the `8 / 21` and `7 / 36` coercivity bounds with midpoint reflection yields the
   sharpened five-point potential floor with symmetric weights `(7/72, 47/504, 13/21, 47/504, 7/72)`:
   $$\left(A(0) + \frac{7}{72}\Phi\left(\frac{L}{6}\right) + \frac{47}{504}\Phi\left(\frac{L}{4}\right)
     + \frac{13}{21}\Phi\left(\frac{L}{2}\right) + \frac{47}{504}\Phi\left(\frac{3L}{4}\right)
     + \frac{7}{72}\Phi(c)\right)\int_{\mathbb{R}} f(u)^2\,du \le W_\infty(f \star \tilde f),$$
   proving unconditional `WindowPositive` on `(0, 9 / 25)` (`= (0, 0.36)`, covering **51.94% of `(0, log 2)`**)!
-/

open Complex MeasureTheory Set Filter Topology Real
open scoped ENNReal FourierTransform ComplexConjugate
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyFibonacciStaircase

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor
open RHTower.WeilLevyQuarterWindow RHTower.WeilLevySymmetricThreePoint
open RHTower.WeilLevySixthWindow

/-! ## Section 1: Fibonacci Optimization on `[L / 4, L / 2]` (`(8 / 21) * ∫ h² ≤ D_h(x)`) -/

/-- Fibonacci-ratio quadratic transport inequality `(8 / 21) * p² - (13 / 21) * q² ≤ (p - q)²`,
proved via the exact sum-of-squares identity
`(p - q)² - ((8 / 21) * p² - (13 / 21) * q²) = (21 / 34) * (p - (34 / 21) * q)² + (1 / 714) * p²`. -/
theorem eight_twenty_firsts_sq_sub_thirteen_twenty_firsts_sq_le_sub_sq (p q : ℝ) :
    (8 / 21 : ℝ) * p ^ 2 - (13 / 21 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  have hid : (p - q) ^ 2 - ((8 / 21 : ℝ) * p ^ 2 - (13 / 21 : ℝ) * q ^ 2) =
      (21 / 34 : ℝ) * (p - (34 / 21 : ℝ) * q) ^ 2 + (1 / 714 : ℝ) * p ^ 2 := by ring
  have hnn : 0 ≤ (21 / 34 : ℝ) * (p - (34 / 21 : ℝ) * q) ^ 2 + (1 / 714 : ℝ) * p ^ 2 := by
    positivity
  linarith

/-- **Fibonacci Core-to-Collar Shift Transport Inequality on `(0, L)`**:
for any `BddSupp A h C` and any `0 ≤ a ≤ x` with `2 * a + x ≤ L`,
`(8 / 21) * ((∫ v in Ioc x (a + x), h v ^ 2) + ∫ u in Ioc (L - x - a) (L - x), h u ^ 2) - (13 / 21) * collarMass h L a ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`. -/
theorem core_slice_sub_collarMass_fibonacci_le_interior_jump_sq {A : Set ℝ} {h : ℝ → ℝ}
    {C L a x : ℝ} (hh : BddSupp A h C) (_ha0 : 0 ≤ a) (_hax : a ≤ x) (h2axL : 2 * a + x ≤ L) :
    (8 / 21 : ℝ) *
        ((∫ v in Ioc x (a + x), h v ^ 2) + ∫ u in Ioc (L - x - a) (L - x), h u ^ 2) -
      (13 / 21 : ℝ) * collarMass h L a ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  have hleft_pt : ∀ u : ℝ,
      (8 / 21 : ℝ) * h (u + x) ^ 2 - (13 / 21 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := eight_twenty_firsts_sq_sub_thirteen_twenty_firsts_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have hleft_int : (8 / 21 : ℝ) * (∫ v in Ioc x (a + x), h v ^ 2) -
      (13 / 21 : ℝ) * (∫ u in Iic a, h u ^ 2) ≤
      ∫ u in Ioc 0 a, (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc 0 a)
      ((hshift.const_mul (8 / 21)).integrableOn.sub (hsq.const_mul (13 / 21)).integrableOn)
      hjump.integrableOn hleft_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (8 / 21)).integrableOn (hsq.const_mul (13 / 21)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 a x, zero_add] at h1
    have hIoc_le_Iic : (∫ u in Ioc 0 a, h u ^ 2) ≤ ∫ u in Iic a, h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Iic_self)
    linarith
  have hright_pt : ∀ u : ℝ,
      (8 / 21 : ℝ) * h u ^ 2 - (13 / 21 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => eight_twenty_firsts_sq_sub_thirteen_twenty_firsts_sq_le_sub_sq (h u) (h (u + x))
  have hright_int : (8 / 21 : ℝ) * (∫ u in Ioc (L - x - a) (L - x), h u ^ 2) -
      (13 / 21 : ℝ) * (∫ v in Ioi (L - a), h v ^ 2) ≤
      ∫ u in Ioc (L - x - a) (L - x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - x - a) (L - x))
      ((hsq.const_mul (8 / 21)).integrableOn.sub (hshift.const_mul (13 / 21)).integrableOn)
      hjump.integrableOn hright_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (8 / 21)).integrableOn (hshift.const_mul (13 / 21)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - x - a) (L - x) x,
      show L - x - a + x = L - a by ring, show L - x + x = L by ring] at h1
    have hIoc_le_Ioi : (∫ v in Ioc (L - a) L, h v ^ 2) ≤ ∫ v in Ioi (L - a), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Ioi_self)
    linarith
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

/-- **Sharpened Universal Quarter-Window Coercivity (`(8 / 21) * ∫ h² ≤ D_h(x)` for all `x ≥ L / 4`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and **every shift `x ≥ L / 4`**,
`(8 / 21) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem eight_twenty_firsts_mul_integral_sq_le_integral_jump_sq_of_quarter_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 4 ≤ x) :
    (8 / 21 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  rcases le_or_gt x (L / 2) with hle | hgt
  · set a := min x ((L - x) / 2)
    have ha0 : 0 ≤ a := le_min (by linarith) (by linarith)
    have hax : a ≤ x := min_le_left _ _
    have h2axL : 2 * a + x ≤ L := by
      have : a ≤ (L - x) / 2 := min_le_right _ _
      linarith
    have hx0 : 0 ≤ x := by linarith
    have hcol_int := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
    have hcol_mono : collarMass h L a ≤ collarMass h L x := collarMass_mono hh hax
    have hfib := core_slice_sub_collarMass_fibonacci_le_interior_jump_sq hh ha0 hax h2axL
    have hcov := coreMass_le_core_slice_of_quarter_le hh hx hle
    have hcons := collarMass_add_coreMass_eq hh hle
    linarith
  · have hhalf := integral_sq_le_integral_jump_sq_of_half_le hh hsupp hL0 hgt.le
    have hE0 : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith

/-- Integrating the sharpened `(8 / 21)` quarter-window coercivity against `-screwRegularKernel x ≥ 0`
over `Ioo a c` (`L / 4 ≤ a ≤ c ≤ screwSignThreshold`) yields
`(4 / 21) * (Φ(a) - Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo a c} (-screwRegularKernel x) D_h(x) dx`. -/
theorem four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L a c : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL : 0 < L) (ha : L / 4 ≤ a) (hac : a ≤ c) (hct : c ≤ screwSignThreshold) :
    (4 / 21 : ℝ) * (levyCoshPotential a - levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo a c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le ha0 hac
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc a c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le ha0 hx.1).neg
  have hI_K : IntegrableOn (fun x => -screwRegularKernel x) (Ioo a c) :=
    hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hh
  have hI_jump : IntegrableOn
      (fun x : ℝ => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) (Ioo a c) := by
    refine (hI_K.mul_const (4 * ∫ u, h u ^ 2)).mono'
      (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans ha0 hx.1)
        (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hval : (∫ x in Ioo a c, (-screwRegularKernel x) * ((8 / 21 : ℝ) * ∫ u, h u ^ 2)) =
      (4 / 21 : ℝ) * (levyCoshPotential a - levyCoshPotential c) * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hac]
    have hFTC := integral_two_mul_screwRegularKernel ha0 hc0
    have hneg : (∫ x in a..c, -screwRegularKernel x) =
        -(1 / 2) * ∫ x in a..c, 2 * screwRegularKernel x := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => by ring
    rw [hneg, hFTC]
    ring
  rw [← hval]
  refine setIntegral_mono_on (hI_K.mul_const _) hI_jump measurableSet_Ioo fun x hx => ?_
  have hK0 : 0 ≤ -screwRegularKernel x :=
    neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans ha0 hx.1)
      (hx.2.le.trans hct))
  exact mul_le_mul_of_nonneg_left
    (eight_twenty_firsts_mul_integral_sq_le_integral_jump_sq_of_quarter_le
      hh hsupp hL.le (ha.trans hx.1.le))
    hK0

/-! ## Section 2: Disjoint Midpoint-Split Two-Step Coercivity on `[L / 6, L / 4]` (`(7 / 36) * ∫ h² ≤ D_h(x)`) -/

/-- First-step quadratic transport inequality `(4 / 9) * p² - (4 / 5) * q² ≤ (p - q)²`,
proved via `(p - q)² - ((4 / 9) * p² - (4 / 5) * q²) = (5 / 9) * (p - (9 / 5) * q)²`. -/
theorem four_ninths_sq_sub_four_fifths_sq_le_sub_sq (p q : ℝ) :
    (4 / 9 : ℝ) * p ^ 2 - (4 / 5 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  have hid : (p - q) ^ 2 - ((4 / 9 : ℝ) * p ^ 2 - (4 / 5 : ℝ) * q ^ 2) =
      (5 / 9 : ℝ) * (p - (9 / 5 : ℝ) * q) ^ 2 := by ring
  have hnn : 0 ≤ (5 / 9 : ℝ) * (p - (9 / 5 : ℝ) * q) ^ 2 := by positivity
  linarith

/-- Second-step quadratic transport inequality `(1 / 5) * p² - (1 / 4) * q² ≤ (p - q)²`,
proved via `(p - q)² - ((1 / 5) * p² - (1 / 4) * q²) = (4 / 5) * (p - (5 / 4) * q)²`. -/
theorem one_fifth_sq_sub_quarter_sq_le_sub_sq (p q : ℝ) :
    (1 / 5 : ℝ) * p ^ 2 - (1 / 4 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  have hid : (p - q) ^ 2 - ((1 / 5 : ℝ) * p ^ 2 - (1 / 4 : ℝ) * q ^ 2) =
      (4 / 5 : ℝ) * (p - (5 / 4 : ℝ) * q) ^ 2 := by ring
  have hnn : 0 ≤ (4 / 5 : ℝ) * (p - (5 / 4 : ℝ) * q) ^ 2 := by positivity
  linarith

/-- **Disjoint Midpoint-Split Two-Step Transport on `[L / 6, L / 4]`**:
for any `BddSupp A h C` and `x ∈ [L / 6, L / 4]` (`0 ≤ L`), the four jump intervals
`Ioc 0 x`, `Ioc x (L / 2 - x)`, `Ioc (L / 2) (L - 2 * x)`, and `Ioc (L - 2 * x) (L - x)`
are pairwise disjoint inside `Ioc 0 (L - x)`, yielding:
`(7 / 36) * ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2)`
`+ (1 / 5) * ((∫ v in Ioc (2 * x) (L / 2), h v ^ 2) + ∫ u in Ioc (L / 2) (L - 2 * x), h u ^ 2)`
`- (4 / 5) * collarMass h L x ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`. -/
theorem disjoint_two_step_slices_le_interior_jump_sq {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hL0 : 0 ≤ L) (hx6 : L / 6 ≤ x) (hx4 : x ≤ L / 4) :
    (7 / 36 : ℝ) *
        ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) +
      (1 / 5 : ℝ) *
        ((∫ v in Ioc (2 * x) (L / 2), h v ^ 2) + ∫ u in Ioc (L / 2) (L - 2 * x), h u ^ 2) -
      (4 / 5 : ℝ) * collarMass h L x ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  -- Step 1 (outer jump intervals `Ioc 0 x` and `Ioc (L - 2x) (L - x)`)
  have h1_left_pt : ∀ u : ℝ,
      (4 / 9 : ℝ) * h (u + x) ^ 2 - (4 / 5 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := four_ninths_sq_sub_four_fifths_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h1_left : (4 / 9 : ℝ) * (∫ v in Ioc x (2 * x), h v ^ 2) -
      (4 / 5 : ℝ) * (∫ u in Iic x, h u ^ 2) ≤
      ∫ u in Ioc 0 x, (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc 0 x)
      ((hshift.const_mul (4 / 9)).integrableOn.sub (hsq.const_mul (4 / 5)).integrableOn)
      hjump.integrableOn h1_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (4 / 9)).integrableOn (hsq.const_mul (4 / 5)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 x x, zero_add,
      show x + x = 2 * x by ring] at h1
    have hIoc_le_Iic : (∫ u in Ioc 0 x, h u ^ 2) ≤ ∫ u in Iic x, h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Iic_self)
    linarith
  have h1_right_pt : ∀ u : ℝ,
      (4 / 9 : ℝ) * h u ^ 2 - (4 / 5 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => four_ninths_sq_sub_four_fifths_sq_le_sub_sq (h u) (h (u + x))
  have h1_right : (4 / 9 : ℝ) * (∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) -
      (4 / 5 : ℝ) * (∫ v in Ioi (L - x), h v ^ 2) ≤
      ∫ u in Ioc (L - 2 * x) (L - x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - 2 * x) (L - x))
      ((hsq.const_mul (4 / 9)).integrableOn.sub (hshift.const_mul (4 / 5)).integrableOn)
      hjump.integrableOn h1_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (4 / 9)).integrableOn (hshift.const_mul (4 / 5)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - 2 * x) (L - x) x,
      show L - 2 * x + x = L - x by ring, show L - x + x = L by ring] at h1
    have hIoc_le_Ioi : (∫ v in Ioc (L - x) L, h v ^ 2) ≤ ∫ v in Ioi (L - x), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Ioi_self)
    linarith
  -- Step 2 (inner jump intervals `Ioc x (L / 2 - x)` and `Ioc (L / 2) (L - 2x)`)
  have h2_left_pt : ∀ u : ℝ,
      (1 / 5 : ℝ) * h (u + x) ^ 2 - (1 / 4 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := one_fifth_sq_sub_quarter_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h2_left : (1 / 5 : ℝ) * (∫ v in Ioc (2 * x) (L / 2), h v ^ 2) -
      (1 / 4 : ℝ) * (∫ u in Ioc x (2 * x), h u ^ 2) ≤
      ∫ u in Ioc x (L / 2 - x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc x (L / 2 - x))
      ((hshift.const_mul (1 / 5)).integrableOn.sub (hsq.const_mul (1 / 4)).integrableOn)
      hjump.integrableOn h2_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (1 / 5)).integrableOn (hsq.const_mul (1 / 4)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) x (L / 2 - x) x,
      show x + x = 2 * x by ring, show L / 2 - x + x = L / 2 by ring] at h1
    have hsub_1L : Ioc x (L / 2 - x) ⊆ Ioc x (2 * x) :=
      Ioc_subset_Ioc_right (by linarith)
    have hmono_1L : (∫ u in Ioc x (L / 2 - x), h u ^ 2) ≤ ∫ u in Ioc x (2 * x), h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall hsub_1L)
    linarith
  have h2_right_pt : ∀ u : ℝ,
      (1 / 5 : ℝ) * h u ^ 2 - (1 / 4 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => one_fifth_sq_sub_quarter_sq_le_sub_sq (h u) (h (u + x))
  have h2_right : (1 / 5 : ℝ) * (∫ u in Ioc (L / 2) (L - 2 * x), h u ^ 2) -
      (1 / 4 : ℝ) * (∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2) ≤
      ∫ u in Ioc (L / 2) (L - 2 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L / 2) (L - 2 * x))
      ((hsq.const_mul (1 / 5)).integrableOn.sub (hshift.const_mul (1 / 4)).integrableOn)
      hjump.integrableOn h2_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (1 / 5)).integrableOn (hshift.const_mul (1 / 4)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L / 2) (L - 2 * x) x,
      show L - 2 * x + x = L - x by ring] at h1
    have hsub_1R : Ioc (L / 2 + x) (L - x) ⊆ Ioc (L - 2 * x) (L - x) :=
      Ioc_subset_Ioc_left (by linarith)
    have hmono_1R : (∫ v in Ioc (L / 2 + x) (L - x), h v ^ 2) ≤
        ∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall hsub_1R)
    linarith
  -- Disjoint union of the two inner intervals inside `Ioc x (L - 2 * x)`
  have hdisj_in : Disjoint (Ioc x (L / 2 - x)) (Ioc (L / 2) (L - 2 * x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hsub_in : Ioc x (L / 2 - x) ∪ Ioc (L / 2) (L - 2 * x) ⊆ Ioc x (L - 2 * x) := by
    intro u hu
    rcases hu with hu1 | hu2
    · exact ⟨hu1.1, by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], hu2.2⟩
  have hunion_in : (∫ u in Ioc x (L / 2 - x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (L / 2) (L - 2 * x), (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc x (L - 2 * x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj_in measurableSet_Ioc hjump.integrableOn hjump.integrableOn]
    exact setIntegral_mono_set hjump.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall hsub_in)
  -- Disjoint union of `Ioc 0 x`, `Ioc x (L - 2 * x)`, and `Ioc (L - 2 * x) (L - x)` inside `Ioc 0 (L - x)`
  have hdisj_01 : Disjoint (Ioc 0 x) (Ioc x (L - 2 * x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hdisj_012 : Disjoint (Ioc 0 x ∪ Ioc x (L - 2 * x)) (Ioc (L - 2 * x) (L - x)) := by
    rw [disjoint_union_left]
    exact ⟨disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1],
      disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]⟩
  have hsub_all : (Ioc 0 x ∪ Ioc x (L - 2 * x)) ∪ Ioc (L - 2 * x) (L - x) ⊆ Ioc 0 (L - x) := by
    intro u hu
    rcases hu with (hu0 | hu1) | hu2
    · exact ⟨hu0.1, by linarith [hu0.2]⟩
    · exact ⟨by linarith [hu1.1], by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], hu2.2⟩
  have hunion_all : (∫ u in Ioc 0 x, (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc x (L - 2 * x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (L - 2 * x) (L - x), (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj_01 measurableSet_Ioc hjump.integrableOn hjump.integrableOn,
      ← setIntegral_union hdisj_012 measurableSet_Ioc
        (hjump.integrableOn.mono_set (subset_univ _)) hjump.integrableOn]
    exact setIntegral_mono_set hjump.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall hsub_all)
  unfold collarMass
  linarith

/-- For any `BddSupp A h C` and `x ≤ L / 4`, the core `Ioc x (L - x)` is covered by the four slices
`Ioc x (2 * x)`, `Ioc (2 * x) (L / 2)`, `Ioc (L / 2) (L - 2 * x)`, and `Ioc (L - 2 * x) (L - x)`. -/
theorem coreMass_le_midpoint_split_layers {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (_hx4 : x ≤ L / 4) :
    coreMass h L x ≤
      ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) +
        ((∫ v in Ioc (2 * x) (L / 2), h v ^ 2) + ∫ u in Ioc (L / 2) (L - 2 * x), h u ^ 2) := by
  unfold coreMass
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have h1 : (∫ u in Ioc x (L - x), h u ^ 2) ≤
      (∫ u in Ioc x (L - 2 * x), h u ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2 := by
    refine setIntegral_le_add_of_subset_union hsq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (L - 2 * x) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨hgt, hu.2⟩
  have h2 : (∫ u in Ioc x (L - 2 * x), h u ^ 2) ≤
      (∫ u in Ioc x (2 * x), h u ^ 2) + ∫ u in Ioc (2 * x) (L - 2 * x), h u ^ 2 := by
    refine setIntegral_le_add_of_subset_union hsq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (2 * x) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨hgt, hu.2⟩
  have h3 : (∫ u in Ioc (2 * x) (L - 2 * x), h u ^ 2) ≤
      (∫ u in Ioc (2 * x) (L / 2), h u ^ 2) + ∫ u in Ioc (L / 2) (L - 2 * x), h u ^ 2 := by
    refine setIntegral_le_add_of_subset_union hsq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (L / 2) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨hgt, hu.2⟩
  linarith

/-- **Sharpened Universal Sixth-Window Coercivity (`(7 / 36) * ∫ h² ≤ D_h(x)` for all `x ≥ L / 6`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and **every shift `x ≥ L / 6`**,
`(7 / 36) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem seven_thirty_sixths_mul_integral_sq_le_integral_jump_sq_of_sixth_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 6 ≤ x) :
    (7 / 36 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  rcases le_or_gt x (L / 4) with hle | hgt
  · have hx0 : 0 ≤ x := by linarith
    have hxL2 : x ≤ L / 2 := by linarith
    have hcol_int := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
    have htwo := disjoint_two_step_slices_le_interior_jump_sq hh hL0 hx hle
    have hcov := coreMass_le_midpoint_split_layers hh hle
    have hcons := collarMass_add_coreMass_eq hh hxL2
    have hcol_nn := collarMass_nonneg h L x
    have hlay2_nn : 0 ≤ (∫ v in Ioc (2 * x) (L / 2), h v ^ 2) +
        ∫ u in Ioc (L / 2) (L - 2 * x), h u ^ 2 :=
      add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    linarith
  · have h4 := eight_twenty_firsts_mul_integral_sq_le_integral_jump_sq_of_quarter_le
      hh hsupp hL0 hgt.le
    have hE0 : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith

/-- Integrating `(7 / 36)` coercivity against `-screwRegularKernel x ≥ 0` over `Ioo a c`
(`L / 6 ≤ a ≤ c ≤ screwSignThreshold`) yields
`(7 / 72) * (Φ(a) - Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo a c} (-screwRegularKernel x) D_h(x) dx`. -/
theorem seven_seventy_seconds_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L a c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL : 0 < L) (ha : L / 6 ≤ a) (hac : a ≤ c)
    (hct : c ≤ screwSignThreshold) :
    (7 / 72 : ℝ) * (levyCoshPotential a - levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo a c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le ha0 hac
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc a c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le ha0 hx.1).neg
  have hI_K : IntegrableOn (fun x => -screwRegularKernel x) (Ioo a c) :=
    hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hh
  have hI_jump : IntegrableOn
      (fun x : ℝ => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) (Ioo a c) := by
    refine (hI_K.mul_const (4 * ∫ u, h u ^ 2)).mono'
      (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans ha0 hx.1)
        (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hval : (∫ x in Ioo a c, (-screwRegularKernel x) * ((7 / 36 : ℝ) * ∫ u, h u ^ 2)) =
      (7 / 72 : ℝ) * (levyCoshPotential a - levyCoshPotential c) * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hac]
    have hFTC := integral_two_mul_screwRegularKernel ha0 hc0
    have hneg : (∫ x in a..c, -screwRegularKernel x) =
        -(1 / 2) * ∫ x in a..c, 2 * screwRegularKernel x := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => by ring
    rw [hneg, hFTC]
    ring
  rw [← hval]
  refine setIntegral_mono_on (hI_K.mul_const _) hI_jump measurableSet_Ioo fun x hx => ?_
  have hK0 : 0 ≤ -screwRegularKernel x :=
    neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans ha0 hx.1)
      (hx.2.le.trans hct))
  exact mul_le_mul_of_nonneg_left
    (seven_thirty_sixths_mul_integral_sq_le_integral_jump_sq_of_sixth_le
      hh hsupp hL.le (ha.trans hx.1.le))
    hK0

/-- **Fibonacci-Staircase Crossover Inequality on `(0, L)` (`L / 4 ≤ c ≤ screwSignThreshold`)**:
combining `(7 / 36)` coercivity on `(L / 6, L / 4)` with `(8 / 21)` coercivity on `(L / 4, c)` yields
`(A(0) + (7 / 72) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (17 / 21) * Φ(c)) * ∫ f² + ... ≤ W_∞(f ⋆ f̃)`. -/
theorem sixth_add_quarter_fibonacci_levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L)
    (hL4c : L / 4 ≤ c) (hct : c ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (7 / 72) * levyCoshPotential (L / 6) +
        (47 / 504) * levyCoshPotential (L / 4) +
        (17 / 21) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL6 : 0 < L / 6 := by linarith
  have hL64 : L / 6 ≤ L / 4 := by linarith
  have hL6c : L / 6 ≤ c := hL64.trans hL4c
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL6 hL6c hct
  have h1 := seven_seventy_seconds_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL le_rfl hL64 (hL4c.trans hct)
  have h2 := four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL le_rfl hL4c hct
  have hD0 : ∀ x, 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 6) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL6 hx.1).neg
  have hI_K : IntegrableOn (fun x => -screwRegularKernel x) (Ioo (L / 6) c) :=
    hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hB
  have hI_jump : IntegrableOn
      (fun x : ℝ => (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2) (Ioo (L / 6) c) := by
    refine (hI_K.mul_const (4 * ∫ u, f u ^ 2)).mono'
      (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans hL6 hx.1)
        (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hB x) hK0
  have hdisj : Disjoint (Ioo (L / 6) (L / 4)) (Ioo (L / 4) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2.le hx2.1
  have hsub : Ioo (L / 6) (L / 4) ∪ Ioo (L / 4) c ⊆ Ioo (L / 6) c := fun x hx => by
    rcases hx with hx1 | hx2
    · exact ⟨hx1.1, lt_of_lt_of_le hx1.2 hL4c⟩
    · exact ⟨lt_of_le_of_lt hL64 hx2.1, hx2.2⟩
  have hunion : (∫ x in Ioo (L / 6) (L / 4),
        (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2) +
      (∫ x in Ioo (L / 4) c,
        (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2) ≤
      ∫ x in Ioo (L / 6) c,
        (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj measurableSet_Ioo
      (hI_jump.mono_set (Ioo_subset_Ioo_right hL4c))
      (hI_jump.mono_set (Ioo_subset_Ioo_left hL64))]
    exact setIntegral_mono_set hI_jump
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx =>
        mul_nonneg (neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
          (lt_trans hL6 hx.1) (hx.2.le.trans hct))) (hD0 x)))
      (Eventually.of_forall hsub)
  linarith

/-- **Fibonacci-Staircase Plastic Floor on `(0, log 2)`**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 (Real.log 2)`,
`(A(0) + (7 / 72) * Φ((log 2)/6) + (47 / 504) * Φ((log 2)/4) + (17 / 21) * Φ(t_*)) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem fibonacci_staircase_log_two_plastic_floor_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hsupp : ∀ u ∉ Ioo 0 (Real.log 2), f u = 0) :
    (EF.gammaBracket 0 + (7 / 72) * levyCoshPotential (Real.log 2 / 6) +
        (47 / 504) * levyCoshPotential (Real.log 2 / 4) +
        (17 / 21) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL4t : Real.log 2 / 4 ≤ screwSignThreshold := by
    linarith [Real.log_two_lt_d9, screwSignThreshold_gt]
  have hmain := sixth_add_quarter_fibonacci_levyCosh_crossover_le_weilArchRe
    hf hfc hL hL4t le_rfl hsupp
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-! ## Section 3: Sharpened Five-Point Potential and Unconditional Positivity on `(0, 9 / 25)` -/

/-- **Sharpened Inner Reflected Shell Coercivity (`(L / 4, L / 2)` paired with `(L / 2, b)`, `b ≤ 3 * L / 4`)**:
retaining the `(8 / 21)` coercivity on the positive kernel excess `(-K(L - y)) - (-K(y)) ≥ 0` yields
`((4 / 21) * Φ(L / 4) + (13 / 21) * Φ(L / 2) - (17 / 21) * Φ(b)) * ∫ h² ≤ ∫_{Ioo (L / 4) b} (-K(x)) D_h(x) dx`. -/
theorem sharpened_inner_shell_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (hL2b : L / 2 ≤ b)
    (hb34 : b ≤ 3 * L / 4) (hbt : b ≤ screwSignThreshold) :
    ((4 / 21 : ℝ) * levyCoshPotential (L / 4) +
        (13 / 21 : ℝ) * levyCoshPotential (L / 2) -
        (17 / 21 : ℝ) * levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 4) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL4 : 0 < L / 4 := by linarith
  have hL2 : 0 < L / 2 := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le hL2 hL2b
  have hbL : b < L := by linarith
  have hLb0 : 0 < L - b := by linarith
  have hL4_Lb : L / 4 ≤ L - b := by linarith
  have hLb_L2 : L - b ≤ L / 2 := by linarith
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K_all : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 4) b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL4 hx.1).neg
  have hIF_all : IntegrableOn F (Ioo (L / 4) b) := by
    refine ((hcont_K_all.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans hL4 hx.1)
        (hx.2.le.trans hbt))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  -- Part 1: on `Ioo (L / 4) (L - b)`
  have hpart1 : (4 / 21 : ℝ) * (levyCoshPotential (L / 4) - levyCoshPotential (L - b)) *
      (∫ u, h u ^ 2) ≤ ∫ x in Ioo (L / 4) (L - b), F x :=
    four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo hh hsupp hL le_rfl hL4_Lb
      (by linarith)
  -- Part 2: on `Ioo (L - b) b`, retaining `(8 / 21)` on the reflected kernel excess
  have hIF_mid : IntegrableOn F (Ioo (L - b) b) :=
    hIF_all.mono_set (Ioo_subset_Ioo hL4_Lb le_rfl)
  have hIF_left : IntegrableOn F (Ioo (L - b) (L / 2)) :=
    hIF_mid.mono_set (Ioo_subset_Ioo_right hL2b)
  have hIF_right : IntegrableOn F (Ioo (L / 2) b) :=
    hIF_mid.mono_set (Ioo_subset_Ioo_left hLb_L2)
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
  have hdisj_mid : Disjoint (Ioo (L - b) (L / 2)) (Ioo (L / 2) b) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2.le hx2.1
  have hsub_mid : Ioo (L - b) (L / 2) ∪ Ioo (L / 2) b ⊆ Ioo (L - b) b := fun x hx => by
    rcases hx with hx1 | hx2
    · exact ⟨hx1.1, lt_of_lt_of_le hx1.2 hL2b⟩
    · exact ⟨lt_of_le_of_lt hLb_L2 hx2.1, hx2.2⟩
  have hsum_ge : (∫ y in Ioo (L / 2) b, F (L - y)) + (∫ y in Ioo (L / 2) b, F y) ≤
      ∫ x in Ioo (L - b) b, F x := by
    have hrefl_eq : (∫ y in Ioo (L / 2) b, F (L - y)) = ∫ x in Ioo (L - b) (L / 2), F x := by
      rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hL2b, ← intervalIntegral.integral_of_le hLb_L2,
        intervalIntegral.integral_comp_sub_left F, show L - (L / 2) = L / 2 by ring]
    rw [hrefl_eq, ← setIntegral_union hdisj_mid measurableSet_Ioo hIF_left hIF_right]
    exact setIntegral_mono_set hIF_mid
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx =>
        mul_nonneg (neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
          (lt_trans hLb0 hx.1) (hx.2.le.trans hbt))) (hD0 x)))
      (Eventually.of_forall hsub_mid)
  have hcont_K : ContinuousOn (fun y => -screwRegularKernel y) (Icc (L / 2) b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun y hy => lt_of_lt_of_le hL2 hy.1).neg
  have hcont_K_refl : ContinuousOn (fun y => -screwRegularKernel (L - y)) (Icc (L / 2) b) := by
    have hcont_Lb : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L - b) b) :=
      (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
        fun x hx => lt_of_lt_of_le hLb0 hx.1).neg
    exact hcont_Lb.comp (continuousOn_const.sub continuousOn_id)
      fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hIK : IntegrableOn (fun y => -screwRegularKernel y) (Ioo (L / 2) b) :=
    hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hIK_refl : IntegrableOn (fun y => -screwRegularKernel (L - y)) (Ioo (L / 2) b) :=
    hcont_K_refl.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hI_low : IntegrableOn
      (fun y => ((8 / 21 : ℝ) * (-screwRegularKernel (L - y)) +
        (34 / 21 : ℝ) * (-screwRegularKernel y)) * ∫ u, h u ^ 2)
      (Ioo (L / 2) b) :=
    ((hIK_refl.const_mul (8 / 21)).add (hIK.const_mul (34 / 21))).mul_const _
  have hval_low : (∫ y in Ioo (L / 2) b,
      ((8 / 21 : ℝ) * (-screwRegularKernel (L - y)) +
        (34 / 21 : ℝ) * (-screwRegularKernel y)) * ∫ u, h u ^ 2) =
      ((4 / 21 : ℝ) * (levyCoshPotential (L - b) - levyCoshPotential (L / 2)) +
        (17 / 21 : ℝ) * (levyCoshPotential (L / 2) - levyCoshPotential b)) * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, integral_add (hIK_refl.const_mul _) (hIK.const_mul _),
      integral_const_mul, integral_const_mul,
      setIntegral_Ioo_reflect_neg_screwRegularKernel hL hL2b hbL,
      setIntegral_Ioo_neg_screwRegularKernel hL2 hL2b]
    ring
  have hpart2 : ((4 / 21 : ℝ) * (levyCoshPotential (L - b) - levyCoshPotential (L / 2)) +
      (17 / 21 : ℝ) * (levyCoshPotential (L / 2) - levyCoshPotential b)) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L - b) b, F x := by
    refine le_trans ?_ hsum_ge
    rw [← integral_add hIF_refl hIF_right, ← hval_low]
    refine setIntegral_mono_on hI_low (hIF_refl.add hIF_right) measurableSet_Ioo fun y hy => ?_
    dsimp only [F, Pi.add_apply]
    have hy0 : 0 < y := lt_trans hL2 hy.1
    have hLy0 : 0 < L - y := by linarith [hy.2]
    have hLy_le : L - y ≤ y := by linarith [hy.1]
    have hyt : y ≤ screwSignThreshold := hy.2.le.trans hbt
    have hKy0 : 0 ≤ -screwRegularKernel y :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold hy0 hyt)
    have hK_diff : 0 ≤ (-screwRegularKernel (L - y)) - (-screwRegularKernel y) :=
      sub_nonneg.mpr (neg_le_neg (monotoneOn_screwRegularKernel hLy0 hy0 hLy_le))
    have hsum := two_mul_integral_sq_le_integral_jump_sq_add_sub hh hsupp hy0.le
      (le_trans hy.2.le hbL.le)
    have hqtr := eight_twenty_firsts_mul_integral_sq_le_integral_jump_sq_of_quarter_le
      hh hsupp hL.le (show L / 4 ≤ L - y by linarith [hy.2, hb34])
    have hstep1 : (-screwRegularKernel y) * (2 * ∫ u, h u ^ 2) ≤
        (-screwRegularKernel y) *
          ((∫ u, (h u - h (u + y)) ^ 2) + ∫ u, (h u - h (u + (L - y))) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hKy0
    have hstep2 : ((-screwRegularKernel (L - y)) - (-screwRegularKernel y)) *
        ((8 / 21 : ℝ) * ∫ u, h u ^ 2) ≤
        ((-screwRegularKernel (L - y)) - (-screwRegularKernel y)) *
          ∫ u, (h u - h (u + (L - y))) ^ 2 :=
      mul_le_mul_of_nonneg_left hqtr hK_diff
    linarith
  have hdisj : Disjoint (Ioo (L / 4) (L - b)) (Ioo (L - b) b) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2.le hx2.1
  have hsub : Ioo (L / 4) (L - b) ∪ Ioo (L - b) b ⊆ Ioo (L / 4) b := fun x hx => by
    rcases hx with hx1 | hx2
    · exact ⟨hx1.1, lt_of_lt_of_le hx1.2 (by linarith)⟩
    · exact ⟨lt_of_le_of_lt hL4_Lb hx2.1, hx2.2⟩
  have hunion : (∫ x in Ioo (L / 4) (L - b), F x) + (∫ x in Ioo (L - b) b, F x) ≤
      ∫ x in Ioo (L / 4) b, F x := by
    rw [← setIntegral_union hdisj measurableSet_Ioo
      (hIF_all.mono_set (Ioo_subset_Ioo_right (by linarith))) hIF_mid]
    exact setIntegral_mono_set hIF_all
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx =>
        mul_nonneg (neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
          (lt_trans hL4 hx.1) (hx.2.le.trans hbt))) (hD0 x)))
      (Eventually.of_forall hsub)
  linarith

/-- **Sharpened Outer Reflected Shell Coercivity (`(L - c, L / 4)` paired with `(3 * L / 4, c)`, `c ≤ 5 * L / 6`)**:
retaining the `(7 / 36)` coercivity on `(L - c, L / 4) ⊆ (L / 6, L / 4)` yields
`((7 / 72) * (Φ(L - c) - Φ(L / 4)) + (65 / 72) * (Φ(3 * L / 4) - Φ(c))) * ∫ h² ≤ ∫_{Ioo (L - c) (L / 4)} + ∫_{Ioo (3 * L / 4) c}`. -/
theorem sharpened_outer_shell_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (h34c : 3 * L / 4 ≤ c)
    (hc56 : c ≤ 5 * L / 6) (hct : c ≤ screwSignThreshold) :
    ((7 / 72 : ℝ) * (levyCoshPotential (L - c) - levyCoshPotential (L / 4)) +
        (65 / 72 : ℝ) * (levyCoshPotential (3 * L / 4) - levyCoshPotential c)) *
        (∫ u, h u ^ 2) ≤
      (∫ x in Ioo (L - c) (L / 4), (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ y in Ioo (3 * L / 4) c, (-screwRegularKernel y) * ∫ u, (h u - h (u + y)) ^ 2 := by
  have hL6 : 0 < L / 6 := by linarith
  have h34_pos : 0 < 3 * L / 4 := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le h34_pos h34c
  have hcL : c < L := by linarith
  have hLc0 : 0 < L - c := by linarith
  have hLc_L4 : L - c ≤ L / 4 := by linarith
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_left : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L - c) (L / 4)) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hLc0 hx.1).neg
  have hIF_left : IntegrableOn F (Ioo (L - c) (L / 4)) := by
    refine ((hcont_left.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans hLc0 hx.1)
        (by linarith [hx.2, h34c, hct]))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hcont_right : ContinuousOn (fun y => -screwRegularKernel y) (Icc (3 * L / 4) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun y hy => lt_of_lt_of_le h34_pos hy.1).neg
  have hIF_right : IntegrableOn F (Ioo (3 * L / 4) c) := by
    refine ((hcont_right.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun y hy => ?_))
    have hK0 : 0 ≤ -screwRegularKernel y :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans h34_pos hy.1)
        (hy.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 y))]
    exact mul_le_mul_of_nonneg_left (jump_le hh y) hK0
  have hIF_refl : IntegrableOn (fun y => F (L - y)) (Ioo (3 * L / 4) c) := by
    have hpre : (fun y : ℝ => -y + L) ⁻¹' Ioo (L - c) (L / 4) = Ioo (3 * L / 4) c := by
      ext y; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith
    have h1 : Integrable (fun y : ℝ => (Ioo (L - c) (L / 4)).indicator F (-y + L)) :=
      (((integrable_indicator_iff measurableSet_Ioo).mpr hIF_left).comp_add_right L).comp_neg
    rw [← integrable_indicator_iff measurableSet_Ioo]
    refine h1.congr (ae_of_all _ fun y => ?_)
    dsimp only
    rw [← Set.indicator_comp_right (fun y : ℝ => -y + L), hpre]
    exact congrArg (fun g => (Ioo (3 * L / 4) c).indicator g y) (funext fun z => congrArg F (by ring))
  have hrefl_eq : (∫ y in Ioo (3 * L / 4) c, F (L - y)) = ∫ x in Ioo (L - c) (L / 4), F x := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le h34c, ← intervalIntegral.integral_of_le hLc_L4,
      intervalIntegral.integral_comp_sub_left F, show L - (3 * L / 4) = L / 4 by ring]
  have hcont_K_refl : ContinuousOn (fun y => -screwRegularKernel (L - y)) (Icc (3 * L / 4) c) :=
    hcont_left.comp (continuousOn_const.sub continuousOn_id)
      fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hIK : IntegrableOn (fun y => -screwRegularKernel y) (Ioo (3 * L / 4) c) :=
    hcont_right.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hIK_refl : IntegrableOn (fun y => -screwRegularKernel (L - y)) (Ioo (3 * L / 4) c) :=
    hcont_K_refl.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hI_low : IntegrableOn
      (fun y => ((7 / 36 : ℝ) * (-screwRegularKernel (L - y)) +
        (65 / 36 : ℝ) * (-screwRegularKernel y)) * ∫ u, h u ^ 2)
      (Ioo (3 * L / 4) c) :=
    ((hIK_refl.const_mul (7 / 36)).add (hIK.const_mul (65 / 36))).mul_const _
  have hval : (∫ y in Ioo (3 * L / 4) c,
      ((7 / 36 : ℝ) * (-screwRegularKernel (L - y)) +
        (65 / 36 : ℝ) * (-screwRegularKernel y)) * ∫ u, h u ^ 2) =
      ((7 / 72 : ℝ) * (levyCoshPotential (L - c) - levyCoshPotential (L / 4)) +
        (65 / 72 : ℝ) * (levyCoshPotential (3 * L / 4) - levyCoshPotential c)) *
        ∫ u, h u ^ 2 := by
    rw [integral_mul_const, integral_add (hIK_refl.const_mul _) (hIK.const_mul _),
      integral_const_mul, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le h34c,
      intervalIntegral.integral_comp_sub_left (fun x => -screwRegularKernel x),
      show L - (3 * L / 4) = L / 4 by ring,
      intervalIntegral.integral_of_le hLc_L4, integral_Ioc_eq_integral_Ioo,
      setIntegral_Ioo_neg_screwRegularKernel hLc0 hLc_L4,
      setIntegral_Ioo_neg_screwRegularKernel h34_pos h34c]
    ring
  rw [← hrefl_eq, ← integral_add hIF_refl hIF_right, ← hval]
  refine setIntegral_mono_on hI_low (hIF_refl.add hIF_right) measurableSet_Ioo fun y hy => ?_
  dsimp only [F, Pi.add_apply]
  have hy0 : 0 < y := lt_trans h34_pos hy.1
  have hLy0 : 0 < L - y := by linarith [hy.2]
  have hLy_le : L - y ≤ y := by linarith [hy.1]
  have hyt : y ≤ screwSignThreshold := hy.2.le.trans hct
  have hKy0 : 0 ≤ -screwRegularKernel y :=
    neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold hy0 hyt)
  have hK_diff : 0 ≤ (-screwRegularKernel (L - y)) - (-screwRegularKernel y) :=
    sub_nonneg.mpr (neg_le_neg (monotoneOn_screwRegularKernel hLy0 hy0 hLy_le))
  have hsum := two_mul_integral_sq_le_integral_jump_sq_add_sub hh hsupp hy0.le
    (le_trans hy.2.le hcL.le)
  have hsixth := seven_thirty_sixths_mul_integral_sq_le_integral_jump_sq_of_sixth_le
    hh hsupp hL.le (show L / 6 ≤ L - y by linarith [hy.2, hc56])
  have hstep1 : (-screwRegularKernel y) * (2 * ∫ u, h u ^ 2) ≤
      (-screwRegularKernel y) *
        ((∫ u, (h u - h (u + y)) ^ 2) + ∫ u, (h u - h (u + (L - y))) ^ 2) :=
    mul_le_mul_of_nonneg_left hsum hKy0
  have hstep2 : ((-screwRegularKernel (L - y)) - (-screwRegularKernel y)) *
      ((7 / 36 : ℝ) * ∫ u, h u ^ 2) ≤
      ((-screwRegularKernel (L - y)) - (-screwRegularKernel y)) *
        ∫ u, (h u - h (u + (L - y))) ^ 2 :=
    mul_le_mul_of_nonneg_left hsixth hK_diff
  linarith

/-- **Sharpened Five-Point Jump-Integral Coercivity on `Ioo (L / 6) c` (`3 * L / 4 ≤ c ≤ 5 * L / 6`)**:
combining `(L / 6, L - c)`, the outer reflected shell `(L - c, L / 4) ∪ (3 * L / 4, c)`, and the
inner reflected shell `(L / 4, 3 * L / 4)` yields:
`((7 / 72) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (13 / 21) * Φ(L / 2) + (47 / 504) * Φ(3 * L / 4) - (65 / 72) * Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo (L / 6) c} (-screwRegularKernel x) D_h(x) dx`. -/
theorem sharpened_five_point_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (h34c : 3 * L / 4 ≤ c)
    (hc56 : c ≤ 5 * L / 6) (hct : c ≤ screwSignThreshold) :
    ((7 / 72 : ℝ) * levyCoshPotential (L / 6) +
        (47 / 504 : ℝ) * levyCoshPotential (L / 4) +
        (13 / 21 : ℝ) * levyCoshPotential (L / 2) +
        (47 / 504 : ℝ) * levyCoshPotential (3 * L / 4) -
        (65 / 72 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 6) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL6 : 0 < L / 6 := by linarith
  have hL6_Lc : L / 6 ≤ L - c := by linarith
  have hLc_L4 : L - c ≤ L / 4 := by linarith
  have hL4_34 : L / 4 ≤ 3 * L / 4 := by linarith
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_all : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 6) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL6 hx.1).neg
  have hIF_all : IntegrableOn F (Ioo (L / 6) c) := by
    refine ((hcont_all.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans hL6 hx.1)
        (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have h1 := seven_seventy_seconds_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL le_rfl hL6_Lc (by linarith)
  have h2 := sharpened_outer_shell_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL h34c hc56 hct
  have h3 := sharpened_inner_shell_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL (by linarith : L / 2 ≤ 3 * L / 4) le_rfl (h34c.trans hct)
  have hIF_1 : IntegrableOn F (Ioo (L / 6) (L - c)) :=
    hIF_all.mono_set (Ioo_subset_Ioo_right (by linarith))
  have hIF_2 : IntegrableOn F (Ioo (L - c) (L / 4)) :=
    hIF_all.mono_set (Ioo_subset_Ioo hL6_Lc (by linarith))
  have hIF_3 : IntegrableOn F (Ioo (L / 4) (3 * L / 4)) :=
    hIF_all.mono_set (Ioo_subset_Ioo (by linarith) h34c)
  have hIF_4 : IntegrableOn F (Ioo (3 * L / 4) c) :=
    hIF_all.mono_set (Ioo_subset_Ioo_left (by linarith))
  have hdisj_12 : Disjoint (Ioo (L / 6) (L - c)) (Ioo (L - c) (L / 4)) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2.le hx2.1
  have hdisj_34 : Disjoint (Ioo (L / 4) (3 * L / 4)) (Ioo (3 * L / 4) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2.le hx2.1
  have hdisj_all : Disjoint (Ioo (L / 6) (L - c) ∪ Ioo (L - c) (L / 4))
      (Ioo (L / 4) (3 * L / 4) ∪ Ioo (3 * L / 4) c) := by
    refine disjoint_left.mpr fun x hx1 hx2 => ?_
    have hx_le : x < L / 4 := by
      rcases hx1 with h1 | h2
      · exact lt_of_lt_of_le h1.2 hLc_L4
      · exact h2.2
    have hx_gt : L / 4 < x := by
      rcases hx2 with h3 | h4
      · exact h3.1
      · exact lt_of_le_of_lt hL4_34 h4.1
    exact not_lt_of_gt hx_gt hx_le
  have hsub_all : (Ioo (L / 6) (L - c) ∪ Ioo (L - c) (L / 4)) ∪
      (Ioo (L / 4) (3 * L / 4) ∪ Ioo (3 * L / 4) c) ⊆ Ioo (L / 6) c := fun x hx => by
    rcases hx with (hx1 | hx2) | (hx3 | hx4)
    · exact ⟨hx1.1, by linarith [hx1.2]⟩
    · exact ⟨lt_of_le_of_lt hL6_Lc hx2.1, by linarith [hx2.2]⟩
    · exact ⟨by linarith [hx3.1], lt_of_lt_of_le hx3.2 h34c⟩
    · exact ⟨by linarith [hx4.1], hx4.2⟩
  have hunion : (∫ x in Ioo (L / 6) (L - c), F x) + (∫ x in Ioo (L - c) (L / 4), F x) +
      ((∫ x in Ioo (L / 4) (3 * L / 4), F x) + (∫ x in Ioo (3 * L / 4) c, F x)) ≤
      ∫ x in Ioo (L / 6) c, F x := by
    rw [← setIntegral_union hdisj_12 measurableSet_Ioo hIF_1 hIF_2,
      ← setIntegral_union hdisj_34 measurableSet_Ioo hIF_3 hIF_4,
      ← setIntegral_union hdisj_all (measurableSet_Ioo.union measurableSet_Ioo)
        (hIF_1.union hIF_2) (hIF_3.union hIF_4)]
    exact setIntegral_mono_set hIF_all
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx =>
        mul_nonneg (neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
          (lt_trans hL6 hx.1) (hx.2.le.trans hct))) (hD0 x)))
      (Eventually.of_forall hsub_all)
  linarith

/-- **Sharpened Five-Point Lévy–Cosh Crossover Inequality on `(0, L)` (`3 * L / 4 ≤ c ≤ 5 * L / 6`)**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`),
`(A(0) + (7 / 72) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (13 / 21) * Φ(L / 2) + (47 / 504) * Φ(3 * L / 4) + (7 / 72) * Φ(c)) * ∫ f² + ... ≤ W_∞(f ⋆ f̃)`. -/
theorem sharpened_five_point_levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L) (h34c : 3 * L / 4 ≤ c)
    (hc56 : c ≤ 5 * L / 6) (hct : c ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (7 / 72) * levyCoshPotential (L / 6) +
        (47 / 504) * levyCoshPotential (L / 4) +
        (13 / 21) * levyCoshPotential (L / 2) +
        (47 / 504) * levyCoshPotential (3 * L / 4) +
        (7 / 72) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL6 : 0 < L / 6 := by linarith
  have hL6c : L / 6 ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL6 hL6c hct
  have hfive := sharpened_five_point_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL h34c hc56 hct
  linarith

/-- **Osculating Lower Bound for the Sharpened Five-Point Potential (`c ≤ 5 * L / 6`)**:
for any `L > 0` and `0 < c ≤ 5 * L / 6`,
`log(1 / (π L)) + (47 / 504) * log(4 / 3) + (7 / 72) * log(9 / 5) + (7 / 4) * L - γ - (49 / 144) * (5 * L / 6 - c)`
`≤ EF.gammaBracket 0 + (7 / 72) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (13 / 21) * Φ(L / 2) + (47 / 504) * Φ(3 * L / 4) + (7 / 72) * Φ(c)`. -/
theorem osculating_le_sharpened_five_point_potential {L c : ℝ} (hL : 0 < L) (hc0 : 0 < c)
    (hc5L6 : c ≤ 5 * L / 6) :
    Real.log (1 / (Real.pi * L)) + (47 / 504 : ℝ) * Real.log (4 / 3) +
        (7 / 72 : ℝ) * Real.log (9 / 5) +
        (7 / 4 : ℝ) * L - Real.eulerMascheroniConstant -
        (49 / 144 : ℝ) * (5 * L / 6 - c) ≤
      EF.gammaBracket 0 + (7 / 72) * levyCoshPotential (L / 6) +
        (47 / 504) * levyCoshPotential (L / 4) +
        (13 / 21) * levyCoshPotential (L / 2) +
        (47 / 504) * levyCoshPotential (3 * L / 4) +
        (7 / 72) * levyCoshPotential c := by
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

/-- Sharp upper bound on `log(9 * π / 25)` by factoring `9 / 25 = (17 / 16)² * (2304 / 7225)`
so that `(2304 / 7225) * π ≈ 1.001836`:
`7 / 8 - (2304 / 7225) * π ≤ log(1 / (π * (9 / 25)))`. -/
theorem seven_eighths_sub_mul_pi_le_log_inv_pi_mul_nine_twenty_fifths :
    (7 / 8 : ℝ) - (2304 / 7225 : ℝ) * Real.pi ≤ Real.log (1 / (Real.pi * (9 / 25))) := by
  have hpos : 0 < (2304 / 7225 : ℝ) * Real.pi := by positivity
  have hfac : Real.pi * (9 / 25 : ℝ) =
      (17 / 16 : ℝ) * (17 / 16 : ℝ) * ((2304 / 7225 : ℝ) * Real.pi) := by ring
  rw [one_div, Real.log_inv, hfac,
    Real.log_mul (by norm_num) hpos.ne',
    Real.log_mul (by norm_num) (by norm_num)]
  have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 17 / 16)
  have h2 := Real.log_le_sub_one_of_pos hpos
  linarith

/-- **Strict Positivity of the Sharpened Five-Point Potential at `L = 9 / 25` (`= 0.36`)**:
`0 ≤ EF.gammaBracket 0 + (7 / 72) * Φ((9/25)/6) + (47 / 504) * Φ((9/25)/4) + (13 / 21) * Φ((9/25)/2) + (47 / 504) * Φ(3*(9/25)/4) + (7 / 72) * Φ(screwSignThreshold)`. -/
theorem zero_le_sharpened_five_point_potential_nine_twenty_fifths :
    0 ≤ EF.gammaBracket 0 + (7 / 72) * levyCoshPotential ((9 / 25 : ℝ) / 6) +
        (47 / 504) * levyCoshPotential ((9 / 25 : ℝ) / 4) +
        (13 / 21) * levyCoshPotential ((9 / 25 : ℝ) / 2) +
        (47 / 504) * levyCoshPotential (3 * (9 / 25 : ℝ) / 4) +
        (7 / 72) * levyCoshPotential screwSignThreshold := by
  have hc0 : 0 < screwSignThreshold := screwSignThreshold_pos
  have hc5L6 : screwSignThreshold ≤ 5 * (9 / 25 : ℝ) / 6 := by
    linarith [screwSignThreshold_lt_787_over_2700]
  have hosc := osculating_le_sharpened_five_point_potential
    (by norm_num : (0 : ℝ) < 9 / 25) hc0 hc5L6
  have hlog_pi := seven_eighths_sub_mul_pi_le_log_inv_pi_mul_nine_twenty_fifths
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hlog43 := two_sevenths_lt_log_four_thirds
  have hlog95 := thirty_two_fifty_fifths_lt_log_nine_fifths
  have ht_gt := screwSignThreshold_gt_6036_over_21509
  have hγ :=
    RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith

/-- **Unconditional nonnegativity of `weilArchRe` on `(0, L)` for all `L ≤ 9 / 25` (`= 0.36`)**:
every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with `L ≤ 9 / 25` (covering **51.94%**
of `(0, log 2)`) satisfies `0 ≤ W_∞(f ⋆ f̃)` unconditionally without `WindowPositive`! -/
theorem weilArchRe_nonneg_of_support_Ioo_le_nine_twenty_fifths {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL : L ≤ 9 / 25)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_9_25 : ∀ u ∉ Ioo (0 : ℝ) (9 / 25), f u = 0 :=
    fun u hu => hsupp u fun h => hu ⟨h.1, lt_of_lt_of_le h.2 hL⟩
  have hmain := sharpened_five_point_levyCosh_crossover_le_weilArchRe hf hfc
    (by norm_num : (0 : ℝ) < 9 / 25)
    (by linarith [screwSignThreshold_gt_6036_over_21509])
    (by linarith [screwSignThreshold_lt_787_over_2700])
    le_rfl hsupp_9_25
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  have hpot := zero_le_sharpened_five_point_potential_nine_twenty_fifths
  have hE0 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hpot_E : 0 ≤ (EF.gammaBracket 0 + (7 / 72) * levyCoshPotential ((9 / 25 : ℝ) / 6) +
        (47 / 504) * levyCoshPotential ((9 / 25 : ℝ) / 4) +
        (13 / 21) * levyCoshPotential ((9 / 25 : ℝ) / 2) +
        (47 / 504) * levyCoshPotential (3 * (9 / 25 : ℝ) / 4) +
        (7 / 72) * levyCoshPotential screwSignThreshold) * ∫ u, f u ^ 2 :=
    mul_nonneg hpot hE0
  linarith

/-- **Unconditional `WindowPositive` on `(0, 9 / 25)` (`= (0, 0.36)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (9 / 25)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_nine_twenty_fifths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (9 / 25)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_nine_twenty_fifths hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

end

end RHTower.WeilLevyFibonacciStaircase
