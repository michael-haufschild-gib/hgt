import GaloisForLFunctions.RHTower.WeilLevySeventhWindowDoubleTransport

/-!
# Harmonic-Doubling Pair-Kernel Coupling, Hyperbolic Partial-Fraction Osculating Floor, and Unconditional Positivity on `(0, 4 / 9)`

This module implements **Cycle 76** of the prime-blind archimedean Weil positivity programme,
breaking the pure jump-integral barrier by coupling the `(L / 3, c)` jump integral directly to the
nonnegative residual 2D pair kernel `2 cosh((u - v) / 2) - levyCoshKernel c |u - v| = screwRegularKernel |u - v|`
for `|u - v| = 2 x > c`:

## Mathematical Architecture

1. **Section 1 — Three-Point Harmonic Doubling Coercivity (`∫ h² ≤ D_h(x) + 2 R(2x)` for all `x ≥ L / 3`)**:
   - From the single-square identity $(p - q)^2 + (q - r)^2 + 2 p r - q^2 = (p - q + r)^2 \ge 0$,
     integrating $p = h(u)$, $q = h(u + x)$, $r = h(u + 2x)$ over $u \in \mathrm{Ioc}\,0\,(L - 2x)$
     for $x \in [L / 3, L / 2]$ (where $\mathrm{Ioc}\,0\,(L - 2x)$ and $\mathrm{Ioc}\,x\,(L - x)$ are
     disjoint inside $\mathrm{Ioc}\,0\,(L - x)$ since $L - 2x \le x$, and $u + x$ covers the entire
     core $\mathrm{Ioc}\,x\,(L - x)$) proves:
     $$\mathrm{coreMass}\ h\ L\ x \le \left(\int_{u \in \mathrm{Ioc}\,0\,(L - x)} (h(u) - h(u + x))^2\,du\right) + 2 * \mathrm{autocorr}\ h\ (2 * x).$$
   - Adding `collarMass h L x` and combining with the half-window bound for $x > L / 2$ (where
     $\mathrm{autocorr}\ h\ (2 * x) = 0$) proves for **all signed** `h` vanishing outside `Ioo 0 L`
     and **every** $x \ge L / 3$:
     $$\int_{\mathbb R} h(u)^2\,du \le \left(\int_{\mathbb R} (h(u) - h(u + x))^2\,du\right) + 2 * \mathrm{autocorr}\ h\ (2 * x).$$

2. **Section 2 — Change of Variables, Residual Pair-Kernel Extraction on `Ioo (2 * a) (2 * b)`, and the Universal Crossing Point at `b₀ = 3 / 16`**:
   - By the linear change of variables $y = 2x$,
     $$\int_{x \in \mathrm{Ioo}\,a\,b} 2 f(2x)\,dx = \int_{y \in \mathrm{Ioo}\,(2a)\,(2b)} f(y)\,dy,$$
     and via `integral_pair_eq_two_mul_Ioi` applied to the indicator kernel
     $k(r) := \mathbf{1}_{\mathrm{Ioo}\,(2a)\,(2b)}(|r|)\,\mathrm{screwRegularKernel}(|r|)$,
     for any nonnegative $h$ vanishing outside $\mathrm{Ioo}\,0\,L$ and $\mathrm{screwSignThreshold} \le c \le 2a$ ($a \le b$):
     $$\int_{x \in \mathrm{Ioo}\,a\,b} \bigl(2\,\mathrm{screwRegularKernel}(2x)\bigr)\bigl(2\,\mathrm{autocorr}\ h\ (2x)\bigr)\,dx
       \le \iint_{\mathbb R^2} h(u) h(v)\bigl(2\cosh((u - v)/2) - K_c(|u - v|)\bigr)\,du\,dv.$$
   - Clearing denominators via `screwRegularKernel_mul_eq_cubic` at $b > 0$ and $2b > 0$ with
     $u = e^{b / 2}$ gives the exact polynomial identities:
     $$\bigl(-\mathrm{screwRegularKernel}(b)\bigr)(u^{10} - u^2) = u(u^4 + 1)(1 + u^2 - u^6),$$
     $$\bigl(2\,\mathrm{screwRegularKernel}(2b)\bigr)(u^{10} - u^2) = 2(u^{12} - u^4 - 1).$$
   - At the dyadic crossing point $b_0 = 3 / 16$ ($2 b_0 = 3 / 8$, $b_0 / 2 = 3 / 32$), the rational
     enclosure $\frac{2249}{2048} \le e^{3 / 32} \le \frac{67}{61}$ certifies both:
     $$-\mathrm{screwRegularKernel}\!\left(\frac{3}{16}\right) \le 2\,\mathrm{screwRegularKernel}\!\left(\frac{3}{8}\right)$$
     and
     $$\frac{19}{20}\cdot 2\,\mathrm{screwRegularKernel}\!\left(\frac{3}{8}\right) \le -\mathrm{screwRegularKernel}\!\left(\frac{3}{16}\right).$$

3. **Section 3 — Full `(L / 3, c)` Harmonic-Doubling Upgrade for `L ≥ 9 / 16` and the Sharpened `(0, log 2)` Plastic Floor (`-0.0100`)**:
   - Since $\frac{3}{16} \le \frac{\log 2}{3}$, on the entire interval $\mathrm{Ioo}\,(\log 2 / 3)\,t_*$
     we have $-\mathrm{screwRegularKernel}(x) \le 2\,\mathrm{screwRegularKernel}(2x)$, upgrading the
     $(L / 3, t_*)$ shell weight from $24 / 41$ to **$1$** and reducing the universal `(0, log 2)`
     constant deficit from `-0.0138` down to **`-0.0100`**.

4. **Section 4 — Hyperbolic Partial-Fraction Decomposition, Cubic-Upgraded Osculating Floor, and Unconditional `WindowPositive` on `(0, 4 / 9)` (`64.12%` of `(0, log 2)`)**:
   - We prove the exact hyperbolic partial-fraction identity for $2\,\mathrm{archLevyDensity}(y)$:
     $$2\,\mathrm{archLevyDensity}(y) = \frac{1}{2\sinh(y / 2)} + \frac{1}{2\cosh(y / 2)} \le \frac{1}{y} + \frac{1}{2},$$
     which combined with $4 + y^2 / 2 \le 4\cosh(y / 2)$ yields the global derivative lower bound
     $$\frac{7}{2} - \frac{1}{y} + \frac{y^2}{2} \le 2\,\mathrm{screwRegularKernel}(y) \qquad \forall y > 0$$
     and the difference inequality for $0 < a \le b$:
     $$\log\!\left(\frac{a}{b}\right) + \frac{7}{2}(b - a) + \frac{b^3 - a^3}{6} \le \Phi(b) - \Phi(a).$$
   - Splitting $\mathrm{Ioo}\,(L / 3)\,c$ at $b_0 = 3 / 16$ combines the $\frac{19}{20}$ harmonic-doubling
     excess on $(L / 3, 3 / 16)$ with full harmonic doubling on $(3 / 16, c)$, yielding a 100% 5-smooth
     logarithmic potential at $L = 4 / 9 \approx 0.444444$ (`64.12%` of `(0, log 2)`) with certified
     strict positivity (`+0.000405 > 0`), and thereby unconditional `WindowPositive` on **`(0, 4 / 9)`**,
     `(0, 11 / 25)` (`= (0, 0.44)`), `(0, 7 / 16)` (`= (0, 0.4375)`), and `(0, 3 / 7)` (`≈ (0, 0.428571)`).
-/

open Complex Real Set MeasureTheory Filter
open scoped Topology
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyHarmonicDoubling

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor
open RHTower.WeilLevyQuarterWindow RHTower.WeilLevySymmetricThreePoint
open RHTower.WeilLevySixthWindow RHTower.WeilLevyFibonacciStaircase
open RHTower.WeilLevyEighthWindow RHTower.WeilLevyThirdWindow
open RHTower.WeilLevyFifthWindow RHTower.WeilLevyTenthWindow
open RHTower.WeilLevySeventhWindow

/-! ## Section 1: Three-Point Harmonic Doubling Coercivity (`∫ h² ≤ D_h(x) + 2 R(2x)` for all `x ≥ L / 3`) -/

/-- Exact three-point harmonic doubling SOS identity: for all `p, q, r : ℝ`,
`q ^ 2 ≤ (p - q) ^ 2 + (q - r) ^ 2 + 2 * (p * r)`, proved via
`(p - q) ^ 2 + (q - r) ^ 2 + 2 * (p * r) - q ^ 2 = (p - q + r) ^ 2 ≥ 0`. -/
theorem sq_le_sub_sq_add_sub_sq_add_two_mul (p q r : ℝ) :
    q ^ 2 ≤ (p - q) ^ 2 + (q - r) ^ 2 + 2 * (p * r) := by
  nlinarith [sq_nonneg (p - q + r)]

/-- For any `BddSupp A h C` vanishing outside `Ioo 0 L`, the autocorrelation `autocorr h y`
is supported on `Ioc 0 (L - y)`:
`(∫ u in Ioc 0 (L - y), h u * h (u + y)) = autocorr h y`. -/
theorem setIntegral_Ioc_mul_shift_eq_autocorr {A : Set ℝ} {h : ℝ → ℝ} {C L y : ℝ}
    (_hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) :
    (∫ u in Ioc 0 (L - y), h u * h (u + y)) = autocorr h y := by
  unfold autocorr
  rw [← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  by_cases hu : u ∈ Ioc 0 (L - y)
  · exact Set.indicator_of_mem hu _
  · rw [Set.indicator_of_notMem hu]
    dsimp only
    by_cases hu0 : 0 < u
    · have huy : L ≤ u + y := by
        have : ¬ u ≤ L - y := fun hle => hu ⟨hu0, hle⟩
        linarith
      rw [hsupp (u + y) (fun hmem => not_lt_of_ge huy hmem.2), mul_zero]
    · rw [hsupp u (fun hmem => hu0 hmem.1), zero_mul]

/-- When `L ≤ y`, the autocorrelation `autocorr h y` vanishes identically for any `BddSupp A h C`
vanishing outside `Ioo 0 L`. -/
theorem autocorr_eq_zero_of_le {A : Set ℝ} {h : ℝ → ℝ} {C L y : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hy : L ≤ y) :
    autocorr h y = 0 := by
  rw [← setIntegral_Ioc_mul_shift_eq_autocorr hh hsupp,
    Ioc_eq_empty (not_lt.mpr (by linarith)), setIntegral_empty]

/-- For any nonnegative `BddSupp A h C`, `0 ≤ autocorr h y` for all `y ∈ ℝ`. -/
theorem autocorr_nonneg {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ} (_hh : BddSupp A h C)
    (hh0 : ∀ u, 0 ≤ h u) (y : ℝ) :
    0 ≤ autocorr h y :=
  integral_nonneg fun u => mul_nonneg (hh0 u) (hh0 (u + y))

/-- **Core-Mass Harmonic Doubling Coercivity on `[L / 3, L / 2]`**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and any `x ∈ [L / 3, L / 2]`,
`coreMass h L x ≤ (∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2) + 2 * autocorr h (2 * x)`. -/
theorem coreMass_le_interior_jump_sq_add_two_mul_autocorr_two_mul
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx3 : L / 3 ≤ x) (_hx2 : x ≤ L / 2) :
    coreMass h L x ≤
      (∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2) + 2 * autocorr h (2 * x) := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift1 : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hmul2 : Integrable (fun u : ℝ => h u * h (u + 2 * x)) := hh.integrable_mul_shift (2 * x)
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift1).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  have hjump_shift : Integrable (fun u : ℝ => (h (u + x) - h (u + 2 * x)) ^ 2) := by
    refine (hjump.comp_add_right x).congr (ae_of_all _ fun u => ?_)
    dsimp only; congr 3; ring
  have hjump12 : Integrable
      (fun u : ℝ => (h u - h (u + x)) ^ 2 + (h (u + x) - h (u + 2 * x)) ^ 2) :=
    hjump.add hjump_shift
  have hpt : ∀ u : ℝ,
      h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 + (h (u + x) - h (u + 2 * x)) ^ 2 +
        2 * (h u * h (u + 2 * x)) :=
    fun u => sq_le_sub_sq_add_sub_sq_add_two_mul (h u) (h (u + x)) (h (u + 2 * x))
  have hint : (∫ u in Ioc 0 (L - 2 * x), h (u + x) ^ 2) ≤
      ∫ u in Ioc 0 (L - 2 * x), ((h u - h (u + x)) ^ 2 +
        (h (u + x) - h (u + 2 * x)) ^ 2 + 2 * (h u * h (u + 2 * x))) :=
    setIntegral_mono hshift1.integrableOn
      (hjump12.integrableOn.add (hmul2.const_mul 2).integrableOn) hpt
  rw [integral_add hjump12.integrableOn (hmul2.const_mul 2).integrableOn,
    integral_add hjump.integrableOn hjump_shift.integrableOn,
    integral_const_mul, setIntegral_Ioc_mul_shift_eq_autocorr hh hsupp] at hint
  have hcore_eq : (∫ u in Ioc 0 (L - 2 * x), h (u + x) ^ 2) = coreMass h L x := by
    have h1 := setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 (L - 2 * x) x
    rw [zero_add, show L - 2 * x + x = L - x by ring] at h1
    exact h1
  have hshift_eq : (∫ u in Ioc 0 (L - 2 * x), (h (u + x) - h (u + 2 * x)) ^ 2) =
      ∫ v in Ioc x (L - x), (h v - h (v + x)) ^ 2 := by
    have h1 := setIntegral_Ioc_add_right (fun v => (h v - h (v + x)) ^ 2) 0 (L - 2 * x) x
    rw [zero_add, show L - 2 * x + x = L - x by ring] at h1
    rw [← h1]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    congr 3; ring
  rw [hcore_eq, hshift_eq] at hint
  have hdisj : Disjoint (Ioc 0 (L - 2 * x)) (Ioc x (L - x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hsub : Ioc 0 (L - 2 * x) ∪ Ioc x (L - x) ⊆ Ioc 0 (L - x) := by
    intro u hu
    rcases hu with hu1 | hu2
    · exact ⟨hu1.1, by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], hu2.2⟩
  have hunion : (∫ u in Ioc 0 (L - 2 * x), (h u - h (u + x)) ^ 2) +
      (∫ v in Ioc x (L - x), (h v - h (v + x)) ^ 2) ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj measurableSet_Ioc hjump.integrableOn hjump.integrableOn]
    exact setIntegral_mono_set hjump.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall hsub)
  linarith

/-- **Universal Harmonic Doubling Coercivity (`∫ h² ≤ D_h(x) + 2 R(2x)` for all `x ≥ L / 3`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and **every shift `x ≥ L / 3`**,
`(∫ u, h u ^ 2) ≤ (∫ u, (h u - h (u + x)) ^ 2) + 2 * autocorr h (2 * x)`. -/
theorem integral_sq_le_integral_jump_sq_add_two_mul_autocorr_two_mul_of_third_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx3 : L / 3 ≤ x) :
    (∫ u, h u ^ 2) ≤ (∫ u, (h u - h (u + x)) ^ 2) + 2 * autocorr h (2 * x) := by
  rcases le_or_gt x (L / 2) with hx2 | hx2
  · have hx0 : 0 ≤ x := by linarith
    have hcore := coreMass_le_interior_jump_sq_add_two_mul_autocorr_two_mul hh hsupp hL0 hx3 hx2
    have hcol := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
    have hcons := collarMass_add_coreMass_eq hh hx2
    linarith
  · rw [autocorr_eq_zero_of_le hh hsupp (by linarith : L ≤ 2 * x), mul_zero, add_zero]
    exact integral_sq_le_integral_jump_sq_of_half_le hh hsupp hL0 hx2.le

/-- **Dual Autocorrelation Harmonic-Doubling Damping (`2 R(x) - 2 R(2x) ≤ ∫ h²` for all `x ≥ L / 3`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and every shift `x ≥ L / 3`,
`2 * autocorr h x - 2 * autocorr h (2 * x) ≤ ∫ u, h u ^ 2`. -/
theorem two_mul_autocorr_sub_two_mul_autocorr_two_mul_le_integral_sq_of_third_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx3 : L / 3 ≤ x) :
    2 * autocorr h x - 2 * autocorr h (2 * x) ≤ ∫ u, h u ^ 2 := by
  have hid := integral_jump_sq hh x
  have hcoerc := integral_sq_le_integral_jump_sq_add_two_mul_autocorr_two_mul_of_third_le
    hh hsupp hL0 hx3
  linarith

/-! ## Section 2: Change of Variables, Residual Pair-Kernel Extraction on `Ioo (2 * a) (2 * b)`, and the Universal Crossing Point at `b₀ = 3 / 16` -/

/-- Exact change of variables `y = 2 * x` on `Ioo a b` (`a ≤ b`):
`(∫ x in Ioo a b, 2 * f (2 * x)) = ∫ y in Ioo (2 * a) (2 * b), f y`. -/
theorem setIntegral_Ioo_two_mul_comp_two_mul (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Ioo a b, 2 * f (2 * x)) = ∫ y in Ioo (2 * a) (2 * b), f y := by
  have h2ab : 2 * a ≤ 2 * b := by linarith
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left f two_ne_zero,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul,
    intervalIntegral.integral_of_le h2ab, integral_Ioc_eq_integral_Ioo]

/-- Exact evaluation of `∫_{x ∈ Ioo a b} 2 * screwRegularKernel (2 * x)` (`0 < a ≤ b`):
`(∫ x in Ioo a b, 2 * screwRegularKernel (2 * x)) = (1 / 2) * (levyCoshPotential (2 * b) - levyCoshPotential (2 * a))`. -/
theorem setIntegral_Ioo_two_mul_screwRegularKernel_two_mul {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in Ioo a b, 2 * screwRegularKernel (2 * x)) =
      (1 / 2 : ℝ) * (levyCoshPotential (2 * b) - levyCoshPotential (2 * a)) := by
  rw [setIntegral_Ioo_two_mul_comp_two_mul screwRegularKernel hab]
  have h := setIntegral_Ioo_neg_screwRegularKernel (by linarith : 0 < 2 * a)
    (by linarith : 2 * a ≤ 2 * b)
  rw [integral_neg] at h
  linarith

/-- For any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`) and `c > 0`, the residual
2D pair integrand `p ↦ h p.1 * h p.2 * (2 * cosh((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)`
is integrable on `ℝ × ℝ`. -/
theorem integrable_pair_two_mul_cosh_sub_levyCoshKernel_of_support_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL : 0 < L) (hc : 0 < c) :
    Integrable (fun p : ℝ × ℝ =>
      h p.1 * h p.2 * (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) := by
  have hI_ker : Integrable (fun p : ℝ × ℝ => h p.1 * h p.2 * levyCoshKernel c |p.1 - p.2|) :=
    integrable_pair_levyCoshKernel hh hc
  have hI_cosh : Integrable (fun p : ℝ × ℝ => h p.1 * h p.2 * (2 * Real.cosh ((p.1 - p.2) / 2))) := by
    rw [Measure.volume_eq_prod]
    refine ((hh.integrable.abs.mul_prod hh.integrable.abs).mul_const (2 * Real.cosh (L / 2))).mono'
      (((hh.meas.comp measurable_fst).mul (hh.meas.comp measurable_snd)).mul
        (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    by_cases hp1 : p.1 ∈ Ioo 0 L
    · by_cases hp2 : p.2 ∈ Ioo 0 L
      · have hcosh : Real.cosh ((p.1 - p.2) / 2) ≤ Real.cosh (L / 2) := by
          rw [Real.cosh_le_cosh, abs_div, abs_two, abs_of_pos (by positivity : 0 < L / 2),
            div_le_div_iff_of_pos_right zero_lt_two, abs_le]
          constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
        rw [abs_of_pos (by positivity : 0 < 2 * Real.cosh ((p.1 - p.2) / 2))]
        exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · simp [hsupp p.2 hp2]
    · simp [hsupp p.1 hp1]
  refine (hI_cosh.sub hI_ker).congr (ae_of_all _ fun p => ?_)
  simp only [Pi.sub_apply]; ring

/-- **Pair-Integral Extraction on `Ioo a b` via Harmonic Doubling (`c ≤ 2 * a`, `a ≤ b`)**:
for any nonnegative `BddSupp A h C` (`∀ u, 0 ≤ h u`) vanishing outside `Ioo 0 L` (`L > 0`) and
any `c, a, b` with `screwSignThreshold ≤ c ≤ 2 * a` and `a ≤ b`,
`∫_{x ∈ Ioo a b} (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))`
`≤ ∫ p : ℝ × ℝ, h p.1 * h p.2 * (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)`. -/
theorem setIntegral_Ioo_two_mul_screwRegularKernel_two_mul_autocorr_le_pair
    {A : Set ℝ} {h : ℝ → ℝ} {C L c a b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u) (hL : 0 < L)
    (hct : screwSignThreshold ≤ c) (hca : c ≤ 2 * a) (hab : a ≤ b) :
    (∫ x in Ioo a b, (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))) ≤
      ∫ p : ℝ × ℝ, h p.1 * h p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|) := by
  have hc0 : 0 < c := lt_of_lt_of_le screwSignThreshold_pos hct
  have ha0 : 0 < a := by linarith
  have h2a0 : 0 < 2 * a := by linarith
  have hconv : (∫ x in Ioo a b, (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))) =
      2 * ∫ y in Ioo (2 * a) (2 * b), screwRegularKernel y * autocorr h y := by
    have h1 := setIntegral_Ioo_two_mul_comp_two_mul
      (fun y => screwRegularKernel y * autocorr h y) hab
    rw [← h1, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo fun x _ => by ring
  rw [hconv]
  set k : ℝ → ℝ := fun r => Set.indicator (Ioo (2 * a) (2 * b)) screwRegularKernel |r| with hkdef
  have hKm : Measurable screwRegularKernel := by
    unfold screwRegularKernel; fun_prop
  have hk_meas : Measurable k :=
    (hKm.indicator measurableSet_Ioo).comp measurable_abs
  set M := max (|screwRegularKernel (2 * a)|) (|screwRegularKernel (2 * b)|)
  have hM0 : 0 ≤ M := le_max_of_le_left (abs_nonneg _)
  have hk_bound : ∀ r, |k r| ≤ M := by
    intro r
    dsimp only [k]
    by_cases hr : |r| ∈ Ioo (2 * a) (2 * b)
    · rw [Set.indicator_of_mem hr]
      have hge : screwRegularKernel |r| ≤ screwRegularKernel (2 * b) :=
        monotoneOn_screwRegularKernel (lt_trans h2a0 hr.1) (lt_trans h2a0 (hr.1.trans hr.2)) hr.2.le
      have hpos : 0 ≤ screwRegularKernel |r| :=
        screwRegularKernel_nonneg_of_threshold_le (hct.trans (hca.trans hr.1.le))
      rw [abs_of_nonneg hpos]
      exact le_trans hge (le_trans (le_abs_self _) (le_max_right _ _))
    · rw [Set.indicator_of_notMem hr, abs_zero]
      exact hM0
  have hpair_k := integral_pair_eq_two_mul_Ioi hh hk_meas hk_bound
  have hIoi_eq : (∫ y in Ioi (0 : ℝ), k y * autocorr h y) =
      ∫ y in Ioo (2 * a) (2 * b), screwRegularKernel y * autocorr h y := by
    have hsub : Ioo (2 * a) (2 * b) ⊆ Ioi (0 : ℝ) := fun y hy => lt_trans h2a0 hy.1
    rw [← inter_eq_self_of_subset_right hsub, ← setIntegral_indicator measurableSet_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    dsimp only [k]
    rw [abs_of_pos (mem_Ioi.mp hy)]
    by_cases hyI : y ∈ Ioo (2 * a) (2 * b)
    · simp [Set.indicator_of_mem hyI]
    · simp [Set.indicator_of_notMem hyI]
  rw [← hIoi_eq, ← hpair_k]
  have hI_k : Integrable (fun p : ℝ × ℝ => h p.1 * h p.2 * k |p.1 - p.2|) := by
    rw [Measure.volume_eq_prod]
    refine ((hh.integrable.abs.mul_prod hh.integrable.abs).mul_const M).mono'
      (((hh.meas.comp measurable_fst).mul (hh.meas.comp measurable_snd)).mul
        (hk_meas.comp (measurable_fst.sub measurable_snd).abs)).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hk_bound |p.1 - p.2|)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hI_rhs := integrable_pair_two_mul_cosh_sub_levyCoshKernel_of_support_Ioo hh hsupp hL hc0
  refine integral_mono hI_k hI_rhs fun p => ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hh0 p.1) (hh0 p.2))
  dsimp only [k]
  rw [abs_abs, two_mul_cosh_sub_levyCoshKernel_eq hc0]
  by_cases hr : |p.1 - p.2| ∈ Ioo (2 * a) (2 * b)
  · rw [Set.indicator_of_mem hr, if_neg (not_le.mpr (lt_of_le_of_lt hca hr.1))]
  · rw [Set.indicator_of_notMem hr]
    split_ifs with hle
    · exact le_rfl
    · exact screwRegularKernel_nonneg_of_threshold_le (hct.trans (not_le.mp hle).le)

/-- Clearing the denominator of `-screwRegularKernel b` (`b > 0`) in terms of `u = exp(b / 2)`:
`(-screwRegularKernel b) * (u ^ 10 - u ^ 2) = u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6)`. -/
theorem neg_screwRegularKernel_mul_eq_of_pos {b : ℝ} (hb : 0 < b) :
    let u := Real.exp (b / 2)
    (-screwRegularKernel b) * (u ^ 10 - u ^ 2) = u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6) := by
  intro u
  have hcub := screwRegularKernel_mul_eq_cubic hb
  have hfac : Real.exp (5 * b / 2) * (1 - Real.exp (-(2 * b))) = u ^ 5 - u := by
    have h1 : Real.exp (5 * b / 2) * Real.exp (-(2 * b)) = u := by
      dsimp only [u]; rw [← Real.exp_add]; congr 1; ring
    have h5 : Real.exp (5 * b / 2) = u ^ 5 := by
      dsimp only [u]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    linarith
  have he1 : Real.exp b = u ^ 2 := by
    dsimp only [u]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hfac, he1] at hcub
  calc (-screwRegularKernel b) * (u ^ 10 - u ^ 2)
      = -(screwRegularKernel b * (u ^ 5 - u)) * (u * (u ^ 4 + 1)) := by ring
    _ = -((u ^ 2) ^ 3 - u ^ 2 - 1) * (u * (u ^ 4 + 1)) := by rw [hcub]
    _ = u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6) := by ring

/-- Clearing the denominator of `2 * screwRegularKernel (2 * b)` (`b > 0`) in terms of `u = exp(b / 2)`:
`(2 * screwRegularKernel (2 * b)) * (u ^ 10 - u ^ 2) = 2 * (u ^ 12 - u ^ 4 - 1)`. -/
theorem two_mul_screwRegularKernel_two_mul_eq_of_pos {b : ℝ} (hb : 0 < b) :
    let u := Real.exp (b / 2)
    (2 * screwRegularKernel (2 * b)) * (u ^ 10 - u ^ 2) = 2 * (u ^ 12 - u ^ 4 - 1) := by
  intro u
  have h2b : 0 < 2 * b := by linarith
  have hcub := screwRegularKernel_mul_eq_cubic h2b
  have hfac : Real.exp (5 * (2 * b) / 2) * (1 - Real.exp (-(2 * (2 * b)))) = u ^ 10 - u ^ 2 := by
    have h1 : Real.exp (5 * (2 * b) / 2) * Real.exp (-(2 * (2 * b))) = u ^ 2 := by
      dsimp only [u]; rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h10 : Real.exp (5 * (2 * b) / 2) = u ^ 10 := by
      dsimp only [u]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    linarith
  have he2 : Real.exp (2 * b) = u ^ 4 := by
    dsimp only [u]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hfac, he2] at hcub
  calc (2 * screwRegularKernel (2 * b)) * (u ^ 10 - u ^ 2)
      = 2 * (screwRegularKernel (2 * b) * (u ^ 10 - u ^ 2)) := by ring
    _ = 2 * ((u ^ 4) ^ 3 - u ^ 4 - 1) := by rw [hcub]
    _ = 2 * (u ^ 12 - u ^ 4 - 1) := by ring

/-- Quadratic Taylor lower bound `1 + x + x ^ 2 / 2 ≤ Real.exp x` for all `x ≥ 0`. -/
theorem one_add_add_half_sq_le_exp {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 ≤ Real.exp x := by
  let g : ℝ → ℝ := fun u => Real.exp u - (1 + u + u ^ 2 / 2)
  have hderiv : ∀ u : ℝ, HasDerivAt g (Real.exp u - 1 - u) u := by
    intro u
    have h1 := Real.hasDerivAt_exp u
    have h2 : HasDerivAt (fun v : ℝ => 1 + v + v ^ 2 / 2) (1 + u) u := by
      have ha : HasDerivAt (fun v : ℝ => 1 + v) 1 u := (hasDerivAt_id u).const_add 1
      have hb : HasDerivAt (fun v : ℝ => v ^ 2 / 2) u u := by
        simpa using ((hasDerivAt_pow 2 u).div_const 2).congr_deriv (by ring)
      exact ha.add hb
    exact (h1.sub h2).congr_deriv (by ring)
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun u _ => (hderiv u).continuousAt.continuousWithinAt
    · exact fun u _ => (hderiv u).differentiableAt.differentiableWithinAt
    · intro u _
      rw [(hderiv u).deriv]
      linarith [Real.add_one_le_exp u]
  have h0 : g 0 ≤ g x := hmono self_mem_Ici hx hx
  dsimp [g] at h0
  rw [Real.exp_zero] at h0
  linarith

/-- Rational lower bound `2249 / 2048 ≤ Real.exp (3 / 32)` via `one_add_add_half_sq_le_exp`. -/
theorem exp_three_thirty_seconds_ge : (2249 : ℝ) / 2048 ≤ Real.exp (3 / 32) := by
  have h := one_add_add_half_sq_le_exp (by norm_num : (0 : ℝ) ≤ 3 / 32)
  linarith

/-- Rational upper bound `Real.exp (3 / 32) ≤ 67 / 61` via `one_sub_exp_neg_half_le` at `3 / 16`. -/
theorem exp_three_thirty_seconds_le : Real.exp (3 / 32) ≤ (67 : ℝ) / 61 := by
  have h := one_sub_exp_neg_half_le (by norm_num : (0 : ℝ) ≤ 3 / 16)
  rw [show -(3 / 16 : ℝ) / 2 = -(3 / 32 : ℝ) by ring, Real.exp_neg] at h
  have hexp : 0 < Real.exp (3 / 32) := Real.exp_pos _
  have hm := mul_le_mul_of_nonneg_right h hexp.le
  have hcancel : (Real.exp (3 / 32))⁻¹ * Real.exp (3 / 32) = 1 := inv_mul_cancel₀ hexp.ne'
  nlinarith

/-- **Harmonic-Doubling Crossing Inequality at `b₀ = 3 / 16` (`2 * b₀ = 3 / 8`)**:
`-screwRegularKernel (3 / 16) ≤ 2 * screwRegularKernel (3 / 8)`. -/
theorem neg_screwRegularKernel_three_sixteenths_le_two_mul_screwRegularKernel_three_eighths :
    -screwRegularKernel (3 / 16) ≤ 2 * screwRegularKernel (3 / 8) := by
  have hb : (0 : ℝ) < 3 / 16 := by norm_num
  have h1 := neg_screwRegularKernel_mul_eq_of_pos hb
  have h2 := two_mul_screwRegularKernel_two_mul_eq_of_pos hb
  dsimp only at h1 h2
  rw [show (2 : ℝ) * (3 / 16) = 3 / 8 by norm_num] at h2
  rw [show (3 / 16 : ℝ) / 2 = 3 / 32 by norm_num] at h1 h2
  set u := Real.exp (3 / 32)
  have hu_ge : (2249 : ℝ) / 2048 ≤ u := exp_three_thirty_seconds_ge
  have hu_le : u ≤ (67 : ℝ) / 61 := exp_three_thirty_seconds_le
  have hden : 0 < u ^ 10 - u ^ 2 := by
    have : ((2249 : ℝ) / 2048) ^ 10 ≤ u ^ 10 := pow_le_pow_left₀ (by norm_num) hu_ge 10
    have : u ^ 2 ≤ ((67 : ℝ) / 61) ^ 2 := pow_le_pow_left₀ (by linarith) hu_le 2
    linarith
  have hpoly : u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6) ≤ 2 * (u ^ 12 - u ^ 4 - 1) := by
    have hp12 : ((2249 : ℝ) / 2048) ^ 12 ≤ u ^ 12 := pow_le_pow_left₀ (by norm_num) hu_ge 12
    have hp4 : u ^ 4 ≤ ((67 : ℝ) / 61) ^ 4 := pow_le_pow_left₀ (by linarith) hu_le 4
    have hp6 : ((2249 : ℝ) / 2048) ^ 6 ≤ u ^ 6 := pow_le_pow_left₀ (by norm_num) hu_ge 6
    have hp2 : u ^ 2 ≤ ((67 : ℝ) / 61) ^ 2 := pow_le_pow_left₀ (by linarith) hu_le 2
    have hfac1 : 0 ≤ u * (u ^ 4 + 1) := by positivity
    have hfac1_le : u * (u ^ 4 + 1) ≤ (67 / 61 : ℝ) * (((67 : ℝ) / 61) ^ 4 + 1) := by nlinarith
    have hfac2_pos : 0 ≤ 1 + ((67 : ℝ) / 61) ^ 2 - ((2249 : ℝ) / 2048) ^ 6 := by norm_num
    have hprod : u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6) ≤
        (67 / 61 : ℝ) * (((67 : ℝ) / 61) ^ 4 + 1) *
          (1 + ((67 : ℝ) / 61) ^ 2 - ((2249 : ℝ) / 2048) ^ 6) := by nlinarith
    linarith
  nlinarith

/-- **Reverse Crossing Ratio at `b₀ = 3 / 16` (`(19 / 20) * 2 K(3 / 8) ≤ -K(3 / 16)`)**:
`(19 / 20 : ℝ) * (2 * screwRegularKernel (3 / 8)) ≤ -screwRegularKernel (3 / 16)`. -/
theorem nineteen_twentieths_mul_two_mul_screwRegularKernel_three_eighths_le_neg_screwRegularKernel_three_sixteenths :
    (19 / 20 : ℝ) * (2 * screwRegularKernel (3 / 8)) ≤ -screwRegularKernel (3 / 16) := by
  have hb : (0 : ℝ) < 3 / 16 := by norm_num
  have h1 := neg_screwRegularKernel_mul_eq_of_pos hb
  have h2 := two_mul_screwRegularKernel_two_mul_eq_of_pos hb
  dsimp only at h1 h2
  rw [show (2 : ℝ) * (3 / 16) = 3 / 8 by norm_num] at h2
  rw [show (3 / 16 : ℝ) / 2 = 3 / 32 by norm_num] at h1 h2
  set u := Real.exp (3 / 32)
  have hu_ge : (2249 : ℝ) / 2048 ≤ u := exp_three_thirty_seconds_ge
  have hu_le : u ≤ (67 : ℝ) / 61 := exp_three_thirty_seconds_le
  have hden : 0 < u ^ 10 - u ^ 2 := by
    have : ((2249 : ℝ) / 2048) ^ 10 ≤ u ^ 10 := pow_le_pow_left₀ (by norm_num) hu_ge 10
    have : u ^ 2 ≤ ((67 : ℝ) / 61) ^ 2 := pow_le_pow_left₀ (by linarith) hu_le 2
    linarith
  have hpoly : (19 / 20 : ℝ) * (2 * (u ^ 12 - u ^ 4 - 1)) ≤
      u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6) := by
    have hp12 : u ^ 12 ≤ ((67 : ℝ) / 61) ^ 12 := pow_le_pow_left₀ (by linarith) hu_le 12
    have hp4_ge : ((2249 : ℝ) / 2048) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu_ge 4
    have hp6_le : u ^ 6 ≤ ((67 : ℝ) / 61) ^ 6 := pow_le_pow_left₀ (by linarith) hu_le 6
    have hp2_ge : ((2249 : ℝ) / 2048) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu_ge 2
    have hfac1_ge : (2249 / 2048 : ℝ) * (((2249 : ℝ) / 2048) ^ 4 + 1) ≤ u * (u ^ 4 + 1) := by
      nlinarith
    have hfac2_ge : 0 ≤ 1 + ((2249 : ℝ) / 2048) ^ 2 - ((67 : ℝ) / 61) ^ 6 := by norm_num
    have hprod : (2249 / 2048 : ℝ) * (((2249 : ℝ) / 2048) ^ 4 + 1) *
        (1 + ((2249 : ℝ) / 2048) ^ 2 - ((67 : ℝ) / 61) ^ 6) ≤
        u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6) := by nlinarith
    linarith
  nlinarith

/-- For every `x ≥ 3 / 16`, `-screwRegularKernel x ≤ 2 * screwRegularKernel (2 * x)`. -/
theorem neg_screwRegularKernel_le_two_mul_screwRegularKernel_two_mul_of_three_sixteenths_le
    {x : ℝ} (hx : 3 / 16 ≤ x) :
    -screwRegularKernel x ≤ 2 * screwRegularKernel (2 * x) := by
  have hx0 : 0 < x := by linarith
  have h1 : screwRegularKernel (3 / 16) ≤ screwRegularKernel x :=
    monotoneOn_screwRegularKernel (by norm_num : (0 : ℝ) < 3 / 16) hx0 hx
  have h2 : screwRegularKernel (3 / 8) ≤ screwRegularKernel (2 * x) :=
    monotoneOn_screwRegularKernel (by norm_num : (0 : ℝ) < 3 / 8) (by linarith : 0 < 2 * x)
      (by linarith)
  linarith [neg_screwRegularKernel_three_sixteenths_le_two_mul_screwRegularKernel_three_eighths]

/-- For every `x ∈ (0, 3 / 16]`,
`(19 / 20 : ℝ) * (2 * screwRegularKernel (2 * x)) ≤ -screwRegularKernel x`. -/
theorem nineteen_twentieths_mul_two_mul_screwRegularKernel_two_mul_le_neg_screwRegularKernel
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 3 / 16) :
    (19 / 20 : ℝ) * (2 * screwRegularKernel (2 * x)) ≤ -screwRegularKernel x := by
  have h1 : screwRegularKernel x ≤ screwRegularKernel (3 / 16) :=
    monotoneOn_screwRegularKernel hx0 (by norm_num : (0 : ℝ) < 3 / 16) hx
  have h2 : screwRegularKernel (2 * x) ≤ screwRegularKernel (3 / 8) :=
    monotoneOn_screwRegularKernel (by linarith : 0 < 2 * x) (by norm_num : (0 : ℝ) < 3 / 8)
      (by linarith)
  linarith [nineteen_twentieths_mul_two_mul_screwRegularKernel_three_eighths_le_neg_screwRegularKernel_three_sixteenths]

/-- Corollary: `screwSignThreshold < 3 / 8 = 2 * (3 / 16)`. -/
theorem screwSignThreshold_lt_three_eighths : screwSignThreshold < (3 : ℝ) / 8 := by
  linarith [screwSignThreshold_lt_thirty_eight_over_one_thirty_five]

/-- Measurability of `x ↦ 2 * autocorr h (2 * x)` for `BddSupp A h C`. -/
theorem measurable_two_mul_autocorr_two_mul {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ}
    (hh : BddSupp A h C) :
    Measurable fun x : ℝ => 2 * autocorr h (2 * x) := by
  rw [show (fun x : ℝ => 2 * autocorr h (2 * x)) =
      fun x : ℝ => 2 * (∫ u, h u ^ 2) - ∫ u, (h u - h (u + 2 * x)) ^ 2 by
    ext x; linarith [integral_jump_sq hh (2 * x)]]
  exact measurable_const.sub ((measurable_jump hh).comp (measurable_const.mul measurable_id))

/-! ## Section 3: Full `(L / 3, c)` Harmonic-Doubling Upgrade for `L ≥ 9 / 16` and the Sharpened `(0, log 2)` Plastic Floor (`-0.0100`) -/

/-- Continuity of `x ↦ 2 * screwRegularKernel (2 * x)` on `Icc a b` for `0 < a`. -/
theorem continuousOn_two_mul_screwRegularKernel_two_mul {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x => 2 * screwRegularKernel (2 * x)) (Icc a b) :=
  continuousOn_const.mul (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.comp
    (continuousOn_const.mul continuousOn_id) fun x hx =>
      mem_Ioi.mpr (by linarith [hx.1]))

/-- **Full-Weight Harmonic-Doubling Jump + Pair Extraction on `Ioo a b` (`3 / 16 ≤ a`, `L / 3 ≤ a`)**:
for any nonnegative `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`) and any `a ≤ b ≤ screwSignThreshold`
with `3 / 16 ≤ a` and `L / 3 ≤ a`,
`(1 / 2) * (Φ(a) - Φ(b)) * ∫ h² ≤ (∫_{x ∈ Ioo a b} (-K(x)) D_h(x)) + ∫_{x ∈ Ioo a b} (2 K(2x)) (2 R(2x))`. -/
theorem half_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_double_autocorr
    {A : Set ℝ} {h : ℝ → ℝ} {C L a b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u) (hL : 0 < L)
    (ha16 : 3 / 16 ≤ a) (ha3 : L / 3 ≤ a) (hab : a ≤ b) (hbt : b ≤ screwSignThreshold) :
    (1 / 2 : ℝ) * (levyCoshPotential a - levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      (∫ x in Ioo a b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ x in Ioo a b, (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x)) := by
  have ha0 : 0 < a := by linarith
  have h2a0 : 0 < 2 * a := by linarith
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  have hR0 : ∀ x, 0 ≤ 2 * autocorr h (2 * x) :=
    fun x => mul_nonneg zero_le_two (autocorr_nonneg hh hh0 (2 * x))
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc a b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le ha0 hx.1).neg
  have hI_K : IntegrableOn (fun x => -screwRegularKernel x) (Ioo a b) :=
    hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hh
  have hI_jump : IntegrableOn
      (fun x : ℝ => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) (Ioo a b) := by
    refine (hI_K.mul_const (4 * ∫ u, h u ^ 2)).mono' (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hbt))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hcont_K2 : ContinuousOn (fun x => 2 * screwRegularKernel (2 * x)) (Icc a b) :=
    continuousOn_two_mul_screwRegularKernel_two_mul ha0
  have hI_K2 : IntegrableOn (fun x => 2 * screwRegularKernel (2 * x)) (Ioo a b) :=
    hcont_K2.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hK2m : Measurable fun x : ℝ => 2 * screwRegularKernel (2 * x) := by
    unfold screwRegularKernel; fun_prop
  have hR2m : Measurable fun x : ℝ => 2 * autocorr h (2 * x) :=
    measurable_two_mul_autocorr_two_mul hh
  have hI_auto : IntegrableOn
      (fun x : ℝ => (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))) (Ioo a b) := by
    refine (hI_K2.mul_const (2 * ∫ u, h u ^ 2)).mono' (hK2m.mul hR2m).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hbt))
    have hK2_0 : 0 ≤ 2 * screwRegularKernel (2 * x) :=
      le_trans hK0 (neg_screwRegularKernel_le_two_mul_screwRegularKernel_two_mul_of_three_sixteenths_le
        (ha16.trans hx.1.le))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK2_0 (hR0 x))]
    have hR_le : 2 * autocorr h (2 * x) ≤ 2 * ∫ u, h u ^ 2 := by
      have hid := integral_jump_sq hh (2 * x)
      have hD_nn := hD0 (2 * x)
      linarith
    exact mul_le_mul_of_nonneg_left hR_le hK2_0
  have hI_lhs : IntegrableOn
      (fun x : ℝ => (-screwRegularKernel x) * ∫ u, h u ^ 2) (Ioo a b) :=
    hI_K.mul_const _
  have hmono : (∫ x in Ioo a b, (-screwRegularKernel x) * ∫ u, h u ^ 2) ≤
      ∫ x in Ioo a b, ((-screwRegularKernel x) * (∫ u, (h u - h (u + x)) ^ 2) +
        (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))) := by
    refine setIntegral_mono_on hI_lhs (hI_jump.add hI_auto) measurableSet_Ioo fun x hx => ?_
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hbt))
    have hhd := integral_sq_le_integral_jump_sq_add_two_mul_autocorr_two_mul_of_third_le
      hh hsupp hL.le (ha3.trans hx.1.le)
    have h1 := mul_le_mul_of_nonneg_left hhd hK0
    have h2 : (-screwRegularKernel x) * (2 * autocorr h (2 * x)) ≤
        (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x)) :=
      mul_le_mul_of_nonneg_right
        (neg_screwRegularKernel_le_two_mul_screwRegularKernel_two_mul_of_three_sixteenths_le
          (ha16.trans hx.1.le))
        (hR0 x)
    linarith
  rw [integral_mul_const, setIntegral_Ioo_neg_screwRegularKernel ha0 hab,
    integral_add hI_jump hI_auto] at hmono
  linarith

/-- **Full-Weight Harmonic-Doubling Potential + Pair Bound on `Ioo a c` (`3 / 16 ≤ a`, `L / 3 ≤ a ≤ c = screwSignThreshold`)**:
for any nonnegative `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`) and `a ≤ screwSignThreshold`
with `3 / 16 ≤ a` and `L / 3 ≤ a`,
`(1 / 2) * (Φ(a) - Φ(screwSignThreshold)) * ∫ h² ≤ (∫_{x ∈ Ioo a screwSignThreshold} (-K(x)) D_h(x)) + pair_{screwSignThreshold}(h)`. -/
theorem half_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_pair_of_three_sixteenths_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L a : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u) (hL : 0 < L)
    (ha16 : 3 / 16 ≤ a) (ha3 : L / 3 ≤ a) (hat : a ≤ screwSignThreshold) :
    (1 / 2 : ℝ) * (levyCoshPotential a - levyCoshPotential screwSignThreshold) * (∫ u, h u ^ 2) ≤
      (∫ x in Ioo a screwSignThreshold, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ p : ℝ × ℝ, h p.1 * h p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) := by
  have h1 := half_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_double_autocorr
    hh hsupp hh0 hL ha16 ha3 hat le_rfl
  have h2 := setIntegral_Ioo_two_mul_screwRegularKernel_two_mul_autocorr_le_pair
    hh hsupp hh0 hL le_rfl (by linarith [screwSignThreshold_lt_three_eighths] : screwSignThreshold ≤ 2 * a) hat
  linarith

/-- **Seven-Shell Harmonic-Doubling Potential + Pair Coercivity for `L ≥ 9 / 16`**:
combining `(L / 10, L / 4)`, `(L / 4, L / 3)`, and `(L / 3, screwSignThreshold)` upgrades the
weight at `L / 3` from `88 / 861` (`≈ 0.1022`) to `13 / 42` (`= 1 / 2 - 4 / 21 ≈ 0.3095`)! -/
theorem tenth_to_third_harmonic_doubling_sub_levyCoshPotential_le_setIntegral_Ioo_add_pair
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hh0 : ∀ u, 0 ≤ h u)
    (hL9_16 : 9 / 16 ≤ L) (hL3t : L / 3 ≤ screwSignThreshold) :
    ((1 / 25 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (3 / 200 : ℝ) * levyCoshPotential (L / 7) +
        (1 / 45 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (2 / 35 : ℝ) * levyCoshPotential (L / 4) +
        (13 / 42 : ℝ) * levyCoshPotential (L / 3) -
        (1 / 2 : ℝ) * levyCoshPotential screwSignThreshold) * (∫ u, h u ^ 2) ≤
      (∫ x in Ioo (L / 10) screwSignThreshold,
        (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ p : ℝ × ℝ, h p.1 * h p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) := by
  have hL0 : 0 < L := by linarith
  have hL10_pos : 0 < L / 10 := by linarith
  have hL10_4 : L / 10 ≤ L / 4 := by linarith
  have hL5_4 : L / 5 ≤ L / 4 := by linarith
  have hL4_3 : L / 4 ≤ L / 3 := by linarith
  have hL4_t : L / 4 ≤ screwSignThreshold := le_trans hL4_3 hL3t
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 10) screwSignThreshold) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL10_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 10) screwSignThreshold) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL10_pos hx.1) hx.2.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_1_Ioc : IntegrableOn F (Ioc (L / 10) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL4_t)
  have hIF_2_Ioc : IntegrableOn F (Ioc (L / 4) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL10_4 hL3t)
  have hIF_3_Ioc : IntegrableOn F (Ioc (L / 3) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo (hL10_4.trans hL4_3) le_rfl)
  have hIF_12_Ioc : IntegrableOn F (Ioc (L / 10) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL3t)
  have hdisj_12 : Disjoint (Ioc (L / 10) (L / 4)) (Ioc (L / 4) (L / 3)) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_123 : Disjoint (Ioc (L / 10) (L / 3)) (Ioc (L / 3) screwSignThreshold) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 10) screwSignThreshold, F x) =
      (∫ x in Ioo (L / 10) (L / 4), F x) + (∫ x in Ioo (L / 4) (L / 3), F x) +
        ∫ x in Ioo (L / 3) screwSignThreshold, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (hL10_4.trans hL4_3) hL3t,
      setIntegral_union hdisj_123 measurableSet_Ioc hIF_12_Ioc hIF_3_Ioc,
      ← Ioc_union_Ioc_eq_Ioc hL10_4 hL4_3,
      setIntegral_union hdisj_12 measurableSet_Ioc hIF_1_Ioc hIF_2_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h105 := tenth_to_fifth_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL5_4 hL4_t
  have h4 := four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL4_3 hL3t
  have h3 := half_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_pair_of_three_sixteenths_le
    hh hsupp hh0 hL0 (by linarith : 3 / 16 ≤ L / 3) le_rfl hL3t
  dsimp only [F] at hsplit
  linarith

/-- **Harmonic-Doubling Plastic-Floor Theorem for `9 / 16 ≤ L ≤ 3 * screwSignThreshold`**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`9 / 16 ≤ L`, `L / 3 ≤ screwSignThreshold`),
the pair integral on `(2 * L / 3, 2 * screwSignThreshold)` upgrades the `(L / 3, screwSignThreshold)`
shell weight from `24 / 41` to `1`, yielding:
`(A(0) + (1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (13 / 42) * Φ(L / 3) + (1 / 2) * Φ(screwSignThreshold)) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem harmonic_doubling_plastic_floor_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL9_16 : 9 / 16 ≤ L) (hL3t : L / 3 ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (3 / 200) * levyCoshPotential (L / 7) +
        (1 / 45) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (13 / 42) * levyCoshPotential (L / 3) +
        (1 / 2) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL10 : 0 < L / 10 := by linarith
  have hL10t : L / 10 ≤ screwSignThreshold := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL10 hL10t le_rfl
  have hhd := tenth_to_third_harmonic_doubling_sub_levyCoshPotential_le_setIntegral_Ioo_add_pair
    hB hsupp hf0 hL9_16 hL3t
  linarith

/-- **Sharpened `(0, log 2)` Plastic-Floor Theorem with Harmonic-Doubling Pair Coupling**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 (Real.log 2)`, the universal constant
floor is boosted to
`A(0) + (1 / 25) * Φ((log 2)/10) + (1 / 50) * Φ((log 2)/8) + (3 / 200) * Φ((log 2)/7) + (1 / 45) * Φ((log 2)/6) + (13 / 360) * Φ((log 2)/5) + (2 / 35) * Φ((log 2)/4) + (13 / 42) * Φ((log 2)/3) + (1 / 2) * Φ(screwSignThreshold)`,
reducing the universal constant deficit on `(0, log 2)` from `-0.0138` down to **`-0.0100`**! -/
theorem harmonic_doubling_log_two_plastic_floor_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hsupp : ∀ u ∉ Ioo 0 (Real.log 2), f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (Real.log 2 / 10) +
        (1 / 50) * levyCoshPotential (Real.log 2 / 8) +
        (3 / 200) * levyCoshPotential (Real.log 2 / 7) +
        (1 / 45) * levyCoshPotential (Real.log 2 / 6) +
        (13 / 360) * levyCoshPotential (Real.log 2 / 5) +
        (2 / 35) * levyCoshPotential (Real.log 2 / 4) +
        (13 / 42) * levyCoshPotential (Real.log 2 / 3) +
        (1 / 2) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  harmonic_doubling_plastic_floor_le_weilArchRe hf hfc hf0
    (by linarith [Real.log_two_gt_d9])
    (by linarith [Real.log_two_lt_d9, screwSignThreshold_gt_6036_over_21509])
    hsupp

/-! ## Section 4: Hyperbolic Partial-Fraction Decomposition, Cubic-Upgraded Osculating Floor, and Unconditional `WindowPositive` on `(0, 4 / 9)` (`64.12%` of `(0, log 2)`) -/

/-- Quadratic lower bound `4 + y ^ 2 / 2 ≤ 4 * Real.cosh (y / 2)` for all `y ≥ 0`. -/
theorem four_add_half_sq_le_four_mul_cosh_half {y : ℝ} (hy : 0 ≤ y) :
    4 + y ^ 2 / 2 ≤ 4 * Real.cosh (y / 2) := by
  let g : ℝ → ℝ := fun u => 4 * Real.cosh (u / 2) - (4 + u ^ 2 / 2)
  have hderiv : ∀ u : ℝ, HasDerivAt g (2 * Real.sinh (u / 2) - u) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => 4 * Real.cosh (v / 2)) (2 * Real.sinh (u / 2)) u := by
      have h := ((hasDerivAt_id u).div_const (2 : ℝ)).cosh.const_mul (4 : ℝ)
      exact h.congr_deriv (by dsimp only [id_eq]; ring)
    have h2 : HasDerivAt (fun v : ℝ => 4 + v ^ 2 / 2) u u := by
      simpa using (((hasDerivAt_pow 2 u).div_const 2).const_add 4).congr_deriv (by ring)
    exact h1.sub h2
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun u _ => (hderiv u).continuousAt.continuousWithinAt
    · exact fun u _ => (hderiv u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hderiv u).deriv]
      have hu0 : 0 ≤ u := interior_subset hu
      linarith [four_mul_le_eight_mul_sinh_half hu0]
  have h0 : g 0 ≤ g y := hmono self_mem_Ici hy hy
  dsimp [g] at h0
  rw [zero_div, Real.cosh_zero] at h0
  linarith

/-- Cubic lower bound `4 * y + y ^ 3 / 6 ≤ 8 * Real.sinh (y / 2)` for all `y ≥ 0`. -/
theorem four_mul_add_sixth_cube_le_eight_mul_sinh_half {y : ℝ} (hy : 0 ≤ y) :
    4 * y + y ^ 3 / 6 ≤ 8 * Real.sinh (y / 2) := by
  let s : ℝ → ℝ := fun u => 8 * Real.sinh (u / 2) - (4 * u + u ^ 3 / 6)
  have hderiv : ∀ u : ℝ, HasDerivAt s (4 * Real.cosh (u / 2) - (4 + u ^ 2 / 2)) u := by
    intro u
    have h1 := hasDerivAt_eight_mul_sinh_half u
    have h2 : HasDerivAt (fun v : ℝ => 4 * v + v ^ 3 / 6) (4 + u ^ 2 / 2) u := by
      have ha : HasDerivAt (fun v : ℝ => 4 * v) 4 u := by
        simpa using (hasDerivAt_id u).const_mul (4 : ℝ)
      have hb : HasDerivAt (fun v : ℝ => v ^ 3 / 6) (u ^ 2 / 2) u := by
        simpa using ((hasDerivAt_pow 3 u).div_const 6).congr_deriv (by ring)
      exact ha.add hb
    exact h1.sub h2
  have hmono : MonotoneOn s (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun u _ => (hderiv u).continuousAt.continuousWithinAt
    · exact fun u _ => (hderiv u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hderiv u).deriv]
      have hu0 : 0 ≤ u := interior_subset hu
      linarith [four_add_half_sq_le_four_mul_cosh_half hu0]
  have h0 : s 0 ≤ s y := hmono self_mem_Ici hy hy
  dsimp [s] at h0
  rw [zero_div, Real.sinh_zero] at h0
  linarith

/-- **Cubic-Upgraded Osculating Lower Bound for `levyCoshPotential y` on `(0, ∞)`**:
for every `y > 0`,
`Real.log (4 / y) + Real.pi / 2 + (7 / 2) * y + y ^ 3 / 6 ≤ levyCoshPotential y`. -/
theorem osculating_add_sixth_cube_le_levyCoshPotential {y : ℝ} (hy : 0 < y) :
    Real.log (4 / y) + Real.pi / 2 + (7 / 2) * y + y ^ 3 / 6 ≤ levyCoshPotential y := by
  unfold levyCoshPotential
  have hsinh := four_mul_add_sixth_cube_le_eight_mul_sinh_half hy.le
  have hΩ := osculating_le_two_mul_archLevyAntideriv hy
  linarith

/-- **Cubic-Upgraded `(π / 2, log 2)` Cancellation for `EF.gammaBracket 0 + levyCoshPotential y`**:
for every `y > 0`,
`Real.log (1 / (2 * Real.pi * y)) + (7 / 2) * y + y ^ 3 / 6 - eulerMascheroniConstant ≤ EF.gammaBracket 0 + levyCoshPotential y`. -/
theorem log_inv_two_pi_add_seven_halves_add_sixth_cube_le_gammaBracket_add_levyCoshPotential
    {y : ℝ} (hy : 0 < y) :
    Real.log (1 / (2 * Real.pi * y)) + (7 / 2) * y + y ^ 3 / 6 - eulerMascheroniConstant ≤
      EF.gammaBracket 0 + levyCoshPotential y := by
  have hA : EF.gammaBracket 0 =
      -(Real.log Real.pi + 3 * Real.log 2 + eulerMascheroniConstant + Real.pi / 2) := by
    linarith [neg_gammaBracket_zero_eq]
  have hlog := log_inv_two_pi_mul_eq hy
  have hΦ := osculating_add_sixth_cube_le_levyCoshPotential hy
  linarith

/-- **Cubic-Upgraded Global Minimum Osculating Law**:
for every `c > 0`,
`Real.log (7 / (4 * Real.pi)) + 1 + c ^ 3 / 6 - eulerMascheroniConstant ≤ EF.gammaBracket 0 + levyCoshPotential c`. -/
theorem log_seven_div_four_pi_add_one_add_sixth_cube_le_gammaBracket_add_levyCoshPotential
    {c : ℝ} (hc : 0 < c) :
    Real.log (7 / (4 * Real.pi)) + 1 + c ^ 3 / 6 - eulerMascheroniConstant ≤
      EF.gammaBracket 0 + levyCoshPotential c := by
  have hmain := log_inv_two_pi_add_seven_halves_add_sixth_cube_le_gammaBracket_add_levyCoshPotential hc
  have hpos : 0 < (7 / 2 : ℝ) * c := by positivity
  have hlog : Real.log (7 / (4 * Real.pi)) =
      Real.log ((7 / 2 : ℝ) * c) + Real.log (1 / (2 * Real.pi * c)) := by
    rw [← Real.log_mul hpos.ne' (by positivity)]
    congr 1; field_simp; ring
  have hle := Real.log_le_sub_one_of_pos hpos
  linarith

/-- **Exact Hyperbolic Partial-Fraction Decomposition of `2 * archLevyDensity y` (`y > 0`)**:
`2 * archLevyDensity y = 1 / (2 * Real.sinh (y / 2)) + 1 / (2 * Real.cosh (y / 2))`. -/
theorem two_mul_archLevyDensity_eq_inv_sinh_add_inv_cosh {y : ℝ} (hy : 0 < y) :
    2 * archLevyDensity y = 1 / (2 * Real.sinh (y / 2)) + 1 / (2 * Real.cosh (y / 2)) := by
  set t := Real.exp (-y / 2)
  have ht_pos : 0 < t := Real.exp_pos _
  have ht_lt : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht2_lt : t ^ 2 < 1 := by nlinarith
  have ht4_lt : t ^ 4 < 1 := by nlinarith
  have hexp_mul : Real.exp (y / 2) * t = 1 := by
    dsimp only [t]; rw [← Real.exp_add]; convert Real.exp_zero; ring
  have hexp_neg : Real.exp (-(y / 2)) = t := by
    dsimp only [t]; congr 1; ring
  have hsinh_pos : 0 < 2 * Real.sinh (y / 2) :=
    mul_pos zero_lt_two (Real.sinh_pos_iff.mpr (by linarith))
  have hsinh_mul : 2 * Real.sinh (y / 2) * t = 1 - t ^ 2 := by
    rw [Real.sinh_eq, hexp_neg]
    linear_combination hexp_mul
  have hcosh_mul : 2 * Real.cosh (y / 2) * t = 1 + t ^ 2 := by
    rw [Real.cosh_eq, hexp_neg]
    linear_combination hexp_mul
  have hsinh_eq : 1 / (2 * Real.sinh (y / 2)) = t / (1 - t ^ 2) := by
    rw [div_eq_div_iff hsinh_pos.ne' (by linarith)]
    linarith [hsinh_mul]
  have hcosh_eq : 1 / (2 * Real.cosh (y / 2)) = t / (1 + t ^ 2) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linarith [hcosh_mul]
  have hlevy_eq : 2 * archLevyDensity y = 2 * t / (1 - t ^ 4) := by
    unfold archLevyDensity
    have h3 : Real.exp (-2 * y) = t ^ 4 := by
      dsimp only [t]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h3]; ring
  rw [hsinh_eq, hcosh_eq, hlevy_eq]
  have hd1 : 1 - t ^ 2 ≠ 0 := by linarith
  have hd2 : 1 + t ^ 2 ≠ 0 := by positivity
  have hd3 : 1 - t ^ 4 ≠ 0 := by linarith
  field_simp
  ring

/-- Global upper bound `2 * archLevyDensity y ≤ 1 / y + 1 / 2` for all `y > 0`. -/
theorem two_mul_archLevyDensity_le_inv_add_half {y : ℝ} (hy : 0 < y) :
    2 * archLevyDensity y ≤ 1 / y + 1 / 2 := by
  rw [two_mul_archLevyDensity_eq_inv_sinh_add_inv_cosh hy]
  have hsinh : y ≤ 2 * Real.sinh (y / 2) := by
    linarith [four_mul_le_eight_mul_sinh_half hy.le]
  have hcosh : (2 : ℝ) ≤ 2 * Real.cosh (y / 2) := by
    linarith [Real.one_le_cosh (y / 2)]
  have h1 : 1 / (2 * Real.sinh (y / 2)) ≤ 1 / y :=
    one_div_le_one_div_of_le hy hsinh
  have h2 : 1 / (2 * Real.cosh (y / 2)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le two_pos hcosh
  linarith

/-- Global pointwise derivative lower bound for `levyCoshPotential`:
for every `y > 0`, `7 / 2 - 1 / y + y ^ 2 / 2 ≤ 2 * screwRegularKernel y`. -/
theorem seven_halves_sub_inv_add_half_sq_le_two_mul_screwRegularKernel {y : ℝ} (hy : 0 < y) :
    (7 / 2 : ℝ) - 1 / y + y ^ 2 / 2 ≤ 2 * screwRegularKernel y := by
  rw [screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity hy]
  have hcosh := four_add_half_sq_le_four_mul_cosh_half hy.le
  have hlevy := two_mul_archLevyDensity_le_inv_add_half hy
  linarith

/-- **Monotonicity of `levyCoshPotential y - (log(4 / y) + π / 2 + (7 / 2) * y + y ^ 3 / 6)`**:
for any `0 < a ≤ b`,
`Real.log (a / b) + (7 / 2) * (b - a) + (b ^ 3 - a ^ 3) / 6 ≤ levyCoshPotential b - levyCoshPotential a`. -/
theorem log_div_add_seven_halves_add_sixth_cube_le_sub_levyCoshPotential
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (a / b) + (7 / 2 : ℝ) * (b - a) + (b ^ 3 - a ^ 3) / 6 ≤
      levyCoshPotential b - levyCoshPotential a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  let Φ_osc : ℝ → ℝ := fun y => -Real.log y + (7 / 2 : ℝ) * y + y ^ 3 / 6
  have hderiv : ∀ y ∈ uIcc a b,
      HasDerivAt (fun u => levyCoshPotential u - Φ_osc u)
        (2 * screwRegularKernel y - ((7 / 2 : ℝ) - 1 / y + y ^ 2 / 2)) y := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have h1 := hasDerivAt_levyCoshPotential hy0
    have h2 : HasDerivAt Φ_osc ((7 / 2 : ℝ) - 1 / y + y ^ 2 / 2) y := by
      have ha' : HasDerivAt (fun u : ℝ => -Real.log u) (-y⁻¹) y := (Real.hasDerivAt_log hy0.ne').neg
      have hb' : HasDerivAt (fun u : ℝ => (7 / 2 : ℝ) * u) (7 / 2) y := by
        simpa using (hasDerivAt_id y).const_mul (7 / 2 : ℝ)
      have hc' : HasDerivAt (fun u : ℝ => u ^ 3 / 6) (y ^ 2 / 2) y := by
        simpa using ((hasDerivAt_pow 3 y).div_const 6).congr_deriv (by ring)
      exact ((ha'.add hb').add hc').congr_deriv (by rw [one_div]; ring)
    exact h1.sub h2
  have hcont : ContinuousOn (fun y => 2 * screwRegularKernel y - ((7 / 2 : ℝ) - 1 / y + y ^ 2 / 2))
      (uIcc a b) := by
    rw [uIcc_of_le hab]
    refine (continuousOn_const.mul (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun y hy => lt_of_lt_of_le ha hy.1)).sub ?_
    refine (continuousOn_const.sub (continuousOn_const.div continuousOn_id fun y hy =>
      (lt_of_lt_of_le ha hy.1).ne')).add (by fun_prop)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hnn : 0 ≤ ∫ y in a..b, (2 * screwRegularKernel y - ((7 / 2 : ℝ) - 1 / y + y ^ 2 / 2)) := by
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_nonneg measurableSet_Ioc fun y hy => ?_
    have hy0 : 0 < y := lt_trans ha hy.1
    linarith [seven_halves_sub_inv_add_half_sq_le_two_mul_screwRegularKernel hy0]
  rw [hFTC] at hnn
  dsimp only [Φ_osc] at hnn
  have hlog : Real.log (a / b) = Real.log a - Real.log b :=
    Real.log_div ha.ne' hb.ne'
  linarith

/-- **Harmonic-Doubling Excess Bound on `Ioo a (3 / 16)` (`L / 3 ≤ a ≤ 3 / 16`, `screwSignThreshold ≤ 2 * a`)**:
retaining `(24 / 41)` coercivity on the positive kernel excess `(-K(x)) - (19 / 20) * (2 * K(2x)) ≥ 0`
and full `1` harmonic-doubling coercivity on `(19 / 20) * (2 * K(2x)) ≥ 0` proves:
`((12 / 41) * (Φ(a) - Φ(3 / 16)) + (323 / 1640) * (Φ(3 / 8) - Φ(2 * a))) * ∫ h²`
`≤ (∫_{x ∈ Ioo a (3 / 16)} (-K(x)) D_h(x)) + ∫_{x ∈ Ioo a (3 / 16)} (2 K(2x)) (2 R(2x))`. -/
theorem harmonic_doubling_below_three_sixteenths_le_setIntegral_Ioo_add_double_autocorr
    {A : Set ℝ} {h : ℝ → ℝ} {C L a : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u) (hL : 0 < L)
    (ha3 : L / 3 ≤ a) (ha16 : a ≤ 3 / 16) (hta : screwSignThreshold ≤ 2 * a) :
    ((12 / 41 : ℝ) * (levyCoshPotential a - levyCoshPotential (3 / 16)) +
        (323 / 1640 : ℝ) * (levyCoshPotential (3 / 8) - levyCoshPotential (2 * a))) *
        (∫ u, h u ^ 2) ≤
      (∫ x in Ioo a (3 / 16), (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ x in Ioo a (3 / 16), (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x)) := by
  have ha0 : 0 < a := by linarith
  have h16_t : (3 : ℝ) / 16 ≤ screwSignThreshold := by
    linarith [screwSignThreshold_gt_6036_over_21509]
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  have hR0 : ∀ x, 0 ≤ 2 * autocorr h (2 * x) :=
    fun x => mul_nonneg zero_le_two (autocorr_nonneg hh hh0 (2 * x))
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc a (3 / 16)) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le ha0 hx.1).neg
  have hI_K : IntegrableOn (fun x => -screwRegularKernel x) (Ioo a (3 / 16)) :=
    hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hDm := measurable_jump hh
  have hI_jump : IntegrableOn
      (fun x : ℝ => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) (Ioo a (3 / 16)) := by
    refine (hI_K.mul_const (4 * ∫ u, h u ^ 2)).mono' (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans h16_t))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hcont_K2 : ContinuousOn (fun x => 2 * screwRegularKernel (2 * x)) (Icc a (3 / 16)) :=
    continuousOn_two_mul_screwRegularKernel_two_mul ha0
  have hI_K2 : IntegrableOn (fun x => 2 * screwRegularKernel (2 * x)) (Ioo a (3 / 16)) :=
    hcont_K2.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hK2m : Measurable fun x : ℝ => 2 * screwRegularKernel (2 * x) := by
    unfold screwRegularKernel; fun_prop
  have hR2m : Measurable fun x : ℝ => 2 * autocorr h (2 * x) :=
    measurable_two_mul_autocorr_two_mul hh
  have hI_auto : IntegrableOn
      (fun x : ℝ => (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))) (Ioo a (3 / 16)) := by
    refine (hI_K2.mul_const (2 * ∫ u, h u ^ 2)).mono' (hK2m.mul hR2m).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK2_0 : 0 ≤ 2 * screwRegularKernel (2 * x) :=
      mul_nonneg zero_le_two (screwRegularKernel_nonneg_of_threshold_le
        (hta.trans (by linarith [hx.1])))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK2_0 (hR0 x))]
    have hR_le : 2 * autocorr h (2 * x) ≤ 2 * ∫ u, h u ^ 2 := by
      have hid := integral_jump_sq hh (2 * x)
      have hD_nn := hD0 (2 * x)
      linarith
    exact mul_le_mul_of_nonneg_left hR_le hK2_0
  let G : ℝ → ℝ := fun x =>
    ((24 / 41 : ℝ) * (-screwRegularKernel x) +
      (323 / 820 : ℝ) * (2 * screwRegularKernel (2 * x))) * ∫ u, h u ^ 2
  have hI_G : IntegrableOn G (Ioo a (3 / 16)) :=
    ((hI_K.const_mul (24 / 41 : ℝ)).add (hI_K2.const_mul (323 / 820 : ℝ))).mul_const _
  have hmono : (∫ x in Ioo a (3 / 16), G x) ≤
      ∫ x in Ioo a (3 / 16), ((-screwRegularKernel x) * (∫ u, (h u - h (u + x)) ^ 2) +
        (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))) := by
    refine setIntegral_mono_on hI_G (hI_jump.add hI_auto) measurableSet_Ioo fun x hx => ?_
    dsimp only [G]
    have hx0 : 0 < x := lt_trans ha0 hx.1
    have hK2_0 : 0 ≤ 2 * screwRegularKernel (2 * x) :=
      mul_nonneg zero_le_two (screwRegularKernel_nonneg_of_threshold_le
        (hta.trans (by linarith [hx.1])))
    have hexcess : 0 ≤ (-screwRegularKernel x) - (19 / 20 : ℝ) * (2 * screwRegularKernel (2 * x)) := by
      linarith [nineteen_twentieths_mul_two_mul_screwRegularKernel_two_mul_le_neg_screwRegularKernel
        hx0 hx.2.le]
    have h3_coerc := twenty_four_forty_firsts_mul_integral_sq_le_integral_jump_sq_of_third_le
      hh hsupp hL.le (ha3.trans hx.1.le)
    have hhd := integral_sq_le_integral_jump_sq_add_two_mul_autocorr_two_mul_of_third_le
      hh hsupp hL.le (ha3.trans hx.1.le)
    have hm1 := mul_le_mul_of_nonneg_left h3_coerc hexcess
    have hm2 := mul_le_mul_of_nonneg_left hhd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 19 / 20) hK2_0)
    have hm3 : (19 / 20 : ℝ) * (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x)) ≤
        (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x)) := by
      nlinarith [hR0 x]
    linarith
  have hval_G : (∫ x in Ioo a (3 / 16), G x) =
      ((12 / 41 : ℝ) * (levyCoshPotential a - levyCoshPotential (3 / 16)) +
        (323 / 1640 : ℝ) * (levyCoshPotential (3 / 8) - levyCoshPotential (2 * a))) *
        ∫ u, h u ^ 2 := by
    dsimp only [G]
    rw [integral_mul_const,
      integral_add (hI_K.const_mul _) (hI_K2.const_mul _),
      integral_const_mul, integral_const_mul,
      setIntegral_Ioo_neg_screwRegularKernel ha0 ha16,
      setIntegral_Ioo_two_mul_screwRegularKernel_two_mul ha0 ha16,
      show (2 : ℝ) * (3 / 16) = 3 / 8 by norm_num]
    ring
  rw [hval_G, integral_add hI_jump hI_auto] at hmono
  linarith

/-- **Split Harmonic-Doubling Potential + Pair Bound on `Ioo (L / 3) screwSignThreshold` (`3 / 2 * screwSignThreshold ≤ L ≤ 9 / 16`)**:
splitting `Ioo (L / 3) screwSignThreshold` at `b₀ = 3 / 16` combines
`harmonic_doubling_below_three_sixteenths_le_setIntegral_Ioo_add_double_autocorr` on `Ioo (L / 3) (3 / 16)`
with `half_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_double_autocorr` on `Ioo (3 / 16) screwSignThreshold`,
and absorbs the combined double-autocorrelation integral on `Ioo (L / 3) screwSignThreshold` into
`pair_{screwSignThreshold}(h)`! -/
theorem split_harmonic_doubling_third_to_threshold_le_setIntegral_Ioo_add_pair
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u)
    (hL_low : 3 * screwSignThreshold / 2 ≤ L) (hL_high : L ≤ 9 / 16) :
    ((12 / 41 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 82 : ℝ) * levyCoshPotential (3 / 16) +
        (323 / 1640 : ℝ) * (levyCoshPotential (3 / 8) - levyCoshPotential (2 * L / 3)) -
        (1 / 2 : ℝ) * levyCoshPotential screwSignThreshold) * (∫ u, h u ^ 2) ≤
      (∫ x in Ioo (L / 3) screwSignThreshold,
        (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ p : ℝ × ℝ, h p.1 * h p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity [screwSignThreshold_pos]) hL_low
  have hL3_pos : 0 < L / 3 := by linarith
  have hL3_16 : L / 3 ≤ 3 / 16 := by linarith
  have h16_t : (3 : ℝ) / 16 ≤ screwSignThreshold := by
    linarith [screwSignThreshold_gt_6036_over_21509]
  have hL3_t : L / 3 ≤ screwSignThreshold := le_trans hL3_16 h16_t
  have ht_2L3 : screwSignThreshold ≤ 2 * (L / 3) := by linarith
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  have hR0 : ∀ x, 0 ≤ 2 * autocorr h (2 * x) :=
    fun x => mul_nonneg zero_le_two (autocorr_nonneg hh hh0 (2 * x))
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 3) screwSignThreshold) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL3_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 3) screwSignThreshold) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL3_pos hx.1) hx.2.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_left_Ioc : IntegrableOn F (Ioc (L / 3) (3 / 16)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl h16_t)
  have hIF_right_Ioc : IntegrableOn F (Ioc (3 / 16) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL3_16 le_rfl)
  have hdisj : Disjoint (Ioc (L / 3) (3 / 16)) (Ioc (3 / 16) screwSignThreshold) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit_F : (∫ x in Ioo (L / 3) screwSignThreshold, F x) =
      (∫ x in Ioo (L / 3) (3 / 16), F x) + ∫ x in Ioo (3 / 16) screwSignThreshold, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL3_16 h16_t,
      setIntegral_union hdisj measurableSet_Ioc hIF_left_Ioc hIF_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  let H : ℝ → ℝ := fun x => (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))
  have hK2m : Measurable fun x : ℝ => 2 * screwRegularKernel (2 * x) := by
    unfold screwRegularKernel; fun_prop
  have hR2m : Measurable fun x : ℝ => 2 * autocorr h (2 * x) :=
    measurable_two_mul_autocorr_two_mul hh
  have hHm : Measurable H := hK2m.mul hR2m
  have hcont_K2 : ContinuousOn (fun x => 2 * screwRegularKernel (2 * x))
      (Icc (L / 3) screwSignThreshold) :=
    continuousOn_two_mul_screwRegularKernel_two_mul hL3_pos
  have hIH : IntegrableOn H (Ioo (L / 3) screwSignThreshold) := by
    refine ((hcont_K2.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (2 * ∫ u, h u ^ 2)).mono' hHm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK2_0 : 0 ≤ 2 * screwRegularKernel (2 * x) :=
      mul_nonneg zero_le_two (screwRegularKernel_nonneg_of_threshold_le
        (ht_2L3.trans (by linarith [hx.1])))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK2_0 (hR0 x))]
    have hR_le : 2 * autocorr h (2 * x) ≤ 2 * ∫ u, h u ^ 2 := by
      have hid := integral_jump_sq hh (2 * x)
      have hD_nn := hD0 (2 * x)
      linarith
    exact mul_le_mul_of_nonneg_left hR_le hK2_0
  have hIH_left_Ioc : IntegrableOn H (Ioc (L / 3) (3 / 16)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIH.mono_set (Ioo_subset_Ioo le_rfl h16_t)
  have hIH_right_Ioc : IntegrableOn H (Ioc (3 / 16) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIH.mono_set (Ioo_subset_Ioo hL3_16 le_rfl)
  have hsplit_H : (∫ x in Ioo (L / 3) screwSignThreshold, H x) =
      (∫ x in Ioo (L / 3) (3 / 16), H x) + ∫ x in Ioo (3 / 16) screwSignThreshold, H x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL3_16 h16_t,
      setIntegral_union hdisj measurableSet_Ioc hIH_left_Ioc hIH_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have hleft := harmonic_doubling_below_three_sixteenths_le_setIntegral_Ioo_add_double_autocorr
    hh hsupp hh0 hL0 le_rfl hL3_16 ht_2L3
  have hright := half_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_double_autocorr
    hh hsupp hh0 hL0 le_rfl hL3_16 h16_t le_rfl
  have hpair := setIntegral_Ioo_two_mul_screwRegularKernel_two_mul_autocorr_le_pair
    hh hsupp hh0 hL0 le_rfl ht_2L3 hL3_t
  dsimp only [F] at hsplit_F
  dsimp only [H] at hsplit_H
  rw [show 2 * (L / 3) = 2 * L / 3 by ring] at hleft
  linarith

/-- **Full Nine-Point Split Harmonic-Doubling Potential + Pair Coercivity on `Ioo (L / 10) screwSignThreshold`**:
for `3 * screwSignThreshold / 2 ≤ L ≤ 9 / 16`, combining `(L / 10, L / 4)`, `(L / 4, L / 3)`,
and `(L / 3, screwSignThreshold)` yields:
`((1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 82) * Φ(3 / 16) + (323 / 1640) * (Φ(3 / 8) - Φ(2 * L / 3)) - (1 / 2) * Φ(screwSignThreshold)) * ∫ h² ≤ (∫_{x ∈ Ioo (L / 10) t_*} (-K(x)) D_h(x)) + pair_{t_*}(h)`. -/
theorem split_harmonic_doubling_tenth_to_threshold_le_setIntegral_Ioo_add_pair
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u)
    (hL_low : 3 * screwSignThreshold / 2 ≤ L) (hL_high : L ≤ 9 / 16) :
    ((1 / 25 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (3 / 200 : ℝ) * levyCoshPotential (L / 7) +
        (1 / 45 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (2 / 35 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 82 : ℝ) * levyCoshPotential (3 / 16) +
        (323 / 1640 : ℝ) * (levyCoshPotential (3 / 8) - levyCoshPotential (2 * L / 3)) -
        (1 / 2 : ℝ) * levyCoshPotential screwSignThreshold) * (∫ u, h u ^ 2) ≤
      (∫ x in Ioo (L / 10) screwSignThreshold,
        (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ p : ℝ × ℝ, h p.1 * h p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity [screwSignThreshold_pos]) hL_low
  have hL10_pos : 0 < L / 10 := by linarith
  have hL10_4 : L / 10 ≤ L / 4 := by linarith
  have hL5_4 : L / 5 ≤ L / 4 := by linarith
  have hL4_3 : L / 4 ≤ L / 3 := by linarith
  have hL3_t : L / 3 ≤ screwSignThreshold := by
    linarith [screwSignThreshold_gt_6036_over_21509]
  have hL4_t : L / 4 ≤ screwSignThreshold := le_trans hL4_3 hL3_t
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 10) screwSignThreshold) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL10_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 10) screwSignThreshold) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL10_pos hx.1) hx.2.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_1_Ioc : IntegrableOn F (Ioc (L / 10) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL4_t)
  have hIF_2_Ioc : IntegrableOn F (Ioc (L / 4) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL10_4 hL3_t)
  have hIF_3_Ioc : IntegrableOn F (Ioc (L / 3) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo (hL10_4.trans hL4_3) le_rfl)
  have hIF_12_Ioc : IntegrableOn F (Ioc (L / 10) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL3_t)
  have hdisj_12 : Disjoint (Ioc (L / 10) (L / 4)) (Ioc (L / 4) (L / 3)) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_123 : Disjoint (Ioc (L / 10) (L / 3)) (Ioc (L / 3) screwSignThreshold) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 10) screwSignThreshold, F x) =
      (∫ x in Ioo (L / 10) (L / 4), F x) + (∫ x in Ioo (L / 4) (L / 3), F x) +
        ∫ x in Ioo (L / 3) screwSignThreshold, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (hL10_4.trans hL4_3) hL3_t,
      setIntegral_union hdisj_123 measurableSet_Ioc hIF_12_Ioc hIF_3_Ioc,
      ← Ioc_union_Ioc_eq_Ioc hL10_4 hL4_3,
      setIntegral_union hdisj_12 measurableSet_Ioc hIF_1_Ioc hIF_2_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h105 := tenth_to_fifth_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL5_4 hL4_t
  have h4 := four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL4_3 hL3_t
  have h3 := split_harmonic_doubling_third_to_threshold_le_setIntegral_Ioo_add_pair
    hh hsupp hh0 hL_low hL_high
  dsimp only [F] at hsplit
  linarith

/-- **Split Harmonic-Doubling Lévy–Cosh Crossover Lower Bound for `weilArchRe` (`3 / 2 * screwSignThreshold ≤ L ≤ 9 / 16`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L`,
`(A(0) + (1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 82) * Φ(3 / 16) + (323 / 1640) * (Φ(3 / 8) - Φ(2 * L / 3)) + (1 / 2) * Φ(screwSignThreshold)) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem split_harmonic_doubling_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL_low : 3 * screwSignThreshold / 2 ≤ L) (hL_high : L ≤ 9 / 16)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (3 / 200) * levyCoshPotential (L / 7) +
        (1 / 45) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (17 / 82) * levyCoshPotential (3 / 16) +
        (323 / 1640) * (levyCoshPotential (3 / 8) - levyCoshPotential (2 * L / 3)) +
        (1 / 2) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity [screwSignThreshold_pos]) hL_low
  have hL10 : 0 < L / 10 := by linarith
  have hL10t : L / 10 ≤ screwSignThreshold := by
    linarith [screwSignThreshold_gt_6036_over_21509]
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL10 hL10t le_rfl
  have hsplit := split_harmonic_doubling_tenth_to_threshold_le_setIntegral_Ioo_add_pair
    hB hsupp hf0 hL_low hL_high
  linarith

/-- Exact 5-smooth factorization of `log(1 / (π * (4 / 9)))` via
`1 / (π * (4 / 9)) = (5 / 4) / ((4 / 3)^2 * (5 * π / 16))` and `log(5 * π / 16) ≤ 5 * π / 16 - 1`:
`Real.log (5 / 4) - 2 * Real.log (4 / 3) + 1 - 5 * Real.pi / 16 ≤ Real.log (1 / (Real.pi * (4 / 9)))`. -/
theorem log_inv_pi_mul_four_ninths_ge :
    Real.log (5 / 4) - 2 * Real.log (4 / 3) + 1 - 5 * Real.pi / 16 ≤
      Real.log (1 / (Real.pi * (4 / 9))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsplit : Real.log (1 / (Real.pi * (4 / 9))) + 2 * Real.log (4 / 3) +
      Real.log (5 * Real.pi / 16) = Real.log (5 / 4) := by
    have h43 : 2 * Real.log (4 / 3) = Real.log (16 / 9) := by
      rw [show (16 / 9 : ℝ) = (4 / 3) ^ 2 by norm_num, Real.log_pow]; ring
    rw [h43, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  have hpi_log : Real.log (5 * Real.pi / 16) ≤ 5 * Real.pi / 16 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  linarith

/-- Exact 5-smooth decomposition `Real.log (7 / 6) = Real.log (4 / 3) - Real.log (5 / 4) + Real.log (35 / 32)`
from `7 / 6 = (4 / 3) / (5 / 4) * (35 / 32)`. -/
theorem log_seven_sixths_eq :
    Real.log (7 / 6 : ℝ) = Real.log (4 / 3) - Real.log (5 / 4) + Real.log (35 / 32) := by
  rw [← Real.log_div (by norm_num) (by norm_num),
    ← Real.log_mul (by norm_num) (by norm_num)]
  congr 1; norm_num

/-- **Cubic-Upgraded Osculating Lower Bound for the Split Harmonic-Doubling Potential at `L = 4 / 9`**:
every logarithm at `L = 4 / 9` factors into `log 2`, `log(4 / 3)`, `log(5 / 4)`, and `log(7 / 6)`. -/
theorem osculating_le_split_harmonic_doubling_potential_four_ninths :
    Real.log (1 / (Real.pi * (4 / 9))) - (10499 / 14760 : ℝ) * Real.log 2 +
        (914551 / 516600 : ℝ) * Real.log (4 / 3) +
        (137 / 1800 : ℝ) * Real.log (5 / 4) +
        (103 / 200 : ℝ) * Real.log (7 / 6) +
        (126882907 / 159408000 : ℝ) +
        (86982931 / 99164528640 : ℝ) +
        (17 / 82 : ℝ) * ((3 / 16 : ℝ) ^ 3 / 6) +
        (1 / 2 : ℝ) * (screwSignThreshold ^ 3 / 6) -
        eulerMascheroniConstant ≤
      EF.gammaBracket 0 + (1 / 25) * levyCoshPotential ((4 / 9 : ℝ) / 10) +
        (1 / 50) * levyCoshPotential ((4 / 9 : ℝ) / 8) +
        (3 / 200) * levyCoshPotential ((4 / 9 : ℝ) / 7) +
        (1 / 45) * levyCoshPotential ((4 / 9 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((4 / 9 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((4 / 9 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((4 / 9 : ℝ) / 3) +
        (17 / 82) * levyCoshPotential (3 / 16) +
        (323 / 1640) * (levyCoshPotential (3 / 8) - levyCoshPotential (2 * (4 / 9 : ℝ) / 3)) +
        (1 / 2) * levyCoshPotential screwSignThreshold := by
  let L : ℝ := 4 / 9
  have hL : 0 < L := by norm_num
  have h10 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 10)
  have h8 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 8)
  have h7 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 7)
  have h6 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 6)
  have h5 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 5)
  have h4 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 4)
  have h3 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 3)
  have hb0 := log_inv_two_pi_add_seven_halves_add_sixth_cube_le_gammaBracket_add_levyCoshPotential
    (by norm_num : (0 : ℝ) < 3 / 16)
  have hc := log_seven_div_four_pi_add_one_add_sixth_cube_le_gammaBracket_add_levyCoshPotential
    screwSignThreshold_pos
  have hhd := log_div_add_seven_halves_add_sixth_cube_le_sub_levyCoshPotential
    (by linarith : 0 < 2 * L / 3) (by norm_num : 2 * L / 3 ≤ 3 / 8)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog3 : Real.log 3 = 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [Real.log_div (by norm_num) (by norm_num), hlog4]; ring
  have hlog10 : Real.log (1 / (2 * Real.pi * (L / 10))) =
      Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 + Real.log (5 / 4) := by
    rw [← hlog4, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog8 : Real.log (1 / (2 * Real.pi * (L / 8))) =
      Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 := by
    rw [← hlog4, ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog7 : Real.log (1 / (2 * Real.pi * (L / 7))) =
      Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 - Real.log (4 / 3) + Real.log (7 / 6) := by
    rw [show Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 - Real.log (4 / 3) + Real.log (7 / 6) =
        Real.log (1 / (Real.pi * L)) + Real.log 3 + Real.log (7 / 6) by linarith [hlog3],
      ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog6 : Real.log (1 / (2 * Real.pi * (L / 6))) =
      Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [show Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 - Real.log (4 / 3) =
        Real.log (1 / (Real.pi * L)) + Real.log 3 by linarith [hlog3],
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog5 : Real.log (1 / (2 * Real.pi * (L / 5))) =
      Real.log (1 / (Real.pi * L)) + Real.log 2 + Real.log (5 / 4) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog4_pt : Real.log (1 / (2 * Real.pi * (L / 4))) =
      Real.log (1 / (Real.pi * L)) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog3_pt : Real.log (1 / (2 * Real.pi * (L / 3))) =
      Real.log (1 / (Real.pi * L)) + Real.log 2 - Real.log (4 / 3) := by
    rw [eq_sub_iff_add_eq, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog_b0 : Real.log (1 / (2 * Real.pi * (3 / 16))) =
      Real.log (1 / (Real.pi * L)) - Real.log 2 + 3 * Real.log (4 / 3) := by
    have h64_27 : 3 * Real.log (4 / 3) = Real.log (64 / 27) := by
      rw [show (64 / 27 : ℝ) = (4 / 3) ^ 3 by norm_num, Real.log_pow]; ring
    rw [h64_27, ← Real.log_div (by positivity) (by norm_num),
      ← Real.log_mul (by positivity) (by norm_num)]
    congr 1; field_simp [L]; ring
  have hlog_c : Real.log (7 / (4 * Real.pi)) =
      Real.log (1 / (Real.pi * L)) - Real.log 2 + Real.log (4 / 3) + Real.log (7 / 6) := by
    rw [← Real.log_div (by positivity) (by norm_num),
      ← Real.log_mul (by positivity) (by norm_num),
      ← Real.log_mul (by positivity) (by norm_num)]
    congr 1; field_simp [L]; ring
  have hlog_hd : Real.log ((2 * L / 3) / (3 / 8)) =
      4 * Real.log (4 / 3) - 2 * Real.log 2 := by
    have h256_81 : 4 * Real.log (4 / 3) = Real.log (256 / 81) := by
      rw [show (256 / 81 : ℝ) = (4 / 3) ^ 4 by norm_num, Real.log_pow]; ring
    rw [h256_81, ← hlog4, ← Real.log_div (by norm_num) (by norm_num)]
    congr 1; norm_num [L]
  linarith

/-- **Strict Positivity of the Split Harmonic-Doubling Potential at `L = 4 / 9` (`≈ 0.444444`, `64.12%` of `(0, log 2)`)**:
certified rational margin `+0.000405 > 0`. -/
theorem zero_le_split_harmonic_doubling_potential_four_ninths :
    0 ≤ EF.gammaBracket 0 + (1 / 25) * levyCoshPotential ((4 / 9 : ℝ) / 10) +
        (1 / 50) * levyCoshPotential ((4 / 9 : ℝ) / 8) +
        (3 / 200) * levyCoshPotential ((4 / 9 : ℝ) / 7) +
        (1 / 45) * levyCoshPotential ((4 / 9 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((4 / 9 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((4 / 9 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((4 / 9 : ℝ) / 3) +
        (17 / 82) * levyCoshPotential (3 / 16) +
        (323 / 1640) * (levyCoshPotential (3 / 8) - levyCoshPotential (2 * (4 / 9 : ℝ) / 3)) +
        (1 / 2) * levyCoshPotential screwSignThreshold := by
  have hosc := osculating_le_split_harmonic_doubling_potential_four_ninths
  have hlog_pi := log_inv_pi_mul_four_ninths_ge
  have hlog76 := log_seven_sixths_eq
  have hlog2_lt := Real.log_two_lt_d9
  have hlog5 := Real.log_five_gt_d9
  have hlog54 := log_five_sub_two_mul_log_two_eq_log_five_fourths
  have hlog43 := log_five_sub_two_mul_log_two_add_two_thirty_firsts_lt_log_four_thirds
  have hlog35 := six_sixty_sevenths_lt_log_35_32
  have hc_cub : ((6036 : ℝ) / 21509) ^ 3 ≤ screwSignThreshold ^ 3 :=
    pow_le_pow_left₀ (by norm_num) screwSignThreshold_gt_6036_over_21509.le 3
  have hpi := Real.pi_lt_d4
  have hgamma :=
    RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith

/-- **Unconditional Archimedean Weil Positivity on `(0, 4 / 9)` (`≈ (0, 0.444444)`, `64.12%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` supported in `Ioo 0 L` with `L ≤ 4 / 9`,
`0 ≤ WeilOneSided.weilArchRe (EF.weilTest f f)`. -/
theorem weilArchRe_nonneg_of_support_Ioo_le_four_ninths {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL : L ≤ 4 / 9) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_4_9 : ∀ u ∉ Ioo (0 : ℝ) (4 / 9), f u = 0 :=
    fun u hu => hsupp u fun huL => hu ⟨huL.1, huL.2.trans_le hL⟩
  have hmain := split_harmonic_doubling_levyCosh_crossover_le_weilArchRe
    hf hfc hf0
    (by linarith [screwSignThreshold_lt_thirty_eight_over_one_thirty_five] :
      3 * screwSignThreshold / 2 ≤ 4 / 9)
    (by norm_num : (4 / 9 : ℝ) ≤ 9 / 16)
    hsupp_4_9
  have hpot := zero_le_split_harmonic_doubling_potential_four_ninths
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact le_trans (mul_nonneg hpot hsq) hmain

/-- **Unconditional `WindowPositive` on `(0, 4 / 9)` (`≈ (0, 0.444444)`, `64.12%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (4 / 9)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_four_ninths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (4 / 9)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_four_ninths hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 11 / 25)` (`= (0, 0.44)`, `63.48%` of `(0, log 2)`)**:
immediate corollary since `11 / 25 ≤ 4 / 9` (`99 ≤ 100`). -/
theorem windowPositive_eleven_twenty_fifths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (11 / 25)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_four_ninths hf hfc hf0 (by norm_num : (11 : ℝ) / 25 ≤ 4 / 9)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 7 / 16)` (`= (0, 0.4375)`, `63.12%` of `(0, log 2)`)**:
immediate corollary since `7 / 16 ≤ 4 / 9` (`63 ≤ 64`). -/
theorem windowPositive_seven_sixteenths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (7 / 16)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_four_ninths hf hfc hf0 (by norm_num : (7 : ℝ) / 16 ≤ 4 / 9)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 3 / 7)` (`≈ (0, 0.428571)`, `61.83%` of `(0, log 2)`)**:
immediate corollary since `3 / 7 ≤ 4 / 9` (`27 ≤ 28`). -/
theorem windowPositive_three_sevenths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (3 / 7)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_four_ninths hf hfc hf0 (by norm_num : (3 : ℝ) / 7 ≤ 4 / 9)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

end

end RHTower.WeilLevyHarmonicDoubling
