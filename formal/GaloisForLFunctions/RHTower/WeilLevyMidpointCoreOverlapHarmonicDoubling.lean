import GaloisForLFunctions.RHTower.WeilLevyHarmonicDoublingPairCoupling

/-!
# Midpoint Core-Overlap Reflection, Universal Weighted Harmonic Doubling, Fourth-Order Osculating Floor, and Unconditional Positivity on `(0, 9 / 20)`

This module implements **Cycle 77** of the prime-blind archimedean Weil positivity programme,
advancing both the universal $L^2(\mathbb R)$ coercivity theory and the hyperbolic partial-fraction
osculating floor to reach unconditional `WindowPositive` on **`(0, 9 / 20)` (`= (0, 0.45)`, `64.92%` of `(0, log 2)`)**:

## Mathematical Architecture

1. **Section 1 — Exact Upper-Half Core-Overlap Bound (`y = L - x ≥ L / 2`) & Universal Midpoint Reflection (`2 ∫ h² ≤ D_h(x) + D_h(L - x)`)**:
   - For any signed `BddSupp A h C` vanishing outside `Ioo 0 L` and any $x \in [0, L / 2]$, the
     reflected shift $y = L - x \ge L / 2$ has overlap domain $\mathrm{Ioc}\,0\,(L - y) = \mathrm{Ioc}\,0\,x$,
     so $2\,\mathrm{autocorr}\ h\ (L - x) \le \mathrm{collarMass}\ h\ L\ x$.
   - Combining $D_h(L - x) = 2\int h^2 - 2\,\mathrm{autocorr}\ h\ (L - x)$ with
     $\mathrm{collarMass}\ h\ L\ x + \mathrm{coreMass}\ h\ L\ x = \int h^2$ proves the exact
     upper-half core-overlap inequality:
     $$\left(\int_{\mathbb R} h(u)^2\,du\right) + \mathrm{coreMass}\ h\ L\ x \le \int_{\mathbb R} \bigl(h(u) - h(u + (L - x))\bigr)^2\,du.$$
   - Adding $\mathrm{collarMass}\ h\ L\ x \le D_h(x)$ yields the **sharp universal midpoint reflection theorem**
     for **all** $x \in [0, L / 2]$:
     $$2\int_{\mathbb R} h(u)^2\,du \le \left(\int_{\mathbb R} \bigl(h(u) - h(u + x)\bigr)^2\,du\right) + \left(\int_{\mathbb R} \bigl(h(u) - h(u + (L - x))\bigr)^2\,du\right),$$
     upgrading the reflected sum across $[0, L / 2]$ to the exact constant **`2`**.

2. **Section 2 — Universal Single-Square `L²(ℝ)` Weighted Harmonic-Doubling Family (No Support Restriction)**:
   - From the single-square identity
     $$(p - 2\alpha q + r)^2 = (1 - 2\alpha) p^2 + (4\alpha^2 - 4\alpha) q^2 + (1 - 2\alpha) r^2 + 2\alpha (p - q)^2 + 2\alpha (q - r)^2 + 2 p r \ge 0,$$
     integrating $p = h(u)$, $q = h(u + x)$, $r = h(u + 2x)$ over all $u \in \mathbb R$ proves for
     **every** `BddSupp A h C` (with no support restriction!) and every $x, \alpha \in \mathbb R$:
     $$\bigl(8\alpha - 2 - 4\alpha^2\bigr)\int_{\mathbb R} h(u)^2\,du \le 4\alpha\left(\int_{\mathbb R} \bigl(h(u) - h(u + x)\bigr)^2\,du\right) + 2\,\mathrm{autocorr}\ h\ (2x).$$
   - Key specializations:
     - $\alpha = 1 / 2$ (Fejér–Bochner): $\int h^2 \le 2 D_h(x) + 2 R(2x)$.
     - $\alpha = 7 / 10$ (near $1 - \sqrt{2}/2$): $\frac{41}{70}\int h^2 \le D_h(x) + \frac{5}{14}\bigl(2 R(2x)\bigr)$.
     - $\alpha = 4 / 5$ (quarter-window partner): $\frac{23}{40}\int h^2 \le D_h(x) + \frac{5}{16}\bigl(2 R(2x)\bigr)$.

3. **Section 3 — Crossing Ratios at `1 / 6` and `3 / 20`, Quarter-Window Harmonic-Doubling Upgrade for `L ≥ 2 / 3`, and the Sharpened `(0, log 2)` Plastic Floor (`-0.0080`)**:
   - At $b = 1 / 6$ ($b / 2 = 1 / 12$), the rational enclosure $\frac{313}{288} \le e^{1 / 12} \le \frac{12}{11}$
     certifies $\frac{5}{14}\bigl(-K(x)\bigr) \le 2 K(2x)$ for all $x \ge 1 / 6$.
   - For $L \ge 2 / 3$ (including $L = \log 2 \approx 0.693147$), $L / 4 \ge 1 / 6$ and $2(L / 4) = L / 2 \ge 1 / 3 > t_*$,
     upgrading the $(L / 4, L / 3)$ shell weight from $8 / 21 \approx 0.3810$ to **$41 / 70 \approx 0.5857$**
     and boosting the $L / 4$ potential weight from $2 / 35$ to **$6 / 35$**!

4. **Section 4 — Fourth-Order Hyperbolic Partial-Fraction Osculating Floor (`+ y² / 48 + (5 / 27) y³`) and Unconditional `WindowPositive` on `(0, 9 / 20)` (`= (0, 0.45)`, `64.92%` of `(0, log 2)`)**:
   - Combining $4 + y^2 / 2 + y^4 / 96 \le 4\cosh(y / 2)$ with the alternating partial-fraction bounds
     $$\frac{1}{2\cosh(y / 2)} \le \frac{1}{2} - \frac{y^2}{16} + \frac{y^4}{128}, \qquad
       \frac{1}{2\sinh(y / 2)} \le \frac{1}{y} - \frac{y}{24} + \frac{y^3}{576}$$
     and the SOS decomposition $\frac{9}{16} y^2 - \frac{y^3}{576} + \frac{y^4}{384} = \frac{5}{9} y^2 + \frac{1}{384} y^2(y - 1/3)^2 + \frac{23}{3456} y^2$
     proves for all $y > 0$:
     $$\frac{7}{2} - \frac{1}{y} + \frac{y}{24} + \frac{5}{9} y^2 \le 2\,\mathrm{screwRegularKernel}(y),$$
     and hence by integration and exact singular cancellation at $a \to 0^+$:
     $$\log\!\left(\frac{4}{y}\right) + \frac{\pi}{2} + \frac{7}{2} y + \frac{y^2}{48} + \frac{5}{27} y^3 \le \mathrm{levyCoshPotential}(y).$$
   - Coupling the active quarter-window sub-shell $\mathrm{Ioo}\,(t_* / 2)\,(L / 3)$ ($\alpha = 4 / 5$, where
     $\frac{16}{5}\bigl(2 K(2x)\bigr) \le -K(x)$ for $x \le 3 / 20$) with the split third-window shells on
     $\mathrm{Ioo}\,(L / 3)\,t_*$ and extracting the joint pair integral on $\mathrm{Ioo}\,(t_* / 2)\,t_*$
     yields an 11-point strictly positive-weight potential at $L = 9 / 20 = 0.45$ (`64.92%` of `(0, log 2)`)
     whose logarithms are 100% 5-smooth (plus $7 / 6$), with certified rational positivity (`+0.000250 > 0`),
     establishing unconditional `WindowPositive` on **`(0, 9 / 20)`** (`= (0, 0.45)`), `(0, 4 / 9)`, and `(0, 7 / 16)`.
-/

open Complex Real Set MeasureTheory Filter
open scoped Topology
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyMidpointCoreOverlap

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor
open RHTower.WeilLevyQuarterWindow RHTower.WeilLevySymmetricThreePoint
open RHTower.WeilLevySixthWindow RHTower.WeilLevyFibonacciStaircase
open RHTower.WeilLevyEighthWindow RHTower.WeilLevyThirdWindow
open RHTower.WeilLevyFifthWindow RHTower.WeilLevyTenthWindow
open RHTower.WeilLevySeventhWindow RHTower.WeilLevyHarmonicDoubling

/-! ## Section 1: Exact Upper-Half Core-Overlap Bound (`y = L - x ≥ L / 2`) & Universal Midpoint Reflection (`2 ∫ h² ≤ D_h(x) + D_h(L - x)`) -/

/-- **Upper-Half Overlap Autocorrelation Bound (`2 * autocorr h (L - x) ≤ collarMass h L x`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` and any `x ∈ [0, L / 2]`,
the reflected shift `L - x` has active overlap `Ioc 0 x`, which shifts into `Ioc (L - x) L`,
so `2 * autocorr h (L - x) ≤ collarMass h L x`. -/
theorem two_mul_autocorr_le_collarMass_of_sub {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (_hx0 : 0 ≤ x) (_hx2 : x ≤ L / 2) :
    2 * autocorr h (L - x) ≤ collarMass h L x := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift : Integrable (fun u : ℝ => h (u + (L - x)) ^ 2) := hsq.comp_add_right (L - x)
  have hmul : Integrable (fun u : ℝ => h u * h (u + (L - x))) := hh.integrable_mul_shift (L - x)
  have hauto := setIntegral_Ioc_mul_shift_eq_autocorr hh hsupp (y := L - x)
  rw [show L - (L - x) = x by ring] at hauto
  have hpt : ∀ u : ℝ, 2 * (h u * h (u + (L - x))) ≤ h u ^ 2 + h (u + (L - x)) ^ 2 := by
    intro u; nlinarith [sq_nonneg (h u - h (u + (L - x)))]
  have hint : (∫ u in Ioc 0 x, 2 * (h u * h (u + (L - x)))) ≤
      ∫ u in Ioc 0 x, (h u ^ 2 + h (u + (L - x)) ^ 2) :=
    setIntegral_mono (hmul.const_mul 2).integrableOn (hsq.add hshift).integrableOn hpt
  rw [integral_const_mul, hauto, integral_add hsq.integrableOn hshift.integrableOn] at hint
  have hright : (∫ u in Ioc 0 x, h (u + (L - x)) ^ 2) = ∫ v in Ioc (L - x) L, h v ^ 2 := by
    have h1 := setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 x (L - x)
    rw [zero_add, show x + (L - x) = L by ring] at h1
    exact h1
  rw [hright] at hint
  have hsub_left : (∫ u in Ioc 0 x, h u ^ 2) ≤ ∫ u in Iic x, h u ^ 2 :=
    setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall fun _ hu => hu.2)
  have hsub_right : (∫ v in Ioc (L - x) L, h v ^ 2) ≤ ∫ v in Ioi (L - x), h v ^ 2 :=
    setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall fun _ hv => hv.1)
  unfold collarMass
  linarith

/-- **Exact Upper-Half Core-Overlap Coercivity (`∫ h² + coreMass h L x ≤ D_h(L - x)`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` and any `x ∈ [0, L / 2]`,
`(∫ u, h u ^ 2) + coreMass h L x ≤ ∫ u, (h u - h (u + (L - x))) ^ 2`. -/
theorem integral_sq_add_coreMass_le_integral_jump_sq_sub {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hx0 : 0 ≤ x) (hx2 : x ≤ L / 2) :
    (∫ u, h u ^ 2) + coreMass h L x ≤ ∫ u, (h u - h (u + (L - x))) ^ 2 := by
  have hid := integral_jump_sq hh (L - x)
  have hauto := two_mul_autocorr_le_collarMass_of_sub hh hsupp hx0 hx2
  have hcons := collarMass_add_coreMass_eq hh hx2
  linarith

/-- **Universal Midpoint Reflection Coercivity (`2 ∫ h² ≤ D_h(x) + D_h(L - x)` for all `x ∈ [0, L / 2]`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` and **every** `x ∈ [0, L / 2]`,
`2 * (∫ u, h u ^ 2) ≤ (∫ u, (h u - h (u + x)) ^ 2) + ∫ u, (h u - h (u + (L - x))) ^ 2`. -/
theorem two_mul_integral_sq_le_integral_jump_sq_add_sub {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hx0 : 0 ≤ x) (hx2 : x ≤ L / 2) :
    2 * (∫ u, h u ^ 2) ≤
      (∫ u, (h u - h (u + x)) ^ 2) + ∫ u, (h u - h (u + (L - x))) ^ 2 := by
  have h1 := integral_sq_add_coreMass_le_integral_jump_sq_sub hh hsupp hx0 hx2
  have hcol := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
  have hint_nn : 0 ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
  have hcons := collarMass_add_coreMass_eq hh hx2
  linarith

/-- **Dual Midpoint Autocorrelation Reflection (`R(x) + R(L - x) ≤ ∫ h²` for all `x ∈ [0, L / 2]`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` and every `x ∈ [0, L / 2]`,
`autocorr h x + autocorr h (L - x) ≤ ∫ u, h u ^ 2`. -/
theorem autocorr_add_autocorr_sub_le_integral_sq {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hx0 : 0 ≤ x) (hx2 : x ≤ L / 2) :
    autocorr h x + autocorr h (L - x) ≤ ∫ u, h u ^ 2 := by
  have hid1 := integral_jump_sq hh x
  have hid2 := integral_jump_sq hh (L - x)
  have href := two_mul_integral_sq_le_integral_jump_sq_add_sub hh hsupp hx0 hx2
  linarith

/-! ## Section 2: Universal Single-Square `L²(ℝ)` Weighted Harmonic-Doubling Family (No Support Restriction) -/

/-- Exact single-square weighted harmonic-doubling identity: for all `p, q, r, α : ℝ`,
`(8 * α - 2 - 4 * α ^ 2) * q ^ 2 + (2 * α - 1) * (p ^ 2 - q ^ 2) + (2 * α - 1) * (r ^ 2 - q ^ 2)`
`≤ 2 * α * (p - q) ^ 2 + 2 * α * (q - r) ^ 2 + 2 * (p * r)`,
proved via `RHS - LHS = (p - 2 * α * q + r) ^ 2 ≥ 0`. -/
theorem weighted_harmonic_doubling_pointwise (p q r α : ℝ) :
    (8 * α - 2 - 4 * α ^ 2) * q ^ 2 + (2 * α - 1) * (p ^ 2 - q ^ 2) +
        (2 * α - 1) * (r ^ 2 - q ^ 2) ≤
      2 * α * (p - q) ^ 2 + 2 * α * (q - r) ^ 2 + 2 * (p * r) := by
  have hid : (2 * α * (p - q) ^ 2 + 2 * α * (q - r) ^ 2 + 2 * (p * r)) -
      ((8 * α - 2 - 4 * α ^ 2) * q ^ 2 + (2 * α - 1) * (p ^ 2 - q ^ 2) +
        (2 * α - 1) * (r ^ 2 - q ^ 2)) = (p - 2 * α * q + r) ^ 2 := by ring
  linarith [sq_nonneg (p - 2 * α * q + r)]

/-- **Universal Single-Square `L²(ℝ)` Weighted Harmonic-Doubling Theorem (No Support Restriction)**:
for **every** `BddSupp A h C` and **every** `x, α : ℝ`,
`(8 * α - 2 - 4 * α ^ 2) * (∫ u, h u ^ 2) ≤ 4 * α * (∫ u, (h u - h (u + x)) ^ 2) + 2 * autocorr h (2 * x)`. -/
theorem weighted_harmonic_doubling_integral_sq_le {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ}
    (hh : BddSupp A h C) (x α : ℝ) :
    (8 * α - 2 - 4 * α ^ 2) * (∫ u, h u ^ 2) ≤
      4 * α * (∫ u, (h u - h (u + x)) ^ 2) + 2 * autocorr h (2 * x) := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hsq1 : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hsq2 : Integrable (fun u : ℝ => h (u + 2 * x) ^ 2) := hsq.comp_add_right (2 * x)
  have hd1 : Integrable (fun u : ℝ => h u ^ 2 - h (u + x) ^ 2) := hsq.sub hsq1
  have hd2 : Integrable (fun u : ℝ => h (u + 2 * x) ^ 2 - h (u + x) ^ 2) := hsq2.sub hsq1
  have hmul2 : Integrable (fun u : ℝ => h u * h (u + 2 * x)) := hh.integrable_mul_shift (2 * x)
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hsq1).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  have hjump1 : Integrable (fun u : ℝ => (h (u + x) - h (u + 2 * x)) ^ 2) := by
    refine (hjump.comp_add_right x).congr (ae_of_all _ fun u => ?_)
    dsimp only; congr 3; ring
  have hI_lhs1 : Integrable (fun u : ℝ => (8 * α - 2 - 4 * α ^ 2) * h (u + x) ^ 2 +
      (2 * α - 1) * (h u ^ 2 - h (u + x) ^ 2)) :=
    (hsq1.const_mul _).add (hd1.const_mul _)
  have hI_lhs : Integrable (fun u : ℝ => (8 * α - 2 - 4 * α ^ 2) * h (u + x) ^ 2 +
      (2 * α - 1) * (h u ^ 2 - h (u + x) ^ 2) +
      (2 * α - 1) * (h (u + 2 * x) ^ 2 - h (u + x) ^ 2)) :=
    hI_lhs1.add (hd2.const_mul _)
  have hI_rhs1 : Integrable (fun u : ℝ => 2 * α * (h u - h (u + x)) ^ 2 +
      2 * α * (h (u + x) - h (u + 2 * x)) ^ 2) :=
    (hjump.const_mul _).add (hjump1.const_mul _)
  have hI_rhs : Integrable (fun u : ℝ => 2 * α * (h u - h (u + x)) ^ 2 +
      2 * α * (h (u + x) - h (u + 2 * x)) ^ 2 + 2 * (h u * h (u + 2 * x))) :=
    hI_rhs1.add (hmul2.const_mul 2)
  have hint := integral_mono hI_lhs hI_rhs fun u =>
    weighted_harmonic_doubling_pointwise (h u) (h (u + x)) (h (u + 2 * x)) α
  rw [integral_add hI_lhs1 (hd2.const_mul _),
    integral_add (hsq1.const_mul _) (hd1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_sub hsq hsq1, integral_sub hsq2 hsq1,
    integral_add hI_rhs1 (hmul2.const_mul 2),
    integral_add (hjump.const_mul _) (hjump1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at hint
  have hshift_sq1 : (∫ u, h (u + x) ^ 2) = ∫ u, h u ^ 2 :=
    integral_add_right_eq_self (μ := volume) (fun v : ℝ => h v ^ 2) x
  have hshift_sq2 : (∫ u, h (u + 2 * x) ^ 2) = ∫ u, h u ^ 2 :=
    integral_add_right_eq_self (μ := volume) (fun v : ℝ => h v ^ 2) (2 * x)
  have hshift_jump : (∫ u, (h (u + x) - h (u + 2 * x)) ^ 2) = ∫ u, (h u - h (u + x)) ^ 2 := by
    have h1 := integral_add_right_eq_self (μ := volume) (fun v : ℝ => (h v - h (v + x)) ^ 2) x
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    dsimp only; congr 3; ring
  rw [hshift_sq1, hshift_sq2, hshift_jump] at hint
  unfold autocorr
  linarith

/-- **Fejér–Bochner `L²(ℝ)` Doubling Inequality (`α = 1 / 2`)**:
for every `BddSupp A h C` and every `x : ℝ`,
`(∫ u, h u ^ 2) ≤ 2 * (∫ u, (h u - h (u + x)) ^ 2) + 2 * autocorr h (2 * x)`. -/
theorem fejer_bochner_integral_sq_le {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ}
    (hh : BddSupp A h C) (x : ℝ) :
    (∫ u, h u ^ 2) ≤ 2 * (∫ u, (h u - h (u + x)) ^ 2) + 2 * autocorr h (2 * x) := by
  have h := weighted_harmonic_doubling_integral_sq_le hh x (1 / 2)
  linarith

/-- **Universal `(41 / 70)` Harmonic-Doubling Coercivity (`α = 7 / 10`)**:
for every `BddSupp A h C` and every `x : ℝ` (with no support restriction!),
`(41 / 70 : ℝ) * (∫ u, h u ^ 2) ≤ (∫ u, (h u - h (u + x)) ^ 2) + (5 / 14 : ℝ) * (2 * autocorr h (2 * x))`. -/
theorem forty_one_seventieths_mul_integral_sq_le_integral_jump_sq_add_autocorr
    {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ} (hh : BddSupp A h C) (x : ℝ) :
    (41 / 70 : ℝ) * (∫ u, h u ^ 2) ≤
      (∫ u, (h u - h (u + x)) ^ 2) + (5 / 14 : ℝ) * (2 * autocorr h (2 * x)) := by
  have h := weighted_harmonic_doubling_integral_sq_le hh x (7 / 10)
  linarith

/-- **Universal `(23 / 40)` Quarter-Window Partner Harmonic-Doubling Coercivity (`α = 4 / 5`)**:
for every `BddSupp A h C` and every `x : ℝ`,
`(23 / 40 : ℝ) * (∫ u, h u ^ 2) ≤ (∫ u, (h u - h (u + x)) ^ 2) + (5 / 16 : ℝ) * (2 * autocorr h (2 * x))`. -/
theorem twenty_three_fortieths_mul_integral_sq_le_integral_jump_sq_add_autocorr
    {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ} (hh : BddSupp A h C) (x : ℝ) :
    (23 / 40 : ℝ) * (∫ u, h u ^ 2) ≤
      (∫ u, (h u - h (u + x)) ^ 2) + (5 / 16 : ℝ) * (2 * autocorr h (2 * x)) := by
  have h := weighted_harmonic_doubling_integral_sq_le hh x (4 / 5)
  linarith

/-! ## Section 3: Crossing Ratios at `1 / 6` and `3 / 20`, Quarter-Window Harmonic-Doubling Upgrade for `L ≥ 2 / 3`, and the Sharpened `(0, log 2)` Plastic Floor (`-0.0080`) -/

/-- Rational lower bound `313 / 288 ≤ Real.exp (1 / 12)` via `one_add_add_half_sq_le_exp`. -/
theorem exp_one_twelfth_ge : (313 : ℝ) / 288 ≤ Real.exp (1 / 12) := by
  have h := one_add_add_half_sq_le_exp (by norm_num : (0 : ℝ) ≤ 1 / 12)
  linarith

/-- Rational upper bound `Real.exp (1 / 12) ≤ 12 / 11` via `Real.add_one_le_exp (-1 / 12)`. -/
theorem exp_one_twelfth_le : Real.exp (1 / 12) ≤ (12 : ℝ) / 11 := by
  have h := Real.add_one_le_exp (-(1 / 12 : ℝ))
  rw [Real.exp_neg] at h
  have hexp : 0 < Real.exp (1 / 12) := Real.exp_pos _
  have hm := mul_le_mul_of_nonneg_right h hexp.le
  have hcancel : (Real.exp (1 / 12))⁻¹ * Real.exp (1 / 12) = 1 := inv_mul_cancel₀ hexp.ne'
  nlinarith

/-- **Harmonic-Doubling Crossing Inequality at `b = 1 / 6` (`2 * b = 1 / 3`)**:
`(5 / 14 : ℝ) * (-screwRegularKernel (1 / 6)) ≤ 2 * screwRegularKernel (1 / 3)`. -/
theorem five_fourteenths_mul_neg_screwRegularKernel_sixth_le_two_mul_screwRegularKernel_third :
    (5 / 14 : ℝ) * (-screwRegularKernel (1 / 6)) ≤ 2 * screwRegularKernel (1 / 3) := by
  have hb : (0 : ℝ) < 1 / 6 := by norm_num
  have h1 := neg_screwRegularKernel_mul_eq_of_pos hb
  have h2 := two_mul_screwRegularKernel_two_mul_eq_of_pos hb
  dsimp only at h1 h2
  rw [show (2 : ℝ) * (1 / 6) = 1 / 3 by norm_num] at h2
  rw [show (1 / 6 : ℝ) / 2 = 1 / 12 by norm_num] at h1 h2
  set u := Real.exp (1 / 12)
  have hu_ge : (313 : ℝ) / 288 ≤ u := exp_one_twelfth_ge
  have hu_le : u ≤ (12 : ℝ) / 11 := exp_one_twelfth_le
  have hden : 0 < u ^ 10 - u ^ 2 := by
    have : ((313 : ℝ) / 288) ^ 10 ≤ u ^ 10 := pow_le_pow_left₀ (by norm_num) hu_ge 10
    have : u ^ 2 ≤ ((12 : ℝ) / 11) ^ 2 := pow_le_pow_left₀ (by linarith) hu_le 2
    linarith
  have hpoly : (5 / 14 : ℝ) * (u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6)) ≤
      2 * (u ^ 12 - u ^ 4 - 1) := by
    have hp12 : ((313 : ℝ) / 288) ^ 12 ≤ u ^ 12 := pow_le_pow_left₀ (by norm_num) hu_ge 12
    have hp4 : u ^ 4 ≤ ((12 : ℝ) / 11) ^ 4 := pow_le_pow_left₀ (by linarith) hu_le 4
    have hp6 : ((313 : ℝ) / 288) ^ 6 ≤ u ^ 6 := pow_le_pow_left₀ (by norm_num) hu_ge 6
    have hp2 : u ^ 2 ≤ ((12 : ℝ) / 11) ^ 2 := pow_le_pow_left₀ (by linarith) hu_le 2
    have hfac1 : 0 ≤ u * (u ^ 4 + 1) := by positivity
    have hfac1_le : u * (u ^ 4 + 1) ≤ (12 / 11 : ℝ) * (((12 : ℝ) / 11) ^ 4 + 1) := by nlinarith
    have hfac2_pos : 0 ≤ 1 + ((12 : ℝ) / 11) ^ 2 - ((313 : ℝ) / 288) ^ 6 := by norm_num
    have hprod : u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6) ≤
        (12 / 11 : ℝ) * (((12 : ℝ) / 11) ^ 4 + 1) *
          (1 + ((12 : ℝ) / 11) ^ 2 - ((313 : ℝ) / 288) ^ 6) := by nlinarith
    linarith
  nlinarith

/-- For every `x ≥ 1 / 6`, `(5 / 14 : ℝ) * (-screwRegularKernel x) ≤ 2 * screwRegularKernel (2 * x)`. -/
theorem five_fourteenths_mul_neg_screwRegularKernel_le_two_mul_screwRegularKernel_two_mul_of_sixth_le
    {x : ℝ} (hx : 1 / 6 ≤ x) :
    (5 / 14 : ℝ) * (-screwRegularKernel x) ≤ 2 * screwRegularKernel (2 * x) := by
  have hx0 : 0 < x := by linarith
  have h1 : screwRegularKernel (1 / 6) ≤ screwRegularKernel x :=
    monotoneOn_screwRegularKernel (by norm_num : (0 : ℝ) < 1 / 6) hx0 hx
  have h2 : screwRegularKernel (1 / 3) ≤ screwRegularKernel (2 * x) :=
    monotoneOn_screwRegularKernel (by norm_num : (0 : ℝ) < 1 / 3) (by linarith : 0 < 2 * x)
      (by linarith)
  linarith [five_fourteenths_mul_neg_screwRegularKernel_sixth_le_two_mul_screwRegularKernel_third]

/-- **Universal `(41 / 70)` Harmonic-Doubling Shell Bound on `Ioo a b` (`1 / 6 ≤ a ≤ b ≤ screwSignThreshold`)**:
for any nonnegative `BddSupp A h C` and any `1 / 6 ≤ a ≤ b ≤ screwSignThreshold`,
`(41 / 140 : ℝ) * (Φ(a) - Φ(b)) * ∫ h² ≤ (∫_{x ∈ Ioo a b} (-K(x)) D_h(x)) + ∫_{x ∈ Ioo a b} (2 K(2x)) (2 R(2x))`. -/
theorem forty_one_one_fortieths_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_double_autocorr
    {A : Set ℝ} {h : ℝ → ℝ} {C a b : ℝ} (hh : BddSupp A h C)
    (hh0 : ∀ u, 0 ≤ h u) (ha6 : 1 / 6 ≤ a) (hab : a ≤ b) (hbt : b ≤ screwSignThreshold) :
    (41 / 140 : ℝ) * (levyCoshPotential a - levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      (∫ x in Ioo a b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ x in Ioo a b, (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x)) := by
  have ha0 : 0 < a := by linarith
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
    have hK2_0 : 0 ≤ 2 * screwRegularKernel (2 * x) := by
      have hcr := five_fourteenths_mul_neg_screwRegularKernel_le_two_mul_screwRegularKernel_two_mul_of_sixth_le
        (ha6.trans hx.1.le)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK2_0 (hR0 x))]
    have hR_le : 2 * autocorr h (2 * x) ≤ 2 * ∫ u, h u ^ 2 := by
      have hid := integral_jump_sq hh (2 * x)
      have hD_nn := hD0 (2 * x)
      linarith
    exact mul_le_mul_of_nonneg_left hR_le hK2_0
  have hI_lhs : IntegrableOn
      (fun x : ℝ => (41 / 70 : ℝ) * (-screwRegularKernel x) * ∫ u, h u ^ 2) (Ioo a b) :=
    (hI_K.const_mul (41 / 70 : ℝ)).mul_const _
  have hmono : (∫ x in Ioo a b, (41 / 70 : ℝ) * (-screwRegularKernel x) * ∫ u, h u ^ 2) ≤
      ∫ x in Ioo a b, ((-screwRegularKernel x) * (∫ u, (h u - h (u + x)) ^ 2) +
        (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))) := by
    refine setIntegral_mono_on hI_lhs (hI_jump.add hI_auto) measurableSet_Ioo fun x hx => ?_
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hbt))
    have hhd := forty_one_seventieths_mul_integral_sq_le_integral_jump_sq_add_autocorr hh x
    have h1 := mul_le_mul_of_nonneg_left hhd hK0
    have h2 : (-screwRegularKernel x) * ((5 / 14 : ℝ) * (2 * autocorr h (2 * x))) ≤
        (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x)) := by
      have hcr := five_fourteenths_mul_neg_screwRegularKernel_le_two_mul_screwRegularKernel_two_mul_of_sixth_le
        (ha6.trans hx.1.le)
      nlinarith [hR0 x]
    linarith
  rw [integral_mul_const, integral_const_mul, setIntegral_Ioo_neg_screwRegularKernel ha0 hab,
    integral_add hI_jump hI_auto] at hmono
  linarith

/-- **Upgraded Seven-Shell Harmonic-Doubling Potential + Pair Coercivity for `2 / 3 ≤ L ≤ 3 * screwSignThreshold`**:
upgrading `Ioo (L / 4) (L / 3)` from `8 / 21` to `41 / 70` via `α = 7 / 10` harmonic doubling and
combining the pair extraction across `Ioo (L / 4) screwSignThreshold` raises the `Φ(L / 4)` weight
from `2 / 35` (`≈ 0.0571`) to **`67 / 420`** (`≈ 0.1595`)! -/
theorem tenth_to_quarter_harmonic_doubling_sub_levyCoshPotential_le_setIntegral_Ioo_add_pair
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hh0 : ∀ u, 0 ≤ h u)
    (hL_two_thirds : 2 / 3 ≤ L) (hL3t : L / 3 ≤ screwSignThreshold) :
    ((1 / 25 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (3 / 200 : ℝ) * levyCoshPotential (L / 7) +
        (1 / 45 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (67 / 420 : ℝ) * levyCoshPotential (L / 4) +
        (29 / 140 : ℝ) * levyCoshPotential (L / 3) -
        (1 / 2 : ℝ) * levyCoshPotential screwSignThreshold) * (∫ u, h u ^ 2) ≤
      (∫ x in Ioo (L / 10) screwSignThreshold,
        (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ p : ℝ × ℝ, h p.1 * h p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) := by
  have hL0 : 0 < L := by linarith
  have hL10_pos : 0 < L / 10 := by linarith
  have hL4_pos : 0 < L / 4 := by linarith
  have hL10_4 : L / 10 ≤ L / 4 := by linarith
  have hL5_4 : L / 5 ≤ L / 4 := by linarith
  have hL4_3 : L / 4 ≤ L / 3 := by linarith
  have hL4_t : L / 4 ≤ screwSignThreshold := le_trans hL4_3 hL3t
  have ht_L2 : screwSignThreshold ≤ 2 * (L / 4) := by
    linarith [screwSignThreshold_lt_thirty_eight_over_one_thirty_five]
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  have hR0 : ∀ x, 0 ≤ 2 * autocorr h (2 * x) :=
    fun x => mul_nonneg zero_le_two (autocorr_nonneg hh hh0 (2 * x))
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
  have hsplit_F : (∫ x in Ioo (L / 10) screwSignThreshold, F x) =
      (∫ x in Ioo (L / 10) (L / 4), F x) + (∫ x in Ioo (L / 4) (L / 3), F x) +
        ∫ x in Ioo (L / 3) screwSignThreshold, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (hL10_4.trans hL4_3) hL3t,
      setIntegral_union hdisj_123 measurableSet_Ioc hIF_12_Ioc hIF_3_Ioc,
      ← Ioc_union_Ioc_eq_Ioc hL10_4 hL4_3,
      setIntegral_union hdisj_12 measurableSet_Ioc hIF_1_Ioc hIF_2_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  let H : ℝ → ℝ := fun x => (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))
  have hK2m : Measurable fun x : ℝ => 2 * screwRegularKernel (2 * x) := by
    unfold screwRegularKernel; fun_prop
  have hR2m : Measurable fun x : ℝ => 2 * autocorr h (2 * x) :=
    measurable_two_mul_autocorr_two_mul hh
  have hHm : Measurable H := hK2m.mul hR2m
  have hcont_K2 : ContinuousOn (fun x => 2 * screwRegularKernel (2 * x))
      (Icc (L / 4) screwSignThreshold) :=
    continuousOn_two_mul_screwRegularKernel_two_mul hL4_pos
  have hIH : IntegrableOn H (Ioo (L / 4) screwSignThreshold) := by
    refine ((hcont_K2.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (2 * ∫ u, h u ^ 2)).mono' hHm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK2_0 : 0 ≤ 2 * screwRegularKernel (2 * x) :=
      mul_nonneg zero_le_two (screwRegularKernel_nonneg_of_threshold_le
        (ht_L2.trans (by linarith [hx.1])))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK2_0 (hR0 x))]
    have hR_le : 2 * autocorr h (2 * x) ≤ 2 * ∫ u, h u ^ 2 := by
      have hid := integral_jump_sq hh (2 * x)
      have hD_nn := hD0 (2 * x)
      linarith
    exact mul_le_mul_of_nonneg_left hR_le hK2_0
  have hIH_left_Ioc : IntegrableOn H (Ioc (L / 4) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIH.mono_set (Ioo_subset_Ioo le_rfl hL3t)
  have hIH_right_Ioc : IntegrableOn H (Ioc (L / 3) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIH.mono_set (Ioo_subset_Ioo hL4_3 le_rfl)
  have hdisj_23 : Disjoint (Ioc (L / 4) (L / 3)) (Ioc (L / 3) screwSignThreshold) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit_H : (∫ x in Ioo (L / 4) screwSignThreshold, H x) =
      (∫ x in Ioo (L / 4) (L / 3), H x) + ∫ x in Ioo (L / 3) screwSignThreshold, H x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL4_3 hL3t,
      setIntegral_union hdisj_23 measurableSet_Ioc hIH_left_Ioc hIH_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h105 := tenth_to_fifth_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL5_4 hL4_t
  have h4 := forty_one_one_fortieths_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_double_autocorr
    hh hh0 (by linarith : 1 / 6 ≤ L / 4) hL4_3 hL3t
  have h3 := half_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_double_autocorr
    hh hsupp hh0 hL0 (by linarith : 3 / 16 ≤ L / 3) le_rfl hL3t le_rfl
  have hpair := setIntegral_Ioo_two_mul_screwRegularKernel_two_mul_autocorr_le_pair
    hh hsupp hh0 hL0 le_rfl ht_L2 hL4_t
  dsimp only [F] at hsplit_F
  dsimp only [H] at hsplit_H
  linarith

/-- **Upgraded Quarter+Third Harmonic-Doubling Plastic-Floor Theorem (`2 / 3 ≤ L ≤ 3 * screwSignThreshold`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`2 / 3 ≤ L`, `L / 3 ≤ screwSignThreshold`),
`(A(0) + (1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (67 / 420) * Φ(L / 4) + (29 / 140) * Φ(L / 3) + (1 / 2) * Φ(screwSignThreshold)) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem quarter_harmonic_doubling_plastic_floor_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL_two_thirds : 2 / 3 ≤ L) (hL3t : L / 3 ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (3 / 200) * levyCoshPotential (L / 7) +
        (1 / 45) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (67 / 420) * levyCoshPotential (L / 4) +
        (29 / 140) * levyCoshPotential (L / 3) +
        (1 / 2) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL0 : 0 < L := by linarith
  have hL10 : 0 < L / 10 := by linarith
  have hL10t : L / 10 ≤ screwSignThreshold := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL10 hL10t le_rfl
  have hjump := tenth_to_quarter_harmonic_doubling_sub_levyCoshPotential_le_setIntegral_Ioo_add_pair
    hB hsupp hf0 hL_two_thirds hL3t
  linarith

/-- **Specialization of the Quarter+Third Harmonic-Doubling Plastic Floor to `L = log 2`**:
reduces the universal `(0, log 2)` constant deficit from `-0.0100` down to **`-0.0080`**. -/
theorem quarter_harmonic_doubling_plastic_floor_log_two_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hsupp : ∀ u ∉ Ioo 0 (Real.log 2), f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (Real.log 2 / 10) +
        (1 / 50) * levyCoshPotential (Real.log 2 / 8) +
        (3 / 200) * levyCoshPotential (Real.log 2 / 7) +
        (1 / 45) * levyCoshPotential (Real.log 2 / 6) +
        (13 / 360) * levyCoshPotential (Real.log 2 / 5) +
        (67 / 420) * levyCoshPotential (Real.log 2 / 4) +
        (29 / 140) * levyCoshPotential (Real.log 2 / 3) +
        (1 / 2) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  quarter_harmonic_doubling_plastic_floor_le_weilArchRe hf hfc hf0
    (by linarith [Real.log_two_gt_d9])
    (by linarith [Real.log_two_lt_d9, screwSignThreshold_gt_6036_over_21509])
    hsupp

/-! ## Section 4: Fourth-Order Hyperbolic Partial-Fraction Osculating Floor (`+ y² / 48 + (5 / 27) y³`) and Unconditional `WindowPositive` on `(0, 9 / 20)` (`= (0, 0.45)`, `64.92%` of `(0, log 2)`) -/

/-- Quartic Taylor lower bound `4 + y ^ 2 / 2 + y ^ 4 / 96 ≤ 4 * Real.cosh (y / 2)` for all `y ≥ 0`. -/
theorem four_add_half_sq_add_ninety_sixth_pow_four_le_four_mul_cosh_half {y : ℝ} (hy : 0 ≤ y) :
    4 + y ^ 2 / 2 + y ^ 4 / 96 ≤ 4 * Real.cosh (y / 2) := by
  let g : ℝ → ℝ := fun u => 4 * Real.cosh (u / 2) - (4 + u ^ 2 / 2 + u ^ 4 / 96)
  have hderiv : ∀ u : ℝ, HasDerivAt g (2 * Real.sinh (u / 2) - (u + u ^ 3 / 24)) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => 4 * Real.cosh (v / 2)) (2 * Real.sinh (u / 2)) u := by
      have h := ((hasDerivAt_id u).div_const (2 : ℝ)).cosh.const_mul (4 : ℝ)
      exact h.congr_deriv (by dsimp only [id_eq]; ring)
    have h2 : HasDerivAt (fun v : ℝ => 4 + v ^ 2 / 2 + v ^ 4 / 96) (u + u ^ 3 / 24) u := by
      have ha : HasDerivAt (fun v : ℝ => 4 + v ^ 2 / 2) u u := by
        simpa using (((hasDerivAt_pow 2 u).div_const 2).const_add 4).congr_deriv (by ring)
      have hb : HasDerivAt (fun v : ℝ => v ^ 4 / 96) (u ^ 3 / 24) u := by
        simpa using ((hasDerivAt_pow 4 u).div_const 96).congr_deriv (by ring)
      exact ha.add hb
    exact h1.sub h2
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun u _ => (hderiv u).continuousAt.continuousWithinAt
    · exact fun u _ => (hderiv u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hderiv u).deriv]
      have hu0 : 0 ≤ u := interior_subset hu
      linarith [four_mul_add_sixth_cube_le_eight_mul_sinh_half hu0]
  have h0 : g 0 ≤ g y := hmono self_mem_Ici hy hy
  dsimp [g] at h0
  rw [zero_div, Real.cosh_zero] at h0
  linarith

/-- Quartic upper bound `1 / (2 * Real.cosh (y / 2)) ≤ 1 / 2 - y ^ 2 / 16 + y ^ 4 / 128` for all `y ≥ 0`,
proved via `(1 / 2 - y^2 / 16 + y^4 / 128) * (4 + y^2 / 2) = 2 + y^6 / 256 ≥ 2`. -/
theorem inv_two_mul_cosh_half_le_quartic {y : ℝ} (hy : 0 ≤ y) :
    1 / (2 * Real.cosh (y / 2)) ≤ 1 / 2 - y ^ 2 / 16 + y ^ 4 / 128 := by
  have hcosh_pos : 0 < 2 * Real.cosh (y / 2) := by positivity
  rw [div_le_iff₀ hcosh_pos]
  have hcosh := four_add_half_sq_le_four_mul_cosh_half hy
  have hpoly_pos : 0 ≤ (1 / 2 : ℝ) - y ^ 2 / 16 + y ^ 4 / 128 := by
    have : (1 / 2 : ℝ) - y ^ 2 / 16 + y ^ 4 / 128 = (y ^ 2 - 4) ^ 2 / 128 + 3 / 8 := by ring
    rw [this]; positivity
  have hm := mul_le_mul_of_nonneg_left hcosh hpoly_pos
  have hid : ((1 / 2 : ℝ) - y ^ 2 / 16 + y ^ 4 / 128) * (4 + y ^ 2 / 2) =
      2 + (y ^ 3) ^ 2 / 256 := by ring
  have hsq : 0 ≤ (y ^ 3) ^ 2 / 256 := by positivity
  linarith

/-- Cubic upper bound `1 / (2 * Real.sinh (y / 2)) ≤ 1 / y - y / 24 + y ^ 3 / 576` for all `y > 0`,
proved via `(1 / y - y / 24 + y^3 / 576) * (4 * y + y^3 / 6) = 4 + y^6 / 3456 ≥ 4`. -/
theorem inv_two_mul_sinh_half_le_cubic {y : ℝ} (hy : 0 < y) :
    1 / (2 * Real.sinh (y / 2)) ≤ 1 / y - y / 24 + y ^ 3 / 576 := by
  have hsinh_pos : 0 < 2 * Real.sinh (y / 2) :=
    mul_pos zero_lt_two (Real.sinh_pos_iff.mpr (by linarith))
  rw [div_le_iff₀ hsinh_pos]
  have hsinh := four_mul_add_sixth_cube_le_eight_mul_sinh_half hy.le
  have hpoly_pos : 0 ≤ 1 / y - y / 24 + y ^ 3 / 576 := by
    have : 1 / y - y / 24 + y ^ 3 / 576 = ((y ^ 2 - 12) ^ 2 / 576 + 3 / 4) / y := by
      field_simp; ring
    rw [this]; positivity
  have hm := mul_le_mul_of_nonneg_left hsinh hpoly_pos
  have hid : (1 / y - y / 24 + y ^ 3 / 576) * (4 * y + y ^ 3 / 6) =
      4 + (y ^ 3) ^ 2 / 3456 := by
    field_simp; ring
  have hsq : 0 ≤ (y ^ 3) ^ 2 / 3456 := by positivity
  linarith

/-- **Global Fourth-Order Derivative Lower Bound for `levyCoshPotential` (`y > 0`)**:
for every `y > 0`, `(7 / 2 : ℝ) - 1 / y + y / 24 + (5 / 9 : ℝ) * y ^ 2 ≤ 2 * screwRegularKernel y`. -/
theorem seven_halves_sub_inv_add_twenty_fourth_add_five_ninths_sq_le_two_mul_screwRegularKernel
    {y : ℝ} (hy : 0 < y) :
    (7 / 2 : ℝ) - 1 / y + y / 24 + (5 / 9 : ℝ) * y ^ 2 ≤ 2 * screwRegularKernel y := by
  rw [screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity hy]
  have hlevy := two_mul_archLevyDensity_eq_inv_sinh_add_inv_cosh hy
  have hcosh := four_add_half_sq_add_ninety_sixth_pow_four_le_four_mul_cosh_half hy.le
  have hinv_cosh := inv_two_mul_cosh_half_le_quartic hy.le
  have hinv_sinh := inv_two_mul_sinh_half_le_cubic hy
  have hsos : 0 ≤ (1 / 384 : ℝ) * (y * (y - 1 / 3)) ^ 2 + (23 / 3456 : ℝ) * y ^ 2 := by
    positivity
  have hid : (4 + y ^ 2 / 2 + y ^ 4 / 96) - (1 / 2 - y ^ 2 / 16 + y ^ 4 / 128) -
      (1 / y - y / 24 + y ^ 3 / 576) =
      ((7 / 2 : ℝ) - 1 / y + y / 24 + (5 / 9 : ℝ) * y ^ 2) +
        ((1 / 384 : ℝ) * (y * (y - 1 / 3)) ^ 2 + (23 / 3456 : ℝ) * y ^ 2) := by ring
  linarith

/-- **Monotonicity of `levyCoshPotential y - (-log y + (7 / 2) * y + y ^ 2 / 48 + (5 / 27) * y ^ 3)`**:
for any `0 < a ≤ b`,
`Real.log (a / b) + (7 / 2) * (b - a) + (b ^ 2 - a ^ 2) / 48 + (5 / 27) * (b ^ 3 - a ^ 3) ≤ levyCoshPotential b - levyCoshPotential a`. -/
theorem log_div_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_sub_levyCoshPotential
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (a / b) + (7 / 2 : ℝ) * (b - a) + (b ^ 2 - a ^ 2) / 48 +
        (5 / 27 : ℝ) * (b ^ 3 - a ^ 3) ≤
      levyCoshPotential b - levyCoshPotential a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  let Φ_osc : ℝ → ℝ := fun y => -Real.log y + (7 / 2 : ℝ) * y + y ^ 2 / 48 + (5 / 27 : ℝ) * y ^ 3
  let dΦ_osc : ℝ → ℝ := fun y => (7 / 2 : ℝ) - 1 / y + y / 24 + (5 / 9 : ℝ) * y ^ 2
  have hderiv : ∀ y ∈ uIcc a b,
      HasDerivAt (fun u => levyCoshPotential u - Φ_osc u)
        (2 * screwRegularKernel y - dΦ_osc y) y := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have h1 := hasDerivAt_levyCoshPotential hy0
    have h2 : HasDerivAt Φ_osc (dΦ_osc y) y := by
      have ha' : HasDerivAt (fun u : ℝ => -Real.log u) (-y⁻¹) y := (Real.hasDerivAt_log hy0.ne').neg
      have hb' : HasDerivAt (fun u : ℝ => (7 / 2 : ℝ) * u) (7 / 2) y := by
        simpa using (hasDerivAt_id y).const_mul (7 / 2 : ℝ)
      have hc' : HasDerivAt (fun u : ℝ => u ^ 2 / 48) (y / 24) y := by
        simpa using ((hasDerivAt_pow 2 y).div_const 48).congr_deriv (by ring)
      have hd' : HasDerivAt (fun u : ℝ => (5 / 27 : ℝ) * u ^ 3) ((5 / 9 : ℝ) * y ^ 2) y := by
        simpa using ((hasDerivAt_pow 3 y).const_mul (5 / 27 : ℝ)).congr_deriv (by ring)
      exact (((ha'.add hb').add hc').add hd').congr_deriv (by dsimp only [dΦ_osc]; rw [one_div]; ring)
    exact h1.sub h2
  have hcont : ContinuousOn (fun y => 2 * screwRegularKernel y - dΦ_osc y) (uIcc a b) := by
    rw [uIcc_of_le hab]
    refine (continuousOn_const.mul (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun y hy => lt_of_lt_of_le ha hy.1)).sub ?_
    dsimp only [dΦ_osc]
    refine ((continuousOn_const.sub (continuousOn_const.div continuousOn_id fun y hy =>
      (lt_of_lt_of_le ha hy.1).ne')).add (by fun_prop)).add (by fun_prop)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hnn : 0 ≤ ∫ y in a..b, (2 * screwRegularKernel y - dΦ_osc y) := by
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_nonneg measurableSet_Ioc fun y hy => ?_
    have hy0 : 0 < y := lt_trans ha hy.1
    dsimp only [dΦ_osc]
    linarith [seven_halves_sub_inv_add_twenty_fourth_add_five_ninths_sq_le_two_mul_screwRegularKernel hy0]
  rw [hFTC] at hnn
  dsimp only [Φ_osc] at hnn
  have hlog : Real.log (a / b) = Real.log a - Real.log b :=
    Real.log_div ha.ne' hb.ne'
  linarith

/-- **Fourth-Order Hyperbolic Partial-Fraction Osculating Lower Bound for `levyCoshPotential y` (`y > 0`)**:
for every `y > 0`,
`Real.log (4 / y) + Real.pi / 2 + (7 / 2) * y + y ^ 2 / 48 + (5 / 27) * y ^ 3 ≤ levyCoshPotential y`. -/
theorem osculating_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_levyCoshPotential
    {y : ℝ} (hy : 0 < y) :
    Real.log (4 / y) + Real.pi / 2 + (7 / 2 : ℝ) * y + y ^ 2 / 48 +
        (5 / 27 : ℝ) * y ^ 3 ≤ levyCoshPotential y := by
  by_contra! hlt
  set δ := (Real.log (4 / y) + Real.pi / 2 + (7 / 2 : ℝ) * y + y ^ 2 / 48 +
    (5 / 27 : ℝ) * y ^ 3) - levyCoshPotential y
  have hδ : 0 < δ := sub_pos.mpr hlt
  set a := min y (min 1 δ)
  have ha0 : 0 < a := lt_min hy (lt_min one_pos hδ)
  have hay : a ≤ y := min_le_left _ _
  have ha1 : a ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have haδ : a ≤ (Real.log (4 / y) + Real.pi / 2 + (7 / 2 : ℝ) * y + y ^ 2 / 48 +
      (5 / 27 : ℝ) * y ^ 3) - levyCoshPotential y :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have h1 := osculating_add_sixth_cube_le_levyCoshPotential ha0
  have h2 := log_div_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_sub_levyCoshPotential
    ha0 hay
  have hlog : Real.log (4 / a) + Real.log (a / y) = Real.log (4 / y) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  have ha2 : a ^ 2 ≤ a := by nlinarith
  have ha3 : a ^ 3 ≤ a := by nlinarith
  linarith

/-- **Fourth-Order `(π / 2, log 2)` Cancellation for `EF.gammaBracket 0 + levyCoshPotential y`**:
for every `y > 0`,
`Real.log (1 / (2 * Real.pi * y)) + (7 / 2) * y + y ^ 2 / 48 + (5 / 27) * y ^ 3 - eulerMascheroniConstant ≤ EF.gammaBracket 0 + levyCoshPotential y`. -/
theorem log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
    {y : ℝ} (hy : 0 < y) :
    Real.log (1 / (2 * Real.pi * y)) + (7 / 2 : ℝ) * y + y ^ 2 / 48 +
        (5 / 27 : ℝ) * y ^ 3 - eulerMascheroniConstant ≤
      EF.gammaBracket 0 + levyCoshPotential y := by
  have hA : EF.gammaBracket 0 =
      -(Real.log Real.pi + 3 * Real.log 2 + eulerMascheroniConstant + Real.pi / 2) := by
    linarith [neg_gammaBracket_zero_eq]
  have hlog := log_inv_two_pi_mul_eq hy
  have hΦ := osculating_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_levyCoshPotential hy
  linarith

/-- **Fourth-Order Global Minimum Osculating Law**:
for every `c > 0`,
`Real.log (7 / (4 * Real.pi)) + 1 + c ^ 2 / 48 + (5 / 27) * c ^ 3 - eulerMascheroniConstant ≤ EF.gammaBracket 0 + levyCoshPotential c`. -/
theorem log_seven_div_four_pi_add_one_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
    {c : ℝ} (hc : 0 < c) :
    Real.log (7 / (4 * Real.pi)) + 1 + c ^ 2 / 48 + (5 / 27 : ℝ) * c ^ 3 -
        eulerMascheroniConstant ≤
      EF.gammaBracket 0 + levyCoshPotential c := by
  have hmain :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential hc
  have hpos : 0 < (7 / 2 : ℝ) * c := by positivity
  have hlog : Real.log (7 / (4 * Real.pi)) =
      Real.log ((7 / 2 : ℝ) * c) + Real.log (1 / (2 * Real.pi * c)) := by
    rw [← Real.log_mul hpos.ne' (by positivity)]
    congr 1; field_simp; ring
  have hle := Real.log_le_sub_one_of_pos hpos
  linarith

/-- Rational lower bound `3449 / 3200 ≤ Real.exp (3 / 40)` via `one_add_add_half_sq_le_exp`. -/
theorem exp_three_fortieths_ge : (3449 : ℝ) / 3200 ≤ Real.exp (3 / 40) := by
  have h := one_add_add_half_sq_le_exp (by norm_num : (0 : ℝ) ≤ 3 / 40)
  linarith

/-- Rational upper bound `Real.exp (3 / 40) ≤ 40 / 37` via `Real.add_one_le_exp (-3 / 40)`. -/
theorem exp_three_fortieths_le : Real.exp (3 / 40) ≤ (40 : ℝ) / 37 := by
  have h := Real.add_one_le_exp (-(3 / 40 : ℝ))
  rw [Real.exp_neg] at h
  have hexp : 0 < Real.exp (3 / 40) := Real.exp_pos _
  have hm := mul_le_mul_of_nonneg_right h hexp.le
  have hcancel : (Real.exp (3 / 40))⁻¹ * Real.exp (3 / 40) = 1 := inv_mul_cancel₀ hexp.ne'
  nlinarith

/-- **Quarter-Window Harmonic-Doubling Crossing Ratio at `b = 3 / 20` (`2 * b = 3 / 10`)**:
`(16 / 5 : ℝ) * (2 * screwRegularKernel (3 / 10)) ≤ -screwRegularKernel (3 / 20)`. -/
theorem sixteen_fifths_mul_two_mul_screwRegularKernel_three_tenths_le_neg_screwRegularKernel_three_twentieths :
    (16 / 5 : ℝ) * (2 * screwRegularKernel (3 / 10)) ≤ -screwRegularKernel (3 / 20) := by
  have hb : (0 : ℝ) < 3 / 20 := by norm_num
  have h1 := neg_screwRegularKernel_mul_eq_of_pos hb
  have h2 := two_mul_screwRegularKernel_two_mul_eq_of_pos hb
  dsimp only at h1 h2
  rw [show (2 : ℝ) * (3 / 20) = 3 / 10 by norm_num] at h2
  rw [show (3 / 20 : ℝ) / 2 = 3 / 40 by norm_num] at h1 h2
  set u := Real.exp (3 / 40)
  have hu_ge : (3449 : ℝ) / 3200 ≤ u := exp_three_fortieths_ge
  have hu_le : u ≤ (40 : ℝ) / 37 := exp_three_fortieths_le
  have hden : 0 < u ^ 10 - u ^ 2 := by
    have : ((3449 : ℝ) / 3200) ^ 10 ≤ u ^ 10 := pow_le_pow_left₀ (by norm_num) hu_ge 10
    have : u ^ 2 ≤ ((40 : ℝ) / 37) ^ 2 := pow_le_pow_left₀ (by linarith) hu_le 2
    linarith
  have hpoly : (16 / 5 : ℝ) * (2 * (u ^ 12 - u ^ 4 - 1)) ≤
      u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6) := by
    have hp12 : u ^ 12 ≤ ((40 : ℝ) / 37) ^ 12 := pow_le_pow_left₀ (by linarith) hu_le 12
    have hp4_ge : ((3449 : ℝ) / 3200) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu_ge 4
    have hp6_le : u ^ 6 ≤ ((40 : ℝ) / 37) ^ 6 := pow_le_pow_left₀ (by linarith) hu_le 6
    have hp2_ge : ((3449 : ℝ) / 3200) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu_ge 2
    have hfac1_ge : (3449 / 3200 : ℝ) * (((3449 : ℝ) / 3200) ^ 4 + 1) ≤ u * (u ^ 4 + 1) := by
      nlinarith
    have hfac2_ge : 0 ≤ 1 + ((3449 : ℝ) / 3200) ^ 2 - ((40 : ℝ) / 37) ^ 6 := by norm_num
    have hprod : (3449 / 3200 : ℝ) * (((3449 : ℝ) / 3200) ^ 4 + 1) *
        (1 + ((3449 : ℝ) / 3200) ^ 2 - ((40 : ℝ) / 37) ^ 6) ≤
        u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6) := by nlinarith
    linarith
  nlinarith

/-- For every `x ∈ (0, 3 / 20]`,
`(16 / 5 : ℝ) * (2 * screwRegularKernel (2 * x)) ≤ -screwRegularKernel x`. -/
theorem sixteen_fifths_mul_two_mul_screwRegularKernel_two_mul_le_neg_screwRegularKernel
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 3 / 20) :
    (16 / 5 : ℝ) * (2 * screwRegularKernel (2 * x)) ≤ -screwRegularKernel x := by
  have h1 : screwRegularKernel x ≤ screwRegularKernel (3 / 20) :=
    monotoneOn_screwRegularKernel hx0 (by norm_num : (0 : ℝ) < 3 / 20) hx
  have h2 : screwRegularKernel (2 * x) ≤ screwRegularKernel (3 / 10) :=
    monotoneOn_screwRegularKernel (by linarith : 0 < 2 * x) (by norm_num : (0 : ℝ) < 3 / 10)
      (by linarith)
  linarith [sixteen_fifths_mul_two_mul_screwRegularKernel_three_tenths_le_neg_screwRegularKernel_three_twentieths]

/-- **Quarter-Window Harmonic-Doubling Excess Bound on `Ioo a b` (`L / 4 ≤ a ≤ b ≤ 3 / 20`, `screwSignThreshold ≤ 2 * a`)**:
retaining `(8 / 21)` coercivity on the positive kernel excess `(-K(x)) - (16 / 5) * (2 * K(2x)) ≥ 0`
and `(23 / 40)` harmonic-doubling coercivity (`α = 4 / 5`) on `(16 / 5) * (2 * K(2x)) ≥ 0` proves:
`((4 / 21) * (Φ(a) - Φ(b)) + (163 / 525) * (Φ(2 * b) - Φ(2 * a))) * ∫ h²`
`≤ (∫_{x ∈ Ioo a b} (-K(x)) D_h(x)) + ∫_{x ∈ Ioo a b} (2 K(2x)) (2 R(2x))`. -/
theorem quarter_harmonic_doubling_below_three_twentieths_le_setIntegral_Ioo_add_double_autocorr
    {A : Set ℝ} {h : ℝ → ℝ} {C L a b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u) (hL : 0 < L)
    (ha4 : L / 4 ≤ a) (hab : a ≤ b) (hb20 : b ≤ 3 / 20) (hta : screwSignThreshold ≤ 2 * a) :
    ((4 / 21 : ℝ) * (levyCoshPotential a - levyCoshPotential b) +
        (163 / 525 : ℝ) * (levyCoshPotential (2 * b) - levyCoshPotential (2 * a))) *
        (∫ u, h u ^ 2) ≤
      (∫ x in Ioo a b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ x in Ioo a b, (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x)) := by
  have ha0 : 0 < a := by linarith
  have hb_t : b ≤ screwSignThreshold := by
    linarith [screwSignThreshold_gt_6036_over_21509]
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
        (lt_trans ha0 hx.1) (hx.2.le.trans hb_t))
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
    ((8 / 21 : ℝ) * (-screwRegularKernel x) +
      (326 / 525 : ℝ) * (2 * screwRegularKernel (2 * x))) * ∫ u, h u ^ 2
  have hI_G : IntegrableOn G (Ioo a b) :=
    ((hI_K.const_mul (8 / 21 : ℝ)).add (hI_K2.const_mul (326 / 525 : ℝ))).mul_const _
  have hmono : (∫ x in Ioo a b, G x) ≤
      ∫ x in Ioo a b, ((-screwRegularKernel x) * (∫ u, (h u - h (u + x)) ^ 2) +
        (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))) := by
    refine setIntegral_mono_on hI_G (hI_jump.add hI_auto) measurableSet_Ioo fun x hx => ?_
    dsimp only [G]
    have hx0 : 0 < x := lt_trans ha0 hx.1
    have hK2_0 : 0 ≤ 2 * screwRegularKernel (2 * x) :=
      mul_nonneg zero_le_two (screwRegularKernel_nonneg_of_threshold_le
        (hta.trans (by linarith [hx.1])))
    have hexcess : 0 ≤ (-screwRegularKernel x) - (16 / 5 : ℝ) * (2 * screwRegularKernel (2 * x)) := by
      linarith [sixteen_fifths_mul_two_mul_screwRegularKernel_two_mul_le_neg_screwRegularKernel
        hx0 (hx.2.le.trans hb20)]
    have h4_coerc := eight_twenty_firsts_mul_integral_sq_le_integral_jump_sq_of_quarter_le
      hh hsupp hL.le (ha4.trans hx.1.le)
    have hhd := twenty_three_fortieths_mul_integral_sq_le_integral_jump_sq_add_autocorr hh x
    have hm1 := mul_le_mul_of_nonneg_left h4_coerc hexcess
    have hm2 := mul_le_mul_of_nonneg_left hhd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16 / 5) hK2_0)
    linarith
  have hval_G : (∫ x in Ioo a b, G x) =
      ((4 / 21 : ℝ) * (levyCoshPotential a - levyCoshPotential b) +
        (163 / 525 : ℝ) * (levyCoshPotential (2 * b) - levyCoshPotential (2 * a))) *
        ∫ u, h u ^ 2 := by
    dsimp only [G]
    rw [integral_mul_const,
      integral_add (hI_K.const_mul _) (hI_K2.const_mul _),
      integral_const_mul, integral_const_mul,
      setIntegral_Ioo_neg_screwRegularKernel ha0 hab,
      setIntegral_Ioo_two_mul_screwRegularKernel_two_mul ha0 hab]
    ring
  rw [hval_G, integral_add hI_jump hI_auto] at hmono
  linarith

/-- **Joint Quarter+Third Harmonic-Doubling Potential + Pair Bound on `Ioo (L / 4) screwSignThreshold` (`3 * screwSignThreshold / 2 ≤ L ≤ 9 / 20`)**:
splitting `Ioo (L / 4) screwSignThreshold` into `Ioo (L / 4) (screwSignThreshold / 2)`,
`Ioo (screwSignThreshold / 2) (L / 3)`, `Ioo (L / 3) (3 / 16)`, and `Ioo (3 / 16) screwSignThreshold`,
cancelling `Φ(screwSignThreshold / 2)`, and extracting the joint pair integral across
`Ioo (screwSignThreshold / 2) screwSignThreshold` yields:
`((4 / 21) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 82) * Φ(3 / 16) + (19549 / 172200) * Φ(2 * L / 3) + (323 / 1640) * Φ(3 / 8) - (851 / 1050) * Φ(screwSignThreshold)) * ∫ h² ≤ (∫_{x ∈ Ioo (L / 4) t_*} (-K(x)) D_h(x)) + pair_{t_*}(h)`. -/
theorem two_shell_harmonic_doubling_quarter_to_threshold_le_setIntegral_Ioo_add_pair
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u)
    (hL_low : 3 * screwSignThreshold / 2 ≤ L) (hL_high : L ≤ 9 / 20) :
    ((4 / 21 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 82 : ℝ) * levyCoshPotential (3 / 16) +
        (19549 / 172200 : ℝ) * levyCoshPotential (2 * L / 3) +
        (323 / 1640 : ℝ) * levyCoshPotential (3 / 8) -
        (851 / 1050 : ℝ) * levyCoshPotential screwSignThreshold) * (∫ u, h u ^ 2) ≤
      (∫ x in Ioo (L / 4) screwSignThreshold,
        (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ p : ℝ × ℝ, h p.1 * h p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity [screwSignThreshold_pos]) hL_low
  have hL4_pos : 0 < L / 4 := by linarith
  have ht2_pos : 0 < screwSignThreshold / 2 := by positivity [screwSignThreshold_pos]
  have hL4_t2 : L / 4 ≤ screwSignThreshold / 2 := by
    linarith [screwSignThreshold_gt_6036_over_21509]
  have ht2_L3 : screwSignThreshold / 2 ≤ L / 3 := by linarith
  have hL3_20 : L / 3 ≤ 3 / 20 := by linarith
  have hL3_16 : L / 3 ≤ 3 / 16 := by linarith
  have h16_t : (3 : ℝ) / 16 ≤ screwSignThreshold := by
    linarith [screwSignThreshold_gt_6036_over_21509]
  have hL3_t : L / 3 ≤ screwSignThreshold := le_trans hL3_16 h16_t
  have ht2_t : screwSignThreshold / 2 ≤ screwSignThreshold := le_trans ht2_L3 hL3_t
  have hL4_L3 : L / 4 ≤ L / 3 := le_trans hL4_t2 ht2_L3
  have hL4_t : L / 4 ≤ screwSignThreshold := le_trans hL4_L3 hL3_t
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  have hR0 : ∀ x, 0 ≤ 2 * autocorr h (2 * x) :=
    fun x => mul_nonneg zero_le_two (autocorr_nonneg hh hh0 (2 * x))
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 4) screwSignThreshold) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL4_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 4) screwSignThreshold) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL4_pos hx.1) hx.2.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_1 : IntegrableOn F (Ioc (L / 4) (screwSignThreshold / 2)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl ht2_t)
  have hIF_2 : IntegrableOn F (Ioc (screwSignThreshold / 2) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL4_t2 hL3_t)
  have hIF_3 : IntegrableOn F (Ioc (L / 3) (3 / 16)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL4_L3 h16_t)
  have hIF_4 : IntegrableOn F (Ioc (3 / 16) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo (hL4_L3.trans hL3_16) le_rfl)
  have hIF_12 : IntegrableOn F (Ioc (L / 4) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL3_t)
  have hIF_34 : IntegrableOn F (Ioc (L / 3) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL4_L3 le_rfl)
  have hdisj_12 : Disjoint (Ioc (L / 4) (screwSignThreshold / 2)) (Ioc (screwSignThreshold / 2) (L / 3)) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_34 : Disjoint (Ioc (L / 3) (3 / 16)) (Ioc (3 / 16) screwSignThreshold) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_1234 : Disjoint (Ioc (L / 4) (L / 3)) (Ioc (L / 3) screwSignThreshold) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit_F : (∫ x in Ioo (L / 4) screwSignThreshold, F x) =
      (∫ x in Ioo (L / 4) (screwSignThreshold / 2), F x) +
        (∫ x in Ioo (screwSignThreshold / 2) (L / 3), F x) +
        (∫ x in Ioo (L / 3) (3 / 16), F x) +
        ∫ x in Ioo (3 / 16) screwSignThreshold, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL4_L3 hL3_t,
      setIntegral_union hdisj_1234 measurableSet_Ioc hIF_12 hIF_34,
      ← Ioc_union_Ioc_eq_Ioc hL4_t2 ht2_L3,
      setIntegral_union hdisj_12 measurableSet_Ioc hIF_1 hIF_2,
      ← Ioc_union_Ioc_eq_Ioc hL3_16 h16_t,
      setIntegral_union hdisj_34 measurableSet_Ioc hIF_3 hIF_4]
    repeat rw [integral_Ioc_eq_integral_Ioo]
    ring
  let H : ℝ → ℝ := fun x => (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))
  have hK2m : Measurable fun x : ℝ => 2 * screwRegularKernel (2 * x) := by
    unfold screwRegularKernel; fun_prop
  have hR2m : Measurable fun x : ℝ => 2 * autocorr h (2 * x) :=
    measurable_two_mul_autocorr_two_mul hh
  have hHm : Measurable H := hK2m.mul hR2m
  have hcont_K2 : ContinuousOn (fun x => 2 * screwRegularKernel (2 * x))
      (Icc (screwSignThreshold / 2) screwSignThreshold) :=
    continuousOn_two_mul_screwRegularKernel_two_mul ht2_pos
  have hIH : IntegrableOn H (Ioo (screwSignThreshold / 2) screwSignThreshold) := by
    refine ((hcont_K2.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (2 * ∫ u, h u ^ 2)).mono' hHm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK2_0 : 0 ≤ 2 * screwRegularKernel (2 * x) :=
      mul_nonneg zero_le_two (screwRegularKernel_nonneg_of_threshold_le (by linarith [hx.1]))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK2_0 (hR0 x))]
    have hR_le : 2 * autocorr h (2 * x) ≤ 2 * ∫ u, h u ^ 2 := by
      have hid := integral_jump_sq hh (2 * x)
      have hD_nn := hD0 (2 * x)
      linarith
    exact mul_le_mul_of_nonneg_left hR_le hK2_0
  have hIH_2 : IntegrableOn H (Ioc (screwSignThreshold / 2) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIH.mono_set (Ioo_subset_Ioo le_rfl hL3_t)
  have hIH_3 : IntegrableOn H (Ioc (L / 3) (3 / 16)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIH.mono_set (Ioo_subset_Ioo ht2_L3 h16_t)
  have hIH_4 : IntegrableOn H (Ioc (3 / 16) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIH.mono_set (Ioo_subset_Ioo (ht2_L3.trans hL3_16) le_rfl)
  have hIH_34 : IntegrableOn H (Ioc (L / 3) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIH.mono_set (Ioo_subset_Ioo ht2_L3 le_rfl)
  have hdisj_H234 : Disjoint (Ioc (screwSignThreshold / 2) (L / 3)) (Ioc (L / 3) screwSignThreshold) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit_H : (∫ x in Ioo (screwSignThreshold / 2) screwSignThreshold, H x) =
      (∫ x in Ioo (screwSignThreshold / 2) (L / 3), H x) +
        (∫ x in Ioo (L / 3) (3 / 16), H x) +
        ∫ x in Ioo (3 / 16) screwSignThreshold, H x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc ht2_L3 hL3_t,
      setIntegral_union hdisj_H234 measurableSet_Ioc hIH_2 hIH_34,
      ← Ioc_union_Ioc_eq_Ioc hL3_16 h16_t,
      setIntegral_union hdisj_34 measurableSet_Ioc hIH_3 hIH_4]
    repeat rw [integral_Ioc_eq_integral_Ioo]
    ring
  have h1 := four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL4_t2 ht2_t
  have h2 := quarter_harmonic_doubling_below_three_twentieths_le_setIntegral_Ioo_add_double_autocorr
    hh hsupp hh0 hL0 hL4_t2 ht2_L3 hL3_20 (by linarith : screwSignThreshold ≤ 2 * (screwSignThreshold / 2))
  have h3 := harmonic_doubling_below_three_sixteenths_le_setIntegral_Ioo_add_double_autocorr
    hh hsupp hh0 hL0 le_rfl hL3_16 (by linarith : screwSignThreshold ≤ 2 * (L / 3))
  have h4 := half_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_double_autocorr
    hh hsupp hh0 hL0 le_rfl hL3_16 h16_t le_rfl
  have hpair := setIntegral_Ioo_two_mul_screwRegularKernel_two_mul_autocorr_le_pair
    hh hsupp hh0 hL0 le_rfl (by linarith : screwSignThreshold ≤ 2 * (screwSignThreshold / 2)) ht2_t
  dsimp only [F] at hsplit_F
  dsimp only [H] at hsplit_H
  rw [show 2 * (L / 3) = 2 * L / 3 by ring,
    show 2 * (screwSignThreshold / 2) = screwSignThreshold by ring] at h2
  rw [show 2 * (L / 3) = 2 * L / 3 by ring] at h3
  linarith

/-- **Full Eleven-Point Two-Shell Harmonic-Doubling Potential + Pair Coercivity on `Ioo (L / 10) screwSignThreshold` (`3 * screwSignThreshold / 2 ≤ L ≤ 9 / 20`)**:
combining `(L / 10, L / 4)` with `two_shell_harmonic_doubling_quarter_to_threshold_le_setIntegral_Ioo_add_pair`
on `(L / 4, screwSignThreshold)` yields:
`((1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 82) * Φ(3 / 16) + (19549 / 172200) * Φ(2 * L / 3) + (323 / 1640) * Φ(3 / 8) - (851 / 1050) * Φ(screwSignThreshold)) * ∫ h² ≤ (∫_{x ∈ Ioo (L / 10) t_*} (-K(x)) D_h(x)) + pair_{t_*}(h)`. -/
theorem two_shell_harmonic_doubling_tenth_to_threshold_le_setIntegral_Ioo_add_pair
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u)
    (hL_low : 3 * screwSignThreshold / 2 ≤ L) (hL_high : L ≤ 9 / 20) :
    ((1 / 25 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (3 / 200 : ℝ) * levyCoshPotential (L / 7) +
        (1 / 45 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (2 / 35 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 82 : ℝ) * levyCoshPotential (3 / 16) +
        (19549 / 172200 : ℝ) * levyCoshPotential (2 * L / 3) +
        (323 / 1640 : ℝ) * levyCoshPotential (3 / 8) -
        (851 / 1050 : ℝ) * levyCoshPotential screwSignThreshold) * (∫ u, h u ^ 2) ≤
      (∫ x in Ioo (L / 10) screwSignThreshold,
        (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ p : ℝ × ℝ, h p.1 * h p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity [screwSignThreshold_pos]) hL_low
  have hL10_pos : 0 < L / 10 := by linarith
  have hL10_4 : L / 10 ≤ L / 4 := by linarith
  have hL5_4 : L / 5 ≤ L / 4 := by linarith
  have hL4_t : L / 4 ≤ screwSignThreshold := by
    linarith [screwSignThreshold_gt_6036_over_21509]
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
  have hIF_1 : IntegrableOn F (Ioc (L / 10) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL4_t)
  have hIF_2 : IntegrableOn F (Ioc (L / 4) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL10_4 le_rfl)
  have hdisj : Disjoint (Ioc (L / 10) (L / 4)) (Ioc (L / 4) screwSignThreshold) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 10) screwSignThreshold, F x) =
      (∫ x in Ioo (L / 10) (L / 4), F x) + ∫ x in Ioo (L / 4) screwSignThreshold, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL10_4 hL4_t,
      setIntegral_union hdisj measurableSet_Ioc hIF_1 hIF_2,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h105 := tenth_to_fifth_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL5_4 hL4_t
  have h4t := two_shell_harmonic_doubling_quarter_to_threshold_le_setIntegral_Ioo_add_pair
    hh hsupp hh0 hL_low hL_high
  dsimp only [F] at hsplit
  linarith

/-- **Two-Shell Harmonic-Doubling Lévy–Cosh Crossover Lower Bound for `weilArchRe` (`3 * screwSignThreshold / 2 ≤ L ≤ 9 / 20`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L`,
`(A(0) + (1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 82) * Φ(3 / 16) + (19549 / 172200) * Φ(2 * L / 3) + (323 / 1640) * Φ(3 / 8) + (199 / 1050) * Φ(screwSignThreshold)) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem two_shell_harmonic_doubling_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL_low : 3 * screwSignThreshold / 2 ≤ L) (hL_high : L ≤ 9 / 20)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (3 / 200) * levyCoshPotential (L / 7) +
        (1 / 45) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (17 / 82) * levyCoshPotential (3 / 16) +
        (19549 / 172200) * levyCoshPotential (2 * L / 3) +
        (323 / 1640) * levyCoshPotential (3 / 8) +
        (199 / 1050) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity [screwSignThreshold_pos]) hL_low
  have hL10 : 0 < L / 10 := by linarith
  have hL10t : L / 10 ≤ screwSignThreshold := by
    linarith [screwSignThreshold_gt_6036_over_21509]
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL10 hL10t le_rfl
  have hsplit := two_shell_harmonic_doubling_tenth_to_threshold_le_setIntegral_Ioo_add_pair
    hB hsupp hf0 hL_low hL_high
  linarith

/-- Exact 5-smooth factorization of `log(1 / (π * (9 / 20)))` via
`1 / (π * (9 / 20)) = (4 / 3)^2 * (5 / 4)^2 / (4 * (5 * π / 16))` and `log(5 * π / 16) ≤ 5 * π / 16 - 1`:
`-2 * Real.log 2 + 2 * Real.log (4 / 3) + 2 * Real.log (5 / 4) + 1 - 5 * Real.pi / 16 ≤ Real.log (1 / (Real.pi * (9 / 20)))`. -/
theorem log_inv_pi_mul_nine_twentieths_ge :
    -2 * Real.log 2 + 2 * Real.log (4 / 3) + 2 * Real.log (5 / 4) + 1 -
        5 * Real.pi / 16 ≤ Real.log (1 / (Real.pi * (9 / 20))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog4 : 2 * Real.log 2 = Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog43 : 2 * Real.log (4 / 3) = Real.log (16 / 9) := by
    rw [show (16 / 9 : ℝ) = (4 / 3) ^ 2 by norm_num, Real.log_pow]; ring
  have hlog54 : 2 * Real.log (5 / 4) = Real.log (25 / 16) := by
    rw [show (25 / 16 : ℝ) = (5 / 4) ^ 2 by norm_num, Real.log_pow]; ring
  have hsplit : Real.log (1 / (Real.pi * (9 / 20))) + 2 * Real.log 2 +
      Real.log (5 * Real.pi / 16) = 2 * Real.log (4 / 3) + 2 * Real.log (5 / 4) := by
    rw [hlog4, hlog43, hlog54, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by norm_num) (by norm_num)]
    congr 1; field_simp; ring
  have hpi_log : Real.log (5 * Real.pi / 16) ≤ 5 * Real.pi / 16 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  linarith

/-- **Fourth-Order Osculating Lower Bound for the Eleven-Point Harmonic-Doubling Potential at `L = 9 / 20`**:
every logarithm at `L = 9 / 20` factors into `log 2`, `log(4 / 3)`, `log(5 / 4)`, and `log(7 / 6)`. -/
theorem osculating_le_two_shell_harmonic_doubling_potential_nine_twentieths :
    Real.log (1 / (Real.pi * (9 / 20))) + (9913 / 12600 : ℝ) * Real.log 2 -
        (3089 / 2520 : ℝ) * Real.log (4 / 3) -
        (133717 / 258300 : ℝ) * Real.log (5 / 4) +
        (859 / 4200 : ℝ) * Real.log (7 / 6) +
        (2325431 / 2870000 : ℝ) +
        (2494473097027 / 648023040000000 : ℝ) +
        (199 / 1050 : ℝ) * (screwSignThreshold ^ 2 / 48 + (5 / 27 : ℝ) * screwSignThreshold ^ 3) -
        eulerMascheroniConstant ≤
      EF.gammaBracket 0 + (1 / 25) * levyCoshPotential ((9 / 20 : ℝ) / 10) +
        (1 / 50) * levyCoshPotential ((9 / 20 : ℝ) / 8) +
        (3 / 200) * levyCoshPotential ((9 / 20 : ℝ) / 7) +
        (1 / 45) * levyCoshPotential ((9 / 20 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((9 / 20 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((9 / 20 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((9 / 20 : ℝ) / 3) +
        (17 / 82) * levyCoshPotential (3 / 16) +
        (19549 / 172200) * levyCoshPotential (2 * (9 / 20 : ℝ) / 3) +
        (323 / 1640) * levyCoshPotential (3 / 8) +
        (199 / 1050) * levyCoshPotential screwSignThreshold := by
  let L : ℝ := 9 / 20
  have hL : 0 < L := by norm_num
  have h10 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by linarith : 0 < L / 10)
  have h8 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by linarith : 0 < L / 8)
  have h7 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by linarith : 0 < L / 7)
  have h6 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by linarith : 0 < L / 6)
  have h5 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by linarith : 0 < L / 5)
  have h4 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by linarith : 0 < L / 4)
  have h3 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by linarith : 0 < L / 3)
  have hb0 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < 3 / 16)
  have h2L3 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by linarith : 0 < 2 * L / 3)
  have h2b0 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < 3 / 8)
  have hc :=
    log_seven_div_four_pi_add_one_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      screwSignThreshold_pos
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
      Real.log (1 / (Real.pi * L)) + Real.log 2 - Real.log (4 / 3) - Real.log (5 / 4) := by
    have h : Real.log (1 / (2 * Real.pi * (3 / 16))) + Real.log (4 / 3) + Real.log (5 / 4) =
        Real.log (1 / (Real.pi * L)) + Real.log 2 := by
      rw [← Real.log_mul (by positivity) (by norm_num),
        ← Real.log_mul (by positivity) (by norm_num),
        ← Real.log_mul (by positivity) (by norm_num)]
      congr 1; field_simp [L]; ring
    linarith
  have hlog_2L3 : Real.log (1 / (2 * Real.pi * (2 * L / 3))) =
      Real.log (1 / (Real.pi * L)) - Real.log (4 / 3) := by
    rw [eq_sub_iff_add_eq, ← Real.log_mul (by positivity) (by norm_num)]
    congr 1; field_simp; ring
  have hlog_2b0 : Real.log (1 / (2 * Real.pi * (3 / 8))) =
      Real.log (1 / (Real.pi * L)) - Real.log (4 / 3) - Real.log (5 / 4) := by
    have h : Real.log (1 / (2 * Real.pi * (3 / 8))) + Real.log (4 / 3) + Real.log (5 / 4) =
        Real.log (1 / (Real.pi * L)) := by
      rw [← Real.log_mul (by positivity) (by norm_num),
        ← Real.log_mul (by positivity) (by norm_num)]
      congr 1; field_simp [L]; ring
    linarith
  have hlog_c : Real.log (7 / (4 * Real.pi)) =
      Real.log (1 / (Real.pi * L)) + Real.log 2 - 3 * Real.log (4 / 3) -
        Real.log (5 / 4) + Real.log (7 / 6) := by
    have h64_27 : 3 * Real.log (4 / 3) = Real.log (64 / 27) := by
      rw [show (64 / 27 : ℝ) = (4 / 3) ^ 3 by norm_num, Real.log_pow]; ring
    have h : Real.log (7 / (4 * Real.pi)) + Real.log (64 / 27) + Real.log (5 / 4) =
        Real.log (1 / (Real.pi * L)) + Real.log 2 + Real.log (7 / 6) := by
      rw [← Real.log_mul (by positivity) (by norm_num),
        ← Real.log_mul (by positivity) (by norm_num),
        ← Real.log_mul (by positivity) (by norm_num),
        ← Real.log_mul (by positivity) (by norm_num)]
      congr 1; field_simp [L]; ring
    linarith
  linarith

/-- **Strict Positivity of the Two-Shell Harmonic-Doubling Potential at `L = 9 / 20` (`= 0.45`, `64.92%` of `(0, log 2)`)**:
certified rational margin `+0.000250 > 0`. -/
theorem zero_le_two_shell_harmonic_doubling_potential_nine_twentieths :
    0 ≤ EF.gammaBracket 0 + (1 / 25) * levyCoshPotential ((9 / 20 : ℝ) / 10) +
        (1 / 50) * levyCoshPotential ((9 / 20 : ℝ) / 8) +
        (3 / 200) * levyCoshPotential ((9 / 20 : ℝ) / 7) +
        (1 / 45) * levyCoshPotential ((9 / 20 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((9 / 20 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((9 / 20 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((9 / 20 : ℝ) / 3) +
        (17 / 82) * levyCoshPotential (3 / 16) +
        (19549 / 172200) * levyCoshPotential (2 * (9 / 20 : ℝ) / 3) +
        (323 / 1640) * levyCoshPotential (3 / 8) +
        (199 / 1050) * levyCoshPotential screwSignThreshold := by
  have hosc := osculating_le_two_shell_harmonic_doubling_potential_nine_twentieths
  have hlog_pi := log_inv_pi_mul_nine_twentieths_ge
  have hlog76 := log_seven_sixths_eq
  have hlog2_lt := Real.log_two_lt_d9
  have hlog5 := Real.log_five_gt_d9
  have hlog54 := log_five_sub_two_mul_log_two_eq_log_five_fourths
  have hlog43 := log_five_sub_two_mul_log_two_add_two_thirty_firsts_lt_log_four_thirds
  have hlog35 := six_sixty_sevenths_lt_log_35_32
  have hc_sq : ((6036 : ℝ) / 21509) ^ 2 ≤ screwSignThreshold ^ 2 :=
    pow_le_pow_left₀ (by norm_num) screwSignThreshold_gt_6036_over_21509.le 2
  have hc_cub : ((6036 : ℝ) / 21509) ^ 3 ≤ screwSignThreshold ^ 3 :=
    pow_le_pow_left₀ (by norm_num) screwSignThreshold_gt_6036_over_21509.le 3
  have hpi := Real.pi_lt_d4
  have hgamma :=
    RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith

/-- **Unconditional Archimedean Weil Positivity on `(0, 9 / 20)` (`= (0, 0.45)`, `64.92%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` supported in `Ioo 0 L` with `L ≤ 9 / 20`,
`0 ≤ WeilOneSided.weilArchRe (EF.weilTest f f)`. -/
theorem weilArchRe_nonneg_of_support_Ioo_le_nine_twentieths {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL : L ≤ 9 / 20) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_9_20 : ∀ u ∉ Ioo (0 : ℝ) (9 / 20), f u = 0 :=
    fun u hu => hsupp u fun huL => hu ⟨huL.1, huL.2.trans_le hL⟩
  have hmain := two_shell_harmonic_doubling_levyCosh_crossover_le_weilArchRe
    hf hfc hf0
    (by linarith [screwSignThreshold_lt_thirty_eight_over_one_thirty_five] :
      3 * screwSignThreshold / 2 ≤ 9 / 20)
    (by norm_num : (9 / 20 : ℝ) ≤ 9 / 20)
    hsupp_9_20
  have hpot := zero_le_two_shell_harmonic_doubling_potential_nine_twentieths
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact le_trans (mul_nonneg hpot hsq) hmain

/-- **Unconditional `WindowPositive` on `(0, 9 / 20)` (`= (0, 0.45)`, `64.92%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (9 / 20)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_nine_twentieths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (9 / 20)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_nine_twentieths hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 4 / 9)` (`≈ (0, 0.444444)`, `64.12%` of `(0, log 2)`)**:
immediate corollary since `4 / 9 ≤ 9 / 20` (`80 ≤ 81`). -/
theorem windowPositive_four_ninths' (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (4 / 9)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_nine_twentieths hf hfc hf0 (by norm_num : (4 : ℝ) / 9 ≤ 9 / 20)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 7 / 16)` (`= (0, 0.4375)`, `63.12%` of `(0, log 2)`)**:
immediate corollary since `7 / 16 ≤ 9 / 20` (`140 ≤ 144`). -/
theorem windowPositive_seven_sixteenths' (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (7 / 16)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_nine_twentieths hf hfc hf0 (by norm_num : (7 : ℝ) / 16 ≤ 9 / 20)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

end

end RHTower.WeilLevyMidpointCoreOverlap
