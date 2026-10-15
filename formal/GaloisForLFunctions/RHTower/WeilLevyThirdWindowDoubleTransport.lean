import GaloisForLFunctions.RHTower.WeilLevyEighthWindowCoercivity

/-!
# Third-Window Double-Collar Core Transport (`24 / 41`), Global Minimum Osculating Law, and Unconditional Positivity on `(0, 2 / 5)`

This module implements **Cycle 72** of the prime-blind archimedean Weil positivity programme,
discovering the **double-collar core transport law on `[L / 3, L / 2]`** (`D_h(x) ≥ (24 / 41) ∫ h²`,
within `0.00042` of the spectral limit `4 sin²(π / 8) = 2 - √2 ≈ 0.585786`), the **global minimum
osculating law** `F_osc(c) ≥ F_osc(2 / 7) = log(7 / (4π)) + 1 - γ` valid for all `c > 0`, and the
resulting **seven-point reflected potential** proving unconditional `WindowPositive` on
**`(0, 2 / 5)`** (`= (0, 0.40)`, **`57.71%` of `(0, log 2)`**).

## Mathematical Architecture

1. **Section 1 — Double-Collar Core Transport on `[L / 3, L / 2]` (`D_h(x) ≥ (24 / 41) ∫ h²`)**:
   - For $x \in [L / 3, L / 2]$, the core $\mathrm{Ioc}\,x\,(L - x)$ has length $L - 2x \le x$.
     Therefore:
     - the left collar sub-interval $J_L = \mathrm{Ioc}\,0\,(L - 2x) \subseteq \mathrm{Ioc}\,0\,x$
       shifts by $+x$ onto the **entire core** $\mathrm{Ioc}\,x\,(L - x)$,
     - the core itself $J_C = \mathrm{Ioc}\,x\,(L - x)$ shifts by $+x$ onto
       $\mathrm{Ioc}\,(2x)\,L \subseteq \mathrm{Ioc}\,(L - x)\,L$ inside the right collar, and
     - because $x \ge L / 3 \iff L - 2x \le x$, $J_L$ and $J_C$ are **disjoint** inside
       $\mathrm{Ioc}\,0\,(L - x)$!
   - Applying the single-square Pell-convergent SOS identity
     $$(p - q)^2 - \left(\frac{12}{41} p^2 - \frac{12}{29} q^2\right)
       = \frac{29}{41}\left(p - \frac{41}{29} q\right)^2 \ge 0$$
     on both $J_L$ and $J_C$ counts $\operatorname{coreMass}_h(L, x)$ **twice**, giving
     $$\frac{24}{41}\operatorname{coreMass}_h(L, x) - \frac{12}{29}\operatorname{collarMass}_h(L, x)
       \le \int_{\mathrm{Ioc}\,0\,(L - x)} (h(u) - h(u + x))^2\,du.$$
   - Combining with boundary collar escape (`1 - 12 / 29 = 17 / 29 = 697 / 1189 ≥ 696 / 1189 = 24 / 41`)
     proves:
     $$\frac{24}{41}\int_{\mathbb R} h(u)^2\,du \le \int_{\mathbb R} (h(u) - h(u + x))^2\,du
       \qquad \forall x \ge \frac{L}{3}$$
     (a $+53.6\%$ jump over the quarter-window constant $8 / 21 \approx 0.380952$).

2. **Section 2 — Third-Window Potential Integrals, Five-Shell `(0, log 2)` Plastic Floor, and Global Minimum Osculating Law**:
   - Because $(\log 2) / 3 \approx 0.231049 < t_* \approx 0.280627$, upgrading the sub-interval
     $((\log 2) / 3, t_*)$ from $8 / 21$ to $24 / 41$ yields a five-shell universal `(0, log 2)`
     plastic floor with weights $(3/50,\ 67/1800,\ 47/504,\ 88/861,\ 29/41)$ at
     $((\log 2)/8,\ (\log 2)/6,\ (\log 2)/4,\ (\log 2)/3,\ t_*)$.
   - Moreover, since $t \mapsto \log(1 / (2\pi t)) + (7 / 2) t - \gamma$ attains its global minimum
     on $(0, \infty)$ at $t = 2 / 7$, we prove the parameter-free universal lower bound
     $$\log\left(\frac{7}{4\pi}\right) + 1 - \gamma \le \mathrm{EF.gammaBracket}\ 0 + \Phi(c)
       \qquad \forall c > 0.$$

3. **Section 3 — Seven-Point Reflected Potential and Unconditional Positivity on `(0, 2 / 5)` (`= (0, 0.40)`)**:
   - Combining `(L / 8, L / 4)`, `(L / 4, L - c)`, the outer reflected shell
     `(L - c, L / 3) ∪ (2 L / 3, c)`, and the inner reflected shell `(L / 3, 2 L / 3)` yields the
     seven-point potential floor with weights
     $(3/50,\ 67/1800,\ 47/504,\ 88/861,\ 17/41,\ 88/861,\ 4/21)$ at
     $(L/8,\ L/6,\ L/4,\ L/3,\ L/2,\ 2L/3,\ c)$ for $2 L / 3 \le c \le 3 L / 4$.
   - At $L = 2 / 5 = 0.40$ and $c = t_*$, the seven-point potential is strictly positive
     (`+0.00230 > 0`), proving unconditional `WindowPositive` on **`(0, 2 / 5)`**
     (**`57.71%` of `(0, log 2)`**).
-/

open Complex Real Set MeasureTheory Filter
open scoped Topology
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyThirdWindow

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor
open RHTower.WeilLevyQuarterWindow RHTower.WeilLevySymmetricThreePoint
open RHTower.WeilLevySixthWindow RHTower.WeilLevyFibonacciStaircase
open RHTower.WeilLevyEighthWindow

/-! ## Section 1: Double-Collar Core Transport on `[L / 3, L / 2]` (`D_h(x) ≥ (24 / 41) ∫ h²`) -/

/-- Exact Pell-convergent SOS inequality (`(12 / 41, 12 / 29)`): for all `p, q : ℝ`,
`(12 / 41) * p ^ 2 - (12 / 29) * q ^ 2 ≤ (p - q) ^ 2`, proved via the exact single-square identity
`(p - q) ^ 2 - ((12 / 41) * p ^ 2 - (12 / 29) * q ^ 2) = (29 / 41) * (p - (41 / 29) * q) ^ 2 ≥ 0`. -/
theorem twelve_forty_firsts_sq_sub_twelve_twenty_ninths_sq_le_sub_sq (p q : ℝ) :
    (12 / 41 : ℝ) * p ^ 2 - (12 / 29 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  nlinarith [sq_nonneg (p - (41 / 29 : ℝ) * q)]

/-- **Double-Collar Core Transport Inequality on `[L / 3, L / 2]`**:
for any `BddSupp A h C` and `x ∈ [L / 3, L / 2]`, the two shift intervals `Ioc 0 (L - 2 * x)`
(which shifts by `+x` onto the entire core `Ioc x (L - x)`) and `Ioc x (L - x)` (the entire core,
which shifts by `+x` into the right collar `Ioc (L - x) L`) are disjoint inside `Ioc 0 (L - x)`,
yielding:
`(24 / 41) * coreMass h L x - (12 / 29) * collarMass h L x ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`. -/
theorem double_collar_coreMass_sub_collarMass_le_interior_jump_sq
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C) (hx3 : L / 3 ≤ x)
    (hx2 : x ≤ L / 2) :
    (24 / 41 : ℝ) * coreMass h L x - (12 / 29 : ℝ) * collarMass h L x ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  -- Left transport: `Ioc 0 (L - 2 * x) ⊆ Iic x` shifts by `+x` onto `Ioc x (L - x)`
  have hleft_pt : ∀ u : ℝ,
      (12 / 41 : ℝ) * h (u + x) ^ 2 - (12 / 29 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := twelve_forty_firsts_sq_sub_twelve_twenty_ninths_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have hleft : (12 / 41 : ℝ) * (∫ v in Ioc x (L - x), h v ^ 2) -
      (12 / 29 : ℝ) * (∫ u in Iic x, h u ^ 2) ≤
      ∫ u in Ioc 0 (L - 2 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc 0 (L - 2 * x))
      ((hshift.const_mul (12 / 41)).integrableOn.sub (hsq.const_mul (12 / 29)).integrableOn)
      hjump.integrableOn hleft_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (12 / 41)).integrableOn (hsq.const_mul (12 / 29)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 (L - 2 * x) x, zero_add,
      show L - 2 * x + x = L - x by ring] at h1
    have hsub_L : Ioc 0 (L - 2 * x) ⊆ Iic x :=
      fun u hu => hu.2.trans (by linarith)
    have hmono_L : (∫ u in Ioc 0 (L - 2 * x), h u ^ 2) ≤ ∫ u in Iic x, h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall hsub_L)
    linarith
  -- Right transport: `Ioc x (L - x)` shifts by `+x` onto `Ioc (2 * x) L ⊆ Ioi (L - x)`
  have hright_pt : ∀ u : ℝ,
      (12 / 41 : ℝ) * h u ^ 2 - (12 / 29 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => twelve_forty_firsts_sq_sub_twelve_twenty_ninths_sq_le_sub_sq (h u) (h (u + x))
  have hright : (12 / 41 : ℝ) * (∫ u in Ioc x (L - x), h u ^ 2) -
      (12 / 29 : ℝ) * (∫ v in Ioi (L - x), h v ^ 2) ≤
      ∫ u in Ioc x (L - x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc x (L - x))
      ((hsq.const_mul (12 / 41)).integrableOn.sub (hshift.const_mul (12 / 29)).integrableOn)
      hjump.integrableOn hright_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (12 / 41)).integrableOn (hshift.const_mul (12 / 29)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) x (L - x) x,
      show x + x = 2 * x by ring, show L - x + x = L by ring] at h1
    have hsub_R : Ioc (2 * x) L ⊆ Ioi (L - x) :=
      fun v hv => lt_of_le_of_lt (by linarith) hv.1
    have hmono_R : (∫ v in Ioc (2 * x) L, h v ^ 2) ≤ ∫ v in Ioi (L - x), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall hsub_R)
    linarith
  -- Disjoint union of `Ioc 0 (L - 2 * x)` and `Ioc x (L - x)` inside `Ioc 0 (L - x)`
  have hdisj : Disjoint (Ioc 0 (L - 2 * x)) (Ioc x (L - x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hsub : Ioc 0 (L - 2 * x) ∪ Ioc x (L - x) ⊆ Ioc 0 (L - x) := by
    intro u hu
    rcases hu with hu1 | hu2
    · exact ⟨hu1.1, by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], hu2.2⟩
  have hunion : (∫ u in Ioc 0 (L - 2 * x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc x (L - x), (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj measurableSet_Ioc hjump.integrableOn hjump.integrableOn]
    exact setIntegral_mono_set hjump.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall hsub)
  unfold coreMass collarMass
  linarith

/-- **Universal Third-Window Coercivity (`(24 / 41) * ∫ h² ≤ D_h(x)` for all `x ≥ L / 3`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and **every shift `x ≥ L / 3`**,
`(24 / 41) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem twenty_four_forty_firsts_mul_integral_sq_le_integral_jump_sq_of_third_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 3 ≤ x) :
    (24 / 41 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  rcases le_or_gt x (L / 2) with hle | hgt
  · have hx0 : 0 ≤ x := by linarith
    have hcol_int := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
    have hdbl := double_collar_coreMass_sub_collarMass_le_interior_jump_sq hh hx hle
    have hcons := collarMass_add_coreMass_eq hh hle
    have hcol_nn := collarMass_nonneg h L x
    linarith
  · have hhalf := integral_sq_le_integral_jump_sq_of_half_le hh hsupp hL0 hgt.le
    have hE0 : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith

/-- **Universal Third-Window Autocorrelation Damping (`2 R(x) ≤ (58 / 41) R(0)` for all `x ≥ L / 3`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and every shift `x ≥ L / 3`,
`2 * autocorr h x ≤ (58 / 41) * ∫ u, h u ^ 2`. -/
theorem two_mul_autocorr_le_fifty_eight_forty_firsts_mul_integral_sq_of_third_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 3 ≤ x) :
    2 * autocorr h x ≤ (58 / 41 : ℝ) * ∫ u, h u ^ 2 := by
  have hid := integral_jump_sq hh x
  have hcoerc := twenty_four_forty_firsts_mul_integral_sq_le_integral_jump_sq_of_third_le
    hh hsupp hL0 hx
  linarith

/-! ## Section 2: Third-Window Potential Integrals, Five-Shell `(0, log 2)` Plastic Floor, and Global Minimum Osculating Law -/

/-- Integrating `(24 / 41)` coercivity against `-screwRegularKernel x ≥ 0` over `Ioo a c`
(`L / 3 ≤ a ≤ c ≤ screwSignThreshold`) yields
`(12 / 41) * (Φ(a) - Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo a c} (-screwRegularKernel x) D_h(x) dx`. -/
theorem twelve_forty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L a c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL : 0 < L) (ha : L / 3 ≤ a) (hac : a ≤ c)
    (hct : c ≤ screwSignThreshold) :
    (12 / 41 : ℝ) * (levyCoshPotential a - levyCoshPotential c) * (∫ u, h u ^ 2) ≤
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
    refine (hI_K.mul_const (4 * ∫ u, h u ^ 2)).mono' (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hI_low : IntegrableOn
      (fun x : ℝ => (-screwRegularKernel x) * ((24 / 41 : ℝ) * ∫ u, h u ^ 2)) (Ioo a c) :=
    hI_K.mul_const _
  have hmono : (∫ x in Ioo a c, (-screwRegularKernel x) * ((24 / 41 : ℝ) * ∫ u, h u ^ 2)) ≤
      ∫ x in Ioo a c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
    refine setIntegral_mono_on hI_low hI_jump measurableSet_Ioo fun x hx => ?_
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hct))
    exact mul_le_mul_of_nonneg_left
      (twenty_four_forty_firsts_mul_integral_sq_le_integral_jump_sq_of_third_le hh hsupp hL.le
        (ha.trans hx.1.le))
      hK0
  rw [integral_mul_const, setIntegral_Ioo_neg_screwRegularKernel ha0 hac] at hmono
  linarith

/-- **Four-Shell Eighth + Sixth + Quarter + Third Jump-Integral Lower Bound on `Ioo (L / 8) c` (`L / 3 ≤ c ≤ screwSignThreshold`)**:
combining `(L / 8, L / 4)`, `(L / 4, L / 3)`, and `(L / 3, c)` yields:
`((3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (88 / 861) * Φ(L / 3) - (12 / 41) * Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo (L / 8) c} (-K(x)) D_h(x) dx`. -/
theorem four_shell_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL : 0 < L) (hL3c : L / 3 ≤ c)
    (hct : c ≤ screwSignThreshold) :
    ((3 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (67 / 1800 : ℝ) * levyCoshPotential (L / 6) +
        (47 / 504 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) -
        (12 / 41 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 8) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL8 : 0 < L / 8 := by linarith
  have hL8_4 : L / 8 ≤ L / 4 := by linarith
  have hL6_4 : L / 6 ≤ L / 4 := by linarith
  have hL4_3 : L / 4 ≤ L / 3 := by linarith
  have hL4t : L / 4 ≤ screwSignThreshold := (hL4_3.trans hL3c).trans hct
  have hL3t : L / 3 ≤ screwSignThreshold := hL3c.trans hct
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 8) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL8 hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 8) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL8 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_1_Ioc : IntegrableOn F (Ioc (L / 8) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl (hL4_3.trans hL3c))
  have hIF_2_Ioc : IntegrableOn F (Ioc (L / 4) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL8_4 hL3c)
  have hIF_3_Ioc : IntegrableOn F (Ioc (L / 3) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo (hL8_4.trans hL4_3) le_rfl)
  have hIF_12_Ioc : IntegrableOn F (Ioc (L / 8) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL3c)
  have hdisj_12 : Disjoint (Ioc (L / 8) (L / 4)) (Ioc (L / 4) (L / 3)) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_123 : Disjoint (Ioc (L / 8) (L / 3)) (Ioc (L / 3) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 8) c, F x) =
      (∫ x in Ioo (L / 8) (L / 4), F x) + (∫ x in Ioo (L / 4) (L / 3), F x) +
        ∫ x in Ioo (L / 3) c, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (hL8_4.trans hL4_3) hL3c,
      setIntegral_union hdisj_123 measurableSet_Ioc hIF_12_Ioc hIF_3_Ioc,
      ← Ioc_union_Ioc_eq_Ioc hL8_4 hL4_3,
      setIntegral_union hdisj_12 measurableSet_Ioc hIF_1_Ioc hIF_2_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h86 := eighth_add_sixth_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL hL6_4 hL4t
  have h4 := four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL le_rfl hL4_3 hL3t
  have h3 := twelve_forty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL le_rfl hL3c hct
  dsimp only [F] at hsplit
  linarith

/-- **Four-Shell Eighth + Sixth + Quarter + Third Lévy–Cosh Crossover Inequality**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and `L / 3 ≤ c ≤ screwSignThreshold`,
`(A(0) + (3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (29 / 41) * Φ(c)) * ∫ f² + ... ≤ W_∞(f ⋆ f̃)`. -/
theorem four_shell_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L)
    (hL3c : L / 3 ≤ c) (hct : c ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (47 / 504) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (29 / 41) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL8 : 0 < L / 8 := by linarith
  have hL8c : L / 8 ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL8 hL8c hct
  have hfour := four_shell_sub_levyCoshPotential_le_setIntegral_Ioo hB hsupp hL hL3c hct
  linarith

/-- **Third-Window Universal Plastic Floor on `(0, log 2)`**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 (Real.log 2)`,
`(A(0) + (3 / 50) * Φ((log 2)/8) + (67 / 1800) * Φ((log 2)/6) + (47 / 504) * Φ((log 2)/4) + (88 / 861) * Φ((log 2)/3) + (29 / 41) * Φ(t_*)) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem third_window_log_two_plastic_floor_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hsupp : ∀ u ∉ Ioo 0 (Real.log 2), f u = 0) :
    (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (Real.log 2 / 8) +
        (67 / 1800) * levyCoshPotential (Real.log 2 / 6) +
        (47 / 504) * levyCoshPotential (Real.log 2 / 4) +
        (88 / 861) * levyCoshPotential (Real.log 2 / 3) +
        (29 / 41) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL3t : Real.log 2 / 3 ≤ screwSignThreshold := by
    linarith [Real.log_two_lt_d9, screwSignThreshold_gt]
  have hmain := four_shell_levyCosh_crossover_le_weilArchRe
    hf hfc hL hL3t le_rfl hsupp
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-- **Parameter-Free Global Minimum Osculating Law (`F_osc(c) ≥ F_osc(2 / 7)` for all `c > 0`)**:
since `c ↦ log(1 / (2 * π * c)) + (7 / 2) * c - γ` attains its global minimum on `(0, ∞)` at
`c = 2 / 7`, we have for **every** `c > 0`:
`log(7 / (4 * π)) + 1 - γ ≤ EF.gammaBracket 0 + levyCoshPotential c`. -/
theorem log_seven_div_four_pi_add_one_le_gammaBracket_add_levyCoshPotential
    {c : ℝ} (hc : 0 < c) :
    Real.log (7 / (4 * Real.pi)) + 1 - Real.eulerMascheroniConstant ≤
      EF.gammaBracket 0 + levyCoshPotential c := by
  have hmain := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential hc
  have hpos : 0 < (7 / 2 : ℝ) * c := by positivity
  have hlog : Real.log (7 / (4 * Real.pi)) =
      Real.log ((7 / 2 : ℝ) * c) + Real.log (1 / (2 * Real.pi * c)) := by
    rw [← Real.log_mul hpos.ne' (by positivity)]
    congr 1; field_simp; ring
  have hle := Real.log_le_sub_one_of_pos hpos
  linarith

/-! ## Section 3: Seven-Point Reflected Potential and Unconditional Positivity on `(0, 2 / 5)` (`= (0, 0.40)`) -/

/-- **Third-Window Inner Reflected Shell Coercivity (`(L / 3, L / 2)` paired with `(L / 2, b)`, `b ≤ 2 * L / 3`)**:
retaining the `(24 / 41)` double-collar coercivity on the positive kernel excess
`(-K(L - y)) - (-K(y)) ≥ 0` yields:
`((12 / 41) * Φ(L / 3) + (17 / 41) * Φ(L / 2) - (29 / 41) * Φ(b)) * ∫ h² ≤ ∫_{Ioo (L / 3) b} (-K(x)) D_h(x) dx`. -/
theorem third_window_inner_shell_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (hL2b : L / 2 ≤ b)
    (hb23 : b ≤ 2 * L / 3) (hbt : b ≤ screwSignThreshold) :
    ((12 / 41 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 41 : ℝ) * levyCoshPotential (L / 2) -
        (29 / 41 : ℝ) * levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 3) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL3 : 0 < L / 3 := by linarith
  have hL2 : 0 < L / 2 := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le hL2 hL2b
  have hbL : b < L := by linarith
  have hLb0 : 0 < L - b := by linarith
  have hL3_Lb : L / 3 ≤ L - b := by linarith
  have hLb_L2 : L - b ≤ L / 2 := by linarith
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K_all : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 3) b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL3 hx.1).neg
  have hIF_all : IntegrableOn F (Ioo (L / 3) b) := by
    refine ((hcont_K_all.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans hL3 hx.1)
        (hx.2.le.trans hbt))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  -- Part 1: on `Ioo (L / 3) (L - b)`
  have hpart1 : (12 / 41 : ℝ) * (levyCoshPotential (L / 3) - levyCoshPotential (L - b)) *
      (∫ u, h u ^ 2) ≤ ∫ x in Ioo (L / 3) (L - b), F x :=
    twelve_forty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo hh hsupp hL le_rfl hL3_Lb
      (by linarith)
  -- Part 2: on `Ioo (L - b) b`, retaining `(24 / 41)` on the reflected kernel excess
  have hIF_mid : IntegrableOn F (Ioo (L - b) b) :=
    hIF_all.mono_set (Ioo_subset_Ioo hL3_Lb le_rfl)
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
      (fun y => ((24 / 41 : ℝ) * (-screwRegularKernel (L - y)) +
        (58 / 41 : ℝ) * (-screwRegularKernel y)) * ∫ u, h u ^ 2)
      (Ioo (L / 2) b) :=
    ((hIK_refl.const_mul (24 / 41)).add (hIK.const_mul (58 / 41))).mul_const _
  have hval_low : (∫ y in Ioo (L / 2) b,
      ((24 / 41 : ℝ) * (-screwRegularKernel (L - y)) +
        (58 / 41 : ℝ) * (-screwRegularKernel y)) * ∫ u, h u ^ 2) =
      ((12 / 41 : ℝ) * (levyCoshPotential (L - b) - levyCoshPotential (L / 2)) +
        (29 / 41 : ℝ) * (levyCoshPotential (L / 2) - levyCoshPotential b)) * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, integral_add (hIK_refl.const_mul _) (hIK.const_mul _),
      integral_const_mul, integral_const_mul,
      setIntegral_Ioo_reflect_neg_screwRegularKernel hL hL2b hbL,
      setIntegral_Ioo_neg_screwRegularKernel hL2 hL2b]
    ring
  have hpart2 : ((12 / 41 : ℝ) * (levyCoshPotential (L - b) - levyCoshPotential (L / 2)) +
      (29 / 41 : ℝ) * (levyCoshPotential (L / 2) - levyCoshPotential b)) * (∫ u, h u ^ 2) ≤
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
    have htrd := twenty_four_forty_firsts_mul_integral_sq_le_integral_jump_sq_of_third_le
      hh hsupp hL.le (show L / 3 ≤ L - y by linarith [hy.2, hb23])
    have hstep1 : (-screwRegularKernel y) * (2 * ∫ u, h u ^ 2) ≤
        (-screwRegularKernel y) *
          ((∫ u, (h u - h (u + y)) ^ 2) + ∫ u, (h u - h (u + (L - y))) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hKy0
    have hstep2 : ((-screwRegularKernel (L - y)) - (-screwRegularKernel y)) *
        ((24 / 41 : ℝ) * ∫ u, h u ^ 2) ≤
        ((-screwRegularKernel (L - y)) - (-screwRegularKernel y)) *
          ∫ u, (h u - h (u + (L - y))) ^ 2 :=
      mul_le_mul_of_nonneg_left htrd hK_diff
    linarith
  have hdisj : Disjoint (Ioo (L / 3) (L - b)) (Ioo (L - b) b) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2.le hx2.1
  have hsub : Ioo (L / 3) (L - b) ∪ Ioo (L - b) b ⊆ Ioo (L / 3) b := fun x hx => by
    rcases hx with hx1 | hx2
    · exact ⟨hx1.1, lt_of_lt_of_le hx1.2 (by linarith)⟩
    · exact ⟨lt_of_le_of_lt hL3_Lb hx2.1, hx2.2⟩
  have hunion : (∫ x in Ioo (L / 3) (L - b), F x) + (∫ x in Ioo (L - b) b, F x) ≤
      ∫ x in Ioo (L / 3) b, F x := by
    rw [← setIntegral_union hdisj measurableSet_Ioo
      (hIF_all.mono_set (Ioo_subset_Ioo_right (by linarith))) hIF_mid]
    exact setIntegral_mono_set hIF_all
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx =>
        mul_nonneg (neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
          (lt_trans hL3 hx.1) (hx.2.le.trans hbt))) (hD0 x)))
      (Eventually.of_forall hsub)
  linarith

/-- **Quarter-Window Outer Reflected Shell Coercivity (`(L - c, L / 3)` paired with `(2 * L / 3, c)`, `2 * L / 3 ≤ c ≤ 3 * L / 4`)**:
retaining the `(8 / 21)` coercivity on the positive kernel excess `(-K(L - y)) - (-K(y)) ≥ 0` yields:
`((4 / 21) * (Φ(L - c) - Φ(L / 3)) + (17 / 21) * (Φ(2 * L / 3) - Φ(c))) * ∫ h² ≤ ∫_{Ioo (L - c) (L / 3)} F + ∫_{Ioo (2 * L / 3) c} F`. -/
theorem quarter_window_outer_shell_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (h23c : 2 * L / 3 ≤ c)
    (hc34 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold) :
    ((4 / 21 : ℝ) * (levyCoshPotential (L - c) - levyCoshPotential (L / 3)) +
        (17 / 21 : ℝ) * (levyCoshPotential (2 * L / 3) - levyCoshPotential c)) *
        (∫ u, h u ^ 2) ≤
      (∫ x in Ioo (L - c) (L / 3), (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ y in Ioo (2 * L / 3) c, (-screwRegularKernel y) * ∫ u, (h u - h (u + y)) ^ 2 := by
  have hL4 : 0 < L / 4 := by linarith
  have h23_pos : 0 < 2 * L / 3 := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le h23_pos h23c
  have hcL : c < L := by linarith
  have hLc0 : 0 < L - c := by linarith
  have hLc_L3 : L - c ≤ L / 3 := by linarith
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_left : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L - c) (L / 3)) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hLc0 hx.1).neg
  have hIF_left : IntegrableOn F (Ioo (L - c) (L / 3)) := by
    refine ((hcont_left.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans hLc0 hx.1)
        (by linarith [hx.2, h23c, hct]))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hcont_right : ContinuousOn (fun y => -screwRegularKernel y) (Icc (2 * L / 3) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun y hy => lt_of_lt_of_le h23_pos hy.1).neg
  have hIF_right : IntegrableOn F (Ioo (2 * L / 3) c) := by
    refine ((hcont_right.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun y hy => ?_))
    have hK0 : 0 ≤ -screwRegularKernel y :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans h23_pos hy.1)
        (hy.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 y))]
    exact mul_le_mul_of_nonneg_left (jump_le hh y) hK0
  have hIF_refl : IntegrableOn (fun y => F (L - y)) (Ioo (2 * L / 3) c) := by
    have hpre : (fun y : ℝ => -y + L) ⁻¹' Ioo (L - c) (L / 3) = Ioo (2 * L / 3) c := by
      ext y; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith
    have h1 : Integrable (fun y : ℝ => (Ioo (L - c) (L / 3)).indicator F (-y + L)) :=
      (((integrable_indicator_iff measurableSet_Ioo).mpr hIF_left).comp_add_right L).comp_neg
    rw [← integrable_indicator_iff measurableSet_Ioo]
    refine h1.congr (ae_of_all _ fun y => ?_)
    dsimp only
    rw [← Set.indicator_comp_right (fun y : ℝ => -y + L), hpre]
    exact congrArg (fun g => (Ioo (2 * L / 3) c).indicator g y) (funext fun z => congrArg F (by ring))
  have hrefl_eq : (∫ y in Ioo (2 * L / 3) c, F (L - y)) = ∫ x in Ioo (L - c) (L / 3), F x := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le h23c, ← intervalIntegral.integral_of_le hLc_L3,
      intervalIntegral.integral_comp_sub_left F, show L - (2 * L / 3) = L / 3 by ring]
  have hcont_K_refl : ContinuousOn (fun y => -screwRegularKernel (L - y)) (Icc (2 * L / 3) c) :=
    hcont_left.comp (continuousOn_const.sub continuousOn_id)
      fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hIK : IntegrableOn (fun y => -screwRegularKernel y) (Ioo (2 * L / 3) c) :=
    hcont_right.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hIK_refl : IntegrableOn (fun y => -screwRegularKernel (L - y)) (Ioo (2 * L / 3) c) :=
    hcont_K_refl.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hI_low : IntegrableOn
      (fun y => ((8 / 21 : ℝ) * (-screwRegularKernel (L - y)) +
        (34 / 21 : ℝ) * (-screwRegularKernel y)) * ∫ u, h u ^ 2)
      (Ioo (2 * L / 3) c) :=
    ((hIK_refl.const_mul (8 / 21)).add (hIK.const_mul (34 / 21))).mul_const _
  have hval : (∫ y in Ioo (2 * L / 3) c,
      ((8 / 21 : ℝ) * (-screwRegularKernel (L - y)) +
        (34 / 21 : ℝ) * (-screwRegularKernel y)) * ∫ u, h u ^ 2) =
      ((4 / 21 : ℝ) * (levyCoshPotential (L - c) - levyCoshPotential (L / 3)) +
        (17 / 21 : ℝ) * (levyCoshPotential (2 * L / 3) - levyCoshPotential c)) *
        ∫ u, h u ^ 2 := by
    rw [integral_mul_const, integral_add (hIK_refl.const_mul _) (hIK.const_mul _),
      integral_const_mul, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le h23c,
      intervalIntegral.integral_comp_sub_left (fun x => -screwRegularKernel x),
      show L - (2 * L / 3) = L / 3 by ring,
      intervalIntegral.integral_of_le hLc_L3, integral_Ioc_eq_integral_Ioo,
      setIntegral_Ioo_neg_screwRegularKernel hLc0 hLc_L3,
      setIntegral_Ioo_neg_screwRegularKernel h23_pos h23c]
    ring
  rw [← hrefl_eq, ← integral_add hIF_refl hIF_right, ← hval]
  refine setIntegral_mono_on hI_low (hIF_refl.add hIF_right) measurableSet_Ioo fun y hy => ?_
  dsimp only [F, Pi.add_apply]
  have hy0 : 0 < y := lt_trans h23_pos hy.1
  have hLy0 : 0 < L - y := by linarith [hy.2]
  have hLy_le : L - y ≤ y := by linarith [hy.1]
  have hyt : y ≤ screwSignThreshold := hy.2.le.trans hct
  have hKy0 : 0 ≤ -screwRegularKernel y :=
    neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold hy0 hyt)
  have hK_diff : 0 ≤ (-screwRegularKernel (L - y)) - (-screwRegularKernel y) :=
    sub_nonneg.mpr (neg_le_neg (monotoneOn_screwRegularKernel hLy0 hy0 hLy_le))
  have hsum := two_mul_integral_sq_le_integral_jump_sq_add_sub hh hsupp hy0.le
    (le_trans hy.2.le hcL.le)
  have hqtr := eight_twenty_firsts_mul_integral_sq_le_integral_jump_sq_of_quarter_le
    hh hsupp hL.le (show L / 4 ≤ L - y by linarith [hy.2, hc34])
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

/-- **Reflected Quarter + Third Shell Jump-Integral Coercivity on `Ioo (L / 4) c` (`2 * L / 3 ≤ c ≤ 3 * L / 4`)**:
combining `(L / 4, L - c)`, the outer reflected shell `(L - c, L / 3) ∪ (2 * L / 3, c)`, and the
inner reflected shell `(L / 3, 2 * L / 3)` yields:
`((4 / 21) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (88 / 861) * Φ(2 * L / 3) - (17 / 21) * Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo (L / 4) c} (-screwRegularKernel x) D_h(x) dx`. -/
theorem quarter_third_reflected_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (h23c : 2 * L / 3 ≤ c)
    (hc34 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold) :
    ((4 / 21 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 41 : ℝ) * levyCoshPotential (L / 2) +
        (88 / 861 : ℝ) * levyCoshPotential (2 * L / 3) -
        (17 / 21 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 4) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL4 : 0 < L / 4 := by linarith
  have hL4_Lc : L / 4 ≤ L - c := by linarith
  have hLc_L3 : L - c ≤ L / 3 := by linarith
  have hL3_23 : L / 3 ≤ 2 * L / 3 := by linarith
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_all : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 4) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL4 hx.1).neg
  have hIF_all : IntegrableOn F (Ioo (L / 4) c) := by
    refine ((hcont_all.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans hL4 hx.1)
        (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have h1 := four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL le_rfl hL4_Lc (by linarith)
  have h2 := quarter_window_outer_shell_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL h23c hc34 hct
  have h3 := third_window_inner_shell_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL (by linarith : L / 2 ≤ 2 * L / 3) le_rfl (h23c.trans hct)
  have hIF_1 : IntegrableOn F (Ioo (L / 4) (L - c)) :=
    hIF_all.mono_set (Ioo_subset_Ioo_right (by linarith))
  have hIF_2 : IntegrableOn F (Ioo (L - c) (L / 3)) :=
    hIF_all.mono_set (Ioo_subset_Ioo hL4_Lc (by linarith))
  have hIF_3 : IntegrableOn F (Ioo (L / 3) (2 * L / 3)) :=
    hIF_all.mono_set (Ioo_subset_Ioo (by linarith) h23c)
  have hIF_4 : IntegrableOn F (Ioo (2 * L / 3) c) :=
    hIF_all.mono_set (Ioo_subset_Ioo_left (by linarith))
  have hdisj_12 : Disjoint (Ioo (L / 4) (L - c)) (Ioo (L - c) (L / 3)) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2.le hx2.1
  have hdisj_34 : Disjoint (Ioo (L / 3) (2 * L / 3)) (Ioo (2 * L / 3) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2.le hx2.1
  have hdisj_all : Disjoint (Ioo (L / 4) (L - c) ∪ Ioo (L - c) (L / 3))
      (Ioo (L / 3) (2 * L / 3) ∪ Ioo (2 * L / 3) c) := by
    refine disjoint_left.mpr fun x hx1 hx2 => ?_
    have hx_le : x < L / 3 := by
      rcases hx1 with h1 | h2
      · exact lt_of_lt_of_le h1.2 hLc_L3
      · exact h2.2
    have hx_gt : L / 3 < x := by
      rcases hx2 with h3 | h4
      · exact h3.1
      · exact lt_of_le_of_lt hL3_23 h4.1
    exact not_lt_of_gt hx_gt hx_le
  have hsub_all : (Ioo (L / 4) (L - c) ∪ Ioo (L - c) (L / 3)) ∪
      (Ioo (L / 3) (2 * L / 3) ∪ Ioo (2 * L / 3) c) ⊆ Ioo (L / 4) c := fun x hx => by
    rcases hx with (hx1 | hx2) | (hx3 | hx4)
    · exact ⟨hx1.1, by linarith [hx1.2]⟩
    · exact ⟨lt_of_le_of_lt hL4_Lc hx2.1, by linarith [hx2.2]⟩
    · exact ⟨by linarith [hx3.1], lt_of_lt_of_le hx3.2 h23c⟩
    · exact ⟨by linarith [hx4.1], hx4.2⟩
  have hunion : (∫ x in Ioo (L / 4) (L - c), F x) + (∫ x in Ioo (L - c) (L / 3), F x) +
      ((∫ x in Ioo (L / 3) (2 * L / 3), F x) + (∫ x in Ioo (2 * L / 3) c, F x)) ≤
      ∫ x in Ioo (L / 4) c, F x := by
    rw [← setIntegral_union hdisj_12 measurableSet_Ioo hIF_1 hIF_2,
      ← setIntegral_union hdisj_34 measurableSet_Ioo hIF_3 hIF_4,
      ← setIntegral_union hdisj_all (measurableSet_Ioo.union measurableSet_Ioo)
        (hIF_1.union hIF_2) (hIF_3.union hIF_4)]
    exact setIntegral_mono_set hIF_all
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx =>
        mul_nonneg (neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
          (lt_trans hL4 hx.1) (hx.2.le.trans hct))) (hD0 x)))
      (Eventually.of_forall hsub_all)
  linarith

/-- **Seven-Point Jump-Integral Coercivity on `Ioo (L / 8) c` (`2 * L / 3 ≤ c ≤ 3 * L / 4`)**:
combining `eighth_add_sixth_sub_levyCoshPotential_le_setIntegral_Ioo` on `Ioo (L / 8) (L / 4)` with
`quarter_third_reflected_sub_levyCoshPotential_le_setIntegral_Ioo` on `Ioo (L / 4) c` yields:
`((3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (88 / 861) * Φ(2 * L / 3) - (17 / 21) * Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo (L / 8) c} (-K(x)) D_h(x) dx`. -/
theorem seven_point_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (h23c : 2 * L / 3 ≤ c)
    (hc34 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold) :
    ((3 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (67 / 1800 : ℝ) * levyCoshPotential (L / 6) +
        (47 / 504 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 41 : ℝ) * levyCoshPotential (L / 2) +
        (88 / 861 : ℝ) * levyCoshPotential (2 * L / 3) -
        (17 / 21 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 8) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL8 : 0 < L / 8 := by linarith
  have hL8_4 : L / 8 ≤ L / 4 := by linarith
  have hL6_4 : L / 6 ≤ L / 4 := by linarith
  have hL4c : L / 4 ≤ c := by linarith
  have hL4t : L / 4 ≤ screwSignThreshold := hL4c.trans hct
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 8) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL8 hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 8) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL8 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_left_Ioc : IntegrableOn F (Ioc (L / 8) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL4c)
  have hIF_right_Ioc : IntegrableOn F (Ioc (L / 4) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL8_4 le_rfl)
  have hdisj : Disjoint (Ioc (L / 8) (L / 4)) (Ioc (L / 4) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 8) c, F x) =
      (∫ x in Ioo (L / 8) (L / 4), F x) + ∫ x in Ioo (L / 4) c, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL8_4 hL4c,
      setIntegral_union hdisj measurableSet_Ioc hIF_left_Ioc hIF_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h86 := eighth_add_sixth_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL hL6_4 hL4t
  have h43 := quarter_third_reflected_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL h23c hc34 hct
  dsimp only [F] at hsplit
  linarith

/-- **Seven-Point Reflected Lévy–Cosh Crossover Inequality on `(0, L)` (`2 * L / 3 ≤ c ≤ 3 * L / 4`)**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`),
`(A(0) + (3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (88 / 861) * Φ(2 * L / 3) + (4 / 21) * Φ(c)) * ∫ f² + ... ≤ W_∞(f ⋆ f̃)`. -/
theorem seven_point_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L)
    (h23c : 2 * L / 3 ≤ c) (hc34 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (47 / 504) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (17 / 41) * levyCoshPotential (L / 2) +
        (88 / 861) * levyCoshPotential (2 * L / 3) +
        (4 / 21) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL8 : 0 < L / 8 := by linarith
  have hL8c : L / 8 ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL8 hL8c hct
  have hseven := seven_point_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL h23c hc34 hct
  linarith

/-- **Osculating Lower Bound for the Seven-Point Reflected Potential (`L > 0`, `c > 0`)**:
using `log_seven_div_four_pi_add_one_le_gammaBracket_add_levyCoshPotential` at `c` and the exact
symmetric pair identity `log(1 / (2π(L / 3))) + log(1 / (2π(2L / 3))) = 2 * log(1 / (πL)) + log(9 / 8)`
yields for **every** `L > 0` and `c > 0`:
`log(1 / (π * L)) + (7 / 72) * log 2 + (1931 / 12600) * log(4 / 3) + (88 / 861) * log(9 / 8) + (4 / 21) * log((21 / 8) * L) + (52397 / 43200) * L + 4 / 21 - γ`
`≤ EF.gammaBracket 0 + (3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (88 / 861) * Φ(2 * L / 3) + (4 / 21) * Φ(c)`. -/
theorem osculating_le_seven_point_potential {L c : ℝ} (hL : 0 < L) (hc0 : 0 < c) :
    Real.log (1 / (Real.pi * L)) + (7 / 72 : ℝ) * Real.log 2 +
        (1931 / 12600 : ℝ) * Real.log (4 / 3) +
        (88 / 861 : ℝ) * Real.log (9 / 8) +
        (4 / 21 : ℝ) * Real.log ((21 / 8 : ℝ) * L) +
        (52397 / 43200 : ℝ) * L + (4 / 21 : ℝ) - Real.eulerMascheroniConstant ≤
      EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (47 / 504) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (17 / 41) * levyCoshPotential (L / 2) +
        (88 / 861) * levyCoshPotential (2 * L / 3) +
        (4 / 21) * levyCoshPotential c := by
  have h1 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 8 by linarith)
  have h2 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 6 by linarith)
  have h3 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 4 by linarith)
  have h4 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 3 by linarith)
  have h5 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 2 by linarith)
  have h6 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < 2 * L / 3 by linarith)
  have h7 := log_seven_div_four_pi_add_one_le_gammaBracket_add_levyCoshPotential hc0
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]; ring
  have hlog3 : Real.log (3 : ℝ) = 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [eq_sub_iff_add_eq, ← Real.log_mul (by positivity) (by positivity), ← hlog4]
    congr 1; norm_num
  have hlog1 : Real.log (1 / (2 * Real.pi * (L / 8))) =
      Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 := by
    rw [← hlog4, ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; norm_num
  have hlog2 : Real.log (1 / (2 * Real.pi * (L / 6))) =
      Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [add_sub_assoc, ← hlog3, ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; norm_num
  have hlog3_pt : Real.log (1 / (2 * Real.pi * (L / 4))) =
      Real.log (1 / (Real.pi * L)) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; norm_num
  have hlog46_pair : Real.log (1 / (2 * Real.pi * (L / 3))) +
      Real.log (1 / (2 * Real.pi * (2 * L / 3))) =
      2 * Real.log (1 / (Real.pi * L)) + Real.log (9 / 8) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      show (2 : ℝ) * Real.log (1 / (Real.pi * L)) =
        Real.log (1 / (Real.pi * L)) + Real.log (1 / (Real.pi * L)) by ring,
      add_assoc, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog5_pt : Real.log (1 / (2 * Real.pi * (L / 2))) =
      Real.log (1 / (Real.pi * L)) := by
    congr 1; field_simp
  have hlog7_pt : Real.log (7 / (4 * Real.pi)) =
      Real.log (1 / (Real.pi * L)) + Real.log (4 / 3) - Real.log 2 +
        Real.log ((21 / 8 : ℝ) * L) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_div (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  linarith

/-- Rational lower bounds `2 / 17 < Real.log (9 / 8)` and `2 / 41 < Real.log (21 / 20)`. -/
theorem two_seventeenths_lt_log_nine_eighths : (2 : ℝ) / 17 < Real.log (9 / 8) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 8)
  norm_num at h ⊢
  exact h

theorem two_forty_firsts_lt_log_twenty_one_twentieths : (2 : ℝ) / 41 < Real.log (21 / 20) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 20)
  norm_num at h ⊢
  exact h

/-- Sharp lower bound on `log(1 / (π * (2 / 5))) = log(5 / (2 * π))` from `log_pi_le_sixteen_fifths`:
`2 * log 5 - 5 * log 2 + 1 - 5 * π / 16 ≤ log(1 / (π * (2 / 5)))`. -/
theorem two_mul_log_five_sub_five_mul_log_two_le_log_inv_pi_mul_two_fifths :
    2 * Real.log 5 - 5 * Real.log 2 + 1 - 5 * Real.pi / 16 ≤
      Real.log (1 / (Real.pi * (2 / 5))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : Real.log (1 / (Real.pi * (2 / 5))) = Real.log 5 - Real.log 2 - Real.log Real.pi := by
    rw [show (1 : ℝ) / (Real.pi * (2 / 5)) = 5 / (2 * Real.pi) by field_simp,
      Real.log_div (by norm_num) (by positivity),
      Real.log_mul two_ne_zero hpi.ne']
    ring
  have h2 := log_pi_le_sixteen_fifths
  linarith

/-- **Strict Positivity of the Seven-Point Reflected Potential at `L = 2 / 5` (`= 0.40`)**:
`0 ≤ EF.gammaBracket 0 + (3 / 50) * Φ((2/5)/8) + (67 / 1800) * Φ((2/5)/6) + (47 / 504) * Φ((2/5)/4) + (88 / 861) * Φ((2/5)/3) + (17 / 41) * Φ((2/5)/2) + (88 / 861) * Φ(2*(2/5)/3) + (4 / 21) * Φ(screwSignThreshold)`. -/
theorem zero_le_seven_point_potential_two_fifths :
    0 ≤ EF.gammaBracket 0 + (3 / 50) * levyCoshPotential ((2 / 5 : ℝ) / 8) +
        (67 / 1800) * levyCoshPotential ((2 / 5 : ℝ) / 6) +
        (47 / 504) * levyCoshPotential ((2 / 5 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((2 / 5 : ℝ) / 3) +
        (17 / 41) * levyCoshPotential ((2 / 5 : ℝ) / 2) +
        (88 / 861) * levyCoshPotential (2 * (2 / 5 : ℝ) / 3) +
        (4 / 21) * levyCoshPotential screwSignThreshold := by
  have hosc := osculating_le_seven_point_potential
    (by norm_num : (0 : ℝ) < 2 / 5) screwSignThreshold_pos
  rw [show (21 / 8 : ℝ) * (2 / 5) = 21 / 20 by norm_num] at hosc
  have hlog_pi := two_mul_log_five_sub_five_mul_log_two_le_log_inv_pi_mul_two_fifths
  have hlog2 := Real.log_two_lt_d9
  have hlog5 := Real.log_five_gt_d9
  have hlog43 := two_sevenths_lt_log_four_thirds
  have hlog98 := two_seventeenths_lt_log_nine_eighths
  have hlog21_20 := two_forty_firsts_lt_log_twenty_one_twentieths
  have hpi := Real.pi_lt_d4
  have hgamma :=
    RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith

/-- **Unconditional Archimedean Weil Positivity on `(0, 2 / 5)` (`= (0, 0.40)`, `57.71%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` supported in `Ioo 0 L` with `L ≤ 2 / 5`,
`0 ≤ WeilOneSided.weilArchRe (EF.weilTest f f)`. -/
theorem weilArchRe_nonneg_of_support_Ioo_le_two_fifths {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL : L ≤ 2 / 5) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_2_5 : ∀ u ∉ Ioo (0 : ℝ) (2 / 5), f u = 0 :=
    fun u hu => hsupp u fun huL => hu ⟨huL.1, huL.2.trans_le hL⟩
  have hmain := seven_point_levyCosh_crossover_le_weilArchRe
    hf hfc (by norm_num : (0 : ℝ) < 2 / 5)
    (by linarith [screwSignThreshold_gt_6036_over_21509])
    (by linarith [screwSignThreshold_lt_two_sevenths])
    le_rfl hsupp_2_5
  have hpot := zero_le_seven_point_potential_two_fifths
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hterm1 : 0 ≤ (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential ((2 / 5 : ℝ) / 8) +
        (67 / 1800) * levyCoshPotential ((2 / 5 : ℝ) / 6) +
        (47 / 504) * levyCoshPotential ((2 / 5 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((2 / 5 : ℝ) / 3) +
        (17 / 41) * levyCoshPotential ((2 / 5 : ℝ) / 2) +
        (88 / 861) * levyCoshPotential (2 * (2 / 5 : ℝ) / 3) +
        (4 / 21) * levyCoshPotential screwSignThreshold) * ∫ u, f u ^ 2 :=
    mul_nonneg hpot hsq
  have hpair : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-- **Unconditional `WindowPositive` on `(0, 2 / 5)` (`= (0, 0.40)`, `57.71%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (2 / 5)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_two_fifths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (2 / 5)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_two_fifths hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

end

end RHTower.WeilLevyThirdWindow
