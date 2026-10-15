import GaloisForLFunctions.RHTower.WeilLevyFifthWindowDoubleTransport

/-!
# Tenth-Window Four-Step Disjoint Staircase Coercivity and Unconditional Positivity on `(0, 5 / 12)`

This module implements **Cycle 74** of the prime-blind archimedean Weil positivity programme,
extending the disjoint midpoint-split staircase from `[L / 8, L / 6]` (`Cycle 71`) by a fourth
interior layer to `[L / 10, L / 8]` and pushing unconditional `WindowPositive` past the `60%`
milestone from `(0, 9 / 22)` (`≈ (0, 0.409091)`, `59.02%` of `(0, log 2)`) to **`(0, 5 / 12)`**
(`≈ (0, 0.416667)`, **`60.11%` of `(0, log 2)`**), which also covers `(0, 7 / 17)` (`≈ (0, 0.411765)`)
and `(0, 29 / 70)` (`≈ (0, 0.414286)`).

## Mathematical Architecture

1. **Section 1 — Disjoint Four-Step Midpoint-Split Coercivity on `[L / 10, L / 8]` (`D_h(x) ≥ (2 / 25) ∫ h²`)**:
   - On `[L / 10, L / 8]`, a shift by $x$ has path length $10$, whose path-graph Dirichlet Laplacian
     $Q_{10}$ has spectral floor $\lambda_{\min}(Q_{10}) = 2 - 2\cos(\pi / 11) \approx 0.081014$.
   - We prove the four exact single-square SOS transport inequalities:
     $$(p - q)^2 - \left(\frac{23}{48} p^2 - \frac{23}{25} q^2\right) = \frac{25}{48}\left(p - \frac{48}{25} q\right)^2 \ge 0,$$
     $$(p - q)^2 - \left(\frac{13}{46} p^2 - \frac{13}{33} q^2\right) = \frac{33}{46}\left(p - \frac{46}{33} q\right)^2 \ge 0,$$
     $$(p - q)^2 - \left(\frac{16}{95} p^2 - \frac{16}{79} q^2\right) = \frac{79}{95}\left(p - \frac{95}{79} q\right)^2 \ge 0,$$
     $$(p - q)^2 - \left(\frac{2}{25} p^2 - \frac{2}{23} q^2\right) = \frac{23}{25}\left(p - \frac{25}{23} q\right)^2 \ge 0.$$
   - For $x \in [L / 10, L / 8]$, splitting the fourth interior layer $\mathrm{Ioc}\,(4x)\,(L - 4x)$ at the
     midpoint $L / 2$ makes all eight shift intervals
     $$\mathrm{Ioc}\,0\,x,\ \mathrm{Ioc}\,x\,(2x),\ \mathrm{Ioc}\,(2x)\,(3x),\ \mathrm{Ioc}\,(3x)\,(L/2 - x),$$
     $$\mathrm{Ioc}\,(L/2)\,(L - 4x),\ \mathrm{Ioc}\,(L - 4x)\,(L - 3x),\ \mathrm{Ioc}\,(L - 3x)\,(L - 2x),\ \mathrm{Ioc}\,(L - 2x)\,(L - x)$$
     **pairwise disjoint** inside $\mathrm{Ioc}\,0\,(L - x)$.
   - Since $1 - \frac{23}{25} = \frac{2}{25}$, $\frac{23}{48} - \frac{13}{33} = \frac{15}{176} \ge \frac{2}{25}$,
     $\frac{13}{46} - \frac{16}{79} = \frac{291}{3634} \ge \frac{2}{25}$, and
     $\frac{16}{95} - \frac{2}{23} = \frac{178}{2185} \ge \frac{2}{25}$, combining the eight disjoint jump
     integrals with collar-escape yields:
     $$\frac{2}{25}\int_{\mathbb R} h(u)^2\,du \le \int_{\mathbb R} (h(u) - h(u + x))^2\,du
       \qquad \forall x \ge \frac{L}{10}$$
     (within $0.001014$ of the theoretical spectral limit $2 - 2\cos(\pi / 11) \approx 0.081014$).

2. **Section 2 — Six-Shell Potential Coercivity and Sharpened `(0, log 2)` Plastic Floor**:
   - Integrating the $2 / 25$ coercivity on $(L / 10, L / 8)$ and combining with the five-shell bound on
     $(L / 8, c)$ (`Cycle 73`) splits the $3 / 50$ weight at $L / 8$ into $1 / 25$ at $L / 10$ and
     $1 / 50$ at $L / 8$:
     $$\left(A(0) + \frac{1}{25}\Phi(L / 10) + \frac{1}{50}\Phi(L / 8) + \frac{67}{1800}\Phi(L / 6)
       + \frac{13}{360}\Phi(L / 5) + \frac{2}{35}\Phi(L / 4) + \frac{88}{861}\Phi(L / 3)
       + \frac{29}{41}\Phi(c)\right)\int_{\mathbb R} f^2 + \mathrm{pair}_c(f) \le W_\infty(f \star \tilde f),$$
     reducing the universal `(0, log 2)` constant deficit from `-0.0221` (`Cycle 73`) down to **`-0.0156`**.

3. **Section 3 — Nine-Point Reflected Potential and Unconditional Positivity on `(0, 5 / 12)` (`60.11%` of `(0, log 2)`)**:
   - Combining `(L / 10, L / 8)` with the eight-point reflected shell (`Cycle 73`) yields the nine-point
     reflected potential with weights $(1 / 25,\ 1 / 50,\ 67 / 1800,\ 13 / 360,\ 2 / 35,\ 88 / 861,\ 17 / 41,\ 88 / 861,\ 4 / 21)$
     at $(L / 10,\ L / 8,\ L / 6,\ L / 5,\ L / 4,\ L / 3,\ L / 2,\ 2 L / 3,\ c)$ for $2 L / 3 \le c \le 3 L / 4$.
   - Its closed-form osculating lower bound is:
     $$\log\left(\frac{1}{\pi L}\right) + \frac{7}{72}\log 2 + \frac{1931}{12600}\log\left(\frac{4}{3}\right)
       + \frac{137}{1800}\log\left(\frac{5}{4}\right) + \frac{88}{861}\log\left(\frac{9}{8}\right)
       + \frac{4}{21}\log\left(\frac{21}{8} L\right) + \frac{32483}{27000} L + \frac{4}{21} - \gamma.$$
   - At $L = 5 / 12 \approx 0.416667$ (`60.11%` of `(0, log 2)`), this bound is strictly positive
     (`+0.003120 > 0`), proving unconditional `WindowPositive` on `(0, 5 / 12)`, `(0, 7 / 17)`, and `(0, 29 / 70)`.
-/

open Complex Real Set MeasureTheory Filter
open scoped Topology
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyTenthWindow

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor
open RHTower.WeilLevyQuarterWindow RHTower.WeilLevySymmetricThreePoint
open RHTower.WeilLevySixthWindow RHTower.WeilLevyFibonacciStaircase
open RHTower.WeilLevyEighthWindow RHTower.WeilLevyThirdWindow
open RHTower.WeilLevyFifthWindow

/-! ## Section 1: Disjoint Four-Step Midpoint-Split Coercivity on `[L / 10, L / 8]` (`D_h(x) ≥ (2 / 25) ∫ h²`) -/

/-- Exact step-1 SOS inequality (`(23 / 48, 23 / 25)`): for all `p, q : ℝ`,
`(23 / 48) * p ^ 2 - (23 / 25) * q ^ 2 ≤ (p - q) ^ 2`, proved via the exact single-square identity
`(p - q) ^ 2 - ((23 / 48) * p ^ 2 - (23 / 25) * q ^ 2) = (25 / 48) * (p - (48 / 25) * q) ^ 2 ≥ 0`. -/
theorem twenty_three_forty_eighths_sq_sub_twenty_three_twenty_fifths_sq_le_sub_sq (p q : ℝ) :
    (23 / 48 : ℝ) * p ^ 2 - (23 / 25 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  nlinarith [sq_nonneg (p - (48 / 25 : ℝ) * q)]

/-- Exact step-2 SOS inequality (`(13 / 46, 13 / 33)`): for all `p, q : ℝ`,
`(13 / 46) * p ^ 2 - (13 / 33) * q ^ 2 ≤ (p - q) ^ 2`, proved via the exact single-square identity
`(p - q) ^ 2 - ((13 / 46) * p ^ 2 - (13 / 33) * q ^ 2) = (33 / 46) * (p - (46 / 33) * q) ^ 2 ≥ 0`. -/
theorem thirteen_forty_sixths_sq_sub_thirteen_thirty_thirds_sq_le_sub_sq (p q : ℝ) :
    (13 / 46 : ℝ) * p ^ 2 - (13 / 33 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  nlinarith [sq_nonneg (p - (46 / 33 : ℝ) * q)]

/-- Exact step-3 SOS inequality (`(16 / 95, 16 / 79)`): for all `p, q : ℝ`,
`(16 / 95) * p ^ 2 - (16 / 79) * q ^ 2 ≤ (p - q) ^ 2`, proved via the exact single-square identity
`(p - q) ^ 2 - ((16 / 95) * p ^ 2 - (16 / 79) * q ^ 2) = (79 / 95) * (p - (95 / 79) * q) ^ 2 ≥ 0`. -/
theorem sixteen_ninety_fifths_sq_sub_sixteen_seventy_ninths_sq_le_sub_sq (p q : ℝ) :
    (16 / 95 : ℝ) * p ^ 2 - (16 / 79 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  nlinarith [sq_nonneg (p - (95 / 79 : ℝ) * q)]

/-- Exact step-4 SOS inequality (`(2 / 25, 2 / 23)`): for all `p, q : ℝ`,
`(2 / 25) * p ^ 2 - (2 / 23) * q ^ 2 ≤ (p - q) ^ 2`, proved via the exact single-square identity
`(p - q) ^ 2 - ((2 / 25) * p ^ 2 - (2 / 23) * q ^ 2) = (23 / 25) * (p - (25 / 23) * q) ^ 2 ≥ 0`. -/
theorem two_twenty_fifths_sq_sub_two_twenty_thirds_sq_le_sub_sq (p q : ℝ) :
    (2 / 25 : ℝ) * p ^ 2 - (2 / 23 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  nlinarith [sq_nonneg (p - (25 / 23 : ℝ) * q)]

/-- **Inner Two-Step Midpoint-Split Jump Bound on `Ioc (2 * x) (L - 3 * x)` (`x ∈ [L / 10, L / 8]`)**:
combining Step 3 (`(16 / 95, 16 / 79)`) on `Ioc (2 * x) (3 * x)` and `Ioc (L - 4 * x) (L - 3 * x)`
with Step 4 (`(2 / 25, 2 / 23)`) on `Ioc (3 * x) (L / 2 - x)` and `Ioc (L / 2) (L - 4 * x)` yields:
`(178 / 2185) * ((∫ v in Ioc (3 * x) (4 * x), h v ^ 2) + ∫ u in Ioc (L - 4 * x) (L - 3 * x), h u ^ 2)`
`+ (2 / 25) * ((∫ v in Ioc (4 * x) (L / 2), h v ^ 2) + ∫ u in Ioc (L / 2) (L - 4 * x), h u ^ 2)`
`- (16 / 79) * ((∫ u in Ioc (2 * x) (3 * x), h u ^ 2) + ∫ v in Ioc (L - 3 * x) (L - 2 * x), h v ^ 2)`
`≤ ∫ u in Ioc (2 * x) (L - 3 * x), (h u - h (u + x)) ^ 2`. -/
theorem inner_two_step_slices_le_setIntegral_Ioc {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hL0 : 0 ≤ L) (hx10 : L / 10 ≤ x) (hx8 : x ≤ L / 8) :
    (178 / 2185 : ℝ) *
        ((∫ v in Ioc (3 * x) (4 * x), h v ^ 2) + ∫ u in Ioc (L - 4 * x) (L - 3 * x), h u ^ 2) +
      (2 / 25 : ℝ) *
        ((∫ v in Ioc (4 * x) (L / 2), h v ^ 2) + ∫ u in Ioc (L / 2) (L - 4 * x), h u ^ 2) -
      (16 / 79 : ℝ) *
        ((∫ u in Ioc (2 * x) (3 * x), h u ^ 2) + ∫ v in Ioc (L - 3 * x) (L - 2 * x), h v ^ 2) ≤
      ∫ u in Ioc (2 * x) (L - 3 * x), (h u - h (u + x)) ^ 2 := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  -- Step 3 (layer-2-to-layer-3 intervals `Ioc (2 * x) (3 * x)` and `Ioc (L - 4 * x) (L - 3 * x)`)
  have h3_left_pt : ∀ u : ℝ,
      (16 / 95 : ℝ) * h (u + x) ^ 2 - (16 / 79 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := sixteen_ninety_fifths_sq_sub_sixteen_seventy_ninths_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h3_left : (16 / 95 : ℝ) * (∫ v in Ioc (3 * x) (4 * x), h v ^ 2) -
      (16 / 79 : ℝ) * (∫ u in Ioc (2 * x) (3 * x), h u ^ 2) ≤
      ∫ u in Ioc (2 * x) (3 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (2 * x) (3 * x))
      ((hshift.const_mul (16 / 95)).integrableOn.sub (hsq.const_mul (16 / 79)).integrableOn)
      hjump.integrableOn h3_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (16 / 95)).integrableOn (hsq.const_mul (16 / 79)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (2 * x) (3 * x) x,
      show 2 * x + x = 3 * x by ring, show 3 * x + x = 4 * x by ring] at h1
    linarith
  have h3_right_pt : ∀ u : ℝ,
      (16 / 95 : ℝ) * h u ^ 2 - (16 / 79 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => sixteen_ninety_fifths_sq_sub_sixteen_seventy_ninths_sq_le_sub_sq (h u) (h (u + x))
  have h3_right : (16 / 95 : ℝ) * (∫ u in Ioc (L - 4 * x) (L - 3 * x), h u ^ 2) -
      (16 / 79 : ℝ) * (∫ v in Ioc (L - 3 * x) (L - 2 * x), h v ^ 2) ≤
      ∫ u in Ioc (L - 4 * x) (L - 3 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - 4 * x) (L - 3 * x))
      ((hsq.const_mul (16 / 95)).integrableOn.sub (hshift.const_mul (16 / 79)).integrableOn)
      hjump.integrableOn h3_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (16 / 95)).integrableOn (hshift.const_mul (16 / 79)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - 4 * x) (L - 3 * x) x,
      show L - 4 * x + x = L - 3 * x by ring, show L - 3 * x + x = L - 2 * x by ring] at h1
    linarith
  -- Step 4 (midpoint-split inner intervals `Ioc (3 * x) (L / 2 - x)` and `Ioc (L / 2) (L - 4 * x)`)
  have h4_left_pt : ∀ u : ℝ,
      (2 / 25 : ℝ) * h (u + x) ^ 2 - (2 / 23 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := two_twenty_fifths_sq_sub_two_twenty_thirds_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h4_left : (2 / 25 : ℝ) * (∫ v in Ioc (4 * x) (L / 2), h v ^ 2) -
      (2 / 23 : ℝ) * (∫ u in Ioc (3 * x) (4 * x), h u ^ 2) ≤
      ∫ u in Ioc (3 * x) (L / 2 - x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (3 * x) (L / 2 - x))
      ((hshift.const_mul (2 / 25)).integrableOn.sub (hsq.const_mul (2 / 23)).integrableOn)
      hjump.integrableOn h4_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (2 / 25)).integrableOn (hsq.const_mul (2 / 23)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (3 * x) (L / 2 - x) x,
      show 3 * x + x = 4 * x by ring, show L / 2 - x + x = L / 2 by ring] at h1
    have hsub_3L : Ioc (3 * x) (L / 2 - x) ⊆ Ioc (3 * x) (4 * x) :=
      Ioc_subset_Ioc_right (by linarith)
    have hmono_3L : (∫ u in Ioc (3 * x) (L / 2 - x), h u ^ 2) ≤ ∫ u in Ioc (3 * x) (4 * x), h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall hsub_3L)
    linarith
  have h4_right_pt : ∀ u : ℝ,
      (2 / 25 : ℝ) * h u ^ 2 - (2 / 23 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => two_twenty_fifths_sq_sub_two_twenty_thirds_sq_le_sub_sq (h u) (h (u + x))
  have h4_right : (2 / 25 : ℝ) * (∫ u in Ioc (L / 2) (L - 4 * x), h u ^ 2) -
      (2 / 23 : ℝ) * (∫ v in Ioc (L - 4 * x) (L - 3 * x), h v ^ 2) ≤
      ∫ u in Ioc (L / 2) (L - 4 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L / 2) (L - 4 * x))
      ((hsq.const_mul (2 / 25)).integrableOn.sub (hshift.const_mul (2 / 23)).integrableOn)
      hjump.integrableOn h4_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (2 / 25)).integrableOn (hshift.const_mul (2 / 23)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L / 2) (L - 4 * x) x,
      show L - 4 * x + x = L - 3 * x by ring] at h1
    have hsub_3R : Ioc (L / 2 + x) (L - 3 * x) ⊆ Ioc (L - 4 * x) (L - 3 * x) :=
      Ioc_subset_Ioc_left (by linarith)
    have hmono_3R : (∫ v in Ioc (L / 2 + x) (L - 3 * x), h v ^ 2) ≤
        ∫ v in Ioc (L - 4 * x) (L - 3 * x), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall hsub_3R)
    linarith
  -- Level 4: `Ioc (3 * x) (L / 2 - x)` and `Ioc (L / 2) (L - 4 * x)` inside `Ioc (3 * x) (L - 4 * x)`
  have hdisj_4 : Disjoint (Ioc (3 * x) (L / 2 - x)) (Ioc (L / 2) (L - 4 * x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hsub_4 : Ioc (3 * x) (L / 2 - x) ∪ Ioc (L / 2) (L - 4 * x) ⊆ Ioc (3 * x) (L - 4 * x) := by
    intro u hu
    rcases hu with hu1 | hu2
    · exact ⟨hu1.1, by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], hu2.2⟩
  have hunion_4 : (∫ u in Ioc (3 * x) (L / 2 - x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (L / 2) (L - 4 * x), (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc (3 * x) (L - 4 * x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj_4 measurableSet_Ioc hjump.integrableOn hjump.integrableOn]
    exact setIntegral_mono_set hjump.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall hsub_4)
  -- Level 3: `Ioc (2 * x) (3 * x)`, `Ioc (3 * x) (L - 4 * x)`, and `Ioc (L - 4 * x) (L - 3 * x)` inside `Ioc (2 * x) (L - 3 * x)`
  have hdisj_3a : Disjoint (Ioc (2 * x) (3 * x)) (Ioc (3 * x) (L - 4 * x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hdisj_3b : Disjoint (Ioc (2 * x) (3 * x) ∪ Ioc (3 * x) (L - 4 * x)) (Ioc (L - 4 * x) (L - 3 * x)) := by
    rw [disjoint_union_left]
    exact ⟨disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1],
      disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]⟩
  have hsub_3 : (Ioc (2 * x) (3 * x) ∪ Ioc (3 * x) (L - 4 * x)) ∪ Ioc (L - 4 * x) (L - 3 * x) ⊆
      Ioc (2 * x) (L - 3 * x) := by
    intro u hu
    rcases hu with (hu0 | hu1) | hu2
    · exact ⟨hu0.1, by linarith [hu0.2]⟩
    · exact ⟨by linarith [hu1.1], by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], hu2.2⟩
  have hunion_3 : (∫ u in Ioc (2 * x) (3 * x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (3 * x) (L - 4 * x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (L - 4 * x) (L - 3 * x), (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc (2 * x) (L - 3 * x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj_3a measurableSet_Ioc hjump.integrableOn hjump.integrableOn,
      ← setIntegral_union hdisj_3b measurableSet_Ioc
        (hjump.integrableOn.mono_set (subset_univ _)) hjump.integrableOn]
    exact setIntegral_mono_set hjump.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall hsub_3)
  linarith

/-- **Disjoint Four-Step Midpoint-Split Interior Jump Bound on `[L / 10, L / 8]`**:
for any `BddSupp A h C` and `x ∈ [L / 10, L / 8]` (`0 ≤ L`), the eight shift intervals
`Ioc 0 x`, `Ioc x (2 * x)`, `Ioc (2 * x) (3 * x)`, `Ioc (3 * x) (L / 2 - x)`,
`Ioc (L / 2) (L - 4 * x)`, `Ioc (L - 4 * x) (L - 3 * x)`, `Ioc (L - 3 * x) (L - 2 * x)`,
and `Ioc (L - 2 * x) (L - x)` are pairwise disjoint inside `Ioc 0 (L - x)`, yielding:
`(15 / 176) * ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2)`
`+ (291 / 3634) * ((∫ v in Ioc (2 * x) (3 * x), h v ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2)`
`+ (178 / 2185) * ((∫ v in Ioc (3 * x) (4 * x), h v ^ 2) + ∫ u in Ioc (L - 4 * x) (L - 3 * x), h u ^ 2)`
`+ (2 / 25) * ((∫ v in Ioc (4 * x) (L / 2), h v ^ 2) + ∫ u in Ioc (L / 2) (L - 4 * x), h u ^ 2)`
`- (23 / 25) * collarMass h L x ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`. -/
theorem disjoint_four_step_slices_le_interior_jump_sq {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hL0 : 0 ≤ L) (hx10 : L / 10 ≤ x) (hx8 : x ≤ L / 8) :
    (15 / 176 : ℝ) *
        ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) +
      (291 / 3634 : ℝ) *
        ((∫ v in Ioc (2 * x) (3 * x), h v ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2) +
      (178 / 2185 : ℝ) *
        ((∫ v in Ioc (3 * x) (4 * x), h v ^ 2) + ∫ u in Ioc (L - 4 * x) (L - 3 * x), h u ^ 2) +
      (2 / 25 : ℝ) *
        ((∫ v in Ioc (4 * x) (L / 2), h v ^ 2) + ∫ u in Ioc (L / 2) (L - 4 * x), h u ^ 2) -
      (23 / 25 : ℝ) * collarMass h L x ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  -- Step 1 (outer collar-to-core intervals `Ioc 0 x` and `Ioc (L - 2x) (L - x)`)
  have h1_left_pt : ∀ u : ℝ,
      (23 / 48 : ℝ) * h (u + x) ^ 2 - (23 / 25 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := twenty_three_forty_eighths_sq_sub_twenty_three_twenty_fifths_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h1_left : (23 / 48 : ℝ) * (∫ v in Ioc x (2 * x), h v ^ 2) -
      (23 / 25 : ℝ) * (∫ u in Iic x, h u ^ 2) ≤
      ∫ u in Ioc 0 x, (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc 0 x)
      ((hshift.const_mul (23 / 48)).integrableOn.sub (hsq.const_mul (23 / 25)).integrableOn)
      hjump.integrableOn h1_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (23 / 48)).integrableOn (hsq.const_mul (23 / 25)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 x x, zero_add,
      show x + x = 2 * x by ring] at h1
    have hIoc_le_Iic : (∫ u in Ioc 0 x, h u ^ 2) ≤ ∫ u in Iic x, h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Iic_self)
    linarith
  have h1_right_pt : ∀ u : ℝ,
      (23 / 48 : ℝ) * h u ^ 2 - (23 / 25 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => twenty_three_forty_eighths_sq_sub_twenty_three_twenty_fifths_sq_le_sub_sq (h u) (h (u + x))
  have h1_right : (23 / 48 : ℝ) * (∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) -
      (23 / 25 : ℝ) * (∫ v in Ioi (L - x), h v ^ 2) ≤
      ∫ u in Ioc (L - 2 * x) (L - x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - 2 * x) (L - x))
      ((hsq.const_mul (23 / 48)).integrableOn.sub (hshift.const_mul (23 / 25)).integrableOn)
      hjump.integrableOn h1_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (23 / 48)).integrableOn (hshift.const_mul (23 / 25)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - 2 * x) (L - x) x,
      show L - 2 * x + x = L - x by ring, show L - x + x = L by ring] at h1
    have hIoc_le_Ioi : (∫ v in Ioc (L - x) L, h v ^ 2) ≤ ∫ v in Ioi (L - x), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Ioi_self)
    linarith
  -- Step 2 (layer-1-to-layer-2 intervals `Ioc x (2 * x)` and `Ioc (L - 3 * x) (L - 2 * x)`)
  have h2_left_pt : ∀ u : ℝ,
      (13 / 46 : ℝ) * h (u + x) ^ 2 - (13 / 33 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := thirteen_forty_sixths_sq_sub_thirteen_thirty_thirds_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h2_left : (13 / 46 : ℝ) * (∫ v in Ioc (2 * x) (3 * x), h v ^ 2) -
      (13 / 33 : ℝ) * (∫ u in Ioc x (2 * x), h u ^ 2) ≤
      ∫ u in Ioc x (2 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc x (2 * x))
      ((hshift.const_mul (13 / 46)).integrableOn.sub (hsq.const_mul (13 / 33)).integrableOn)
      hjump.integrableOn h2_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (13 / 46)).integrableOn (hsq.const_mul (13 / 33)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) x (2 * x) x,
      show x + x = 2 * x by ring, show 2 * x + x = 3 * x by ring] at h1
    linarith
  have h2_right_pt : ∀ u : ℝ,
      (13 / 46 : ℝ) * h u ^ 2 - (13 / 33 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => thirteen_forty_sixths_sq_sub_thirteen_thirty_thirds_sq_le_sub_sq (h u) (h (u + x))
  have h2_right : (13 / 46 : ℝ) * (∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2) -
      (13 / 33 : ℝ) * (∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2) ≤
      ∫ u in Ioc (L - 3 * x) (L - 2 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - 3 * x) (L - 2 * x))
      ((hsq.const_mul (13 / 46)).integrableOn.sub (hshift.const_mul (13 / 33)).integrableOn)
      hjump.integrableOn h2_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (13 / 46)).integrableOn (hshift.const_mul (13 / 33)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - 3 * x) (L - 2 * x) x,
      show L - 3 * x + x = L - 2 * x by ring, show L - 2 * x + x = L - x by ring] at h1
    linarith
  have hinner := inner_two_step_slices_le_setIntegral_Ioc hh hL0 hx10 hx8
  -- Level 2: `Ioc x (2 * x)`, `Ioc (2 * x) (L - 3 * x)`, and `Ioc (L - 3 * x) (L - 2 * x)` inside `Ioc x (L - 2 * x)`
  have hdisj_2a : Disjoint (Ioc x (2 * x)) (Ioc (2 * x) (L - 3 * x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hdisj_2b : Disjoint (Ioc x (2 * x) ∪ Ioc (2 * x) (L - 3 * x)) (Ioc (L - 3 * x) (L - 2 * x)) := by
    rw [disjoint_union_left]
    exact ⟨disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1],
      disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]⟩
  have hsub_2 : (Ioc x (2 * x) ∪ Ioc (2 * x) (L - 3 * x)) ∪ Ioc (L - 3 * x) (L - 2 * x) ⊆
      Ioc x (L - 2 * x) := by
    intro u hu
    rcases hu with (hu0 | hu1) | hu2
    · exact ⟨hu0.1, by linarith [hu0.2]⟩
    · exact ⟨by linarith [hu1.1], by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], hu2.2⟩
  have hunion_2 : (∫ u in Ioc x (2 * x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (2 * x) (L - 3 * x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (L - 3 * x) (L - 2 * x), (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc x (L - 2 * x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj_2a measurableSet_Ioc hjump.integrableOn hjump.integrableOn,
      ← setIntegral_union hdisj_2b measurableSet_Ioc
        (hjump.integrableOn.mono_set (subset_univ _)) hjump.integrableOn]
    exact setIntegral_mono_set hjump.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall hsub_2)
  -- Level 1: `Ioc 0 x`, `Ioc x (L - 2 * x)`, and `Ioc (L - 2 * x) (L - x)` inside `Ioc 0 (L - x)`
  have hdisj_1a : Disjoint (Ioc 0 x) (Ioc x (L - 2 * x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hdisj_1b : Disjoint (Ioc 0 x ∪ Ioc x (L - 2 * x)) (Ioc (L - 2 * x) (L - x)) := by
    rw [disjoint_union_left]
    exact ⟨disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1],
      disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]⟩
  have hsub_1 : (Ioc 0 x ∪ Ioc x (L - 2 * x)) ∪ Ioc (L - 2 * x) (L - x) ⊆ Ioc 0 (L - x) := by
    intro u hu
    rcases hu with (hu0 | hu1) | hu2
    · exact ⟨hu0.1, by linarith [hu0.2]⟩
    · exact ⟨by linarith [hu1.1], by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], hu2.2⟩
  have hunion_1 : (∫ u in Ioc 0 x, (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc x (L - 2 * x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (L - 2 * x) (L - x), (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj_1a measurableSet_Ioc hjump.integrableOn hjump.integrableOn,
      ← setIntegral_union hdisj_1b measurableSet_Ioc
        (hjump.integrableOn.mono_set (subset_univ _)) hjump.integrableOn]
    exact setIntegral_mono_set hjump.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall hsub_1)
  unfold collarMass
  linarith

/-- For any `BddSupp A h C`, the core `Ioc x (L - x)` is covered by the eight slices
`Ioc x (2 * x)`, `Ioc (L - 2 * x) (L - x)`, `Ioc (2 * x) (3 * x)`, `Ioc (L - 3 * x) (L - 2 * x)`,
`Ioc (3 * x) (4 * x)`, `Ioc (L - 4 * x) (L - 3 * x)`, `Ioc (4 * x) (L / 2)`, and `Ioc (L / 2) (L - 4 * x)`. -/
theorem coreMass_le_four_step_midpoint_split_layers {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) :
    coreMass h L x ≤
      ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) +
        ((∫ v in Ioc (2 * x) (3 * x), h v ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2) +
        ((∫ v in Ioc (3 * x) (4 * x), h v ^ 2) + ∫ u in Ioc (L - 4 * x) (L - 3 * x), h u ^ 2) +
        ((∫ v in Ioc (4 * x) (L / 2), h v ^ 2) + ∫ u in Ioc (L / 2) (L - 4 * x), h u ^ 2) := by
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
      (∫ u in Ioc (2 * x) (L - 3 * x), h u ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2 := by
    refine setIntegral_le_add_of_subset_union hsq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (L - 3 * x) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨hgt, hu.2⟩
  have h4 : (∫ u in Ioc (2 * x) (L - 3 * x), h u ^ 2) ≤
      (∫ u in Ioc (2 * x) (3 * x), h u ^ 2) + ∫ u in Ioc (3 * x) (L - 3 * x), h u ^ 2 := by
    refine setIntegral_le_add_of_subset_union hsq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (3 * x) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨hgt, hu.2⟩
  have h5 : (∫ u in Ioc (3 * x) (L - 3 * x), h u ^ 2) ≤
      (∫ u in Ioc (3 * x) (L - 4 * x), h u ^ 2) + ∫ u in Ioc (L - 4 * x) (L - 3 * x), h u ^ 2 := by
    refine setIntegral_le_add_of_subset_union hsq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (L - 4 * x) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨hgt, hu.2⟩
  have h6 : (∫ u in Ioc (3 * x) (L - 4 * x), h u ^ 2) ≤
      (∫ u in Ioc (3 * x) (4 * x), h u ^ 2) + ∫ u in Ioc (4 * x) (L - 4 * x), h u ^ 2 := by
    refine setIntegral_le_add_of_subset_union hsq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (4 * x) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨hgt, hu.2⟩
  have h7 : (∫ u in Ioc (4 * x) (L - 4 * x), h u ^ 2) ≤
      (∫ u in Ioc (4 * x) (L / 2), h u ^ 2) + ∫ u in Ioc (L / 2) (L - 4 * x), h u ^ 2 := by
    refine setIntegral_le_add_of_subset_union hsq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (L / 2) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨hgt, hu.2⟩
  linarith

/-- **Universal Tenth-Window Coercivity (`(2 / 25) * ∫ h² ≤ D_h(x)` for all `x ≥ L / 10`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and **every shift `x ≥ L / 10`**,
`(2 / 25) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem two_twenty_fifths_mul_integral_sq_le_integral_jump_sq_of_tenth_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 10 ≤ x) :
    (2 / 25 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  rcases le_or_gt x (L / 8) with hle | hgt
  · have hx0 : 0 ≤ x := by linarith
    have hxL2 : x ≤ L / 2 := by linarith
    have hcol_int := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
    have hfour := disjoint_four_step_slices_le_interior_jump_sq hh hL0 hx hle
    have hcov := coreMass_le_four_step_midpoint_split_layers (L := L) (x := x) hh
    have hcons := collarMass_add_coreMass_eq hh hxL2
    have hlay1_nn : 0 ≤ (∫ v in Ioc x (2 * x), h v ^ 2) +
        ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2 :=
      add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    have hlay2_nn : 0 ≤ (∫ v in Ioc (2 * x) (3 * x), h v ^ 2) +
        ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2 :=
      add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    have hlay3_nn : 0 ≤ (∫ v in Ioc (3 * x) (4 * x), h v ^ 2) +
        ∫ u in Ioc (L - 4 * x) (L - 3 * x), h u ^ 2 :=
      add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    linarith
  · have h8 := three_twenty_fifths_mul_integral_sq_le_integral_jump_sq_of_eighth_le
      hh hsupp hL0 hgt.le
    have hE0 : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith

/-- **Universal Tenth-Window Autocorrelation Damping (`2 R(x) ≤ (48 / 25) R(0)` for all `x ≥ L / 10`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and every shift `x ≥ L / 10`,
`2 * autocorr h x ≤ (48 / 25) * ∫ u, h u ^ 2`. -/
theorem two_mul_autocorr_le_forty_eight_twenty_fifths_mul_integral_sq_of_tenth_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 10 ≤ x) :
    2 * autocorr h x ≤ (48 / 25 : ℝ) * ∫ u, h u ^ 2 := by
  have hid := integral_jump_sq hh x
  have hcoerc := two_twenty_fifths_mul_integral_sq_le_integral_jump_sq_of_tenth_le
    hh hsupp hL0 hx
  linarith

/-! ## Section 2: Six-Shell Potential Coercivity and Sharpened `(0, log 2)` Plastic Floor -/

/-- Integrating `(2 / 25)` coercivity against `-screwRegularKernel x ≥ 0` over `Ioo a c`
(`L / 10 ≤ a ≤ c ≤ screwSignThreshold`) yields
`(1 / 25) * (Φ(a) - Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo a c} (-screwRegularKernel x) D_h(x) dx`. -/
theorem one_twenty_fifth_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L a c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL : 0 < L) (ha : L / 10 ≤ a) (hac : a ≤ c)
    (hct : c ≤ screwSignThreshold) :
    (1 / 25 : ℝ) * (levyCoshPotential a - levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo a c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have ha0 : 0 < a := by linarith
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
      (fun x : ℝ => (-screwRegularKernel x) * ((2 / 25 : ℝ) * ∫ u, h u ^ 2)) (Ioo a c) :=
    hI_K.mul_const _
  have hmono : (∫ x in Ioo a c, (-screwRegularKernel x) * ((2 / 25 : ℝ) * ∫ u, h u ^ 2)) ≤
      ∫ x in Ioo a c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
    refine setIntegral_mono_on hI_low hI_jump measurableSet_Ioo fun x hx => ?_
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hct))
    exact mul_le_mul_of_nonneg_left
      (two_twenty_fifths_mul_integral_sq_le_integral_jump_sq_of_tenth_le hh hsupp hL.le
        (ha.trans hx.1.le))
      hK0
  rw [integral_mul_const, setIntegral_Ioo_neg_screwRegularKernel ha0 hac] at hmono
  linarith

/-- **Six-Shell `(L / 10, L / 8) ∪ (L / 8, L / 6) ∪ (L / 6, L / 5) ∪ (L / 5, L / 4) ∪ (L / 4, L / 3) ∪ (L / 3, c)` Jump Coercivity**:
for `L / 3 ≤ c ≤ screwSignThreshold`,
`((1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) - (12 / 41) * Φ(c)) * ∫ u, h u ^ 2`
`≤ ∫ x in Ioo (L / 10) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem tenth_to_third_with_fifth_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL0 : 0 < L) (hL3c : L / 3 ≤ c)
    (hct : c ≤ screwSignThreshold) :
    ((1 / 25 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (67 / 1800 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (2 / 35 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) -
        (12 / 41 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 10) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL10_pos : 0 < L / 10 := by linarith
  have hL10_8 : L / 10 ≤ L / 8 := by linarith
  have hL8_c : L / 8 ≤ c := by linarith
  have hL8_t : L / 8 ≤ screwSignThreshold := le_trans hL8_c hct
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 10) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL10_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 10) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL10_pos hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_left_Ioc : IntegrableOn F (Ioc (L / 10) (L / 8)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL8_c)
  have hIF_right_Ioc : IntegrableOn F (Ioc (L / 8) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL10_8 le_rfl)
  have hdisj : Disjoint (Ioc (L / 10) (L / 8)) (Ioc (L / 8) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 10) c, F x) =
      (∫ x in Ioo (L / 10) (L / 8), F x) + ∫ x in Ioo (L / 8) c, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL10_8 hL8_c,
      setIntegral_union hdisj measurableSet_Ioc hIF_left_Ioc hIF_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h10 := one_twenty_fifth_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL10_8 hL8_t
  have h83 := eighth_to_third_with_fifth_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL3c hct
  dsimp only [F] at hsplit
  linarith

/-- **Six-Shell `(L / 10, L / 8, L / 6, L / 5, L / 4, L / 3, c)` Lévy–Cosh Crossover Inequality**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and any `c` with
`L / 3 ≤ c ≤ screwSignThreshold`,
`(A(0) + (1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (29 / 41) * Φ(c)) * ∫ f²`
`+ ∫∫ f(u)f(v)(2 cosh((u-v)/2) - K_c(|u-v|)) ≤ W_∞(f ⋆ f̃)`. -/
theorem tenth_to_third_with_fifth_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L)
    (hL3c : L / 3 ≤ c) (hct : c ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (29 / 41) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL10 : 0 < L / 10 := by linarith
  have hL10c : L / 10 ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL10 hL10c hct
  have hsub := tenth_to_third_with_fifth_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL hL3c hct
  linarith

/-- **Sharpened `(0, log 2)` Plastic-Floor Theorem with Tenth-Window Coercivity**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 (log 2)`, the universal constant floor is
boosted to `A(0) + (1 / 25) * Φ((log 2)/10) + (1 / 50) * Φ((log 2)/8) + (67 / 1800) * Φ((log 2)/6) + (13 / 360) * Φ((log 2)/5) + (2 / 35) * Φ((log 2)/4) + (88 / 861) * Φ((log 2)/3) + (29 / 41) * Φ(screwSignThreshold)`
(reducing the universal constant deficit on `(0, log 2)` from `-0.0221` down to **`-0.0156`**). -/
theorem tenth_window_log_two_plastic_floor_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hsupp : ∀ u ∉ Ioo 0 (Real.log 2), f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (Real.log 2 / 10) +
        (1 / 50) * levyCoshPotential (Real.log 2 / 8) +
        (67 / 1800) * levyCoshPotential (Real.log 2 / 6) +
        (13 / 360) * levyCoshPotential (Real.log 2 / 5) +
        (2 / 35) * levyCoshPotential (Real.log 2 / 4) +
        (88 / 861) * levyCoshPotential (Real.log 2 / 3) +
        (29 / 41) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 / 3 ≤ screwSignThreshold := by
    linarith [Real.log_two_lt_d9, screwSignThreshold_gt_6036_over_21509]
  have hmain := tenth_to_third_with_fifth_levyCosh_crossover_le_weilArchRe
    hf hfc hlog2 hlt le_rfl hsupp
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-! ## Section 3: Nine-Point Reflected Potential and Unconditional Positivity on `(0, 5 / 12)` (`60.11%` of `(0, log 2)`) -/

/-- **Nine-Point Reflected Shell Jump-Integral Coercivity on `Ioo (L / 10) c` (`2 * L / 3 ≤ c ≤ 3 * L / 4`)**:
combining `(L / 10, L / 8)` with the eight-point reflected shell on `(L / 8, c)` yields:
`((1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (88 / 861) * Φ(2 * L / 3) - (17 / 21) * Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo (L / 10) c} (-screwRegularKernel x) D_h(x) dx`. -/
theorem nine_point_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (h23c : 2 * L / 3 ≤ c)
    (hc34 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold) :
    ((1 / 25 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (67 / 1800 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (2 / 35 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 41 : ℝ) * levyCoshPotential (L / 2) +
        (88 / 861 : ℝ) * levyCoshPotential (2 * L / 3) -
        (17 / 21 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 10) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL10 : 0 < L / 10 := by linarith
  have hL10_8 : L / 10 ≤ L / 8 := by linarith
  have hL8c : L / 8 ≤ c := by linarith
  have hL8t : L / 8 ≤ screwSignThreshold := le_trans hL8c hct
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 10) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL10 hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 10) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL10 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_left_Ioc : IntegrableOn F (Ioc (L / 10) (L / 8)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL8c)
  have hIF_right_Ioc : IntegrableOn F (Ioc (L / 8) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL10_8 le_rfl)
  have hdisj : Disjoint (Ioc (L / 10) (L / 8)) (Ioc (L / 8) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 10) c, F x) =
      (∫ x in Ioo (L / 10) (L / 8), F x) + ∫ x in Ioo (L / 8) c, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL10_8 hL8c,
      setIntegral_union hdisj measurableSet_Ioc hIF_left_Ioc hIF_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h10 := one_twenty_fifth_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL le_rfl hL10_8 hL8t
  have h8 := eight_point_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL h23c hc34 hct
  dsimp only [F] at hsplit
  linarith

/-- **Nine-Point Reflected Lévy–Cosh Crossover Inequality on `(0, L)` (`2 * L / 3 ≤ c ≤ 3 * L / 4`)**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`),
`(A(0) + (1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (88 / 861) * Φ(2 * L / 3) + (4 / 21) * Φ(c)) * ∫ f² + ... ≤ W_∞(f ⋆ f̃)`. -/
theorem nine_point_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L)
    (h23c : 2 * L / 3 ≤ c) (hc34 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (17 / 41) * levyCoshPotential (L / 2) +
        (88 / 861) * levyCoshPotential (2 * L / 3) +
        (4 / 21) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL10 : 0 < L / 10 := by linarith
  have hL10c : L / 10 ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL10 hL10c hct
  have hnine := nine_point_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL h23c hc34 hct
  linarith

/-- **Osculating Lower Bound for the Nine-Point Reflected Potential (`L > 0`, `c > 0`)**:
splitting `3 / 50` at `L / 8` into `1 / 25` at `L / 10` and `1 / 50` at `L / 8`
(where `log(1 / (2π(L / 10))) - log(1 / (2π(L / 8))) = log(5 / 4)` and
`(7 / 2) * (L / 10 - L / 8) = -(7 / 80) * L`) yields for **every** `L > 0` and `c > 0`:
`log(1 / (π * L)) + (7 / 72) * log 2 + (1931 / 12600) * log(4 / 3) + (137 / 1800) * log(5 / 4) + (88 / 861) * log(9 / 8) + (4 / 21) * log((21 / 8) * L) + (32483 / 27000) * L + 4 / 21 - γ`
`≤ EF.gammaBracket 0 + (1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (88 / 861) * Φ(2 * L / 3) + (4 / 21) * Φ(c)`. -/
theorem osculating_le_nine_point_potential {L c : ℝ} (hL : 0 < L) (hc0 : 0 < c) :
    Real.log (1 / (Real.pi * L)) + (7 / 72 : ℝ) * Real.log 2 +
        (1931 / 12600 : ℝ) * Real.log (4 / 3) +
        (137 / 1800 : ℝ) * Real.log (5 / 4) +
        (88 / 861 : ℝ) * Real.log (9 / 8) +
        (4 / 21 : ℝ) * Real.log ((21 / 8 : ℝ) * L) +
        (32483 / 27000 : ℝ) * L + 4 / 21 - eulerMascheroniConstant ≤
      EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (17 / 41) * levyCoshPotential (L / 2) +
        (88 / 861) * levyCoshPotential (2 * L / 3) +
        (4 / 21) * levyCoshPotential c := by
  have h10 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 10)
  have h1 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 8)
  have h2 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 6)
  have h5_pt := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 5)
  have h3 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 4)
  have h4 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 3)
  have h5 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 2)
  have h6 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < 2 * L / 3)
  have h7 := log_seven_div_four_pi_add_one_le_gammaBracket_add_levyCoshPotential hc0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog3 : Real.log 3 = 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [Real.log_div (by norm_num) (by norm_num), hlog4]; ring
  have hlog10 : Real.log (1 / (2 * Real.pi * (L / 10))) =
      Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 + Real.log (5 / 4) := by
    rw [← hlog4, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog1 : Real.log (1 / (2 * Real.pi * (L / 8))) =
      Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 := by
    rw [← hlog4, ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog2 : Real.log (1 / (2 * Real.pi * (L / 6))) =
      Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [show Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 - Real.log (4 / 3) =
        Real.log (1 / (Real.pi * L)) + Real.log 3 by linarith [hlog3],
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog_fifth : Real.log (1 / (2 * Real.pi * (L / 5))) =
      Real.log (1 / (Real.pi * L)) + Real.log 2 + Real.log (5 / 4) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog3_pt : Real.log (1 / (2 * Real.pi * (L / 4))) =
      Real.log (1 / (Real.pi * L)) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
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

/-- Rational lower bound `6 / 67 < Real.log (35 / 32)` via `Real.lt_log_one_add_of_pos` at `3 / 32`. -/
theorem six_sixty_sevenths_lt_log_35_32 :
    (6 : ℝ) / 67 < Real.log (35 / 32) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 3 / 32)
  norm_num at h ⊢
  exact h

/-- Lower bound on `log(1 / (π * (5 / 12)))` derived from
`two_mul_log_five_sub_five_mul_log_two_le_log_inv_pi_mul_two_fifths` and `log(25 / 24) ≤ 1 / 24`:
`2 * log 5 - 5 * log 2 + 23 / 24 - 5 * π / 16 ≤ log(1 / (π * (5 / 12)))`. -/
theorem log_inv_pi_mul_five_twelfths_ge :
    2 * Real.log 5 - 5 * Real.log 2 + 23 / 24 - 5 * Real.pi / 16 ≤
      Real.log (1 / (Real.pi * (5 / 12))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsplit : Real.log (1 / (Real.pi * (2 / 5))) =
      Real.log (1 / (Real.pi * (5 / 12))) + Real.log (25 / 24) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog25_24 : Real.log (25 / 24 : ℝ) ≤ 1 / 24 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 25 / 24)
    linarith
  have hbase := two_mul_log_five_sub_five_mul_log_two_le_log_inv_pi_mul_two_fifths
  linarith

/-- **Strict Positivity of the Nine-Point Reflected Potential at `L = 5 / 12` (`≈ 0.416667`, `60.11%` of `(0, log 2)`)**:
`0 ≤ EF.gammaBracket 0 + (1 / 25) * Φ((5/12)/10) + (1 / 50) * Φ((5/12)/8) + (67 / 1800) * Φ((5/12)/6) + (13 / 360) * Φ((5/12)/5) + (2 / 35) * Φ((5/12)/4) + (88 / 861) * Φ((5/12)/3) + (17 / 41) * Φ((5/12)/2) + (88 / 861) * Φ(2*(5/12)/3) + (4 / 21) * Φ(screwSignThreshold)`. -/
theorem zero_le_nine_point_potential_five_twelfths :
    0 ≤ EF.gammaBracket 0 + (1 / 25) * levyCoshPotential ((5 / 12 : ℝ) / 10) +
        (1 / 50) * levyCoshPotential ((5 / 12 : ℝ) / 8) +
        (67 / 1800) * levyCoshPotential ((5 / 12 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((5 / 12 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((5 / 12 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((5 / 12 : ℝ) / 3) +
        (17 / 41) * levyCoshPotential ((5 / 12 : ℝ) / 2) +
        (88 / 861) * levyCoshPotential (2 * (5 / 12 : ℝ) / 3) +
        (4 / 21) * levyCoshPotential screwSignThreshold := by
  have hosc := osculating_le_nine_point_potential
    (by norm_num : (0 : ℝ) < 5 / 12) screwSignThreshold_pos
  rw [show (21 / 8 : ℝ) * (5 / 12) = 35 / 32 by norm_num] at hosc
  have hlog_pi := log_inv_pi_mul_five_twelfths_ge
  have hlog2_lt := Real.log_two_lt_d9
  have hlog2_gt := Real.log_two_gt_d9
  have hlog5 := Real.log_five_gt_d9
  have hlog43 := two_sevenths_lt_log_four_thirds
  have hlog54 := two_ninths_lt_log_five_fourths
  have hlog98 := two_seventeenths_lt_log_nine_eighths
  have hlog35 := six_sixty_sevenths_lt_log_35_32
  have hpi := Real.pi_lt_d4
  have hgamma :=
    RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith

/-- **Unconditional Archimedean Weil Positivity on `(0, 5 / 12)` (`≈ (0, 0.416667)`, `60.11%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` supported in `Ioo 0 L` with `L ≤ 5 / 12`,
`0 ≤ WeilOneSided.weilArchRe (EF.weilTest f f)`. -/
theorem weilArchRe_nonneg_of_support_Ioo_le_five_twelfths {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL : L ≤ 5 / 12) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_5_12 : ∀ u ∉ Ioo (0 : ℝ) (5 / 12), f u = 0 :=
    fun u hu => hsupp u fun huL => hu ⟨huL.1, huL.2.trans_le hL⟩
  have hmain := nine_point_levyCosh_crossover_le_weilArchRe
    hf hfc (by norm_num : (0 : ℝ) < 5 / 12)
    (by linarith [screwSignThreshold_gt_6036_over_21509])
    (by linarith [screwSignThreshold_lt_two_sevenths])
    le_rfl hsupp_5_12
  have hpot := zero_le_nine_point_potential_five_twelfths
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hterm1 : 0 ≤ (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential ((5 / 12 : ℝ) / 10) +
        (1 / 50) * levyCoshPotential ((5 / 12 : ℝ) / 8) +
        (67 / 1800) * levyCoshPotential ((5 / 12 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((5 / 12 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((5 / 12 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((5 / 12 : ℝ) / 3) +
        (17 / 41) * levyCoshPotential ((5 / 12 : ℝ) / 2) +
        (88 / 861) * levyCoshPotential (2 * (5 / 12 : ℝ) / 3) +
        (4 / 21) * levyCoshPotential screwSignThreshold) * ∫ u, f u ^ 2 :=
    mul_nonneg hpot hsq
  have hpair : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-- **Unconditional `WindowPositive` on `(0, 5 / 12)` (`≈ (0, 0.416667)`, `60.11%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (5 / 12)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_five_twelfths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (5 / 12)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_five_twelfths hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 29 / 70)` (`≈ (0, 0.414286)`, `59.77%` of `(0, log 2)`)**:
immediate corollary since `29 / 70 ≤ 5 / 12` (`348 ≤ 350`). -/
theorem windowPositive_twenty_nine_seventieths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (29 / 70)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_five_twelfths hf hfc hf0 (by norm_num : (29 : ℝ) / 70 ≤ 5 / 12)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 7 / 17)` (`≈ (0, 0.411765)`, `59.41%` of `(0, log 2)`)**:
immediate corollary since `7 / 17 ≤ 5 / 12` (`84 ≤ 85`). -/
theorem windowPositive_seven_seventeenths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (7 / 17)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_five_twelfths hf hfc hf0 (by norm_num : (7 : ℝ) / 17 ≤ 5 / 12)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

end

end RHTower.WeilLevyTenthWindow
