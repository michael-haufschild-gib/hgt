import GaloisForLFunctions.RHTower.WeilLevyTenthWindowCoercivity

/-!
# Seventh-Window Three-Step Double-Collar Core Transport and Unconditional Positivity on `(0, 19 / 45)`

This module implements **Cycle 75** of the prime-blind archimedean Weil positivity programme,
establishing the three-step double-collar core transport on `[L / 7, L / 6]` (`D_h(x) ≥ (3 / 20) ∫ h²`),
unlocking the inner-reflected potential regime `L / 2 ≤ c ≤ 2 * L / 3` beyond the
`L = (3 / 2) * screwSignThreshold ≈ 0.42094` barrier, and pushing unconditional `WindowPositive`
from `(0, 5 / 12)` (`≈ (0, 0.416667)`, `60.11%` of `(0, log 2)`) to **`(0, 19 / 45)`**
(`≈ (0, 0.422222)`, **`60.91%` of `(0, log 2)`**), as well as `(0, 27 / 64)`, `(0, 8 / 19)`,
and `(0, 29 / 69)`.

## Mathematical Architecture

1. **Section 1 — Three-Step Double-Collar Core Transport on `[L / 7, L / 6]` (`D_h(x) ≥ (3 / 20) ∫ h²`)**:
   - On `[L / 7, L / 6]`, a shift by $x$ has path length $7$, whose path-graph Dirichlet Laplacian
     $Q_7$ has spectral floor $\lambda_{\min}(Q_7) = 2 - 2\cos(\pi / 8) = 2 - \sqrt{2 + \sqrt{2}} \approx 0.152241$.
   - We prove the three exact single-square SOS transport inequalities:
     $$(p - q)^2 - \left(\frac{17}{37} p^2 - \frac{17}{20} q^2\right) = \frac{20}{37}\left(p - \frac{37}{20} q\right)^2 \ge 0,$$
     $$(p - q)^2 - \left(\frac{4}{17} p^2 - \frac{4}{13} q^2\right) = \frac{13}{17}\left(p - \frac{17}{13} q\right)^2 \ge 0,$$
     $$(p - q)^2 - \left(\frac{1}{13} p^2 - \frac{1}{12} q^2\right) = \frac{12}{13}\left(p - \frac{13}{12} q\right)^2 \ge 0.$$
   - For $x \in [L / 7, L / 6]$, we have $L - 4x \le 3x \le L - 3x$, so the six shift intervals
     $$\mathrm{Ioc}\,0\,x,\ \mathrm{Ioc}\,x\,(2x),\ \mathrm{Ioc}\,(2x)\,(L - 4x),\
       \mathrm{Ioc}\,(3x)\,(L - 3x),\ \mathrm{Ioc}\,(L - 3x)\,(L - 2x),\ \mathrm{Ioc}\,(L - 2x)\,(L - x)$$
     satisfy $0 \le x \le 2x \le L - 4x \le 3x \le L - 3x \le L - 2x \le L - x$ and are **pairwise disjoint**
     inside $\mathrm{Ioc}\,0\,(L - x)$, while both $\mathrm{Ioc}\,(2x)\,(L - 4x) + x = \mathrm{Ioc}\,(3x)\,(L - 3x)$
     and $\mathrm{Ioc}\,(3x)\,(L - 3x)$ cover the **entire central core** $\mathrm{Ioc}\,(3x)\,(L - 3x)$ twice!
   - Since $1 - \frac{17}{20} = \frac{3}{20}$, $\frac{17}{37} - \frac{4}{13} = \frac{73}{481} \ge \frac{3}{20}$,
     $\frac{4}{17} - \frac{1}{12} = \frac{31}{204} \ge \frac{3}{20}$, and $2 \cdot \frac{1}{13} = \frac{2}{13} \ge \frac{3}{20}$,
     this proves:
     $$\frac{3}{20}\int_{\mathbb R} h(u)^2\,du \le \int_{\mathbb R} (h(u) - h(u + x))^2\,du
       \qquad \forall x \ge \frac{L}{7}$$
     (a $+25\%$ jump over $3 / 25 = 0.12$ on `[L / 7, L / 6]`, within $0.00224$ of $2 - \sqrt{2 + \sqrt{2}} \approx 0.152241$).

2. **Section 2 — Seven-Shell Potential Coercivity and Sharpened `(0, log 2)` Plastic Floor**:
   - Inserting `(L / 7, L / 6)` (`3 / 40`) between `(L / 8, L / 7)` (`3 / 50`) and `(L / 6, L / 5)` (`7 / 72`)
     splits the $67 / 1800$ weight at $L / 6$ into $3 / 200$ at $L / 7$ and $1 / 45$ at $L / 6$,
     reducing the universal `(0, log 2)` constant deficit from `-0.0156` down to **`-0.0138`**.

3. **Section 3 — Inner-Reflected Nine-Point Potential (`L / 2 ≤ c ≤ 2 * L / 3`) and Positivity on `(0, 19 / 45)` (`60.91%` of `(0, log 2)`)**:
   - For $L > \frac{3}{2} t_* \approx 0.42094$, the plastic crossover $c = t_*$ enters $[L / 2, 2 L / 3]$,
     where `third_window_inner_shell_sub_levyCoshPotential_le_setIntegral_Ioo` (`Cycle 72`) applies
     directly on `(L / 3, c)`, yielding the inner-reflected nine-point potential with weights
     $(1 / 25,\ 1 / 50,\ 3 / 200,\ 1 / 45,\ 13 / 360,\ 2 / 35,\ 88 / 861,\ 17 / 41,\ 12 / 41)$
     at $(L / 10,\ L / 8,\ L / 7,\ L / 6,\ L / 5,\ L / 4,\ L / 3,\ L / 2,\ c)$.
   - Using the 5-smooth logarithmic identities $\log(5 / 4) = \log 5 - 2\log 2$,
     $\log(4 / 3) = \log 5 - 2\log 2 + \log(16 / 15) > \log 5 - 2\log 2 + 2 / 31$, and
     $\frac{1}{\pi L} = \frac{16}{5\pi} \cdot \frac{1}{2} \cdot \frac{4}{3} \cdot \frac{15}{32 L}$,
     we prove strict positivity (`+0.000260 > 0`) at $L = 19 / 45 \approx 0.422222$ (`60.91%` of `(0, log 2)`).
-/

open Complex Real Set MeasureTheory Filter
open scoped Topology
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevySeventhWindow

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor
open RHTower.WeilLevyQuarterWindow RHTower.WeilLevySymmetricThreePoint
open RHTower.WeilLevySixthWindow RHTower.WeilLevyFibonacciStaircase
open RHTower.WeilLevyEighthWindow RHTower.WeilLevyThirdWindow
open RHTower.WeilLevyFifthWindow RHTower.WeilLevyTenthWindow

/-! ## Section 1: Three-Step Double-Collar Core Transport on `[L / 7, L / 6]` (`D_h(x) ≥ (3 / 20) ∫ h²`) -/

/-- Exact step-1 SOS inequality (`(17 / 37, 17 / 20)`): for all `p, q : ℝ`,
`(17 / 37) * p ^ 2 - (17 / 20) * q ^ 2 ≤ (p - q) ^ 2`, proved via the exact single-square identity
`(p - q) ^ 2 - ((17 / 37) * p ^ 2 - (17 / 20) * q ^ 2) = (20 / 37) * (p - (37 / 20) * q) ^ 2 ≥ 0`. -/
theorem seventeen_thirty_sevenths_sq_sub_seventeen_twentieths_sq_le_sub_sq (p q : ℝ) :
    (17 / 37 : ℝ) * p ^ 2 - (17 / 20 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  nlinarith [sq_nonneg (p - (37 / 20 : ℝ) * q)]

/-- Exact step-2 SOS inequality (`(4 / 17, 4 / 13)`): for all `p, q : ℝ`,
`(4 / 17) * p ^ 2 - (4 / 13) * q ^ 2 ≤ (p - q) ^ 2`, proved via the exact single-square identity
`(p - q) ^ 2 - ((4 / 17) * p ^ 2 - (4 / 13) * q ^ 2) = (13 / 17) * (p - (17 / 13) * q) ^ 2 ≥ 0`. -/
theorem four_seventeenths_sq_sub_four_thirteenths_sq_le_sub_sq (p q : ℝ) :
    (4 / 17 : ℝ) * p ^ 2 - (4 / 13 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  nlinarith [sq_nonneg (p - (17 / 13 : ℝ) * q)]

/-- Exact step-3 SOS inequality (`(1 / 13, 1 / 12)`): for all `p, q : ℝ`,
`(1 / 13) * p ^ 2 - (1 / 12) * q ^ 2 ≤ (p - q) ^ 2`, proved via the exact single-square identity
`(p - q) ^ 2 - ((1 / 13) * p ^ 2 - (1 / 12) * q ^ 2) = (12 / 13) * (p - (13 / 12) * q) ^ 2 ≥ 0`. -/
theorem one_thirteenth_sq_sub_one_twelfth_sq_le_sub_sq (p q : ℝ) :
    (1 / 13 : ℝ) * p ^ 2 - (1 / 12 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  nlinarith [sq_nonneg (p - (13 / 12 : ℝ) * q)]

/-- **Inner Two-Step Double-Collar Transport Bound on `Ioc x (L - 2 * x)` (`x ∈ [L / 7, L / 6]`)**:
combining Step 2 (`(4 / 17, 4 / 13)`) on `Ioc x (2 * x)` and `Ioc (L - 3 * x) (L - 2 * x)`
with Step 3 (`(1 / 13, 1 / 12)`) on `Ioc (2 * x) (L - 4 * x)` (shifting onto the entire central
core `Ioc (3 * x) (L - 3 * x)`) and `Ioc (3 * x) (L - 3 * x)` (shifting into `Ioc (L - 3 * x) (L - 2 * x)`)
yields:
`(31 / 204) * ((∫ v in Ioc (2 * x) (3 * x), h v ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2)`
`+ (2 / 13) * (∫ u in Ioc (3 * x) (L - 3 * x), h u ^ 2)`
`- (4 / 13) * ((∫ u in Ioc x (2 * x), h u ^ 2) + ∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2)`
`≤ ∫ u in Ioc x (L - 2 * x), (h u - h (u + x)) ^ 2`. -/
theorem seventh_inner_double_transport_le_setIntegral_Ioc {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hL0 : 0 ≤ L) (hx7 : L / 7 ≤ x) (hx6 : x ≤ L / 6) :
    (31 / 204 : ℝ) *
        ((∫ v in Ioc (2 * x) (3 * x), h v ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2) +
      (2 / 13 : ℝ) * (∫ u in Ioc (3 * x) (L - 3 * x), h u ^ 2) -
      (4 / 13 : ℝ) *
        ((∫ u in Ioc x (2 * x), h u ^ 2) + ∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2) ≤
      ∫ u in Ioc x (L - 2 * x), (h u - h (u + x)) ^ 2 := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  -- Step 2 (layer-1-to-layer-2 intervals `Ioc x (2 * x)` and `Ioc (L - 3 * x) (L - 2 * x)`)
  have h2_left_pt : ∀ u : ℝ,
      (4 / 17 : ℝ) * h (u + x) ^ 2 - (4 / 13 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := four_seventeenths_sq_sub_four_thirteenths_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h2_left : (4 / 17 : ℝ) * (∫ v in Ioc (2 * x) (3 * x), h v ^ 2) -
      (4 / 13 : ℝ) * (∫ u in Ioc x (2 * x), h u ^ 2) ≤
      ∫ u in Ioc x (2 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc x (2 * x))
      ((hshift.const_mul (4 / 17)).integrableOn.sub (hsq.const_mul (4 / 13)).integrableOn)
      hjump.integrableOn h2_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (4 / 17)).integrableOn (hsq.const_mul (4 / 13)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) x (2 * x) x,
      show x + x = 2 * x by ring, show 2 * x + x = 3 * x by ring] at h1
    linarith
  have h2_right_pt : ∀ u : ℝ,
      (4 / 17 : ℝ) * h u ^ 2 - (4 / 13 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => four_seventeenths_sq_sub_four_thirteenths_sq_le_sub_sq (h u) (h (u + x))
  have h2_right : (4 / 17 : ℝ) * (∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2) -
      (4 / 13 : ℝ) * (∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2) ≤
      ∫ u in Ioc (L - 3 * x) (L - 2 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - 3 * x) (L - 2 * x))
      ((hsq.const_mul (4 / 17)).integrableOn.sub (hshift.const_mul (4 / 13)).integrableOn)
      hjump.integrableOn h2_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (4 / 17)).integrableOn (hshift.const_mul (4 / 13)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - 3 * x) (L - 2 * x) x,
      show L - 3 * x + x = L - 2 * x by ring, show L - 2 * x + x = L - x by ring] at h1
    linarith
  -- Step 3 (double-collar central core intervals `Ioc (2 * x) (L - 4 * x)` and `Ioc (3 * x) (L - 3 * x)`)
  have h3_left_pt : ∀ u : ℝ,
      (1 / 13 : ℝ) * h (u + x) ^ 2 - (1 / 12 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := one_thirteenth_sq_sub_one_twelfth_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h3_left : (1 / 13 : ℝ) * (∫ v in Ioc (3 * x) (L - 3 * x), h v ^ 2) -
      (1 / 12 : ℝ) * (∫ u in Ioc (2 * x) (3 * x), h u ^ 2) ≤
      ∫ u in Ioc (2 * x) (L - 4 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (2 * x) (L - 4 * x))
      ((hshift.const_mul (1 / 13)).integrableOn.sub (hsq.const_mul (1 / 12)).integrableOn)
      hjump.integrableOn h3_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (1 / 13)).integrableOn (hsq.const_mul (1 / 12)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (2 * x) (L - 4 * x) x,
      show 2 * x + x = 3 * x by ring, show L - 4 * x + x = L - 3 * x by ring] at h1
    have hsub_2L : Ioc (2 * x) (L - 4 * x) ⊆ Ioc (2 * x) (3 * x) :=
      Ioc_subset_Ioc_right (by linarith)
    have hmono_2L : (∫ u in Ioc (2 * x) (L - 4 * x), h u ^ 2) ≤ ∫ u in Ioc (2 * x) (3 * x), h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall hsub_2L)
    linarith
  have h3_right_pt : ∀ u : ℝ,
      (1 / 13 : ℝ) * h u ^ 2 - (1 / 12 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => one_thirteenth_sq_sub_one_twelfth_sq_le_sub_sq (h u) (h (u + x))
  have h3_right : (1 / 13 : ℝ) * (∫ u in Ioc (3 * x) (L - 3 * x), h u ^ 2) -
      (1 / 12 : ℝ) * (∫ v in Ioc (L - 3 * x) (L - 2 * x), h v ^ 2) ≤
      ∫ u in Ioc (3 * x) (L - 3 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (3 * x) (L - 3 * x))
      ((hsq.const_mul (1 / 13)).integrableOn.sub (hshift.const_mul (1 / 12)).integrableOn)
      hjump.integrableOn h3_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (1 / 13)).integrableOn (hshift.const_mul (1 / 12)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (3 * x) (L - 3 * x) x,
      show 3 * x + x = 4 * x by ring, show L - 3 * x + x = L - 2 * x by ring] at h1
    have hsub_2R : Ioc (4 * x) (L - 2 * x) ⊆ Ioc (L - 3 * x) (L - 2 * x) :=
      Ioc_subset_Ioc_left (by linarith)
    have hmono_2R : (∫ v in Ioc (4 * x) (L - 2 * x), h v ^ 2) ≤
        ∫ v in Ioc (L - 3 * x) (L - 2 * x), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall hsub_2R)
    linarith
  -- Level 3: `Ioc (2 * x) (L - 4 * x)` and `Ioc (3 * x) (L - 3 * x)` inside `Ioc (2 * x) (L - 3 * x)`
  have hdisj_3 : Disjoint (Ioc (2 * x) (L - 4 * x)) (Ioc (3 * x) (L - 3 * x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hsub_3 : Ioc (2 * x) (L - 4 * x) ∪ Ioc (3 * x) (L - 3 * x) ⊆ Ioc (2 * x) (L - 3 * x) := by
    intro u hu
    rcases hu with hu1 | hu2
    · exact ⟨hu1.1, by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], hu2.2⟩
  have hunion_3 : (∫ u in Ioc (2 * x) (L - 4 * x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (3 * x) (L - 3 * x), (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc (2 * x) (L - 3 * x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj_3 measurableSet_Ioc hjump.integrableOn hjump.integrableOn]
    exact setIntegral_mono_set hjump.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall hsub_3)
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
  linarith

/-- **Disjoint Three-Step Double-Collar Core Transport Bound on `[L / 7, L / 6]`**:
for any `BddSupp A h C` and `x ∈ [L / 7, L / 6]` (`0 ≤ L`), combining Step 1 (`(17 / 37, 17 / 20)`)
on `Ioc 0 x` and `Ioc (L - 2 * x) (L - x)` with `seventh_inner_double_transport_le_setIntegral_Ioc`
yields:
`(73 / 481) * ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2)`
`+ (31 / 204) * ((∫ v in Ioc (2 * x) (3 * x), h v ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2)`
`+ (2 / 13) * (∫ u in Ioc (3 * x) (L - 3 * x), h u ^ 2)`
`- (17 / 20) * collarMass h L x ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`. -/
theorem disjoint_three_step_double_transport_slices_le_interior_jump_sq {A : Set ℝ} {h : ℝ → ℝ}
    {C L x : ℝ} (hh : BddSupp A h C) (hL0 : 0 ≤ L) (hx7 : L / 7 ≤ x) (hx6 : x ≤ L / 6) :
    (73 / 481 : ℝ) *
        ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) +
      (31 / 204 : ℝ) *
        ((∫ v in Ioc (2 * x) (3 * x), h v ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2) +
      (2 / 13 : ℝ) * (∫ u in Ioc (3 * x) (L - 3 * x), h u ^ 2) -
      (17 / 20 : ℝ) * collarMass h L x ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  -- Step 1 (outer collar-to-core intervals `Ioc 0 x` and `Ioc (L - 2x) (L - x)`)
  have h1_left_pt : ∀ u : ℝ,
      (17 / 37 : ℝ) * h (u + x) ^ 2 - (17 / 20 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := seventeen_thirty_sevenths_sq_sub_seventeen_twentieths_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h1_left : (17 / 37 : ℝ) * (∫ v in Ioc x (2 * x), h v ^ 2) -
      (17 / 20 : ℝ) * (∫ u in Iic x, h u ^ 2) ≤
      ∫ u in Ioc 0 x, (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc 0 x)
      ((hshift.const_mul (17 / 37)).integrableOn.sub (hsq.const_mul (17 / 20)).integrableOn)
      hjump.integrableOn h1_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (17 / 37)).integrableOn (hsq.const_mul (17 / 20)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 x x, zero_add,
      show x + x = 2 * x by ring] at h1
    have hIoc_le_Iic : (∫ u in Ioc 0 x, h u ^ 2) ≤ ∫ u in Iic x, h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Iic_self)
    linarith
  have h1_right_pt : ∀ u : ℝ,
      (17 / 37 : ℝ) * h u ^ 2 - (17 / 20 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => seventeen_thirty_sevenths_sq_sub_seventeen_twentieths_sq_le_sub_sq (h u) (h (u + x))
  have h1_right : (17 / 37 : ℝ) * (∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) -
      (17 / 20 : ℝ) * (∫ v in Ioi (L - x), h v ^ 2) ≤
      ∫ u in Ioc (L - 2 * x) (L - x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - 2 * x) (L - x))
      ((hsq.const_mul (17 / 37)).integrableOn.sub (hshift.const_mul (17 / 20)).integrableOn)
      hjump.integrableOn h1_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (17 / 37)).integrableOn (hshift.const_mul (17 / 20)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - 2 * x) (L - x) x,
      show L - 2 * x + x = L - x by ring, show L - x + x = L by ring] at h1
    have hIoc_le_Ioi : (∫ v in Ioc (L - x) L, h v ^ 2) ≤ ∫ v in Ioi (L - x), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Ioi_self)
    linarith
  have hinner := seventh_inner_double_transport_le_setIntegral_Ioc hh hL0 hx7 hx6
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

/-- For any `BddSupp A h C`, the core `Ioc x (L - x)` is covered by the five slices
`Ioc x (2 * x)`, `Ioc (L - 2 * x) (L - x)`, `Ioc (2 * x) (3 * x)`, `Ioc (L - 3 * x) (L - 2 * x)`,
and `Ioc (3 * x) (L - 3 * x)`. -/
theorem coreMass_le_five_layers_seventh {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) :
    coreMass h L x ≤
      ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) +
        ((∫ v in Ioc (2 * x) (3 * x), h v ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2) +
        ∫ u in Ioc (3 * x) (L - 3 * x), h u ^ 2 := by
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
  linarith

/-- **Universal Seventh-Window Coercivity (`(3 / 20) * ∫ h² ≤ D_h(x)` for all `x ≥ L / 7`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and **every shift `x ≥ L / 7`**,
`(3 / 20) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem three_twentieths_mul_integral_sq_le_integral_jump_sq_of_seventh_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 7 ≤ x) :
    (3 / 20 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  rcases le_or_gt x (L / 6) with hle | hgt
  · have hx0 : 0 ≤ x := by linarith
    have hxL2 : x ≤ L / 2 := by linarith
    have hcol_int := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
    have hthree := disjoint_three_step_double_transport_slices_le_interior_jump_sq hh hL0 hx hle
    have hcov := coreMass_le_five_layers_seventh (L := L) (x := x) hh
    have hcons := collarMass_add_coreMass_eq hh hxL2
    have hlay1_nn : 0 ≤ (∫ v in Ioc x (2 * x), h v ^ 2) +
        ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2 :=
      add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    have hlay2_nn : 0 ≤ (∫ v in Ioc (2 * x) (3 * x), h v ^ 2) +
        ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2 :=
      add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    have hlay3_nn : 0 ≤ ∫ u in Ioc (3 * x) (L - 3 * x), h u ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    linarith
  · have h6 := seven_thirty_sixths_mul_integral_sq_le_integral_jump_sq_of_sixth_le
      hh hsupp hL0 hgt.le
    have hE0 : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith

/-- **Universal Seventh-Window Autocorrelation Damping (`2 R(x) ≤ (37 / 20) R(0)` for all `x ≥ L / 7`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and every shift `x ≥ L / 7`,
`2 * autocorr h x ≤ (37 / 20) * ∫ u, h u ^ 2`. -/
theorem two_mul_autocorr_le_thirty_seven_twentieths_mul_integral_sq_of_seventh_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 7 ≤ x) :
    2 * autocorr h x ≤ (37 / 20 : ℝ) * ∫ u, h u ^ 2 := by
  have hid := integral_jump_sq hh x
  have hcoerc := three_twentieths_mul_integral_sq_le_integral_jump_sq_of_seventh_le
    hh hsupp hL0 hx
  linarith

/-! ## Section 2: Seven-Shell Potential Coercivity and Sharpened `(0, log 2)` Plastic Floor -/

/-- Integrating `(3 / 20)` coercivity against `-screwRegularKernel x ≥ 0` over `Ioo a c`
(`L / 7 ≤ a ≤ c ≤ screwSignThreshold`) yields
`(3 / 40) * (Φ(a) - Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo a c} (-screwRegularKernel x) D_h(x) dx`. -/
theorem three_fortieths_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L a c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL : 0 < L) (ha : L / 7 ≤ a) (hac : a ≤ c)
    (hct : c ≤ screwSignThreshold) :
    (3 / 40 : ℝ) * (levyCoshPotential a - levyCoshPotential c) * (∫ u, h u ^ 2) ≤
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
      (fun x : ℝ => (-screwRegularKernel x) * ((3 / 20 : ℝ) * ∫ u, h u ^ 2)) (Ioo a c) :=
    hI_K.mul_const _
  have hmono : (∫ x in Ioo a c, (-screwRegularKernel x) * ((3 / 20 : ℝ) * ∫ u, h u ^ 2)) ≤
      ∫ x in Ioo a c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
    refine setIntegral_mono_on hI_low hI_jump measurableSet_Ioo fun x hx => ?_
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hct))
    exact mul_le_mul_of_nonneg_left
      (three_twentieths_mul_integral_sq_le_integral_jump_sq_of_seventh_le hh hsupp hL.le
        (ha.trans hx.1.le))
      hK0
  rw [integral_mul_const, setIntegral_Ioo_neg_screwRegularKernel ha0 hac] at hmono
  linarith

/-- **Three-Shell `(L / 10, L / 8) ∪ (L / 8, L / 7) ∪ (L / 7, L / 6)` Jump-Integral Coercivity**:
for `L / 6 ≤ screwSignThreshold`,
`((1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) - (3 / 40) * Φ(L / 6)) * ∫ h²`
`≤ ∫ x in Ioo (L / 10) (L / 6), (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem tenth_add_eighth_add_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL0 : 0 < L) (hL6t : L / 6 ≤ screwSignThreshold) :
    ((1 / 25 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (3 / 200 : ℝ) * levyCoshPotential (L / 7) -
        (3 / 40 : ℝ) * levyCoshPotential (L / 6)) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 10) (L / 6), (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL10_pos : 0 < L / 10 := by linarith
  have hL10_8 : L / 10 ≤ L / 8 := by linarith
  have hL8_7 : L / 8 ≤ L / 7 := by linarith
  have hL7_6 : L / 7 ≤ L / 6 := by linarith
  have hL8_6 : L / 8 ≤ L / 6 := by linarith
  have hL7t : L / 7 ≤ screwSignThreshold := le_trans hL7_6 hL6t
  have hL8t : L / 8 ≤ screwSignThreshold := le_trans hL8_6 hL6t
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 10) (L / 6)) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL10_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 10) (L / 6)) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL10_pos hx.1) (hx.2.le.trans hL6t))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_1_Ioc : IntegrableOn F (Ioc (L / 10) (L / 8)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL8_6)
  have hIF_2_Ioc : IntegrableOn F (Ioc (L / 8) (L / 7)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL10_8 hL7_6)
  have hIF_3_Ioc : IntegrableOn F (Ioc (L / 7) (L / 6)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo (hL10_8.trans hL8_7) le_rfl)
  have hIF_12_Ioc : IntegrableOn F (Ioc (L / 10) (L / 7)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL7_6)
  have hdisj_12 : Disjoint (Ioc (L / 10) (L / 8)) (Ioc (L / 8) (L / 7)) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_123 : Disjoint (Ioc (L / 10) (L / 7)) (Ioc (L / 7) (L / 6)) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 10) (L / 6), F x) =
      (∫ x in Ioo (L / 10) (L / 8), F x) + (∫ x in Ioo (L / 8) (L / 7), F x) +
        ∫ x in Ioo (L / 7) (L / 6), F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (hL10_8.trans hL8_7) hL7_6,
      setIntegral_union hdisj_123 measurableSet_Ioc hIF_12_Ioc hIF_3_Ioc,
      ← Ioc_union_Ioc_eq_Ioc hL10_8 hL8_7,
      setIntegral_union hdisj_12 measurableSet_Ioc hIF_1_Ioc hIF_2_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h10 := one_twenty_fifth_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL10_8 hL8t
  have h8 := three_fiftieths_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL8_7 hL7t
  have h7 := three_fortieths_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL7_6 hL6t
  dsimp only [F] at hsplit
  linarith

/-- **Five-Shell `(L / 10, L / 8) ∪ (L / 8, L / 7) ∪ (L / 7, L / 6) ∪ (L / 6, L / 5) ∪ (L / 5, b)` Jump Coercivity**:
for `L / 5 ≤ b ≤ screwSignThreshold`,
`((1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) - (2 / 15) * Φ(b)) * ∫ h²`
`≤ ∫ x in Ioo (L / 10) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem tenth_to_fifth_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL0 : 0 < L) (hL5b : L / 5 ≤ b)
    (hbt : b ≤ screwSignThreshold) :
    ((1 / 25 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (3 / 200 : ℝ) * levyCoshPotential (L / 7) +
        (1 / 45 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) -
        (2 / 15 : ℝ) * levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 10) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL10_pos : 0 < L / 10 := by linarith
  have hL10_6 : L / 10 ≤ L / 6 := by linarith
  have hL6_b : L / 6 ≤ b := by linarith
  have hL6t : L / 6 ≤ screwSignThreshold := le_trans hL6_b hbt
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 10) b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL10_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 10) b) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL10_pos hx.1) (hx.2.le.trans hbt))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_left_Ioc : IntegrableOn F (Ioc (L / 10) (L / 6)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL6_b)
  have hIF_right_Ioc : IntegrableOn F (Ioc (L / 6) b) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL10_6 le_rfl)
  have hdisj : Disjoint (Ioc (L / 10) (L / 6)) (Ioc (L / 6) b) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 10) b, F x) =
      (∫ x in Ioo (L / 10) (L / 6), F x) + ∫ x in Ioo (L / 6) b, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL10_6 hL6_b,
      setIntegral_union hdisj measurableSet_Ioc hIF_left_Ioc hIF_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h1087 := tenth_add_eighth_add_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL6t
  have h65 := sixth_add_fifth_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL5b hbt
  dsimp only [F] at hsplit
  linarith

/-- **Seven-Shell `(L / 10, L / 8, L / 7, L / 6, L / 5, L / 4, L / 3, c)` Jump Coercivity**:
for `L / 3 ≤ c ≤ screwSignThreshold`,
`((1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) - (12 / 41) * Φ(c)) * ∫ h²`
`≤ ∫ x in Ioo (L / 10) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem tenth_to_third_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL0 : 0 < L) (hL3c : L / 3 ≤ c)
    (hct : c ≤ screwSignThreshold) :
    ((1 / 25 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (3 / 200 : ℝ) * levyCoshPotential (L / 7) +
        (1 / 45 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (2 / 35 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) -
        (12 / 41 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 10) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL10_pos : 0 < L / 10 := by linarith
  have hL10_4 : L / 10 ≤ L / 4 := by linarith
  have hL5_4 : L / 5 ≤ L / 4 := by linarith
  have hL4_3 : L / 4 ≤ L / 3 := by linarith
  have hL4_c : L / 4 ≤ c := by linarith
  have hL4_t : L / 4 ≤ screwSignThreshold := le_trans hL4_c hct
  have hL3_t : L / 3 ≤ screwSignThreshold := le_trans hL3c hct
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
  have hIF_1_Ioc : IntegrableOn F (Ioc (L / 10) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL4_c)
  have hIF_2_Ioc : IntegrableOn F (Ioc (L / 4) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL10_4 hL3c)
  have hIF_3_Ioc : IntegrableOn F (Ioc (L / 3) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo (hL10_4.trans hL4_3) le_rfl)
  have hIF_12_Ioc : IntegrableOn F (Ioc (L / 10) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL3c)
  have hdisj_12 : Disjoint (Ioc (L / 10) (L / 4)) (Ioc (L / 4) (L / 3)) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_123 : Disjoint (Ioc (L / 10) (L / 3)) (Ioc (L / 3) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 10) c, F x) =
      (∫ x in Ioo (L / 10) (L / 4), F x) + (∫ x in Ioo (L / 4) (L / 3), F x) +
        ∫ x in Ioo (L / 3) c, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (hL10_4.trans hL4_3) hL3c,
      setIntegral_union hdisj_123 measurableSet_Ioc hIF_12_Ioc hIF_3_Ioc,
      ← Ioc_union_Ioc_eq_Ioc hL10_4 hL4_3,
      setIntegral_union hdisj_12 measurableSet_Ioc hIF_1_Ioc hIF_2_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h105 := tenth_to_fifth_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL5_4 hL4_t
  have h4 := four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL4_3 hL3_t
  have h3 := twelve_forty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL3c hct
  dsimp only [F] at hsplit
  linarith

/-- **Seven-Shell `(L / 10, L / 8, L / 7, L / 6, L / 5, L / 4, L / 3, c)` Lévy–Cosh Crossover Inequality**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and any `c` with
`L / 3 ≤ c ≤ screwSignThreshold`,
`(A(0) + (1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (29 / 41) * Φ(c)) * ∫ f²`
`+ ∫∫ f(u)f(v)(2 cosh((u-v)/2) - K_c(|u-v|)) ≤ W_∞(f ⋆ f̃)`. -/
theorem tenth_to_third_with_seventh_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L)
    (hL3c : L / 3 ≤ c) (hct : c ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (3 / 200) * levyCoshPotential (L / 7) +
        (1 / 45) * levyCoshPotential (L / 6) +
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
  have hsub := tenth_to_third_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL hL3c hct
  linarith

/-- **Sharpened `(0, log 2)` Plastic-Floor Theorem with Seventh-Window Double Transport**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 (log 2)`, the universal constant floor is
boosted to `A(0) + (1 / 25) * Φ((log 2)/10) + (1 / 50) * Φ((log 2)/8) + (3 / 200) * Φ((log 2)/7) + (1 / 45) * Φ((log 2)/6) + (13 / 360) * Φ((log 2)/5) + (2 / 35) * Φ((log 2)/4) + (88 / 861) * Φ((log 2)/3) + (29 / 41) * Φ(screwSignThreshold)`
(reducing the universal constant deficit on `(0, log 2)` from `-0.0156` down to **`-0.0138`**). -/
theorem seventh_window_log_two_plastic_floor_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hsupp : ∀ u ∉ Ioo 0 (Real.log 2), f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (Real.log 2 / 10) +
        (1 / 50) * levyCoshPotential (Real.log 2 / 8) +
        (3 / 200) * levyCoshPotential (Real.log 2 / 7) +
        (1 / 45) * levyCoshPotential (Real.log 2 / 6) +
        (13 / 360) * levyCoshPotential (Real.log 2 / 5) +
        (2 / 35) * levyCoshPotential (Real.log 2 / 4) +
        (88 / 861) * levyCoshPotential (Real.log 2 / 3) +
        (29 / 41) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 / 3 ≤ screwSignThreshold := by
    linarith [Real.log_two_lt_d9, screwSignThreshold_gt_6036_over_21509]
  have hmain := tenth_to_third_with_seventh_levyCosh_crossover_le_weilArchRe
    hf hfc hlog2 hlt le_rfl hsupp
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-! ## Section 3: Inner-Reflected Nine-Point Potential (`L / 2 ≤ c ≤ 2 * L / 3`) and Unconditional Positivity on `(0, 19 / 45)` (`60.91%` of `(0, log 2)`) -/

/-- **Inner-Reflected Nine-Point Shell Jump-Integral Coercivity on `Ioo (L / 10) c` (`L / 2 ≤ c ≤ 2 * L / 3`)**:
combining `tenth_to_fifth_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo` on `(L / 10, L / 4)`,
`four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo` on `(L / 4, L / 3)`, and
`third_window_inner_shell_sub_levyCoshPotential_le_setIntegral_Ioo` on `(L / 3, c)` yields:
`((1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) - (29 / 41) * Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo (L / 10) c} (-screwRegularKernel x) D_h(x) dx`. -/
theorem inner_reflected_nine_point_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (hL2c : L / 2 ≤ c)
    (hc23 : c ≤ 2 * L / 3) (hct : c ≤ screwSignThreshold) :
    ((1 / 25 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (3 / 200 : ℝ) * levyCoshPotential (L / 7) +
        (1 / 45 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (2 / 35 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 41 : ℝ) * levyCoshPotential (L / 2) -
        (29 / 41 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 10) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL10_pos : 0 < L / 10 := by linarith
  have hL10_4 : L / 10 ≤ L / 4 := by linarith
  have hL5_4 : L / 5 ≤ L / 4 := by linarith
  have hL4_3 : L / 4 ≤ L / 3 := by linarith
  have hL3c : L / 3 ≤ c := by linarith
  have hL4_c : L / 4 ≤ c := by linarith
  have hL4_t : L / 4 ≤ screwSignThreshold := le_trans hL4_c hct
  have hL3_t : L / 3 ≤ screwSignThreshold := le_trans hL3c hct
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
  have hIF_1_Ioc : IntegrableOn F (Ioc (L / 10) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL4_c)
  have hIF_2_Ioc : IntegrableOn F (Ioc (L / 4) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL10_4 hL3c)
  have hIF_3_Ioc : IntegrableOn F (Ioc (L / 3) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo (hL10_4.trans hL4_3) le_rfl)
  have hIF_12_Ioc : IntegrableOn F (Ioc (L / 10) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL3c)
  have hdisj_12 : Disjoint (Ioc (L / 10) (L / 4)) (Ioc (L / 4) (L / 3)) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_123 : Disjoint (Ioc (L / 10) (L / 3)) (Ioc (L / 3) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 10) c, F x) =
      (∫ x in Ioo (L / 10) (L / 4), F x) + (∫ x in Ioo (L / 4) (L / 3), F x) +
        ∫ x in Ioo (L / 3) c, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (hL10_4.trans hL4_3) hL3c,
      setIntegral_union hdisj_123 measurableSet_Ioc hIF_12_Ioc hIF_3_Ioc,
      ← Ioc_union_Ioc_eq_Ioc hL10_4 hL4_3,
      setIntegral_union hdisj_12 measurableSet_Ioc hIF_1_Ioc hIF_2_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h105 := tenth_to_fifth_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL hL5_4 hL4_t
  have h4 := four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL le_rfl hL4_3 hL3_t
  have h3 := third_window_inner_shell_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL hL2c hc23 hct
  dsimp only [F] at hsplit
  linarith

/-- **Inner-Reflected Nine-Point Lévy–Cosh Crossover Inequality on `(0, L)` (`L / 2 ≤ c ≤ 2 * L / 3`)**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`),
`(A(0) + (1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (12 / 41) * Φ(c)) * ∫ f² + ... ≤ W_∞(f ⋆ f̃)`. -/
theorem inner_reflected_nine_point_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L)
    (hL2c : L / 2 ≤ c) (hc23 : c ≤ 2 * L / 3) (hct : c ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (3 / 200) * levyCoshPotential (L / 7) +
        (1 / 45) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (17 / 41) * levyCoshPotential (L / 2) +
        (12 / 41) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL10 : 0 < L / 10 := by linarith
  have hL10c : L / 10 ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL10 hL10c hct
  have hnine := inner_reflected_nine_point_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL hL2c hc23 hct
  linarith

/-- **Osculating Lower Bound for the Inner-Reflected Nine-Point Potential (`L > 0`, `c > 0`)**:
for every `L > 0` and `c > 0`,
`log(1 / (π * L)) + (7 / 72) * log 2 + (1931 / 12600) * log(4 / 3) + (137 / 1800) * log(5 / 4) + (3 / 200) * log(7 / 6) + (12 / 41) * log((21 / 8) * L) + (4265677 / 4428000) * L + 12 / 41 - γ`
`≤ EF.gammaBracket 0 + (1 / 25) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (12 / 41) * Φ(c)`. -/
theorem osculating_le_inner_reflected_nine_point_potential {L c : ℝ} (hL : 0 < L) (hc0 : 0 < c) :
    Real.log (1 / (Real.pi * L)) + (7 / 72 : ℝ) * Real.log 2 +
        (1931 / 12600 : ℝ) * Real.log (4 / 3) +
        (137 / 1800 : ℝ) * Real.log (5 / 4) +
        (3 / 200 : ℝ) * Real.log (7 / 6) +
        (12 / 41 : ℝ) * Real.log ((21 / 8 : ℝ) * L) +
        (4265677 / 4428000 : ℝ) * L + 12 / 41 - eulerMascheroniConstant ≤
      EF.gammaBracket 0 + (1 / 25) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (3 / 200) * levyCoshPotential (L / 7) +
        (1 / 45) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (17 / 41) * levyCoshPotential (L / 2) +
        (12 / 41) * levyCoshPotential c := by
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
  have h2 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 2)
  have hc := log_seven_div_four_pi_add_one_le_gammaBracket_add_levyCoshPotential hc0
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
  have hlog2_pt : Real.log (1 / (2 * Real.pi * (L / 2))) =
      Real.log (1 / (Real.pi * L)) := by
    congr 1; field_simp
  have hlogc_pt : Real.log (7 / (4 * Real.pi)) =
      Real.log (1 / (Real.pi * L)) + Real.log (4 / 3) - Real.log 2 +
        Real.log ((21 / 8 : ℝ) * L) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_div (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  linarith

/-- Exact 5-smooth identity `Real.log 5 - 2 * Real.log 2 = Real.log (5 / 4)`. -/
theorem log_five_sub_two_mul_log_two_eq_log_five_fourths :
    Real.log 5 - 2 * Real.log 2 = Real.log (5 / 4) := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  rw [Real.log_div (by norm_num) (by norm_num), hlog4]

/-- Sharpened 5-smooth lower bound `Real.log 5 - 2 * Real.log 2 + 2 / 31 < Real.log (4 / 3)`
via `4 / 3 = (5 / 4) * (16 / 15)` and `Real.lt_log_one_add_of_pos` at `1 / 15`. -/
theorem log_five_sub_two_mul_log_two_add_two_thirty_firsts_lt_log_four_thirds :
    Real.log 5 - 2 * Real.log 2 + 2 / 31 < Real.log (4 / 3) := by
  have h16_15 : (2 : ℝ) / 31 < Real.log (16 / 15) := by
    have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 15)
    norm_num at h ⊢
    exact h
  have hsplit : Real.log (4 / 3 : ℝ) = Real.log (5 / 4) + Real.log (16 / 15) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  linarith [log_five_sub_two_mul_log_two_eq_log_five_fourths]

/-- Rational lower bound `2 / 13 < Real.log (7 / 6)` via `Real.lt_log_one_add_of_pos` at `1 / 6`. -/
theorem two_thirteenths_lt_log_seven_sixths :
    (2 : ℝ) / 13 < Real.log (7 / 6) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 6)
  norm_num at h ⊢
  exact h

/-- Rational lower bound `26 / 253 < Real.log (133 / 120)` via `Real.lt_log_one_add_of_pos` at `13 / 120`. -/
theorem twenty_six_two_hundred_fifty_thirds_lt_log_133_120 :
    (26 : ℝ) / 253 < Real.log (133 / 120) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 13 / 120)
  norm_num at h ⊢
  exact h

/-- Tightened upper rational enclosure `screwSignThreshold < 38 / 135` (`t_* < 0.281481`),
proved from `exp_half_screwSignThreshold_lt` (`exp(t_* / 2) < 1151 / 1000`) via the inverse
5-smooth factorization `5 / 4 = (1151 / 1000) * (1250 / 1151)` and `Real.lt_log_one_add_of_pos`
at `99 / 1151`. -/
theorem screwSignThreshold_lt_thirty_eight_over_one_thirty_five :
    screwSignThreshold < (38 : ℝ) / 135 := by
  have hexp := exp_half_screwSignThreshold_lt
  have hlog := Real.log_lt_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  have hfac : Real.log (5 / 4 : ℝ) = Real.log (1151 / 1000) + Real.log (1250 / 1151) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hpade : (198 : ℝ) / 2401 < Real.log (1250 / 1151) := by
    have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 99 / 1151)
    norm_num at h ⊢
    exact h
  have hlog54 := log_five_sub_two_mul_log_two_eq_log_five_fourths
  have hlog5_lt := Real.log_five_lt_d9
  have hlog2_gt := Real.log_two_gt_d9
  linarith

/-- Lower bound on `log(1 / (π * (19 / 45)))` via the factorization
`1 / (π * (19 / 45)) = (4 / 3) * (675 / 608) / (2 * (5 * π / 16))` and `Real.lt_log_one_add_of_pos`
at `67 / 608`:
`Real.log (4 / 3) - Real.log 2 + 1417 / 1283 - 5 * Real.pi / 16 ≤ Real.log (1 / (Real.pi * (19 / 45)))`. -/
theorem log_inv_pi_mul_nineteen_forty_fifths_ge :
    Real.log (4 / 3) - Real.log 2 + 1417 / 1283 - 5 * Real.pi / 16 ≤
      Real.log (1 / (Real.pi * (19 / 45))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsplit : Real.log (1 / (Real.pi * (19 / 45))) + Real.log 2 + Real.log (5 * Real.pi / 16) =
      Real.log (4 / 3) + Real.log (675 / 608) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hpade : (134 : ℝ) / 1283 < Real.log (675 / 608) := by
    have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 67 / 608)
    norm_num at h ⊢
    exact h
  have hpi_log : Real.log (5 * Real.pi / 16) ≤ 5 * Real.pi / 16 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  linarith

/-- **Strict Positivity of the Inner-Reflected Nine-Point Potential at `L = 19 / 45` (`≈ 0.422222`, `60.91%` of `(0, log 2)`)**:
`0 ≤ EF.gammaBracket 0 + (1 / 25) * Φ((19/45)/10) + (1 / 50) * Φ((19/45)/8) + (3 / 200) * Φ((19/45)/7) + (1 / 45) * Φ((19/45)/6) + (13 / 360) * Φ((19/45)/5) + (2 / 35) * Φ((19/45)/4) + (88 / 861) * Φ((19/45)/3) + (17 / 41) * Φ((19/45)/2) + (12 / 41) * Φ(screwSignThreshold)`. -/
theorem zero_le_inner_reflected_nine_point_potential_nineteen_forty_fifths :
    0 ≤ EF.gammaBracket 0 + (1 / 25) * levyCoshPotential ((19 / 45 : ℝ) / 10) +
        (1 / 50) * levyCoshPotential ((19 / 45 : ℝ) / 8) +
        (3 / 200) * levyCoshPotential ((19 / 45 : ℝ) / 7) +
        (1 / 45) * levyCoshPotential ((19 / 45 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((19 / 45 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((19 / 45 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((19 / 45 : ℝ) / 3) +
        (17 / 41) * levyCoshPotential ((19 / 45 : ℝ) / 2) +
        (12 / 41) * levyCoshPotential screwSignThreshold := by
  have hosc := osculating_le_inner_reflected_nine_point_potential
    (by norm_num : (0 : ℝ) < 19 / 45) screwSignThreshold_pos
  rw [show (21 / 8 : ℝ) * (19 / 45) = 133 / 120 by norm_num] at hosc
  have hlog_pi := log_inv_pi_mul_nineteen_forty_fifths_ge
  have hlog2_lt := Real.log_two_lt_d9
  have hlog2_gt := Real.log_two_gt_d9
  have hlog5 := Real.log_five_gt_d9
  have hlog54 := log_five_sub_two_mul_log_two_eq_log_five_fourths
  have hlog43 := log_five_sub_two_mul_log_two_add_two_thirty_firsts_lt_log_four_thirds
  have hlog76 := two_thirteenths_lt_log_seven_sixths
  have hlog133 := twenty_six_two_hundred_fifty_thirds_lt_log_133_120
  have hpi := Real.pi_lt_d4
  have hgamma :=
    RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith

/-- **Unconditional Archimedean Weil Positivity on `(0, 19 / 45)` (`≈ (0, 0.422222)`, `60.91%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` supported in `Ioo 0 L` with `L ≤ 19 / 45`,
`0 ≤ WeilOneSided.weilArchRe (EF.weilTest f f)`. -/
theorem weilArchRe_nonneg_of_support_Ioo_le_nineteen_forty_fifths {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL : L ≤ 19 / 45) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_19_45 : ∀ u ∉ Ioo (0 : ℝ) (19 / 45), f u = 0 :=
    fun u hu => hsupp u fun huL => hu ⟨huL.1, huL.2.trans_le hL⟩
  have hmain := inner_reflected_nine_point_levyCosh_crossover_le_weilArchRe
    hf hfc (by norm_num : (0 : ℝ) < 19 / 45)
    (by linarith [screwSignThreshold_gt_6036_over_21509])
    (by linarith [screwSignThreshold_lt_thirty_eight_over_one_thirty_five])
    le_rfl hsupp_19_45
  have hpot := zero_le_inner_reflected_nine_point_potential_nineteen_forty_fifths
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hterm1 : 0 ≤ (EF.gammaBracket 0 + (1 / 25) * levyCoshPotential ((19 / 45 : ℝ) / 10) +
        (1 / 50) * levyCoshPotential ((19 / 45 : ℝ) / 8) +
        (3 / 200) * levyCoshPotential ((19 / 45 : ℝ) / 7) +
        (1 / 45) * levyCoshPotential ((19 / 45 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((19 / 45 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((19 / 45 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((19 / 45 : ℝ) / 3) +
        (17 / 41) * levyCoshPotential ((19 / 45 : ℝ) / 2) +
        (12 / 41) * levyCoshPotential screwSignThreshold) * ∫ u, f u ^ 2 :=
    mul_nonneg hpot hsq
  have hpair : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-- **Unconditional `WindowPositive` on `(0, 19 / 45)` (`≈ (0, 0.422222)`, `60.91%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (19 / 45)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_nineteen_forty_fifths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (19 / 45)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_nineteen_forty_fifths hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 27 / 64)` (`≈ (0, 0.421875)`, `60.86%` of `(0, log 2)`)**:
immediate corollary since `27 / 64 ≤ 19 / 45` (`1215 ≤ 1216`). -/
theorem windowPositive_twenty_seven_sixty_fourths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (27 / 64)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_nineteen_forty_fifths hf hfc hf0 (by norm_num : (27 : ℝ) / 64 ≤ 19 / 45)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 8 / 19)` (`≈ (0, 0.421053)`, `60.75%` of `(0, log 2)`)**:
immediate corollary since `8 / 19 ≤ 19 / 45` (`360 ≤ 361`). -/
theorem windowPositive_eight_nineteenths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (8 / 19)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_nineteen_forty_fifths hf hfc hf0 (by norm_num : (8 : ℝ) / 19 ≤ 19 / 45)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 29 / 69)` (`≈ (0, 0.420290)`, `60.64%` of `(0, log 2)`)**:
immediate corollary since `29 / 69 ≤ 19 / 45`. -/
theorem windowPositive_twenty_nine_sixty_ninths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (29 / 69)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_nineteen_forty_fifths hf hfc hf0 (by norm_num : (29 : ℝ) / 69 ≤ 19 / 45)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

end

end RHTower.WeilLevySeventhWindow
