import GaloisForLFunctions.RHTower.WeilLevyFibonacciStaircaseCoercivity

/-!
# Eighth-Window Disjoint Three-Step Staircase Coercivity and Unconditional Positivity on `(0, 8 / 21)`

This module implements **Cycle 71** of the prime-blind archimedean Weil positivity programme,
extending the disjoint midpoint-split staircase from `[L / 6, L / 4]` (`Cycle 70`) by a third
interior layer to `[L / 8, L / 6]` and pushing unconditional `WindowPositive` from `(0, 9 / 25)`
(`= (0, 0.36)`, `51.94%` of `(0, log 2)`) to the exact Fibonacci ratio **`(0, 8 / 21)`**
(`≈ (0, 0.380952)`, **`54.96%` of `(0, log 2)`**), which also covers `(0, 3 / 8)` (`= (0, 0.375)`)
and `(0, 19 / 50)` (`= (0, 0.38)`).

## Mathematical Architecture

1. **Section 1 — Disjoint Three-Step Midpoint-Split Coercivity on `[L / 8, L / 6]` (`D_h(x) ≥ (3 / 25) ∫ h²`)**:
   - We prove the three exact single-square transport inequalities:
     $$(p - q)^2 - \left(\frac{22}{47} p^2 - \frac{22}{25} q^2\right) = \frac{25}{47}\left(p - \frac{47}{25} q\right)^2 \ge 0,$$
     $$(p - q)^2 - \left(\frac{8}{31} p^2 - \frac{8}{23} q^2\right) = \frac{23}{31}\left(p - \frac{31}{23} q\right)^2 \ge 0,$$
     $$(p - q)^2 - \left(\frac{3}{25} p^2 - \frac{3}{22} q^2\right) = \frac{22}{25}\left(p - \frac{25}{22} q\right)^2 \ge 0.$$
   - For $x \in [L / 8, L / 6]$, splitting the third interior layer $\mathrm{Ioc}\,(3x)\,(L - 3x)$ at the
     midpoint $L / 2$ makes all six shift intervals
     $$\mathrm{Ioc}\,0\,x,\ \mathrm{Ioc}\,x\,(2x),\ \mathrm{Ioc}\,(2x)\,(L/2 - x),\
       \mathrm{Ioc}\,(L/2)\,(L - 3x),\ \mathrm{Ioc}\,(L - 3x)\,(L - 2x),\ \mathrm{Ioc}\,(L - 2x)\,(L - x)$$
     **pairwise disjoint** inside $\mathrm{Ioc}\,0\,(L - x)$.
   - Since $1 - \frac{22}{25} = \frac{3}{25}$, $\frac{22}{47} - \frac{8}{23} = \frac{130}{1081} \ge \frac{3}{25}$,
     and $\frac{8}{31} - \frac{3}{22} = \frac{83}{682} \ge \frac{3}{25}$, combining the six disjoint jump
     integrals with collar-escape yields:
     $$\frac{3}{25}\int_{\mathbb R} h(u)^2\,du \le \int_{\mathbb R} (h(u) - h(u + x))^2\,du
       \qquad \forall x \ge \frac{L}{8}$$
     (a $+125\%$ improvement over the unoptimized $1 / 16$ three-step bound, within $0.00062$ of the
     theoretical spectral limit $4 \sin^2(\pi / 18) \approx 0.120615$).

2. **Section 2 — Eighth-Window Potential Coercivity and Universal `(0, log 2)` Plastic Floor**:
   - Integrating the $3 / 25$ coercivity on $(L / 8, L / 6)$, the $7 / 36$ coercivity on $(L / 6, L / 4)$,
     and the $8 / 21$ coercivity on $(L / 4, c)$ yields the four-shell Lévy–cosh crossover bound:
     $$\left(A(0) + \frac{3}{50}\Phi(L / 8) + \frac{67}{1800}\Phi(L / 6)
       + \frac{47}{504}\Phi(L / 4) + \frac{17}{21}\Phi(c)\right)\int_{\mathbb R} f^2
       + \mathrm{pair}_c(f) \le W_\infty(f \star \tilde f),$$
     reducing the universal `(0, log 2)` constant deficit from `-0.0525` (`Cycle 70`) to **`-0.0413`**.

3. **Section 3 — Eighth-Window Five-Point Reflected Potential and Unconditional Positivity on `(0, 8 / 21)`**:
   - Combining `(L / 8, L / 6)` and `(L / 6, L / 4)` with the inner reflected shell `(L / 4, c)`
     (`L / 2 ≤ c ≤ 3 L / 4`) yields the five-point potential floor with weights
     $(3 / 50,\ 67 / 1800,\ 47 / 504,\ 13 / 21,\ 4 / 21)$ at $(L / 8,\ L / 6,\ L / 4,\ L / 2,\ c)$.
   - Since the osculating lower bound $F_{\mathrm{osc}}(t) = \log(1 / (2\pi t)) + (7 / 2) t - \gamma$
     attains its global minimum at $t = 2 / 7$ (`= 3 * (8 / 21) / 4` at the Fibonacci ratio $L = 8 / 21$!)
     and is strictly decreasing on $(0, 2 / 7]$, we have $F_{\mathrm{osc}}(3 L / 4) \le F_{\mathrm{osc}}(c)$
     for every $0 < c \le 3 L / 4 \le 2 / 7$ with **zero linear penalty**.
   - At $L = 8 / 21$ and $c = 7 / 25 = 0.28 < t_*$, the five-point potential is strictly positive
     (`+0.004598 > 0`), proving unconditional `WindowPositive (8 / 21)` (`54.96%` of `(0, log 2)`),
     as well as `WindowPositive (3 / 8)` and `WindowPositive (19 / 50)`.
-/

open Complex Real Set MeasureTheory Filter
open scoped Topology
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyEighthWindow

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor
open RHTower.WeilLevyQuarterWindow RHTower.WeilLevySymmetricThreePoint
open RHTower.WeilLevySixthWindow RHTower.WeilLevyFibonacciStaircase

/-! ## Section 1: Disjoint Three-Step Midpoint-Split Coercivity on `[L / 8, L / 6]` (`D_h(x) ≥ (3 / 25) ∫ h²`) -/

/-- Exact step-1 SOS inequality (`(22 / 47, 22 / 25)`): for all `p, q : ℝ`,
`(22 / 47) * p ^ 2 - (22 / 25) * q ^ 2 ≤ (p - q) ^ 2`, proved via the exact single-square identity
`(p - q) ^ 2 - ((22 / 47) * p ^ 2 - (22 / 25) * q ^ 2) = (25 / 47) * (p - (47 / 25) * q) ^ 2 ≥ 0`. -/
theorem twenty_two_forty_sevenths_sq_sub_twenty_two_twenty_fifths_sq_le_sub_sq (p q : ℝ) :
    (22 / 47 : ℝ) * p ^ 2 - (22 / 25 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  nlinarith [sq_nonneg (p - (47 / 25 : ℝ) * q)]

/-- Exact step-2 SOS inequality (`(8 / 31, 8 / 23)`): for all `p, q : ℝ`,
`(8 / 31) * p ^ 2 - (8 / 23) * q ^ 2 ≤ (p - q) ^ 2`, proved via the exact single-square identity
`(p - q) ^ 2 - ((8 / 31) * p ^ 2 - (8 / 23) * q ^ 2) = (23 / 31) * (p - (31 / 23) * q) ^ 2 ≥ 0`. -/
theorem eight_thirty_firsts_sq_sub_eight_twenty_thirds_sq_le_sub_sq (p q : ℝ) :
    (8 / 31 : ℝ) * p ^ 2 - (8 / 23 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  nlinarith [sq_nonneg (p - (31 / 23 : ℝ) * q)]

/-- Exact step-3 SOS inequality (`(3 / 25, 3 / 22)`): for all `p, q : ℝ`,
`(3 / 25) * p ^ 2 - (3 / 22) * q ^ 2 ≤ (p - q) ^ 2`, proved via the exact single-square identity
`(p - q) ^ 2 - ((3 / 25) * p ^ 2 - (3 / 22) * q ^ 2) = (22 / 25) * (p - (25 / 22) * q) ^ 2 ≥ 0`. -/
theorem three_twenty_fifths_sq_sub_three_twenty_seconds_sq_le_sub_sq (p q : ℝ) :
    (3 / 25 : ℝ) * p ^ 2 - (3 / 22 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  nlinarith [sq_nonneg (p - (25 / 22 : ℝ) * q)]

/-- **Disjoint Three-Step Midpoint-Split Interior Jump Bound on `[L / 8, L / 6]`**:
for any `BddSupp A h C` and `x ∈ [L / 8, L / 6]` (`0 ≤ L`), the six shift intervals
`Ioc 0 x`, `Ioc x (2 * x)`, `Ioc (2 * x) (L / 2 - x)`, `Ioc (L / 2) (L - 3 * x)`,
`Ioc (L - 3 * x) (L - 2 * x)`, and `Ioc (L - 2 * x) (L - x)` are pairwise disjoint inside
`Ioc 0 (L - x)`, yielding:
`(130 / 1081) * ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2)`
`+ (83 / 682) * ((∫ v in Ioc (2 * x) (3 * x), h v ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2)`
`+ (3 / 25) * ((∫ v in Ioc (3 * x) (L / 2), h v ^ 2) + ∫ u in Ioc (L / 2) (L - 3 * x), h u ^ 2)`
`- (22 / 25) * collarMass h L x ≤ ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2`. -/
theorem disjoint_three_step_slices_le_interior_jump_sq {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hL0 : 0 ≤ L) (hx8 : L / 8 ≤ x) (hx6 : x ≤ L / 6) :
    (130 / 1081 : ℝ) *
        ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) +
      (83 / 682 : ℝ) *
        ((∫ v in Ioc (2 * x) (3 * x), h v ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2) +
      (3 / 25 : ℝ) *
        ((∫ v in Ioc (3 * x) (L / 2), h v ^ 2) + ∫ u in Ioc (L / 2) (L - 3 * x), h u ^ 2) -
      (22 / 25 : ℝ) * collarMass h L x ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hshift : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hshift).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  -- Step 1 (outer collar-to-core intervals `Ioc 0 x` and `Ioc (L - 2x) (L - x)`)
  have h1_left_pt : ∀ u : ℝ,
      (22 / 47 : ℝ) * h (u + x) ^ 2 - (22 / 25 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := twenty_two_forty_sevenths_sq_sub_twenty_two_twenty_fifths_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h1_left : (22 / 47 : ℝ) * (∫ v in Ioc x (2 * x), h v ^ 2) -
      (22 / 25 : ℝ) * (∫ u in Iic x, h u ^ 2) ≤
      ∫ u in Ioc 0 x, (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc 0 x)
      ((hshift.const_mul (22 / 47)).integrableOn.sub (hsq.const_mul (22 / 25)).integrableOn)
      hjump.integrableOn h1_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (22 / 47)).integrableOn (hsq.const_mul (22 / 25)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 x x, zero_add,
      show x + x = 2 * x by ring] at h1
    have hIoc_le_Iic : (∫ u in Ioc 0 x, h u ^ 2) ≤ ∫ u in Iic x, h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Iic_self)
    linarith
  have h1_right_pt : ∀ u : ℝ,
      (22 / 47 : ℝ) * h u ^ 2 - (22 / 25 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => twenty_two_forty_sevenths_sq_sub_twenty_two_twenty_fifths_sq_le_sub_sq (h u) (h (u + x))
  have h1_right : (22 / 47 : ℝ) * (∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) -
      (22 / 25 : ℝ) * (∫ v in Ioi (L - x), h v ^ 2) ≤
      ∫ u in Ioc (L - 2 * x) (L - x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - 2 * x) (L - x))
      ((hsq.const_mul (22 / 47)).integrableOn.sub (hshift.const_mul (22 / 25)).integrableOn)
      hjump.integrableOn h1_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (22 / 47)).integrableOn (hshift.const_mul (22 / 25)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - 2 * x) (L - x) x,
      show L - 2 * x + x = L - x by ring, show L - x + x = L by ring] at h1
    have hIoc_le_Ioi : (∫ v in Ioc (L - x) L, h v ^ 2) ≤ ∫ v in Ioi (L - x), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall Ioc_subset_Ioi_self)
    linarith
  -- Step 2 (layer-1-to-layer-2 intervals `Ioc x (2 * x)` and `Ioc (L - 3 * x) (L - 2 * x)`)
  have h2_left_pt : ∀ u : ℝ,
      (8 / 31 : ℝ) * h (u + x) ^ 2 - (8 / 23 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := eight_thirty_firsts_sq_sub_eight_twenty_thirds_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h2_left : (8 / 31 : ℝ) * (∫ v in Ioc (2 * x) (3 * x), h v ^ 2) -
      (8 / 23 : ℝ) * (∫ u in Ioc x (2 * x), h u ^ 2) ≤
      ∫ u in Ioc x (2 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc x (2 * x))
      ((hshift.const_mul (8 / 31)).integrableOn.sub (hsq.const_mul (8 / 23)).integrableOn)
      hjump.integrableOn h2_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (8 / 31)).integrableOn (hsq.const_mul (8 / 23)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) x (2 * x) x,
      show x + x = 2 * x by ring, show 2 * x + x = 3 * x by ring] at h1
    linarith
  have h2_right_pt : ∀ u : ℝ,
      (8 / 31 : ℝ) * h u ^ 2 - (8 / 23 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => eight_thirty_firsts_sq_sub_eight_twenty_thirds_sq_le_sub_sq (h u) (h (u + x))
  have h2_right : (8 / 31 : ℝ) * (∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2) -
      (8 / 23 : ℝ) * (∫ v in Ioc (L - 2 * x) (L - x), h v ^ 2) ≤
      ∫ u in Ioc (L - 3 * x) (L - 2 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - 3 * x) (L - 2 * x))
      ((hsq.const_mul (8 / 31)).integrableOn.sub (hshift.const_mul (8 / 23)).integrableOn)
      hjump.integrableOn h2_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (8 / 31)).integrableOn (hshift.const_mul (8 / 23)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - 3 * x) (L - 2 * x) x,
      show L - 3 * x + x = L - 2 * x by ring, show L - 2 * x + x = L - x by ring] at h1
    linarith
  -- Step 3 (midpoint-split inner intervals `Ioc (2 * x) (L / 2 - x)` and `Ioc (L / 2) (L - 3 * x)`)
  have h3_left_pt : ∀ u : ℝ,
      (3 / 25 : ℝ) * h (u + x) ^ 2 - (3 / 22 : ℝ) * h u ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := three_twenty_fifths_sq_sub_three_twenty_seconds_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have h3_left : (3 / 25 : ℝ) * (∫ v in Ioc (3 * x) (L / 2), h v ^ 2) -
      (3 / 22 : ℝ) * (∫ u in Ioc (2 * x) (3 * x), h u ^ 2) ≤
      ∫ u in Ioc (2 * x) (L / 2 - x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (2 * x) (L / 2 - x))
      ((hshift.const_mul (3 / 25)).integrableOn.sub (hsq.const_mul (3 / 22)).integrableOn)
      hjump.integrableOn h3_left_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hshift.const_mul (3 / 25)).integrableOn (hsq.const_mul (3 / 22)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (2 * x) (L / 2 - x) x,
      show 2 * x + x = 3 * x by ring, show L / 2 - x + x = L / 2 by ring] at h1
    have hsub_2L : Ioc (2 * x) (L / 2 - x) ⊆ Ioc (2 * x) (3 * x) :=
      Ioc_subset_Ioc_right (by linarith)
    have hmono_2L : (∫ u in Ioc (2 * x) (L / 2 - x), h u ^ 2) ≤ ∫ u in Ioc (2 * x) (3 * x), h u ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall hsub_2L)
    linarith
  have h3_right_pt : ∀ u : ℝ,
      (3 / 25 : ℝ) * h u ^ 2 - (3 / 22 : ℝ) * h (u + x) ^ 2 ≤ (h u - h (u + x)) ^ 2 :=
    fun u => three_twenty_fifths_sq_sub_three_twenty_seconds_sq_le_sub_sq (h u) (h (u + x))
  have h3_right : (3 / 25 : ℝ) * (∫ u in Ioc (L / 2) (L - 3 * x), h u ^ 2) -
      (3 / 22 : ℝ) * (∫ v in Ioc (L - 3 * x) (L - 2 * x), h v ^ 2) ≤
      ∫ u in Ioc (L / 2) (L - 3 * x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L / 2) (L - 3 * x))
      ((hsq.const_mul (3 / 25)).integrableOn.sub (hshift.const_mul (3 / 22)).integrableOn)
      hjump.integrableOn h3_right_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul (3 / 25)).integrableOn (hshift.const_mul (3 / 22)).integrableOn,
      integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L / 2) (L - 3 * x) x,
      show L - 3 * x + x = L - 2 * x by ring] at h1
    have hsub_2R : Ioc (L / 2 + x) (L - 2 * x) ⊆ Ioc (L - 3 * x) (L - 2 * x) :=
      Ioc_subset_Ioc_left (by linarith)
    have hmono_2R : (∫ v in Ioc (L / 2 + x) (L - 2 * x), h v ^ 2) ≤
        ∫ v in Ioc (L - 3 * x) (L - 2 * x), h v ^ 2 :=
      setIntegral_mono_set hsq.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (Eventually.of_forall hsub_2R)
    linarith
  -- Hierarchical disjoint union of the 6 intervals inside `Ioc 0 (L - x)`
  -- Level 3: `Ioc (2 * x) (L / 2 - x)` and `Ioc (L / 2) (L - 3 * x)` inside `Ioc (2 * x) (L - 3 * x)`
  have hdisj_3 : Disjoint (Ioc (2 * x) (L / 2 - x)) (Ioc (L / 2) (L - 3 * x)) :=
    disjoint_left.mpr fun u hu1 hu2 => by linarith [hu1.2, hu2.1]
  have hsub_3 : Ioc (2 * x) (L / 2 - x) ∪ Ioc (L / 2) (L - 3 * x) ⊆ Ioc (2 * x) (L - 3 * x) := by
    intro u hu
    rcases hu with hu1 | hu2
    · exact ⟨hu1.1, by linarith [hu1.2]⟩
    · exact ⟨by linarith [hu2.1], hu2.2⟩
  have hunion_3 : (∫ u in Ioc (2 * x) (L / 2 - x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (L / 2) (L - 3 * x), (h u - h (u + x)) ^ 2) ≤
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

/-- For any `BddSupp A h C`, the core `Ioc x (L - x)` is covered by the six slices
`Ioc x (2 * x)`, `Ioc (L - 2 * x) (L - x)`, `Ioc (2 * x) (3 * x)`, `Ioc (L - 3 * x) (L - 2 * x)`,
`Ioc (3 * x) (L / 2)`, and `Ioc (L / 2) (L - 3 * x)`. -/
theorem coreMass_le_three_step_midpoint_split_layers {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) :
    coreMass h L x ≤
      ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) +
        ((∫ v in Ioc (2 * x) (3 * x), h v ^ 2) + ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2) +
        ((∫ v in Ioc (3 * x) (L / 2), h v ^ 2) + ∫ u in Ioc (L / 2) (L - 3 * x), h u ^ 2) := by
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
      (∫ u in Ioc (3 * x) (L / 2), h u ^ 2) + ∫ u in Ioc (L / 2) (L - 3 * x), h u ^ 2 := by
    refine setIntegral_le_add_of_subset_union hsq (fun _ => sq_nonneg _)
      measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
    rcases le_or_gt u (L / 2) with hle | hgt
    · exact Or.inl ⟨hu.1, hle⟩
    · exact Or.inr ⟨hgt, hu.2⟩
  linarith

/-- **Universal Eighth-Window Coercivity (`(3 / 25) * ∫ h² ≤ D_h(x)` for all `x ≥ L / 8`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and **every shift `x ≥ L / 8`**,
`(3 / 25) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem three_twenty_fifths_mul_integral_sq_le_integral_jump_sq_of_eighth_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 8 ≤ x) :
    (3 / 25 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  rcases le_or_gt x (L / 6) with hle | hgt
  · have hx0 : 0 ≤ x := by linarith
    have hxL2 : x ≤ L / 2 := by linarith
    have hcol_int := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
    have hthree := disjoint_three_step_slices_le_interior_jump_sq hh hL0 hx hle
    have hcov := coreMass_le_three_step_midpoint_split_layers (L := L) (x := x) hh
    have hcons := collarMass_add_coreMass_eq hh hxL2
    have hlay1_nn : 0 ≤ (∫ v in Ioc x (2 * x), h v ^ 2) +
        ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2 :=
      add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    have hlay2_nn : 0 ≤ (∫ v in Ioc (2 * x) (3 * x), h v ^ 2) +
        ∫ u in Ioc (L - 3 * x) (L - 2 * x), h u ^ 2 :=
      add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    linarith
  · have h6 := seven_thirty_sixths_mul_integral_sq_le_integral_jump_sq_of_sixth_le
      hh hsupp hL0 hgt.le
    have hE0 : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith

/-- **Universal Eighth-Window Autocorrelation Damping (`2 R(x) ≤ (47 / 25) R(0)` for all `x ≥ L / 8`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and every shift `x ≥ L / 8`,
`2 * autocorr h x ≤ (47 / 25) * ∫ u, h u ^ 2`. -/
theorem two_mul_autocorr_le_forty_seven_twenty_fifths_mul_integral_sq_of_eighth_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hL0 : 0 ≤ L) (hx : L / 8 ≤ x) :
    2 * autocorr h x ≤ (47 / 25 : ℝ) * ∫ u, h u ^ 2 := by
  have hid := integral_jump_sq hh x
  have hcoerc := three_twenty_fifths_mul_integral_sq_le_integral_jump_sq_of_eighth_le
    hh hsupp hL0 hx
  linarith

/-! ## Section 2: Eighth-Window Potential Coercivity and Universal `(0, log 2)` Plastic Floor -/

/-- Integrating `(3 / 25)` coercivity against `-screwRegularKernel x ≥ 0` over `Ioo a c`
(`L / 8 ≤ a ≤ c ≤ screwSignThreshold`) yields
`(3 / 50) * (Φ(a) - Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo a c} (-screwRegularKernel x) D_h(x) dx`. -/
theorem three_fiftieths_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L a c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL : 0 < L) (ha : L / 8 ≤ a) (hac : a ≤ c)
    (hct : c ≤ screwSignThreshold) :
    (3 / 50 : ℝ) * (levyCoshPotential a - levyCoshPotential c) * (∫ u, h u ^ 2) ≤
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
      (fun x : ℝ => (-screwRegularKernel x) * ((3 / 25 : ℝ) * ∫ u, h u ^ 2)) (Ioo a c) :=
    hI_K.mul_const _
  have hmono : (∫ x in Ioo a c, (-screwRegularKernel x) * ((3 / 25 : ℝ) * ∫ u, h u ^ 2)) ≤
      ∫ x in Ioo a c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
    refine setIntegral_mono_on hI_low hI_jump measurableSet_Ioo fun x hx => ?_
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hct))
    exact mul_le_mul_of_nonneg_left
      (three_twenty_fifths_mul_integral_sq_le_integral_jump_sq_of_eighth_le hh hsupp hL.le
        (ha.trans hx.1.le))
      hK0
  rw [integral_mul_const, setIntegral_Ioo_neg_screwRegularKernel ha0 hac] at hmono
  linarith

/-- **Two-Shell Eighth + Sixth Potential Lower Bound on `Ioo (L / 8) b` (`L / 6 ≤ b ≤ screwSignThreshold`)**:
combining `(3 / 25)` coercivity on `Ioo (L / 8) (L / 6)` with `(7 / 36)` coercivity on
`Ioo (L / 6) b` yields:
`((3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) - (7 / 72) * Φ(b)) * ∫ h² ≤ ∫_{x ∈ Ioo (L / 8) b} (-K(x)) D_h(x) dx`. -/
theorem eighth_add_sixth_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL : 0 < L) (hb6 : L / 6 ≤ b)
    (hbt : b ≤ screwSignThreshold) :
    ((3 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (67 / 1800 : ℝ) * levyCoshPotential (L / 6) -
        (7 / 72 : ℝ) * levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 8) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL8 : 0 < L / 8 := by linarith
  have hL8_6 : L / 8 ≤ L / 6 := by linarith
  have hL6t : L / 6 ≤ screwSignThreshold := hb6.trans hbt
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 8) b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL8 hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 8) b) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL8 hx.1) (hx.2.le.trans hbt))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_left_Ioc : IntegrableOn F (Ioc (L / 8) (L / 6)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hb6)
  have hIF_right_Ioc : IntegrableOn F (Ioc (L / 6) b) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL8_6 le_rfl)
  have hdisj : Disjoint (Ioc (L / 8) (L / 6)) (Ioc (L / 6) b) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 8) b, F x) =
      (∫ x in Ioo (L / 8) (L / 6), F x) + ∫ x in Ioo (L / 6) b, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL8_6 hb6,
      setIntegral_union hdisj measurableSet_Ioc hIF_left_Ioc hIF_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h8 := three_fiftieths_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL le_rfl hL8_6 hL6t
  have h6 := seven_seventy_seconds_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL le_rfl hb6 hbt
  dsimp only [F] at hsplit
  linarith

/-- **Three-Shell Eighth + Sixth + Quarter Lévy–Cosh Crossover Inequality**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and `L / 4 ≤ c ≤ screwSignThreshold`,
`(A(0) + (3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (17 / 21) * Φ(c)) * ∫ f²`
`+ ∫∫ f(u) f(v) (2 cosh((u - v)/2) - K_c(|u - v|)) ≤ W_∞(f ⋆ f̃)`. -/
theorem eighth_add_sixth_add_quarter_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L)
    (hL4c : L / 4 ≤ c) (hct : c ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (47 / 504) * levyCoshPotential (L / 4) +
        (17 / 21) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL8 : 0 < L / 8 := by linarith
  have hL4 : 0 < L / 4 := by linarith
  have hL8_4 : L / 8 ≤ L / 4 := by linarith
  have hL6_4 : L / 6 ≤ L / 4 := by linarith
  have hL8c : L / 8 ≤ c := hL8_4.trans hL4c
  have hL4t : L / 4 ≤ screwSignThreshold := hL4c.trans hct
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL8 hL8c hct
  have h86 := eighth_add_sixth_sub_levyCoshPotential_le_setIntegral_Ioo hB hsupp hL hL6_4 hL4t
  have h4 := four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL le_rfl hL4c hct
  have hD0 : ∀ x, 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (f u - f (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hB)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 8) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL8 hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 8) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, f u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL8 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hB x) hK0
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
  dsimp only [F] at hsplit
  linarith

/-- **Eighth-Window Universal Plastic Floor on `(0, log 2)`**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 (Real.log 2)`,
`(A(0) + (3 / 50) * Φ((log 2)/8) + (67 / 1800) * Φ((log 2)/6) + (47 / 504) * Φ((log 2)/4) + (17 / 21) * Φ(t_*)) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem eighth_window_log_two_plastic_floor_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hsupp : ∀ u ∉ Ioo 0 (Real.log 2), f u = 0) :
    (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (Real.log 2 / 8) +
        (67 / 1800) * levyCoshPotential (Real.log 2 / 6) +
        (47 / 504) * levyCoshPotential (Real.log 2 / 4) +
        (17 / 21) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL4t : Real.log 2 / 4 ≤ screwSignThreshold := by
    linarith [Real.log_two_lt_d9, screwSignThreshold_gt]
  have hmain := eighth_add_sixth_add_quarter_levyCosh_crossover_le_weilArchRe
    hf hfc hL hL4t le_rfl hsupp
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-! ## Section 3: Eighth-Window Five-Point Reflected Potential and Unconditional Positivity on `(0, 8 / 21)` -/

/-- **Eighth-Window Five-Point Reflected Jump-Integral Coercivity on `Ioo (L / 8) c` (`L / 2 ≤ c ≤ 3 * L / 4`)**:
combining `eighth_add_sixth_sub_levyCoshPotential_le_setIntegral_Ioo` on `Ioo (L / 8) (L / 4)` with
`sharpened_inner_shell_sub_levyCoshPotential_le_setIntegral_Ioo` on `Ioo (L / 4) c` yields:
`((3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (13 / 21) * Φ(L / 2) - (17 / 21) * Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo (L / 8) c} (-K(x)) D_h(x) dx`. -/
theorem eighth_window_reflected_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (hL2c : L / 2 ≤ c)
    (hc34 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold) :
    ((3 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (67 / 1800 : ℝ) * levyCoshPotential (L / 6) +
        (47 / 504 : ℝ) * levyCoshPotential (L / 4) +
        (13 / 21 : ℝ) * levyCoshPotential (L / 2) -
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
  have hin := sharpened_inner_shell_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL hL2c hc34 hct
  dsimp only [F] at hsplit
  linarith

/-- **Eighth-Window Five-Point Reflected Lévy–Cosh Crossover Inequality (`L / 2 ≤ c ≤ 3 * L / 4`)**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`),
`(A(0) + (3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (13 / 21) * Φ(L / 2) + (4 / 21) * Φ(c)) * ∫ f² + ... ≤ W_∞(f ⋆ f̃)`. -/
theorem eighth_window_reflected_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L)
    (hL2c : L / 2 ≤ c) (hc34 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (47 / 504) * levyCoshPotential (L / 4) +
        (13 / 21) * levyCoshPotential (L / 2) +
        (4 / 21) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL8 : 0 < L / 8 := by linarith
  have hL8c : L / 8 ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL8 hL8c hct
  have href := eighth_window_reflected_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL hL2c hc34 hct
  linarith

/-- **Osculating Lower Bound for the Eighth-Window Reflected Potential (`L ≤ 8 / 21`, `c ≤ 3 * L / 4`)**:
because `t ↦ log(1 / (2 * π * t)) + (7 / 2) * t - γ` is strictly decreasing on `(0, 2 / 7]`
and `3 * L / 4 ≤ 2 / 7` for `L ≤ 8 / 21`, we have `F_osc(3 * L / 4) ≤ F_osc(c) ≤ A(0) + Φ(c)`
with **zero linear penalty**, yielding:
`log(1 / (π * L)) + (7 / 72) * log 2 + (1931 / 12600) * log(4 / 3) + (73997 / 43200) * L - γ`
`≤ EF.gammaBracket 0 + (3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (47 / 504) * Φ(L / 4) + (13 / 21) * Φ(L / 2) + (4 / 21) * Φ(c)`. -/
theorem osculating_le_eighth_window_reflected_potential {L c : ℝ} (hL : 0 < L)
    (hL_max : L ≤ 8 / 21) (hc0 : 0 < c) (hc34 : c ≤ 3 * L / 4) :
    Real.log (1 / (Real.pi * L)) + (7 / 72 : ℝ) * Real.log 2 +
        (1931 / 12600 : ℝ) * Real.log (4 / 3) +
        (73997 / 43200 : ℝ) * L - Real.eulerMascheroniConstant ≤
      EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (47 / 504) * levyCoshPotential (L / 4) +
        (13 / 21) * levyCoshPotential (L / 2) +
        (4 / 21) * levyCoshPotential c := by
  have h1 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 8 by linarith)
  have h2 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 6 by linarith)
  have h3 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 4 by linarith)
  have h4 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (show 0 < L / 2 by linarith)
  have h5 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential hc0
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
  have hlog4_pt : Real.log (1 / (2 * Real.pi * (L / 2))) =
      Real.log (1 / (Real.pi * L)) := by
    congr 1; field_simp
  have hlog5_34 : Real.log (1 / (2 * Real.pi * (3 * L / 4))) =
      Real.log (1 / (Real.pi * L)) + Real.log (4 / 3) - Real.log 2 := by
    rw [eq_sub_iff_add_eq, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  -- Show `F_osc(3 * L / 4) ≤ F_osc(c)` for `0 < c ≤ 3 * L / 4 ≤ 2 / 7`
  have h34_pos : 0 < 3 * L / 4 := by linarith
  have hlog_ratio : Real.log (1 / (2 * Real.pi * (3 * L / 4))) =
      Real.log (c / (3 * L / 4)) + Real.log (1 / (2 * Real.pi * c)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  have hlog_le : Real.log (c / (3 * L / 4)) ≤ c / (3 * L / 4) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hc0 h34_pos)
  have hdiv_eq : 1 - c / (3 * L / 4) = (3 * L / 4 - c) / (3 * L / 4) := by
    field_simp
  have hslope : (7 / 2 : ℝ) * (3 * L / 4 - c) ≤ (3 * L / 4 - c) / (3 * L / 4) := by
    rw [le_div_iff₀ h34_pos]
    nlinarith
  linarith

/-- Sharp lower bound on `log(1 / (π * (8 / 21)))` using the exact factorization
`π * (8 / 21) = 2 * (3 / 4)² * (17 / 16) * ((1024 / 3213) * π)` where `(1024 / 3213) * π ≈ 1.001242`:
`-log 2 + 2 * log(4 / 3) + 15 / 16 - (1024 / 3213) * π ≤ log(1 / (π * (8 / 21)))`. -/
theorem fifteen_sixteenths_sub_mul_pi_le_log_inv_pi_mul_eight_twenty_firsts :
    -Real.log 2 + 2 * Real.log (4 / 3) + (15 / 16 : ℝ) - (1024 / 3213 : ℝ) * Real.pi ≤
      Real.log (1 / (Real.pi * (8 / 21))) := by
  have hpos : 0 < (1024 / 3213 : ℝ) * Real.pi := by positivity
  have hfac : Real.pi * (8 / 21 : ℝ) =
      2 * (3 / 4 : ℝ) * (3 / 4 : ℝ) * (17 / 16 : ℝ) * ((1024 / 3213 : ℝ) * Real.pi) := by ring
  have hlog34 : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3) := by
    rw [← Real.log_inv]; congr 1; norm_num
  rw [one_div, Real.log_inv, hfac,
    Real.log_mul (by positivity) hpos.ne',
    Real.log_mul (by positivity) (by norm_num),
    Real.log_mul (by positivity) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    hlog34]
  have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 17 / 16)
  have h2 := Real.log_le_sub_one_of_pos hpos
  linarith

/-- Tightened upper rational enclosure `screwSignThreshold < (2 : ℝ) / 7` (`t_* < 0.285714`),
derived from `exp_half_screwSignThreshold_lt` by factoring
`1151 / 1000 = (31 / 30)⁴ * (932310 / 923521)`. -/
theorem screwSignThreshold_lt_two_sevenths :
    screwSignThreshold < (2 : ℝ) / 7 := by
  have hexp := exp_half_screwSignThreshold_lt
  have hlog := Real.log_lt_log (Real.exp_pos _) hexp
  rw [Real.log_exp,
    show (1151 : ℝ) / 1000 =
      (31 / 30) * (31 / 30) * (31 / 30) * (31 / 30) * (932310 / 923521) by norm_num,
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)] at hlog
  have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 31 / 30)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 932310 / 923521)
  linarith

/-- **Strict Positivity of the Eighth-Window Reflected Potential at `L = 8 / 21` and `c = screwSignThreshold`**:
`0 ≤ EF.gammaBracket 0 + (3 / 50) * Φ((8/21)/8) + (67 / 1800) * Φ((8/21)/6) + (47 / 504) * Φ((8/21)/4) + (13 / 21) * Φ((8/21)/2) + (4 / 21) * Φ(screwSignThreshold)`. -/
theorem zero_le_eighth_window_reflected_potential_eight_twenty_firsts :
    0 ≤ EF.gammaBracket 0 + (3 / 50) * levyCoshPotential ((8 / 21 : ℝ) / 8) +
        (67 / 1800) * levyCoshPotential ((8 / 21 : ℝ) / 6) +
        (47 / 504) * levyCoshPotential ((8 / 21 : ℝ) / 4) +
        (13 / 21) * levyCoshPotential ((8 / 21 : ℝ) / 2) +
        (4 / 21) * levyCoshPotential screwSignThreshold := by
  have hc0 : 0 < screwSignThreshold := screwSignThreshold_pos
  have hc34 : screwSignThreshold ≤ 3 * (8 / 21 : ℝ) / 4 := by
    linarith [screwSignThreshold_lt_two_sevenths]
  have hosc := osculating_le_eighth_window_reflected_potential
    (by norm_num : (0 : ℝ) < 8 / 21) le_rfl hc0 hc34
  have hlog_pi := fifteen_sixteenths_sub_mul_pi_le_log_inv_pi_mul_eight_twenty_firsts
  have hlog2 := Real.log_two_lt_d9
  have hlog43 := two_sevenths_lt_log_four_thirds
  have hpi := Real.pi_lt_d4
  have hgamma :=
    RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith

/-- **Unconditional Archimedean Weil Positivity on `(0, 8 / 21)` (`≈ (0, 0.380952)`, `54.96%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` supported in `Ioo 0 L` with `L ≤ 8 / 21`,
`0 ≤ WeilOneSided.weilArchRe (EF.weilTest f f)`. -/
theorem weilArchRe_nonneg_of_support_Ioo_le_eight_twenty_firsts {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL : L ≤ 8 / 21) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_8_21 : ∀ u ∉ Ioo (0 : ℝ) (8 / 21), f u = 0 :=
    fun u hu => hsupp u fun huL => hu ⟨huL.1, huL.2.trans_le hL⟩
  have hmain := eighth_window_reflected_levyCosh_crossover_le_weilArchRe
    hf hfc (by norm_num : (0 : ℝ) < 8 / 21)
    (by linarith [screwSignThreshold_gt_6036_over_21509])
    (by linarith [screwSignThreshold_lt_two_sevenths])
    le_rfl hsupp_8_21
  have hpot := zero_le_eighth_window_reflected_potential_eight_twenty_firsts
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hterm1 : 0 ≤ (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential ((8 / 21 : ℝ) / 8) +
        (67 / 1800) * levyCoshPotential ((8 / 21 : ℝ) / 6) +
        (47 / 504) * levyCoshPotential ((8 / 21 : ℝ) / 4) +
        (13 / 21) * levyCoshPotential ((8 / 21 : ℝ) / 2) +
        (4 / 21) * levyCoshPotential screwSignThreshold) * ∫ u, f u ^ 2 :=
    mul_nonneg hpot hsq
  have hpair : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-- **Unconditional `WindowPositive` on `(0, 8 / 21)` (`≈ (0, 0.380952)`, `54.96%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (8 / 21)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_eight_twenty_firsts (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (8 / 21)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_eight_twenty_firsts hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 3 / 8)` (`= (0, 0.375)`, `54.10%` of `(0, log 2)`)**:
immediate corollary since `3 / 8 = 63 / 168 < 64 / 168 = 8 / 21`. -/
theorem windowPositive_three_eighths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (3 / 8)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_eight_twenty_firsts hf hfc hf0 (by norm_num)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 19 / 50)` (`= (0, 0.38)`, `54.82%` of `(0, log 2)`)**:
immediate corollary since `19 / 50 = 399 / 1050 < 400 / 1050 = 8 / 21`. -/
theorem windowPositive_nineteen_fiftieths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (19 / 50)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_eight_twenty_firsts hf hfc hf0 (by norm_num)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

end

end RHTower.WeilLevyEighthWindow
