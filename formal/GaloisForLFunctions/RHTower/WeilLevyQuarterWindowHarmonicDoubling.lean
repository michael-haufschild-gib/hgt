import GaloisForLFunctions.RHTower.WeilLevyMidpointCoreOverlapHarmonicDoubling

/-!
# Support-Aware Quarter-Window Harmonic Doubling, Universal Fejér–Bochner Jump-Doubling, and Unconditional Positivity on `(0, 12 / 25)`

This module implements **Cycle 78** of the prime-blind archimedean Weil positivity programme,
establishing the support-aware quarter-window harmonic-doubling coercivity family on `x ≥ L / 4`,
the universal two-line Fejér–Bochner jump-doubling law `D_h(2x) ≤ 4 D_h(x)` with its dyadic
sub-tenth coercivity cascade on `[L / 20, L / 10]`, the upgraded `(0, log 2)` plastic floor
(reducing the universal constant deficit from `-0.0080` down to **`-0.0033`**), and unconditional
`WindowPositive` on **`(0, 12 / 25)` (`= (0, 0.48)`, `69.25%` of `(0, log 2)`)**:

## Mathematical Architecture

1. **Section 1 — Support-Aware Quarter-Window Harmonic-Doubling Coercivity Family (`x ≥ L / 4`)**:
   - For $x \in [L / 4, L / 3]$, we have $0 \le x \le L - 2x \le 2x \le L - x \le L$. Integrating a
     3-point inequality
     $$A(p^2 + r^2) + B q^2 \le \frac{1}{2}(p - q)^2 + \frac{1}{2}(q - r)^2 + \theta(2 p r)$$
     over $u \in \mathrm{Ioc}\,0\,(L - 2x)$ (where $u + x \in \mathrm{Ioc}\,x\,(L - x)$ covers the
     entire core) and adding $\frac{1}{2}$ of a 2-point collar-to-core inequality
     $\alpha_c a^2 - \beta_c b^2 \le (a - b)^2$ on $u \in \mathrm{Ioc}\,0\,x$ and
     $u \in \mathrm{Ioc}\,(L - 2x)\,(L - x)$ pairs into two exact adjacent interval unions on the RHS:
     $$\mathrm{Ioc}\,0\,(L - 2x) \cup \mathrm{Ioc}\,(L - 2x)\,(L - x) = \mathrm{Ioc}\,0\,(L - x), \qquad
       \mathrm{Ioc}\,0\,x \cup \mathrm{Ioc}\,x\,(L - x) = \mathrm{Ioc}\,0\,(L - x),$$
     and two exact adjacent interval unions on the LHS:
     $$\mathrm{Ioc}\,0\,(L - 2x) \cup \mathrm{Ioc}\,(L - 2x)\,(L - x) = \mathrm{Ioc}\,0\,(L - x), \qquad
       \mathrm{Ioc}\,x\,(2x) \cup \mathrm{Ioc}\,(2x)\,L = \mathrm{Ioc}\,x\,L$$
     (whose sum is $\mathrm{collarMass}\ h\ L\ x + 2\,\mathrm{coreMass}\ h\ L\ x$), while the remaining
     $(\alpha_c / 2 - A)$ weight on $\mathrm{Ioc}\,x\,(2x)$ and $\mathrm{Ioc}\,(L - 2x)\,(L - x)$
     covers $\mathrm{coreMass}\ h\ L\ x$ since $L - 2x \le 2x$.
   - Combining with $x \ge L / 3$ (where $\int h^2 \le D_h(x) + 2 R(2x)$ and $(24 / 41)\int h^2 \le D_h(x)$)
     yields two sharp specializations valid for **all** $x \ge L / 4$:
     - **Theorem 1A ($\theta = 1 / 3$)**:
       $$\frac{2}{3}\int_{\mathbb R} h(u)^2\,du \le \left(\int_{\mathbb R} \bigl(h(u) - h(u + x)\bigr)^2\,du\right) + \frac{1}{3}\bigl(2\,\mathrm{autocorr}\ h\ (2x)\bigr),$$
       raising the quarter-window harmonic-doubling excess gain per unit of $2 K(2x)$ from
       $163 / 525$ (`Cycle 77`) to **$3 / 7 = 225 / 525$** (`+38%` boost on $\Phi(2 L / 3) - \Phi(t_*)$).
     - **Theorem 1B ($\theta = 2 / 5$)**:
       $$\frac{251}{360}\int_{\mathbb R} h(u)^2\,du \le \left(\int_{\mathbb R} \bigl(h(u) - h(u + x)\bigr)^2\,du\right) + \frac{2}{5}\bigl(2\,\mathrm{autocorr}\ h\ (2x)\bigr),$$
       upgrading the `[L / 4, L / 3]` shell weight for $L \ge 2 / 3$ from $41 / 70 \approx 0.5857$
       to **$251 / 360 \approx 0.6972$**.

2. **Section 2 — Universal Fejér–Bochner Jump-Doubling (`D_h(2x) ≤ 4 D_h(x)`), Dyadic Sub-Tenth Coercivity on `[L / 20, L / 10]`, and the Sharpened `(0, log 2)` Plastic Floor (`-0.0033`)**:
   - Adding $\int h^2 \le 2 D_h(x) + 2 R(2x)$ and $D_h(2x) = 2\int h^2 - 2 R(2x)$ proves the
     universal jump-doubling law $D_h(2x) \le 4 D_h(x)$ for **every** `BddSupp A h C` and $x \in \mathbb R$.
   - Applying this to $2x \ge L / 6, L / 7, L / 8, L / 10$ gives $(7 / 144)\int h^2 \le D_h(x)$ for
     $x \ge L / 12$, $(3 / 80)\int h^2 \le D_h(x)$ for $x \ge L / 14$, $(3 / 100)\int h^2 \le D_h(x)$
     for $x \ge L / 16$, and $(1 / 50)\int h^2 \le D_h(x)$ for $x \ge L / 20$.
   - Combining these four dyadic sub-tenth shells with the $251 / 360$ quarter-window upgrade reduces
     the universal `(0, log 2)` constant deficit from `-0.0080` all the way down to **`-0.0033`**.

3. **Section 3 — Crossing Ratio at `4 / 25`, Fifteen-Point Potential, and Unconditional `WindowPositive` on `(0, 12 / 25)` (`= (0, 0.48)`, `69.25%` of `(0, log 2)`)**:
   - At $b = 4 / 25 = 0.16$ ($b / 2 = 2 / 25$), the rational enclosure $\frac{677}{625} \le e^{2 / 25} \le \frac{13}{12}$
     certifies $3 \cdot \bigl(2\,\mathrm{screwRegularKernel}(2x)\bigr) \le -\mathrm{screwRegularKernel}(x)$
     for all $x \in (0, 4 / 25]$.
   - Combining the 4 dyadic sub-tenth shells with the $(3 / 7)$ quarter-window harmonic-doubling
     excess bound yields a 15-point strictly positive-weight potential at $L = 12 / 25 = 0.48$
     (`69.25%` of `(0, log 2)`) whose logarithms are 100% 5-smooth (plus $7 / 6$), with certified
     rational margin `+0.000452 > 0`, establishing unconditional `WindowPositive` on **`(0, 12 / 25)`**
     (`= (0, 0.48)`), `(0, 10 / 21)`, `(0, 15 / 32)`, `(0, 7 / 15)`, and `(0, 5 / 11)`.
-/

open Complex Real Set MeasureTheory Filter
open scoped Topology
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyQuarterHarmonicDoubling

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor
open RHTower.WeilLevyQuarterWindow RHTower.WeilLevySymmetricThreePoint
open RHTower.WeilLevySixthWindow RHTower.WeilLevyFibonacciStaircase
open RHTower.WeilLevyEighthWindow RHTower.WeilLevyThirdWindow
open RHTower.WeilLevyFifthWindow RHTower.WeilLevyTenthWindow
open RHTower.WeilLevySeventhWindow RHTower.WeilLevyHarmonicDoubling
open RHTower.WeilLevyMidpointCoreOverlap

/-! ## Section 1: Support-Aware Quarter-Window Harmonic-Doubling Coercivity Family (`x ≥ L / 4`) -/

/-- For any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and `x ∈ [0, L]`,
the collar mass `collarMass h L x` equals `(∫ u in Ioc 0 x, h u ^ 2) + ∫ u in Ioc (L - x) L, h u ^ 2`. -/
theorem setIntegral_Ioc_add_Ioc_eq_collarMass {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hx0 : 0 ≤ x) (_hxL : x ≤ L) :
    (∫ u in Ioc 0 x, h u ^ 2) + (∫ u in Ioc (L - x) L, h u ^ 2) = collarMass h L x := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hIic0 : (∫ u in Iic 0, h u ^ 2) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu => by
      rw [hsupp u (fun hmem => not_lt_of_ge (mem_Iic.mp hu) hmem.1)]; ring
  have hIoiL : (∫ u in Ioi L, h u ^ 2) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu => by
      rw [hsupp u (fun hmem => not_lt_of_ge (mem_Ioi.mp hu).le hmem.2)]; ring
  have hleft : (∫ u in Iic x, h u ^ 2) = ∫ u in Ioc 0 x, h u ^ 2 := by
    rw [← Iic_union_Ioc_eq_Iic hx0,
      setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        hsq.integrableOn hsq.integrableOn, hIic0, zero_add]
  have hright : (∫ u in Ioi (L - x), h u ^ 2) = ∫ u in Ioc (L - x) L, h u ^ 2 := by
    rw [← Ioc_union_Ioi_eq_Ioi (by linarith : L - x ≤ L),
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hsq.integrableOn hsq.integrableOn, hIoiL, add_zero]
  unfold collarMass
  linarith

/-- For any `BddSupp A h C` and any `x ∈ [L / 4, L / 3]` (`0 ≤ L`), the two intervals `Ioc x (2 * x)`
and `Ioc (L - 2 * x) (L - x)` cover the core `Ioc x (L - x)`. -/
theorem coreMass_le_setIntegral_Ioc_two_mul_add_sub_two_mul {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hx4 : L / 4 ≤ x) (_hx3 : x ≤ L / 3) :
    coreMass h L x ≤
      (∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2 := by
  unfold coreMass
  refine setIntegral_le_add_of_subset_union hh.integrable_sq (fun _ => sq_nonneg _)
    measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc fun u hu => ?_
  rcases le_or_gt u (2 * x) with hle | hgt
  · exact Or.inl ⟨hu.1, hle⟩
  · exact Or.inr ⟨by linarith, hu.2⟩

/-- **General Support-Aware Quarter-Window Harmonic-Doubling Theorem on `[L / 4, L / 3]`**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`), any `x ∈ [L / 4, L / 3]`,
and any parameters `A₀ B₀ θ αh βh : ℝ` with `A₀ ≤ αh` satisfying:
- `∀ p q r, A₀ * (p ^ 2 + r ^ 2) + B₀ * q ^ 2 ≤ (1 / 2) * (p - q) ^ 2 + (1 / 2) * (q - r) ^ 2 + θ * (2 * (p * r))`,
- `∀ a b, αh * a ^ 2 - βh * b ^ 2 ≤ (1 / 2) * (a - b) ^ 2`,
we have:
`(1 + A₀ - βh) * collarMass h L x + (A₀ + B₀ + αh) * coreMass h L x`
`≤ (∫ u, (h u - h (u + x)) ^ 2) + θ * (2 * autocorr h (2 * x))`. -/
theorem quarter_three_point_add_two_point_le_integral_jump_sq_add_autocorr_of_quarter_to_third
    {A : Set ℝ} {h : ℝ → ℝ} {C L x A₀ B₀ θ αh βh : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx4 : L / 4 ≤ x) (hx3 : x ≤ L / 3)
    (hAα : A₀ ≤ αh)
    (h3pt : ∀ p q r : ℝ,
      A₀ * (p ^ 2 + r ^ 2) + B₀ * q ^ 2 ≤
        (1 / 2 : ℝ) * (p - q) ^ 2 + (1 / 2 : ℝ) * (q - r) ^ 2 + θ * (2 * (p * r)))
    (h2pt : ∀ a b : ℝ, αh * a ^ 2 - βh * b ^ 2 ≤ (1 / 2 : ℝ) * (a - b) ^ 2) :
    (1 + A₀ - βh) * collarMass h L x + (A₀ + B₀ + αh) * coreMass h L x ≤
      (∫ u, (h u - h (u + x)) ^ 2) + θ * (2 * autocorr h (2 * x)) := by
  have hx0 : 0 ≤ x := by linarith
  have hxL2 : x ≤ L / 2 := by linarith
  have hxL : x ≤ L := by linarith
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hsq1 : Integrable (fun u : ℝ => h (u + x) ^ 2) := hsq.comp_add_right x
  have hsq2 : Integrable (fun u : ℝ => h (u + 2 * x) ^ 2) := hsq.comp_add_right (2 * x)
  have hmul2 : Integrable (fun u : ℝ => h u * h (u + 2 * x)) := hh.integrable_mul_shift (2 * x)
  have hjump : Integrable (fun u : ℝ => (h u - h (u + x)) ^ 2) := by
    have hmul : Integrable (fun u : ℝ => h u * h (u + x)) := hh.integrable_mul_shift x
    refine ((hsq.add hsq1).sub (hmul.const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  have hjump1 : Integrable (fun u : ℝ => (h (u + x) - h (u + 2 * x)) ^ 2) := by
    refine (hjump.comp_add_right x).congr (ae_of_all _ fun u => ?_)
    dsimp only; congr 3; ring
  -- 1. Integrate the 3-point inequality over `Ioc 0 (L - 2 * x)`
  have hI_sq02 : Integrable (fun u : ℝ => h u ^ 2 + h (u + 2 * x) ^ 2) := hsq.add hsq2
  have hI_3lhs : Integrable (fun u : ℝ =>
      A₀ * (h u ^ 2 + h (u + 2 * x) ^ 2) + B₀ * h (u + x) ^ 2) :=
    (hI_sq02.const_mul A₀).add (hsq1.const_mul B₀)
  have hI_3rhs1 : Integrable (fun u : ℝ =>
      (1 / 2 : ℝ) * (h u - h (u + x)) ^ 2 + (1 / 2 : ℝ) * (h (u + x) - h (u + 2 * x)) ^ 2) :=
    (hjump.const_mul (1 / 2)).add (hjump1.const_mul (1 / 2))
  have hI_3rhs : Integrable (fun u : ℝ =>
      (1 / 2 : ℝ) * (h u - h (u + x)) ^ 2 + (1 / 2 : ℝ) * (h (u + x) - h (u + 2 * x)) ^ 2 +
        θ * (2 * (h u * h (u + 2 * x)))) :=
    hI_3rhs1.add ((hmul2.const_mul 2).const_mul θ)
  have hint3 := setIntegral_mono (s := Ioc 0 (L - 2 * x))
    hI_3lhs.integrableOn hI_3rhs.integrableOn
    fun u => h3pt (h u) (h (u + x)) (h (u + 2 * x))
  rw [integral_add (hI_sq02.const_mul A₀).integrableOn (hsq1.const_mul B₀).integrableOn,
    integral_const_mul, integral_add hsq.integrableOn hsq2.integrableOn, integral_const_mul,
    integral_add hI_3rhs1.integrableOn ((hmul2.const_mul 2).const_mul θ).integrableOn,
    integral_add (hjump.const_mul (1 / 2)).integrableOn (hjump1.const_mul (1 / 2)).integrableOn,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    setIntegral_Ioc_mul_shift_eq_autocorr hh hsupp] at hint3
  have hshift_core : (∫ u in Ioc 0 (L - 2 * x), h (u + x) ^ 2) = coreMass h L x := by
    have h1 := setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 (L - 2 * x) x
    rw [zero_add, show L - 2 * x + x = L - x by ring] at h1
    exact h1
  have hshift_2x : (∫ u in Ioc 0 (L - 2 * x), h (u + 2 * x) ^ 2) = ∫ v in Ioc (2 * x) L, h v ^ 2 := by
    have h1 := setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 (L - 2 * x) (2 * x)
    rw [zero_add, show L - 2 * x + 2 * x = L by ring] at h1
    exact h1
  have hshift_j1 : (∫ u in Ioc 0 (L - 2 * x), (h (u + x) - h (u + 2 * x)) ^ 2) =
      ∫ v in Ioc x (L - x), (h v - h (v + x)) ^ 2 := by
    have h1 := setIntegral_Ioc_add_right (fun v => (h v - h (v + x)) ^ 2) 0 (L - 2 * x) x
    rw [zero_add, show L - 2 * x + x = L - x by ring] at h1
    rw [← h1]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    congr 3; ring
  rw [hshift_core, hshift_2x, hshift_j1] at hint3
  -- 2. Integrate the 2-point inequality over `Ioc 0 x` and `Ioc (L - 2 * x) (L - x)`
  have hleft_pt : ∀ u : ℝ,
      αh * h (u + x) ^ 2 - βh * h u ^ 2 ≤ (1 / 2 : ℝ) * (h u - h (u + x)) ^ 2 :=
    fun u => by
      have := h2pt (h (u + x)) (h u)
      linarith [show (h (u + x) - h u) ^ 2 = (h u - h (u + x)) ^ 2 by ring]
  have hint_left : αh * (∫ v in Ioc x (2 * x), h v ^ 2) - βh * (∫ u in Ioc 0 x, h u ^ 2) ≤
      (1 / 2 : ℝ) * ∫ u in Ioc 0 x, (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc 0 x)
      ((hsq1.const_mul αh).sub (hsq.const_mul βh)).integrableOn
      (hjump.const_mul (1 / 2)).integrableOn hleft_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq1.const_mul αh).integrableOn (hsq.const_mul βh).integrableOn,
      integral_const_mul, integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) 0 x x, zero_add,
      show x + x = 2 * x by ring] at h1
    exact h1
  have hright_pt : ∀ u : ℝ,
      αh * h u ^ 2 - βh * h (u + x) ^ 2 ≤ (1 / 2 : ℝ) * (h u - h (u + x)) ^ 2 :=
    fun u => h2pt (h u) (h (u + x))
  have hint_right : αh * (∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) -
      βh * (∫ v in Ioc (L - x) L, h v ^ 2) ≤
      (1 / 2 : ℝ) * ∫ u in Ioc (L - 2 * x) (L - x), (h u - h (u + x)) ^ 2 := by
    have h1 := setIntegral_mono (s := Ioc (L - 2 * x) (L - x))
      ((hsq.const_mul αh).sub (hsq1.const_mul βh)).integrableOn
      (hjump.const_mul (1 / 2)).integrableOn hright_pt
    dsimp only [Pi.sub_apply] at h1
    rw [integral_sub (hsq.const_mul αh).integrableOn (hsq1.const_mul βh).integrableOn,
      integral_const_mul, integral_const_mul, integral_const_mul,
      setIntegral_Ioc_add_right (fun v => h v ^ 2) (L - 2 * x) (L - x) x,
      show L - 2 * x + x = L - x by ring, show L - x + x = L by ring] at h1
    exact h1
  -- 3. Adjacent interval unions on RHS and LHS
  have h0_L2x : 0 ≤ L - 2 * x := by linarith
  have hL2x_Lx : L - 2 * x ≤ L - x := by linarith
  have hx_Lx : x ≤ L - x := by linarith
  have hx_2x : x ≤ 2 * x := by linarith
  have h2x_L : 2 * x ≤ L := by linarith
  have hLx_L : L - x ≤ L := by linarith
  have hdisj_L2x : Disjoint (Ioc 0 (L - 2 * x)) (Ioc (L - 2 * x) (L - x)) :=
    disjoint_left.mpr fun _ hu1 hu2 => not_lt_of_ge hu1.2 hu2.1
  have hdisj_x : Disjoint (Ioc 0 x) (Ioc x (L - x)) :=
    disjoint_left.mpr fun _ hu1 hu2 => not_lt_of_ge hu1.2 hu2.1
  have hdisj_2x : Disjoint (Ioc x (2 * x)) (Ioc (2 * x) L) :=
    disjoint_left.mpr fun _ hu1 hu2 => not_lt_of_ge hu1.2 hu2.1
  have hdisj_Lx : Disjoint (Ioc x (L - x)) (Ioc (L - x) L) :=
    disjoint_left.mpr fun _ hu1 hu2 => not_lt_of_ge hu1.2 hu2.1
  have hj_union1 : (∫ u in Ioc 0 (L - 2 * x), (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc (L - 2 * x) (L - x), (h u - h (u + x)) ^ 2) =
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj_L2x measurableSet_Ioc hjump.integrableOn hjump.integrableOn,
      Ioc_union_Ioc_eq_Ioc h0_L2x hL2x_Lx]
  have hj_union2 : (∫ u in Ioc 0 x, (h u - h (u + x)) ^ 2) +
      (∫ u in Ioc x (L - x), (h u - h (u + x)) ^ 2) =
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
    rw [← setIntegral_union hdisj_x measurableSet_Ioc hjump.integrableOn hjump.integrableOn,
      Ioc_union_Ioc_eq_Ioc hx0 hx_Lx]
  have hsq_union1 : (∫ u in Ioc 0 (L - 2 * x), h u ^ 2) +
      (∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) =
      (∫ u in Ioc 0 x, h u ^ 2) + coreMass h L x := by
    unfold coreMass
    rw [← setIntegral_union hdisj_L2x measurableSet_Ioc hsq.integrableOn hsq.integrableOn,
      Ioc_union_Ioc_eq_Ioc h0_L2x hL2x_Lx,
      ← setIntegral_union hdisj_x measurableSet_Ioc hsq.integrableOn hsq.integrableOn,
      Ioc_union_Ioc_eq_Ioc hx0 hx_Lx]
  have hsq_union2 : (∫ v in Ioc x (2 * x), h v ^ 2) + (∫ v in Ioc (2 * x) L, h v ^ 2) =
      coreMass h L x + ∫ v in Ioc (L - x) L, h v ^ 2 := by
    unfold coreMass
    rw [← setIntegral_union hdisj_2x measurableSet_Ioc hsq.integrableOn hsq.integrableOn,
      Ioc_union_Ioc_eq_Ioc hx_2x h2x_L,
      ← setIntegral_union hdisj_Lx measurableSet_Ioc hsq.integrableOn hsq.integrableOn,
      Ioc_union_Ioc_eq_Ioc hx_Lx hLx_L]
  have hcol_eq := setIntegral_Ioc_add_Ioc_eq_collarMass hh hsupp hx0 hxL
  have hcov := coreMass_le_setIntegral_Ioc_two_mul_add_sub_two_mul hh hx4 hx3
  have hcov_mul : (αh - A₀) * coreMass h L x ≤
      (αh - A₀) * ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) :=
    mul_le_mul_of_nonneg_left hcov (sub_nonneg.mpr hAα)
  have hlhs_eq :
      (1 + A₀ - βh) * collarMass h L x + (A₀ + B₀ + αh) * coreMass h L x +
        (αh - A₀) * ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) =
      collarMass h L x +
        (A₀ * ((∫ u in Ioc 0 (L - 2 * x), h u ^ 2) + ∫ v in Ioc (2 * x) L, h v ^ 2) +
          B₀ * coreMass h L x) +
        (αh * (∫ v in Ioc x (2 * x), h v ^ 2) - βh * (∫ u in Ioc 0 x, h u ^ 2)) +
        (αh * (∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) - βh * (∫ v in Ioc (L - x) L, h v ^ 2)) +
        (αh - A₀) * coreMass h L x := by
    have h1 : (∫ u in Ioc 0 (L - 2 * x), h u ^ 2) =
        (∫ u in Ioc 0 x, h u ^ 2) + coreMass h L x - ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2 := by
      linarith [hsq_union1]
    have h2 : (∫ v in Ioc (2 * x) L, h v ^ 2) =
        coreMass h L x + (∫ v in Ioc (L - x) L, h v ^ 2) - ∫ v in Ioc x (2 * x), h v ^ 2 := by
      linarith [hsq_union2]
    rw [← hcol_eq, h1, h2]
    ring
  have hcol_int := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
  linarith

/-- Pointwise 3-point harmonic-doubling SOS inequality for `θ = 1 / 3` (`A₀ = 1 / 6, B₀ = 1 / 4`),
proved via `RHS - LHS = (1 / 3) * (p - (3 / 2) * q + r) ^ 2 ≥ 0`. -/
theorem one_sixth_add_quarter_le_half_jump_add_third_mul (p q r : ℝ) :
    (1 / 6 : ℝ) * (p ^ 2 + r ^ 2) + (1 / 4 : ℝ) * q ^ 2 ≤
      (1 / 2 : ℝ) * (p - q) ^ 2 + (1 / 2 : ℝ) * (q - r) ^ 2 + (1 / 3 : ℝ) * (2 * (p * r)) := by
  have hid : ((1 / 2 : ℝ) * (p - q) ^ 2 + (1 / 2 : ℝ) * (q - r) ^ 2 + (1 / 3 : ℝ) * (2 * (p * r))) -
      ((1 / 6 : ℝ) * (p ^ 2 + r ^ 2) + (1 / 4 : ℝ) * q ^ 2) =
      (1 / 3 : ℝ) * (p - (3 / 2 : ℝ) * q + r) ^ 2 := by ring
  nlinarith [sq_nonneg (p - (3 / 2 : ℝ) * q + r)]

/-- Pointwise 2-point collar-to-core SOS inequality for `αh = 1 / 4, βh = 1 / 2`,
proved via `(1 / 2) * (a - b) ^ 2 - ((1 / 4) * a ^ 2 - (1 / 2) * b ^ 2) = (1 / 4) * (a - 2 * b) ^ 2 ≥ 0`. -/
theorem one_quarter_sq_sub_half_sq_le_half_sub_sq (a b : ℝ) :
    (1 / 4 : ℝ) * a ^ 2 - (1 / 2 : ℝ) * b ^ 2 ≤ (1 / 2 : ℝ) * (a - b) ^ 2 := by
  nlinarith [sq_nonneg (a - 2 * b)]

/-- **Theorem 1A — Support-Aware Quarter-Window Harmonic-Doubling Coercivity (`θ = 1 / 3`, `x ≥ L / 4`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and **every shift `x ≥ L / 4`**,
`(2 / 3 : ℝ) * (∫ u, h u ^ 2) ≤ (∫ u, (h u - h (u + x)) ^ 2) + (1 / 3 : ℝ) * (2 * autocorr h (2 * x))`. -/
theorem two_thirds_mul_integral_sq_le_integral_jump_sq_add_third_autocorr_of_quarter_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx4 : L / 4 ≤ x) :
    (2 / 3 : ℝ) * (∫ u, h u ^ 2) ≤
      (∫ u, (h u - h (u + x)) ^ 2) + (1 / 3 : ℝ) * (2 * autocorr h (2 * x)) := by
  rcases le_or_gt x (L / 3) with hx3 | hx3
  · have hq := quarter_three_point_add_two_point_le_integral_jump_sq_add_autocorr_of_quarter_to_third
      (A₀ := 1 / 6) (B₀ := 1 / 4) (θ := 1 / 3) (αh := 1 / 4) (βh := 1 / 2)
      hh hsupp hL0 hx4 hx3 (by norm_num)
      one_sixth_add_quarter_le_half_jump_add_third_mul
      one_quarter_sq_sub_half_sq_le_half_sub_sq
    have hcons := collarMass_add_coreMass_eq hh (by linarith : x ≤ L / 2)
    linarith
  · have h1 := integral_sq_le_integral_jump_sq_add_two_mul_autocorr_two_mul_of_third_le
      hh hsupp hL0 hx3.le
    have h2 := twenty_four_forty_firsts_mul_integral_sq_le_integral_jump_sq_of_third_le
      hh hsupp hL0 hx3.le
    have hE0 : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith

/-- Pointwise 3-point harmonic-doubling SOS inequality for `θ = 2 / 5` (`A₀ = 1 / 10, B₀ = 3 / 8`),
proved via `RHS - LHS = (2 / 5) * (p - (5 / 4) * q + r) ^ 2 ≥ 0`. -/
theorem one_tenth_add_three_eighths_le_half_jump_add_two_fifths_mul (p q r : ℝ) :
    (1 / 10 : ℝ) * (p ^ 2 + r ^ 2) + (3 / 8 : ℝ) * q ^ 2 ≤
      (1 / 2 : ℝ) * (p - q) ^ 2 + (1 / 2 : ℝ) * (q - r) ^ 2 + (2 / 5 : ℝ) * (2 * (p * r)) := by
  have hid : ((1 / 2 : ℝ) * (p - q) ^ 2 + (1 / 2 : ℝ) * (q - r) ^ 2 + (2 / 5 : ℝ) * (2 * (p * r))) -
      ((1 / 10 : ℝ) * (p ^ 2 + r ^ 2) + (3 / 8 : ℝ) * q ^ 2) =
      (2 / 5 : ℝ) * (p - (5 / 4 : ℝ) * q + r) ^ 2 := by ring
  nlinarith [sq_nonneg (p - (5 / 4 : ℝ) * q + r)]

/-- Pointwise 2-point collar-to-core SOS inequality for `αh = 2 / 9, βh = 2 / 5`,
proved via `(1 / 2) * (a - b) ^ 2 - ((2 / 9) * a ^ 2 - (2 / 5) * b ^ 2) = (5 / 18) * (a - (9 / 5) * b) ^ 2 ≥ 0`. -/
theorem two_ninths_sq_sub_two_fifths_sq_le_half_sub_sq (a b : ℝ) :
    (2 / 9 : ℝ) * a ^ 2 - (2 / 5 : ℝ) * b ^ 2 ≤ (1 / 2 : ℝ) * (a - b) ^ 2 := by
  nlinarith [sq_nonneg (a - (9 / 5 : ℝ) * b)]

/-- **Theorem 1B — Support-Aware Quarter-Window Harmonic-Doubling Coercivity (`θ = 2 / 5`, `x ≥ L / 4`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and **every shift `x ≥ L / 4`**,
`(251 / 360 : ℝ) * (∫ u, h u ^ 2) ≤ (∫ u, (h u - h (u + x)) ^ 2) + (2 / 5 : ℝ) * (2 * autocorr h (2 * x))`. -/
theorem two_fifty_one_three_sixtieths_mul_integral_sq_le_integral_jump_sq_add_two_fifths_autocorr_of_quarter_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx4 : L / 4 ≤ x) :
    (251 / 360 : ℝ) * (∫ u, h u ^ 2) ≤
      (∫ u, (h u - h (u + x)) ^ 2) + (2 / 5 : ℝ) * (2 * autocorr h (2 * x)) := by
  rcases le_or_gt x (L / 3) with hx3 | hx3
  · have hq := quarter_three_point_add_two_point_le_integral_jump_sq_add_autocorr_of_quarter_to_third
      (A₀ := 1 / 10) (B₀ := 3 / 8) (θ := 2 / 5) (αh := 2 / 9) (βh := 2 / 5)
      hh hsupp hL0 hx4 hx3 (by norm_num)
      one_tenth_add_three_eighths_le_half_jump_add_two_fifths_mul
      two_ninths_sq_sub_two_fifths_sq_le_half_sub_sq
    have hcol0 : 0 ≤ collarMass h L x := collarMass_nonneg h L x
    have hcons := collarMass_add_coreMass_eq hh (by linarith : x ≤ L / 2)
    linarith
  · have h1 := integral_sq_le_integral_jump_sq_add_two_mul_autocorr_two_mul_of_third_le
      hh hsupp hL0 hx3.le
    have h2 := twenty_four_forty_firsts_mul_integral_sq_le_integral_jump_sq_of_third_le
      hh hsupp hL0 hx3.le
    have hE0 : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith

/-! ## Section 2: Universal Fejér–Bochner Jump-Doubling (`D_h(2x) ≤ 4 D_h(x)`), Dyadic Sub-Tenth Coercivity on `[L / 20, L / 10]`, and the Sharpened `(0, log 2)` Plastic Floor (`-0.0033`) -/

/-- **Universal Fejér–Bochner `L²(ℝ)` Jump-Doubling Law (`D_h(2x) ≤ 4 D_h(x)`)**:
for **every** `BddSupp A h C` and **every** `x : ℝ` (with no support restriction!),
`(∫ u, (h u - h (u + 2 * x)) ^ 2) ≤ 4 * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem integral_jump_sq_two_mul_le_four_mul {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ}
    (hh : BddSupp A h C) (x : ℝ) :
    (∫ u, (h u - h (u + 2 * x)) ^ 2) ≤ 4 * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hsq : Integrable (fun u : ℝ => h u ^ 2) := hh.integrable_sq
  have hjump : ∀ y : ℝ, Integrable (fun u : ℝ => (h u - h (u + y)) ^ 2) := fun y => by
    refine ((hsq.add (hsq.comp_add_right y)).sub
      ((hh.integrable_mul_shift y).const_mul 2)).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  have hjump1 : Integrable (fun u : ℝ => (h (u + x) - h (u + 2 * x)) ^ 2) := by
    refine ((hjump x).comp_add_right x).congr (ae_of_all _ fun u => ?_)
    dsimp only; congr 3; ring
  have hint := integral_mono (hjump (2 * x))
    (((hjump x).const_mul 2).add (hjump1.const_mul 2)) fun u => by
      dsimp only [Pi.add_apply]
      nlinarith [sq_nonneg (h u - 2 * h (u + x) + h (u + 2 * x))]
  dsimp only [Pi.add_apply] at hint
  rw [integral_add ((hjump x).const_mul 2) (hjump1.const_mul 2),
    integral_const_mul, integral_const_mul] at hint
  have hshift : (∫ u, (h (u + x) - h (u + 2 * x)) ^ 2) = ∫ u, (h u - h (u + x)) ^ 2 := by
    rw [← integral_add_right_eq_self (μ := volume) (fun v : ℝ => (h v - h (v + x)) ^ 2) x]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    dsimp only; congr 3; ring
  linarith

/-- **Twelfth-Window Coercivity (`(7 / 144) ∫ h² ≤ D_h(x)` for all `x ≥ L / 12`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and every `x ≥ L / 12`,
`(7 / 144 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem seven_one_forty_fourths_mul_integral_sq_le_integral_jump_sq_of_twelfth_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx : L / 12 ≤ x) :
    (7 / 144 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  have h6 := seven_thirty_sixths_mul_integral_sq_le_integral_jump_sq_of_sixth_le
    hh hsupp hL0 (by linarith : L / 6 ≤ 2 * x)
  have hd := integral_jump_sq_two_mul_le_four_mul hh x
  linarith

/-- **Fourteenth-Window Coercivity (`(3 / 80) ∫ h² ≤ D_h(x)` for all `x ≥ L / 14`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and every `x ≥ L / 14`,
`(3 / 80 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem three_eightieths_mul_integral_sq_le_integral_jump_sq_of_fourteenth_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx : L / 14 ≤ x) :
    (3 / 80 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  have h7 := three_twentieths_mul_integral_sq_le_integral_jump_sq_of_seventh_le
    hh hsupp hL0 (by linarith : L / 7 ≤ 2 * x)
  have hd := integral_jump_sq_two_mul_le_four_mul hh x
  linarith

/-- **Sixteenth-Window Coercivity (`(3 / 100) ∫ h² ≤ D_h(x)` for all `x ≥ L / 16`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and every `x ≥ L / 16`,
`(3 / 100 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem three_hundredths_mul_integral_sq_le_integral_jump_sq_of_sixteenth_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx : L / 16 ≤ x) :
    (3 / 100 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  have h8 := three_twenty_fifths_mul_integral_sq_le_integral_jump_sq_of_eighth_le
    hh hsupp hL0 (by linarith : L / 8 ≤ 2 * x)
  have hd := integral_jump_sq_two_mul_le_four_mul hh x
  linarith

/-- **Twentieth-Window Coercivity (`(1 / 50) ∫ h² ≤ D_h(x)` for all `x ≥ L / 20`)**:
for any signed `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and every `x ≥ L / 20`,
`(1 / 50 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem one_fiftieth_mul_integral_sq_le_integral_jump_sq_of_twentieth_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL0 : 0 ≤ L) (hx : L / 20 ≤ x) :
    (1 / 50 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  have h10 := two_twenty_fifths_mul_integral_sq_le_integral_jump_sq_of_tenth_le
    hh hsupp hL0 (by linarith : L / 10 ≤ 2 * x)
  have hd := integral_jump_sq_two_mul_le_four_mul hh x
  linarith

/-- Parametric shell integration lemma: if `c₀ * ∫ h² ≤ D_h(x)` for all `x ∈ Ioo a b`
(`0 < a ≤ b ≤ screwSignThreshold`), then
`(c₀ / 2) * (Φ(a) - Φ(b)) * ∫ h² ≤ ∫_{x ∈ Ioo a b} (-K(x)) D_h(x)`. -/
theorem half_const_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C a b c₀ : ℝ} (hh : BddSupp A h C)
    (ha0 : 0 < a) (hab : a ≤ b) (hbt : b ≤ screwSignThreshold)
    (hcoerc : ∀ x ∈ Ioo a b, c₀ * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2) :
    (c₀ / 2) * (levyCoshPotential a - levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo a b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
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
  have hI_lhs : IntegrableOn
      (fun x : ℝ => c₀ * (-screwRegularKernel x) * ∫ u, h u ^ 2) (Ioo a b) :=
    (hI_K.const_mul c₀).mul_const _
  have hmono : (∫ x in Ioo a b, c₀ * (-screwRegularKernel x) * ∫ u, h u ^ 2) ≤
      ∫ x in Ioo a b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
    refine setIntegral_mono_on hI_lhs hI_jump measurableSet_Ioo fun x hx => ?_
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hbt))
    have hm := mul_le_mul_of_nonneg_left (hcoerc x hx) hK0
    linarith
  rw [integral_mul_const, integral_const_mul, setIntegral_Ioo_neg_screwRegularKernel ha0 hab] at hmono
  linarith

/-- **Four-Shell Dyadic Sub-Tenth Potential Bound on `Ioo (L / 20) (L / 10)` (`L / 10 ≤ screwSignThreshold`)**:
combining `Ioo (L / 20) (L / 16)`, `Ioo (L / 16) (L / 14)`, `Ioo (L / 14) (L / 12)`, and `Ioo (L / 12) (L / 10)` yields:
`((1 / 100) * Φ(L / 20) + (1 / 200) * Φ(L / 16) + (3 / 800) * Φ(L / 14) + (1 / 180) * Φ(L / 12) - (7 / 288) * Φ(L / 10)) * ∫ h² ≤ ∫_{x ∈ Ioo (L / 20) (L / 10)} (-K(x)) D_h(x)`. -/
theorem twentieth_to_tenth_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL : 0 < L) (hL10t : L / 10 ≤ screwSignThreshold) :
    ((1 / 100 : ℝ) * levyCoshPotential (L / 20) +
        (1 / 200 : ℝ) * levyCoshPotential (L / 16) +
        (3 / 800 : ℝ) * levyCoshPotential (L / 14) +
        (1 / 180 : ℝ) * levyCoshPotential (L / 12) -
        (7 / 288 : ℝ) * levyCoshPotential (L / 10)) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 20) (L / 10),
        (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have h20_pos : 0 < L / 20 := by linarith
  have h16_pos : 0 < L / 16 := by linarith
  have h14_pos : 0 < L / 14 := by linarith
  have h12_pos : 0 < L / 12 := by linarith
  have h20_16 : L / 20 ≤ L / 16 := by linarith
  have h16_14 : L / 16 ≤ L / 14 := by linarith
  have h14_12 : L / 14 ≤ L / 12 := by linarith
  have h12_10 : L / 12 ≤ L / 10 := by linarith
  have h20_14 : L / 20 ≤ L / 14 := le_trans h20_16 h16_14
  have h14_10 : L / 14 ≤ L / 10 := le_trans h14_12 h12_10
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 20) (L / 10)) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le h20_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 20) (L / 10)) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans h20_pos hx.1) (hx.2.le.trans hL10t))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_1 : IntegrableOn F (Ioc (L / 20) (L / 16)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl (h16_14.trans h14_10))
  have hIF_2 : IntegrableOn F (Ioc (L / 16) (L / 14)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo h20_16 h14_10)
  have hIF_3 : IntegrableOn F (Ioc (L / 14) (L / 12)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo h20_14 h12_10)
  have hIF_4 : IntegrableOn F (Ioc (L / 12) (L / 10)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo (h20_14.trans h14_12) le_rfl)
  have hIF_12 : IntegrableOn F (Ioc (L / 20) (L / 14)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl h14_10)
  have hIF_34 : IntegrableOn F (Ioc (L / 14) (L / 10)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo h20_14 le_rfl)
  have hdisj_12 : Disjoint (Ioc (L / 20) (L / 16)) (Ioc (L / 16) (L / 14)) :=
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_34 : Disjoint (Ioc (L / 14) (L / 12)) (Ioc (L / 12) (L / 10)) :=
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_1234 : Disjoint (Ioc (L / 20) (L / 14)) (Ioc (L / 14) (L / 10)) :=
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 20) (L / 10), F x) =
      (∫ x in Ioo (L / 20) (L / 16), F x) +
        (∫ x in Ioo (L / 16) (L / 14), F x) +
        (∫ x in Ioo (L / 14) (L / 12), F x) +
        ∫ x in Ioo (L / 12) (L / 10), F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc h20_14 h14_10,
      setIntegral_union hdisj_1234 measurableSet_Ioc hIF_12 hIF_34,
      ← Ioc_union_Ioc_eq_Ioc h20_16 h16_14,
      setIntegral_union hdisj_12 measurableSet_Ioc hIF_1 hIF_2,
      ← Ioc_union_Ioc_eq_Ioc h14_12 h12_10,
      setIntegral_union hdisj_34 measurableSet_Ioc hIF_3 hIF_4]
    repeat rw [integral_Ioc_eq_integral_Ioo]
    ring
  have h1 := half_const_mul_sub_levyCoshPotential_le_setIntegral_Ioo (c₀ := 1 / 50)
    hh h20_pos h20_16 (h16_14.trans (h14_10.trans hL10t))
    (fun x hx => one_fiftieth_mul_integral_sq_le_integral_jump_sq_of_twentieth_le hh hsupp hL.le hx.1.le)
  have h2 := half_const_mul_sub_levyCoshPotential_le_setIntegral_Ioo (c₀ := 3 / 100)
    hh h16_pos h16_14 (h14_10.trans hL10t)
    (fun x hx => three_hundredths_mul_integral_sq_le_integral_jump_sq_of_sixteenth_le hh hsupp hL.le hx.1.le)
  have h3 := half_const_mul_sub_levyCoshPotential_le_setIntegral_Ioo (c₀ := 3 / 80)
    hh h14_pos h14_12 (h12_10.trans hL10t)
    (fun x hx => three_eightieths_mul_integral_sq_le_integral_jump_sq_of_fourteenth_le hh hsupp hL.le hx.1.le)
  have h4 := half_const_mul_sub_levyCoshPotential_le_setIntegral_Ioo (c₀ := 7 / 144)
    hh h12_pos h12_10 hL10t
    (fun x hx => seven_one_forty_fourths_mul_integral_sq_le_integral_jump_sq_of_twelfth_le hh hsupp hL.le hx.1.le)
  dsimp only [F] at hsplit
  linarith

/-- **Nine-Shell Potential Coercivity on `Ioo (L / 20) (L / 4)` (`L / 4 ≤ screwSignThreshold`)**:
combining `twentieth_to_tenth_sub_levyCoshPotential_le_setIntegral_Ioo` on `Ioo (L / 20) (L / 10)`
with `tenth_to_fifth_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo` on `Ioo (L / 10) (L / 4)` yields:
`((1 / 100) * Φ(L / 20) + (1 / 200) * Φ(L / 16) + (3 / 800) * Φ(L / 14) + (1 / 180) * Φ(L / 12) + (113 / 7200) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) - (2 / 15) * Φ(L / 4)) * ∫ h² ≤ ∫_{x ∈ Ioo (L / 20) (L / 4)} (-K(x)) D_h(x)`. -/
theorem twentieth_to_quarter_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hL : 0 < L) (hL4t : L / 4 ≤ screwSignThreshold) :
    ((1 / 100 : ℝ) * levyCoshPotential (L / 20) +
        (1 / 200 : ℝ) * levyCoshPotential (L / 16) +
        (3 / 800 : ℝ) * levyCoshPotential (L / 14) +
        (1 / 180 : ℝ) * levyCoshPotential (L / 12) +
        (113 / 7200 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (3 / 200 : ℝ) * levyCoshPotential (L / 7) +
        (1 / 45 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) -
        (2 / 15 : ℝ) * levyCoshPotential (L / 4)) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 20) (L / 4),
        (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have h20_pos : 0 < L / 20 := by linarith
  have h20_10 : L / 20 ≤ L / 10 := by linarith
  have h10_4 : L / 10 ≤ L / 4 := by linarith
  have h5_4 : L / 5 ≤ L / 4 := by linarith
  have h10_t : L / 10 ≤ screwSignThreshold := le_trans h10_4 hL4t
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 20) (L / 4)) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le h20_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 20) (L / 4)) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans h20_pos hx.1) (hx.2.le.trans hL4t))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_1 : IntegrableOn F (Ioc (L / 20) (L / 10)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl h10_4)
  have hIF_2 : IntegrableOn F (Ioc (L / 10) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo h20_10 le_rfl)
  have hdisj : Disjoint (Ioc (L / 20) (L / 10)) (Ioc (L / 10) (L / 4)) :=
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 20) (L / 4), F x) =
      (∫ x in Ioo (L / 20) (L / 10), F x) + ∫ x in Ioo (L / 10) (L / 4), F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc h20_10 h10_4,
      setIntegral_union hdisj measurableSet_Ioc hIF_1 hIF_2,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h1 := twentieth_to_tenth_sub_levyCoshPotential_le_setIntegral_Ioo hh hsupp hL h10_t
  have h2 := tenth_to_fifth_with_seventh_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL h5_4 hL4t
  dsimp only [F] at hsplit
  linarith

/-- **Harmonic-Doubling Crossing Inequality at `b = 1 / 6` for `θ = 2 / 5`**:
`(2 / 5 : ℝ) * (-screwRegularKernel (1 / 6)) ≤ 2 * screwRegularKernel (1 / 3)`. -/
theorem two_fifths_mul_neg_screwRegularKernel_sixth_le_two_mul_screwRegularKernel_third :
    (2 / 5 : ℝ) * (-screwRegularKernel (1 / 6)) ≤ 2 * screwRegularKernel (1 / 3) := by
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
  have hpoly : (2 / 5 : ℝ) * (u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6)) ≤
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

/-- For every `x ≥ 1 / 6`, `(2 / 5 : ℝ) * (-screwRegularKernel x) ≤ 2 * screwRegularKernel (2 * x)`. -/
theorem two_fifths_mul_neg_screwRegularKernel_le_two_mul_screwRegularKernel_two_mul_of_sixth_le
    {x : ℝ} (hx : 1 / 6 ≤ x) :
    (2 / 5 : ℝ) * (-screwRegularKernel x) ≤ 2 * screwRegularKernel (2 * x) := by
  have hx0 : 0 < x := by linarith
  have h1 : screwRegularKernel (1 / 6) ≤ screwRegularKernel x :=
    monotoneOn_screwRegularKernel (by norm_num : (0 : ℝ) < 1 / 6) hx0 hx
  have h2 : screwRegularKernel (1 / 3) ≤ screwRegularKernel (2 * x) :=
    monotoneOn_screwRegularKernel (by norm_num : (0 : ℝ) < 1 / 3) (by linarith : 0 < 2 * x)
      (by linarith)
  linarith [two_fifths_mul_neg_screwRegularKernel_sixth_le_two_mul_screwRegularKernel_third]

/-- **Support-Aware `(251 / 360)` Quarter-Window Harmonic-Doubling Shell Bound on `Ioo a b` (`L / 4 ≤ a`, `1 / 6 ≤ a ≤ b ≤ screwSignThreshold`)**:
`(251 / 720 : ℝ) * (Φ(a) - Φ(b)) * ∫ h² ≤ (∫_{x ∈ Ioo a b} (-K(x)) D_h(x)) + ∫_{x ∈ Ioo a b} (2 K(2x)) (2 R(2x))`. -/
theorem two_fifty_one_seven_twentieths_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_double_autocorr
    {A : Set ℝ} {h : ℝ → ℝ} {C L a b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u) (hL : 0 < L)
    (ha4 : L / 4 ≤ a) (ha6 : 1 / 6 ≤ a) (hab : a ≤ b) (hbt : b ≤ screwSignThreshold) :
    (251 / 720 : ℝ) * (levyCoshPotential a - levyCoshPotential b) * (∫ u, h u ^ 2) ≤
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
      have hcr := two_fifths_mul_neg_screwRegularKernel_le_two_mul_screwRegularKernel_two_mul_of_sixth_le
        (ha6.trans hx.1.le)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK2_0 (hR0 x))]
    have hR_le : 2 * autocorr h (2 * x) ≤ 2 * ∫ u, h u ^ 2 := by
      have hid := integral_jump_sq hh (2 * x)
      have hD_nn := hD0 (2 * x)
      linarith
    exact mul_le_mul_of_nonneg_left hR_le hK2_0
  have hI_lhs : IntegrableOn
      (fun x : ℝ => (251 / 360 : ℝ) * (-screwRegularKernel x) * ∫ u, h u ^ 2) (Ioo a b) :=
    (hI_K.const_mul (251 / 360 : ℝ)).mul_const _
  have hmono : (∫ x in Ioo a b, (251 / 360 : ℝ) * (-screwRegularKernel x) * ∫ u, h u ^ 2) ≤
      ∫ x in Ioo a b, ((-screwRegularKernel x) * (∫ u, (h u - h (u + x)) ^ 2) +
        (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))) := by
    refine setIntegral_mono_on hI_lhs (hI_jump.add hI_auto) measurableSet_Ioo fun x hx => ?_
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans ha0 hx.1) (hx.2.le.trans hbt))
    have hhd :=
      two_fifty_one_three_sixtieths_mul_integral_sq_le_integral_jump_sq_add_two_fifths_autocorr_of_quarter_le
        hh hsupp hL.le (ha4.trans hx.1.le)
    have h1 := mul_le_mul_of_nonneg_left hhd hK0
    have h2 : (-screwRegularKernel x) * ((2 / 5 : ℝ) * (2 * autocorr h (2 * x))) ≤
        (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x)) := by
      have hcr := two_fifths_mul_neg_screwRegularKernel_le_two_mul_screwRegularKernel_two_mul_of_sixth_le
        (ha6.trans hx.1.le)
      nlinarith [hR0 x]
    linarith
  rw [integral_mul_const, integral_const_mul, setIntegral_Ioo_neg_screwRegularKernel ha0 hab,
    integral_add hI_jump hI_auto] at hmono
  linarith

/-- **Upgraded Eleven-Shell Dyadic + Quarter Harmonic-Doubling Potential + Pair Coercivity for `2 / 3 ≤ L ≤ 3 * screwSignThreshold`**:
combining the 4 dyadic sub-tenth shells on `[L / 20, L / 10]` with the `(251 / 360)` quarter-window
harmonic-doubling shell on `[L / 4, L / 3]` and full harmonic doubling on `[L / 3, screwSignThreshold]`! -/
theorem twentieth_to_quarter_harmonic_doubling_sub_levyCoshPotential_le_setIntegral_Ioo_add_pair
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hh0 : ∀ u, 0 ≤ h u)
    (hL_two_thirds : 2 / 3 ≤ L) (hL3t : L / 3 ≤ screwSignThreshold) :
    ((1 / 100 : ℝ) * levyCoshPotential (L / 20) +
        (1 / 200 : ℝ) * levyCoshPotential (L / 16) +
        (3 / 800 : ℝ) * levyCoshPotential (L / 14) +
        (1 / 180 : ℝ) * levyCoshPotential (L / 12) +
        (113 / 7200 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (3 / 200 : ℝ) * levyCoshPotential (L / 7) +
        (1 / 45 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (31 / 144 : ℝ) * levyCoshPotential (L / 4) +
        (109 / 720 : ℝ) * levyCoshPotential (L / 3) -
        (1 / 2 : ℝ) * levyCoshPotential screwSignThreshold) * (∫ u, h u ^ 2) ≤
      (∫ x in Ioo (L / 20) screwSignThreshold,
        (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ p : ℝ × ℝ, h p.1 * h p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) := by
  have hL0 : 0 < L := by linarith
  have hL20_pos : 0 < L / 20 := by linarith
  have hL4_pos : 0 < L / 4 := by linarith
  have hL20_4 : L / 20 ≤ L / 4 := by linarith
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
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 20) screwSignThreshold) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL20_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 20) screwSignThreshold) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL20_pos hx.1) hx.2.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_1 : IntegrableOn F (Ioc (L / 20) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL4_t)
  have hIF_2 : IntegrableOn F (Ioc (L / 4) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL20_4 hL3t)
  have hIF_3 : IntegrableOn F (Ioc (L / 3) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo (hL20_4.trans hL4_3) le_rfl)
  have hIF_12 : IntegrableOn F (Ioc (L / 20) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL3t)
  have hdisj_12 : Disjoint (Ioc (L / 20) (L / 4)) (Ioc (L / 4) (L / 3)) :=
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_123 : Disjoint (Ioc (L / 20) (L / 3)) (Ioc (L / 3) screwSignThreshold) :=
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit_F : (∫ x in Ioo (L / 20) screwSignThreshold, F x) =
      (∫ x in Ioo (L / 20) (L / 4), F x) + (∫ x in Ioo (L / 4) (L / 3), F x) +
        ∫ x in Ioo (L / 3) screwSignThreshold, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (hL20_4.trans hL4_3) hL3t,
      setIntegral_union hdisj_123 measurableSet_Ioc hIF_12 hIF_3,
      ← Ioc_union_Ioc_eq_Ioc hL20_4 hL4_3,
      setIntegral_union hdisj_12 measurableSet_Ioc hIF_1 hIF_2,
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
  have hIH_left : IntegrableOn H (Ioc (L / 4) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIH.mono_set (Ioo_subset_Ioo le_rfl hL3t)
  have hIH_right : IntegrableOn H (Ioc (L / 3) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIH.mono_set (Ioo_subset_Ioo hL4_3 le_rfl)
  have hdisj_23 : Disjoint (Ioc (L / 4) (L / 3)) (Ioc (L / 3) screwSignThreshold) :=
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit_H : (∫ x in Ioo (L / 4) screwSignThreshold, H x) =
      (∫ x in Ioo (L / 4) (L / 3), H x) + ∫ x in Ioo (L / 3) screwSignThreshold, H x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL4_3 hL3t,
      setIntegral_union hdisj_23 measurableSet_Ioc hIH_left hIH_right,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h20_4 := twentieth_to_quarter_sub_levyCoshPotential_le_setIntegral_Ioo hh hsupp hL0 hL4_t
  have h4 := two_fifty_one_seven_twentieths_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_double_autocorr
    hh hsupp hh0 hL0 le_rfl (by linarith : 1 / 6 ≤ L / 4) hL4_3 hL3t
  have h3 := half_mul_sub_levyCoshPotential_le_setIntegral_Ioo_add_double_autocorr
    hh hsupp hh0 hL0 (by linarith : 3 / 16 ≤ L / 3) le_rfl hL3t le_rfl
  have hpair := setIntegral_Ioo_two_mul_screwRegularKernel_two_mul_autocorr_le_pair
    hh hsupp hh0 hL0 le_rfl ht_L2 hL4_t
  dsimp only [F] at hsplit_F
  dsimp only [H] at hsplit_H
  linarith

/-- **Upgraded Eleven-Shell Dyadic + Quarter Harmonic-Doubling Plastic-Floor Theorem (`2 / 3 ≤ L ≤ 3 * screwSignThreshold`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`2 / 3 ≤ L`, `L / 3 ≤ screwSignThreshold`),
`(A(0) + (1 / 100) * Φ(L / 20) + (1 / 200) * Φ(L / 16) + (3 / 800) * Φ(L / 14) + (1 / 180) * Φ(L / 12) + (113 / 7200) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (31 / 144) * Φ(L / 4) + (109 / 720) * Φ(L / 3) + (1 / 2) * Φ(screwSignThreshold)) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem dyadic_quarter_harmonic_doubling_plastic_floor_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL_two_thirds : 2 / 3 ≤ L) (hL3t : L / 3 ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 100) * levyCoshPotential (L / 20) +
        (1 / 200) * levyCoshPotential (L / 16) +
        (3 / 800) * levyCoshPotential (L / 14) +
        (1 / 180) * levyCoshPotential (L / 12) +
        (113 / 7200) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (3 / 200) * levyCoshPotential (L / 7) +
        (1 / 45) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (31 / 144) * levyCoshPotential (L / 4) +
        (109 / 720) * levyCoshPotential (L / 3) +
        (1 / 2) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL20 : 0 < L / 20 := by linarith
  have hL20t : L / 20 ≤ screwSignThreshold := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL20 hL20t le_rfl
  have hjump := twentieth_to_quarter_harmonic_doubling_sub_levyCoshPotential_le_setIntegral_Ioo_add_pair
    hB hsupp hf0 hL_two_thirds hL3t
  linarith

/-- **Specialization of the Upgraded Eleven-Shell Plastic Floor to `L = log 2`**:
reduces the universal `(0, log 2)` constant deficit from `-0.0080` down to **`-0.0033`**. -/
theorem dyadic_quarter_harmonic_doubling_plastic_floor_log_two_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hsupp : ∀ u ∉ Ioo 0 (Real.log 2), f u = 0) :
    (EF.gammaBracket 0 + (1 / 100) * levyCoshPotential (Real.log 2 / 20) +
        (1 / 200) * levyCoshPotential (Real.log 2 / 16) +
        (3 / 800) * levyCoshPotential (Real.log 2 / 14) +
        (1 / 180) * levyCoshPotential (Real.log 2 / 12) +
        (113 / 7200) * levyCoshPotential (Real.log 2 / 10) +
        (1 / 50) * levyCoshPotential (Real.log 2 / 8) +
        (3 / 200) * levyCoshPotential (Real.log 2 / 7) +
        (1 / 45) * levyCoshPotential (Real.log 2 / 6) +
        (13 / 360) * levyCoshPotential (Real.log 2 / 5) +
        (31 / 144) * levyCoshPotential (Real.log 2 / 4) +
        (109 / 720) * levyCoshPotential (Real.log 2 / 3) +
        (1 / 2) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  dyadic_quarter_harmonic_doubling_plastic_floor_le_weilArchRe hf hfc hf0
    (by linarith [Real.log_two_gt_d9])
    (by linarith [Real.log_two_lt_d9, screwSignThreshold_gt_6036_over_21509])
    hsupp

/-! ## Section 3: Crossing Ratio at `4 / 25`, Fifteen-Point Potential, and Unconditional `WindowPositive` on `(0, 12 / 25)` (`= (0, 0.48)`, `69.25%` of `(0, log 2)`) -/

/-- Rational lower bound `677 / 625 ≤ Real.exp (2 / 25)` via `one_add_add_half_sq_le_exp`. -/
theorem exp_two_twenty_fifths_ge : (677 : ℝ) / 625 ≤ Real.exp (2 / 25) := by
  have h := one_add_add_half_sq_le_exp (by norm_num : (0 : ℝ) ≤ 2 / 25)
  linarith

/-- Rational upper bound `Real.exp (2 / 25) ≤ 13 / 12` via `one_sub_exp_neg_half_le` at `4 / 25`. -/
theorem exp_two_twenty_fifths_le : Real.exp (2 / 25) ≤ (13 : ℝ) / 12 := by
  have h := one_sub_exp_neg_half_le (by norm_num : (0 : ℝ) ≤ 4 / 25)
  rw [show -(4 / 25 : ℝ) / 2 = -(2 / 25 : ℝ) by ring, Real.exp_neg] at h
  have hexp : 0 < Real.exp (2 / 25) := Real.exp_pos _
  have hm := mul_le_mul_of_nonneg_right h hexp.le
  have hcancel : (Real.exp (2 / 25))⁻¹ * Real.exp (2 / 25) = 1 := inv_mul_cancel₀ hexp.ne'
  nlinarith

/-- **Quarter-Window Harmonic-Doubling Crossing Ratio at `b = 4 / 25` (`2 * b = 8 / 25`)**:
`3 * (2 * screwRegularKernel (8 / 25)) ≤ -screwRegularKernel (4 / 25)`. -/
theorem three_mul_two_mul_screwRegularKernel_eight_twenty_fifths_le_neg_screwRegularKernel_four_twenty_fifths :
    3 * (2 * screwRegularKernel (8 / 25)) ≤ -screwRegularKernel (4 / 25) := by
  have hb : (0 : ℝ) < 4 / 25 := by norm_num
  have h1 := neg_screwRegularKernel_mul_eq_of_pos hb
  have h2 := two_mul_screwRegularKernel_two_mul_eq_of_pos hb
  dsimp only at h1 h2
  rw [show (2 : ℝ) * (4 / 25) = 8 / 25 by norm_num] at h2
  rw [show (4 / 25 : ℝ) / 2 = 2 / 25 by norm_num] at h1 h2
  set u := Real.exp (2 / 25)
  have hu_ge : (677 : ℝ) / 625 ≤ u := exp_two_twenty_fifths_ge
  have hu_le : u ≤ (13 : ℝ) / 12 := exp_two_twenty_fifths_le
  have hden : 0 < u ^ 10 - u ^ 2 := by
    have : ((677 : ℝ) / 625) ^ 10 ≤ u ^ 10 := pow_le_pow_left₀ (by norm_num) hu_ge 10
    have : u ^ 2 ≤ ((13 : ℝ) / 12) ^ 2 := pow_le_pow_left₀ (by linarith) hu_le 2
    linarith
  have hpoly : 3 * (2 * (u ^ 12 - u ^ 4 - 1)) ≤
      u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6) := by
    have hp12 : u ^ 12 ≤ ((13 : ℝ) / 12) ^ 12 := pow_le_pow_left₀ (by linarith) hu_le 12
    have hp4_ge : ((677 : ℝ) / 625) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu_ge 4
    have hp6_le : u ^ 6 ≤ ((13 : ℝ) / 12) ^ 6 := pow_le_pow_left₀ (by linarith) hu_le 6
    have hp2_ge : ((677 : ℝ) / 625) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu_ge 2
    have hfac1_ge : (677 / 625 : ℝ) * (((677 : ℝ) / 625) ^ 4 + 1) ≤ u * (u ^ 4 + 1) := by
      nlinarith
    have hfac2_ge : 0 ≤ 1 + ((677 : ℝ) / 625) ^ 2 - ((13 : ℝ) / 12) ^ 6 := by norm_num
    have hprod : (677 / 625 : ℝ) * (((677 : ℝ) / 625) ^ 4 + 1) *
        (1 + ((677 : ℝ) / 625) ^ 2 - ((13 : ℝ) / 12) ^ 6) ≤
        u * (u ^ 4 + 1) * (1 + u ^ 2 - u ^ 6) := by nlinarith
    linarith
  nlinarith

/-- For every `x ∈ (0, 4 / 25]`,
`3 * (2 * screwRegularKernel (2 * x)) ≤ -screwRegularKernel x`. -/
theorem three_mul_two_mul_screwRegularKernel_two_mul_le_neg_screwRegularKernel
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 4 / 25) :
    3 * (2 * screwRegularKernel (2 * x)) ≤ -screwRegularKernel x := by
  have h1 : screwRegularKernel x ≤ screwRegularKernel (4 / 25) :=
    monotoneOn_screwRegularKernel hx0 (by norm_num : (0 : ℝ) < 4 / 25) hx
  have h2 : screwRegularKernel (2 * x) ≤ screwRegularKernel (8 / 25) :=
    monotoneOn_screwRegularKernel (by linarith : 0 < 2 * x) (by norm_num : (0 : ℝ) < 8 / 25)
      (by linarith)
  linarith [three_mul_two_mul_screwRegularKernel_eight_twenty_fifths_le_neg_screwRegularKernel_four_twenty_fifths]

/-- **Upgraded `(3 / 7)` Quarter-Window Harmonic-Doubling Excess Bound on `Ioo a b` (`L / 4 ≤ a ≤ b ≤ 4 / 25`, `screwSignThreshold ≤ 2 * a`)**:
retaining `(8 / 21)` coercivity on the positive kernel excess `(-K(x)) - 3 * (2 * K(2x)) ≥ 0`
and `(2 / 3)` support-aware quarter-window harmonic-doubling coercivity (`θ = 1 / 3`) on `3 * (2 * K(2x)) ≥ 0` proves:
`((4 / 21) * (Φ(a) - Φ(b)) + (3 / 7) * (Φ(2 * b) - Φ(2 * a))) * ∫ h²`
`≤ (∫_{x ∈ Ioo a b} (-K(x)) D_h(x)) + ∫_{x ∈ Ioo a b} (2 K(2x)) (2 R(2x))`. -/
theorem quarter_harmonic_doubling_below_four_twenty_fifths_le_setIntegral_Ioo_add_double_autocorr
    {A : Set ℝ} {h : ℝ → ℝ} {C L a b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u) (hL : 0 < L)
    (ha4 : L / 4 ≤ a) (hab : a ≤ b) (hb25 : b ≤ 4 / 25) (hta : screwSignThreshold ≤ 2 * a) :
    ((4 / 21 : ℝ) * (levyCoshPotential a - levyCoshPotential b) +
        (3 / 7 : ℝ) * (levyCoshPotential (2 * b) - levyCoshPotential (2 * a))) *
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
      (6 / 7 : ℝ) * (2 * screwRegularKernel (2 * x))) * ∫ u, h u ^ 2
  have hI_G : IntegrableOn G (Ioo a b) :=
    ((hI_K.const_mul (8 / 21 : ℝ)).add (hI_K2.const_mul (6 / 7 : ℝ))).mul_const _
  have hmono : (∫ x in Ioo a b, G x) ≤
      ∫ x in Ioo a b, ((-screwRegularKernel x) * (∫ u, (h u - h (u + x)) ^ 2) +
        (2 * screwRegularKernel (2 * x)) * (2 * autocorr h (2 * x))) := by
    refine setIntegral_mono_on hI_G (hI_jump.add hI_auto) measurableSet_Ioo fun x hx => ?_
    dsimp only [G]
    have hx0 : 0 < x := lt_trans ha0 hx.1
    have hK2_0 : 0 ≤ 2 * screwRegularKernel (2 * x) :=
      mul_nonneg zero_le_two (screwRegularKernel_nonneg_of_threshold_le
        (hta.trans (by linarith [hx.1])))
    have hexcess : 0 ≤ (-screwRegularKernel x) - 3 * (2 * screwRegularKernel (2 * x)) := by
      linarith [three_mul_two_mul_screwRegularKernel_two_mul_le_neg_screwRegularKernel
        hx0 (hx.2.le.trans hb25)]
    have h4_coerc := eight_twenty_firsts_mul_integral_sq_le_integral_jump_sq_of_quarter_le
      hh hsupp hL.le (ha4.trans hx.1.le)
    have hhd := two_thirds_mul_integral_sq_le_integral_jump_sq_add_third_autocorr_of_quarter_le
      hh hsupp hL.le (ha4.trans hx.1.le)
    have hm1 := mul_le_mul_of_nonneg_left h4_coerc hexcess
    have hm2 := mul_le_mul_of_nonneg_left hhd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hK2_0)
    linarith
  have hval_G : (∫ x in Ioo a b, G x) =
      ((4 / 21 : ℝ) * (levyCoshPotential a - levyCoshPotential b) +
        (3 / 7 : ℝ) * (levyCoshPotential (2 * b) - levyCoshPotential (2 * a))) *
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

/-- **Upgraded Quarter+Third Harmonic-Doubling Potential + Pair Bound on `Ioo (L / 4) screwSignThreshold` (`3 * screwSignThreshold / 2 ≤ L ≤ 12 / 25`)**:
combining `Ioo (L / 4) (screwSignThreshold / 2)`, `Ioo (screwSignThreshold / 2) (L / 3)` (with `(3 / 7)` harmonic-doubling excess),
`Ioo (L / 3) (3 / 16)`, and `Ioo (3 / 16) screwSignThreshold` yields:
`((4 / 21) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 82) * Φ(3 / 16) + (2659 / 11480) * Φ(2 * L / 3) + (323 / 1640) * Φ(3 / 8) - (13 / 14) * Φ(screwSignThreshold)) * ∫ h² ≤ (∫_{x ∈ Ioo (L / 4) t_*} (-K(x)) D_h(x)) + pair_{t_*}(h)`. -/
theorem quarter_harmonic_doubling_quarter_to_threshold_le_setIntegral_Ioo_add_pair
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u)
    (hL_low : 3 * screwSignThreshold / 2 ≤ L) (hL_high : L ≤ 12 / 25) :
    ((4 / 21 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 82 : ℝ) * levyCoshPotential (3 / 16) +
        (2659 / 11480 : ℝ) * levyCoshPotential (2 * L / 3) +
        (323 / 1640 : ℝ) * levyCoshPotential (3 / 8) -
        (13 / 14 : ℝ) * levyCoshPotential screwSignThreshold) * (∫ u, h u ^ 2) ≤
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
  have hL3_25 : L / 3 ≤ 4 / 25 := by linarith
  have hL3_16 : L / 3 ≤ 3 / 16 := by linarith
  have h16_t : (3 : ℝ) / 16 ≤ screwSignThreshold := by
    linarith [screwSignThreshold_gt_6036_over_21509]
  have hL3_t : L / 3 ≤ screwSignThreshold := le_trans hL3_16 h16_t
  have ht2_t : screwSignThreshold / 2 ≤ screwSignThreshold := le_trans ht2_L3 hL3_t
  have hL4_L3 : L / 4 ≤ L / 3 := le_trans hL4_t2 ht2_L3
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
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_34 : Disjoint (Ioc (L / 3) (3 / 16)) (Ioc (3 / 16) screwSignThreshold) :=
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_1234 : Disjoint (Ioc (L / 4) (L / 3)) (Ioc (L / 3) screwSignThreshold) :=
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
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
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
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
  have h2 := quarter_harmonic_doubling_below_four_twenty_fifths_le_setIntegral_Ioo_add_double_autocorr
    hh hsupp hh0 hL0 hL4_t2 ht2_L3 hL3_25 (by linarith : screwSignThreshold ≤ 2 * (screwSignThreshold / 2))
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

/-- **Full Fifteen-Point Dyadic + Quarter Harmonic-Doubling Potential + Pair Coercivity on `Ioo (L / 20) screwSignThreshold` (`3 * screwSignThreshold / 2 ≤ L ≤ 12 / 25`)**:
combining `twentieth_to_quarter_sub_levyCoshPotential_le_setIntegral_Ioo` on `Ioo (L / 20) (L / 4)`
with `quarter_harmonic_doubling_quarter_to_threshold_le_setIntegral_Ioo_add_pair` on `Ioo (L / 4) screwSignThreshold`! -/
theorem fifteen_point_quarter_harmonic_doubling_twentieth_to_threshold_le_setIntegral_Ioo_add_pair
    {A : Set ℝ} {h : ℝ → ℝ} {C L : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ v ∉ Ioo 0 L, h v = 0) (hh0 : ∀ u, 0 ≤ h u)
    (hL_low : 3 * screwSignThreshold / 2 ≤ L) (hL_high : L ≤ 12 / 25) :
    ((1 / 100 : ℝ) * levyCoshPotential (L / 20) +
        (1 / 200 : ℝ) * levyCoshPotential (L / 16) +
        (3 / 800 : ℝ) * levyCoshPotential (L / 14) +
        (1 / 180 : ℝ) * levyCoshPotential (L / 12) +
        (113 / 7200 : ℝ) * levyCoshPotential (L / 10) +
        (1 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (3 / 200 : ℝ) * levyCoshPotential (L / 7) +
        (1 / 45 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (2 / 35 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 82 : ℝ) * levyCoshPotential (3 / 16) +
        (2659 / 11480 : ℝ) * levyCoshPotential (2 * L / 3) +
        (323 / 1640 : ℝ) * levyCoshPotential (3 / 8) -
        (13 / 14 : ℝ) * levyCoshPotential screwSignThreshold) * (∫ u, h u ^ 2) ≤
      (∫ x in Ioo (L / 20) screwSignThreshold,
        (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) +
        ∫ p : ℝ × ℝ, h p.1 * h p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity [screwSignThreshold_pos]) hL_low
  have h20_pos : 0 < L / 20 := by linarith
  have h20_4 : L / 20 ≤ L / 4 := by linarith
  have h4_t : L / 4 ≤ screwSignThreshold := by
    linarith [screwSignThreshold_gt_6036_over_21509]
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 20) screwSignThreshold) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le h20_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 20) screwSignThreshold) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans h20_pos hx.1) hx.2.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_1 : IntegrableOn F (Ioc (L / 20) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl h4_t)
  have hIF_2 : IntegrableOn F (Ioc (L / 4) screwSignThreshold) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo h20_4 le_rfl)
  have hdisj : Disjoint (Ioc (L / 20) (L / 4)) (Ioc (L / 4) screwSignThreshold) :=
    disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 20) screwSignThreshold, F x) =
      (∫ x in Ioo (L / 20) (L / 4), F x) + ∫ x in Ioo (L / 4) screwSignThreshold, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc h20_4 h4_t,
      setIntegral_union hdisj measurableSet_Ioc hIF_1 hIF_2,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h20_4_bound := twentieth_to_quarter_sub_levyCoshPotential_le_setIntegral_Ioo hh hsupp hL0 h4_t
  have h4_t_bound := quarter_harmonic_doubling_quarter_to_threshold_le_setIntegral_Ioo_add_pair
    hh hsupp hh0 hL_low hL_high
  dsimp only [F] at hsplit
  linarith

/-- **Fifteen-Point Dyadic + Quarter Harmonic-Doubling Lévy–Cosh Crossover Lower Bound for `weilArchRe` (`3 * screwSignThreshold / 2 ≤ L ≤ 12 / 25`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L`,
`(A(0) + (1 / 100) * Φ(L / 20) + (1 / 200) * Φ(L / 16) + (3 / 800) * Φ(L / 14) + (1 / 180) * Φ(L / 12) + (113 / 7200) * Φ(L / 10) + (1 / 50) * Φ(L / 8) + (3 / 200) * Φ(L / 7) + (1 / 45) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 82) * Φ(3 / 16) + (2659 / 11480) * Φ(2 * L / 3) + (323 / 1640) * Φ(3 / 8) + (1 / 14) * Φ(screwSignThreshold)) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem fifteen_point_quarter_harmonic_doubling_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL_low : 3 * screwSignThreshold / 2 ≤ L) (hL_high : L ≤ 12 / 25)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (1 / 100) * levyCoshPotential (L / 20) +
        (1 / 200) * levyCoshPotential (L / 16) +
        (3 / 800) * levyCoshPotential (L / 14) +
        (1 / 180) * levyCoshPotential (L / 12) +
        (113 / 7200) * levyCoshPotential (L / 10) +
        (1 / 50) * levyCoshPotential (L / 8) +
        (3 / 200) * levyCoshPotential (L / 7) +
        (1 / 45) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (17 / 82) * levyCoshPotential (3 / 16) +
        (2659 / 11480) * levyCoshPotential (2 * L / 3) +
        (323 / 1640) * levyCoshPotential (3 / 8) +
        (1 / 14) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity [screwSignThreshold_pos]) hL_low
  have hL20 : 0 < L / 20 := by linarith
  have hL20t : L / 20 ≤ screwSignThreshold := by
    linarith [screwSignThreshold_gt_6036_over_21509]
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL20 hL20t le_rfl
  have hsplit := fifteen_point_quarter_harmonic_doubling_twentieth_to_threshold_le_setIntegral_Ioo_add_pair
    hB hsupp hf0 hL_low hL_high
  linarith

/-- Exact 5-smooth factorization of `log(1 / (π * (12 / 25)))` via
`1 / (π * (12 / 25)) = (4 / 3) * (5 / 4)^3 / (4 * (5 * π / 16))` and `log(5 * π / 16) ≤ 5 * π / 16 - 1`:
`-2 * Real.log 2 + Real.log (4 / 3) + 3 * Real.log (5 / 4) + 1 - 5 * Real.pi / 16 ≤ Real.log (1 / (Real.pi * (12 / 25)))`. -/
theorem log_inv_pi_mul_twelve_twenty_fifths_ge :
    -2 * Real.log 2 + Real.log (4 / 3) + 3 * Real.log (5 / 4) + 1 -
        5 * Real.pi / 16 ≤ Real.log (1 / (Real.pi * (12 / 25))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog4 : 2 * Real.log 2 = Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog54 : 3 * Real.log (5 / 4) = Real.log (125 / 64) := by
    rw [show (125 / 64 : ℝ) = (5 / 4) ^ 3 by norm_num, Real.log_pow]; ring
  have hsplit : Real.log (1 / (Real.pi * (12 / 25))) + 2 * Real.log 2 +
      Real.log (5 * Real.pi / 16) = Real.log (4 / 3) + 3 * Real.log (5 / 4) := by
    rw [hlog4, hlog54, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by norm_num) (by norm_num)]
    congr 1; field_simp; ring
  have hpi_log : Real.log (5 * Real.pi / 16) ≤ 5 * Real.pi / 16 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  linarith

/-- **Fourth-Order Osculating Lower Bound for the Fifteen-Point Potential at `L = 12 / 25`**:
every logarithm at `L = 12 / 25` factors into `log 2`, `log(4 / 3)`, `log(5 / 4)`, and `log(7 / 6)`. -/
theorem osculating_le_fifteen_point_quarter_harmonic_doubling_potential_twelve_twenty_fifths :
    Real.log (1 / (Real.pi * (12 / 25))) + (1397 / 2016 : ℝ) * Real.log 2 -
        (216233 / 413280 : ℝ) * Real.log (4 / 3) -
        (367649 / 413280 : ℝ) * Real.log (5 / 4) +
        (101 / 1120 : ℝ) * Real.log (7 / 6) +
        (288612119 / 344400000 : ℝ) +
        (151778990566619 / 30376080000000000 : ℝ) +
        (1 / 14 : ℝ) * (screwSignThreshold ^ 2 / 48 + (5 / 27 : ℝ) * screwSignThreshold ^ 3) -
        eulerMascheroniConstant ≤
      EF.gammaBracket 0 + (1 / 100) * levyCoshPotential ((12 / 25 : ℝ) / 20) +
        (1 / 200) * levyCoshPotential ((12 / 25 : ℝ) / 16) +
        (3 / 800) * levyCoshPotential ((12 / 25 : ℝ) / 14) +
        (1 / 180) * levyCoshPotential ((12 / 25 : ℝ) / 12) +
        (113 / 7200) * levyCoshPotential ((12 / 25 : ℝ) / 10) +
        (1 / 50) * levyCoshPotential ((12 / 25 : ℝ) / 8) +
        (3 / 200) * levyCoshPotential ((12 / 25 : ℝ) / 7) +
        (1 / 45) * levyCoshPotential ((12 / 25 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((12 / 25 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((12 / 25 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((12 / 25 : ℝ) / 3) +
        (17 / 82) * levyCoshPotential (3 / 16) +
        (2659 / 11480) * levyCoshPotential (2 * (12 / 25 : ℝ) / 3) +
        (323 / 1640) * levyCoshPotential (3 / 8) +
        (1 / 14) * levyCoshPotential screwSignThreshold := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog8_val : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; ring
  have hlog3 : Real.log 3 = 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [Real.log_div (by norm_num) (by norm_num), hlog4]; ring
  have hlog6_val : Real.log 6 = 3 * Real.log 2 - Real.log (4 / 3) := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), hlog3]; ring
  have hlog10 : Real.log (1 / (2 * Real.pi * ((12 / 25 : ℝ) / 10))) =
      Real.log (1 / (Real.pi * (12 / 25))) + 2 * Real.log 2 + Real.log (5 / 4) := by
    rw [← hlog4, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog8 : Real.log (1 / (2 * Real.pi * ((12 / 25 : ℝ) / 8))) =
      Real.log (1 / (Real.pi * (12 / 25))) + 2 * Real.log 2 := by
    rw [← hlog4, ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog7 : Real.log (1 / (2 * Real.pi * ((12 / 25 : ℝ) / 7))) =
      Real.log (1 / (Real.pi * (12 / 25))) + 2 * Real.log 2 - Real.log (4 / 3) + Real.log (7 / 6) := by
    rw [show Real.log (1 / (Real.pi * (12 / 25))) + 2 * Real.log 2 - Real.log (4 / 3) + Real.log (7 / 6) =
        Real.log (1 / (Real.pi * (12 / 25))) + Real.log 3 + Real.log (7 / 6) by linarith [hlog3],
      ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog6 : Real.log (1 / (2 * Real.pi * ((12 / 25 : ℝ) / 6))) =
      Real.log (1 / (Real.pi * (12 / 25))) + 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [show Real.log (1 / (Real.pi * (12 / 25))) + 2 * Real.log 2 - Real.log (4 / 3) =
        Real.log (1 / (Real.pi * (12 / 25))) + Real.log 3 by linarith [hlog3],
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog5 : Real.log (1 / (2 * Real.pi * ((12 / 25 : ℝ) / 5))) =
      Real.log (1 / (Real.pi * (12 / 25))) + Real.log 2 + Real.log (5 / 4) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog4_pt : Real.log (1 / (2 * Real.pi * ((12 / 25 : ℝ) / 4))) =
      Real.log (1 / (Real.pi * (12 / 25))) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog3_pt : Real.log (1 / (2 * Real.pi * ((12 / 25 : ℝ) / 3))) =
      Real.log (1 / (Real.pi * (12 / 25))) + Real.log 2 - Real.log (4 / 3) := by
    rw [eq_sub_iff_add_eq, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog20 : Real.log (1 / (2 * Real.pi * ((12 / 25 : ℝ) / 20))) =
      Real.log (1 / (Real.pi * (12 / 25))) + 3 * Real.log 2 + Real.log (5 / 4) := by
    rw [← hlog8_val, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog16 : Real.log (1 / (2 * Real.pi * ((12 / 25 : ℝ) / 16))) =
      Real.log (1 / (Real.pi * (12 / 25))) + 3 * Real.log 2 := by
    rw [← hlog8_val, ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog14 : Real.log (1 / (2 * Real.pi * ((12 / 25 : ℝ) / 14))) =
      Real.log (1 / (Real.pi * (12 / 25))) + 3 * Real.log 2 - Real.log (4 / 3) + Real.log (7 / 6) := by
    rw [show Real.log (1 / (Real.pi * (12 / 25))) + 3 * Real.log 2 - Real.log (4 / 3) + Real.log (7 / 6) =
        Real.log (1 / (Real.pi * (12 / 25))) + Real.log 6 + Real.log (7 / 6) by linarith [hlog6_val],
      ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog12 : Real.log (1 / (2 * Real.pi * ((12 / 25 : ℝ) / 12))) =
      Real.log (1 / (Real.pi * (12 / 25))) + 3 * Real.log 2 - Real.log (4 / 3) := by
    rw [show Real.log (1 / (Real.pi * (12 / 25))) + 3 * Real.log 2 - Real.log (4 / 3) =
        Real.log (1 / (Real.pi * (12 / 25))) + Real.log 6 by linarith [hlog6_val],
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have h25_16 : 2 * Real.log (5 / 4) = Real.log (25 / 16) := by
    rw [show (25 / 16 : ℝ) = (5 / 4) ^ 2 by norm_num, Real.log_pow]; ring
  have h16_9 : 2 * Real.log (4 / 3) = Real.log (16 / 9) := by
    rw [show (16 / 9 : ℝ) = (4 / 3) ^ 2 by norm_num, Real.log_pow]; ring
  have hlog_b0 : Real.log (1 / (2 * Real.pi * (3 / 16))) =
      Real.log (1 / (Real.pi * (12 / 25))) + Real.log 2 - 2 * Real.log (5 / 4) := by
    have h : Real.log (1 / (2 * Real.pi * (3 / 16))) + Real.log (25 / 16) =
        Real.log (1 / (Real.pi * (12 / 25))) + Real.log 2 := by
      rw [← Real.log_mul (by positivity) (by norm_num),
        ← Real.log_mul (by positivity) (by norm_num)]
      congr 1; field_simp; ring
    linarith
  have hlog_2L3 : Real.log (1 / (2 * Real.pi * (2 * (12 / 25 : ℝ) / 3))) =
      Real.log (1 / (Real.pi * (12 / 25))) - Real.log (4 / 3) := by
    rw [eq_sub_iff_add_eq, ← Real.log_mul (by positivity) (by norm_num)]
    congr 1; field_simp; ring
  have hlog_2b0 : Real.log (1 / (2 * Real.pi * (3 / 8))) =
      Real.log (1 / (Real.pi * (12 / 25))) - 2 * Real.log (5 / 4) := by
    have h : Real.log (1 / (2 * Real.pi * (3 / 8))) + Real.log (25 / 16) =
        Real.log (1 / (Real.pi * (12 / 25))) := by
      rw [← Real.log_mul (by positivity) (by norm_num)]
      congr 1; field_simp; ring
    linarith
  have hlog_c : Real.log (7 / (4 * Real.pi)) =
      Real.log (1 / (Real.pi * (12 / 25))) + Real.log 2 - 2 * Real.log (4 / 3) -
        2 * Real.log (5 / 4) + Real.log (7 / 6) := by
    have h : Real.log (7 / (4 * Real.pi)) + Real.log (16 / 9) + Real.log (25 / 16) =
        Real.log (1 / (Real.pi * (12 / 25))) + Real.log 2 + Real.log (7 / 6) := by
      rw [← Real.log_mul (by positivity) (by norm_num),
        ← Real.log_mul (by positivity) (by norm_num),
        ← Real.log_mul (by positivity) (by norm_num),
        ← Real.log_mul (by positivity) (by norm_num)]
      congr 1; field_simp; ring
    linarith
  have h20 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < (12 / 25 : ℝ) / 20)
  have h16 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < (12 / 25 : ℝ) / 16)
  have h14 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < (12 / 25 : ℝ) / 14)
  have h12 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < (12 / 25 : ℝ) / 12)
  have h10 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < (12 / 25 : ℝ) / 10)
  have h8 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < (12 / 25 : ℝ) / 8)
  have h7 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < (12 / 25 : ℝ) / 7)
  have h6 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < (12 / 25 : ℝ) / 6)
  have h5 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < (12 / 25 : ℝ) / 5)
  have h4 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < (12 / 25 : ℝ) / 4)
  have h3 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < (12 / 25 : ℝ) / 3)
  have hb0 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < 3 / 16)
  have h2L3 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < 2 * (12 / 25 : ℝ) / 3)
  have h2b0 :=
    log_inv_two_pi_add_seven_halves_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < 3 / 8)
  have hc :=
    log_seven_div_four_pi_add_one_add_forty_eighth_sq_add_five_twenty_sevenths_cube_le_gammaBracket_add_levyCoshPotential
      screwSignThreshold_pos
  rw [hlog20] at h20
  rw [hlog16] at h16
  rw [hlog14] at h14
  rw [hlog12] at h12
  rw [hlog10] at h10
  rw [hlog8] at h8
  rw [hlog7] at h7
  rw [hlog6] at h6
  rw [hlog5] at h5
  rw [hlog4_pt] at h4
  rw [hlog3_pt] at h3
  rw [hlog_b0] at hb0
  rw [hlog_2L3] at h2L3
  rw [hlog_2b0] at h2b0
  rw [hlog_c] at hc
  have hpart1a :
      (7 / 288 : ℝ) * Real.log (1 / (Real.pi * (12 / 25))) + (7 / 96 : ℝ) * Real.log 2 -
        (67 / 7200 : ℝ) * Real.log (4 / 3) + (1 / 100 : ℝ) * Real.log (5 / 4) +
        (3 / 800 : ℝ) * Real.log (7 / 6) + (4667 / 1800000 : ℝ) +
        (1058872163 / 1666980000000000 : ℝ) - (7 / 288 : ℝ) * eulerMascheroniConstant ≤
      (7 / 288 : ℝ) * EF.gammaBracket 0 +
        (1 / 100) * levyCoshPotential ((12 / 25 : ℝ) / 20) +
        (1 / 200) * levyCoshPotential ((12 / 25 : ℝ) / 16) +
        (3 / 800) * levyCoshPotential ((12 / 25 : ℝ) / 14) +
        (1 / 180) * levyCoshPotential ((12 / 25 : ℝ) / 12) := by
    linarith only [h20, h16, h14, h12]
  have hpart1b :
      (7 / 96 : ℝ) * Real.log (1 / (Real.pi * (12 / 25))) + (7 / 48 : ℝ) * Real.log 2 -
        (67 / 1800 : ℝ) * Real.log (4 / 3) + (113 / 7200 : ℝ) * Real.log (5 / 4) +
        (3 / 200 : ℝ) * Real.log (7 / 6) + (14993 / 900000 : ℝ) +
        (563112563 / 52093125000000 : ℝ) - (7 / 96 : ℝ) * eulerMascheroniConstant ≤
      (7 / 96 : ℝ) * EF.gammaBracket 0 +
        (113 / 7200) * levyCoshPotential ((12 / 25 : ℝ) / 10) +
        (1 / 50) * levyCoshPotential ((12 / 25 : ℝ) / 8) +
        (3 / 200) * levyCoshPotential ((12 / 25 : ℝ) / 7) +
        (1 / 45) * levyCoshPotential ((12 / 25 : ℝ) / 6) := by
    linarith only [h10, h8, h7, h6]
  have hpart2a :
      (29 / 72 : ℝ) * Real.log (1 / (Real.pi * (12 / 25))) + (29 / 72 : ℝ) * Real.log 2 -
        (88 / 861 : ℝ) * Real.log (4 / 3) - (5587 / 14760 : ℝ) * Real.log (5 / 4) +
        (1128751 / 4920000 : ℝ) + (27209705443 / 46494000000000 : ℝ) -
        (29 / 72 : ℝ) * eulerMascheroniConstant ≤
      (29 / 72 : ℝ) * EF.gammaBracket 0 +
        (13 / 360) * levyCoshPotential ((12 / 25 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((12 / 25 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((12 / 25 : ℝ) / 3) +
        (17 / 82) * levyCoshPotential (3 / 16) := by
    linarith only [h5, h4, h3, hb0]
  have hpart2b :
      (1 / 2 : ℝ) * Real.log (1 / (Real.pi * (12 / 25))) + (1 / 14 : ℝ) * Real.log 2 -
        (4299 / 11480 : ℝ) * Real.log (4 / 3) - (3081 / 5740 : ℝ) * Real.log (5 / 4) +
        (1 / 14 : ℝ) * Real.log (7 / 6) + (2706257 / 4592000 : ℝ) +
        (4364223047 / 991872000000 : ℝ) +
        (1 / 14 : ℝ) * (screwSignThreshold ^ 2 / 48 + (5 / 27 : ℝ) * screwSignThreshold ^ 3) -
        (1 / 2 : ℝ) * eulerMascheroniConstant ≤
      (1 / 2 : ℝ) * EF.gammaBracket 0 +
        (2659 / 11480) * levyCoshPotential (2 * (12 / 25 : ℝ) / 3) +
        (323 / 1640) * levyCoshPotential (3 / 8) +
        (1 / 14) * levyCoshPotential screwSignThreshold := by
    linarith only [h2L3, h2b0, hc]
  linarith only [hpart1a, hpart1b, hpart2a, hpart2b]

/-- **Strict Positivity of the Fifteen-Point Potential at `L = 12 / 25` (`= 0.48`, `69.25%` of `(0, log 2)`)**:
certified rational margin `+0.000452 > 0`. -/
theorem zero_le_fifteen_point_quarter_harmonic_doubling_potential_twelve_twenty_fifths :
    0 ≤ EF.gammaBracket 0 + (1 / 100) * levyCoshPotential ((12 / 25 : ℝ) / 20) +
        (1 / 200) * levyCoshPotential ((12 / 25 : ℝ) / 16) +
        (3 / 800) * levyCoshPotential ((12 / 25 : ℝ) / 14) +
        (1 / 180) * levyCoshPotential ((12 / 25 : ℝ) / 12) +
        (113 / 7200) * levyCoshPotential ((12 / 25 : ℝ) / 10) +
        (1 / 50) * levyCoshPotential ((12 / 25 : ℝ) / 8) +
        (3 / 200) * levyCoshPotential ((12 / 25 : ℝ) / 7) +
        (1 / 45) * levyCoshPotential ((12 / 25 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((12 / 25 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((12 / 25 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((12 / 25 : ℝ) / 3) +
        (17 / 82) * levyCoshPotential (3 / 16) +
        (2659 / 11480) * levyCoshPotential (2 * (12 / 25 : ℝ) / 3) +
        (323 / 1640) * levyCoshPotential (3 / 8) +
        (1 / 14) * levyCoshPotential screwSignThreshold := by
  have hosc := osculating_le_fifteen_point_quarter_harmonic_doubling_potential_twelve_twenty_fifths
  have hlog_pi := log_inv_pi_mul_twelve_twenty_fifths_ge
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

/-- **Unconditional Archimedean Weil Positivity on `(0, 12 / 25)` (`= (0, 0.48)`, `69.25%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` supported in `Ioo 0 L` with `L ≤ 12 / 25`,
`0 ≤ WeilOneSided.weilArchRe (EF.weilTest f f)`. -/
theorem weilArchRe_nonneg_of_support_Ioo_le_twelve_twenty_fifths {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL : L ≤ 12 / 25) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_12_25 : ∀ u ∉ Ioo (0 : ℝ) (12 / 25), f u = 0 :=
    fun u hu => hsupp u fun huL => hu ⟨huL.1, huL.2.trans_le hL⟩
  have hmain := fifteen_point_quarter_harmonic_doubling_levyCosh_crossover_le_weilArchRe
    hf hfc hf0
    (by linarith [screwSignThreshold_lt_thirty_eight_over_one_thirty_five] :
      3 * screwSignThreshold / 2 ≤ 12 / 25)
    (by norm_num : (12 / 25 : ℝ) ≤ 12 / 25)
    hsupp_12_25
  have hpot := zero_le_fifteen_point_quarter_harmonic_doubling_potential_twelve_twenty_fifths
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact le_trans (mul_nonneg hpot hsq) hmain

/-- **Unconditional `WindowPositive` on `(0, 12 / 25)` (`= (0, 0.48)`, `69.25%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (12 / 25)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_twelve_twenty_fifths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (12 / 25)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_twelve_twenty_fifths hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 10 / 21)` (`≈ (0, 0.476190)`, `68.70%` of `(0, log 2)`)**:
immediate corollary since `10 / 21 ≤ 12 / 25` (`250 ≤ 252`). -/
theorem windowPositive_ten_twenty_firsts (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (10 / 21)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_twelve_twenty_fifths hf hfc hf0 (by norm_num : (10 : ℝ) / 21 ≤ 12 / 25)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 15 / 32)` (`= (0, 0.46875)`, `67.63%` of `(0, log 2)`)**:
immediate corollary since `15 / 32 ≤ 12 / 25` (`375 ≤ 384`). -/
theorem windowPositive_fifteen_thirty_seconds (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (15 / 32)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_twelve_twenty_fifths hf hfc hf0 (by norm_num : (15 : ℝ) / 32 ≤ 12 / 25)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 7 / 15)` (`≈ (0, 0.466667)`, `67.33%` of `(0, log 2)`)**:
immediate corollary since `7 / 15 ≤ 12 / 25` (`175 ≤ 180`). -/
theorem windowPositive_seven_fifteenths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (7 / 15)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_twelve_twenty_fifths hf hfc hf0 (by norm_num : (7 : ℝ) / 15 ≤ 12 / 25)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 5 / 11)` (`≈ (0, 0.454545)`, `65.58%` of `(0, log 2)`)**:
immediate corollary since `5 / 11 ≤ 12 / 25` (`125 ≤ 132`). -/
theorem windowPositive_five_elevenths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (5 / 11)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_twelve_twenty_fifths hf hfc hf0 (by norm_num : (5 : ℝ) / 11 ≤ 12 / 25)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

end

end RHTower.WeilLevyQuarterHarmonicDoubling
