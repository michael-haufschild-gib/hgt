import GaloisForLFunctions.TransHorizonIncidenceMechanics.UnconditionalSchurRatioAndGlobalLowPrimeBudget

/-!
# Support-Radius Collar Cutoff, Two-Regime Gluing, and All-Scale Obstacle B Bridge

This module completes the all-scale synthesis for **Obstacle B** by combining the unconditional
low-prime Schur-complement bridge from
`UnconditionalSchurRatioAndGlobalLowPrimeBudget.lean` with the support-radius disjointness of the
even profile $w$ above twice its support radius $2R$.

## Mathematical Overview

Let $w : \mathbb{R} \to \mathbb{R}$ be an even continuous compactly supported profile supported in
$(-R, R)$ (`∀ u, R ≤ u → w u = 0` for $R \ge 0$), and let $a > 0$ be the polar shift parameter of
the secondary odd ground profile $m_a(x) = \operatorname{oddProfile}(a, x)$.

1. **Zero-Archimedean-Cost Collar Domination Above Twice the Support Radius ($2R \le \log d \le a - R$, §1):**
   - For any shift $t \ge 2R$ with $t + R \le a$ and any $x \in (0, t/2)$:
     - If $x \ge R$, then both $x \ge R$ and $t - x > t/2 \ge R$, so $w(x) = w(t - x) = 0$ and
       $\operatorname{oddProfileCollarDiffSq}(a, w, t, x) = 0 \le \operatorname{oddProfileShiftJump}(a, w, t, x)$.
     - If $0 < x < R$, then $t - x > t/2 \ge R$ and $x + t > t \ge 2R \ge R$, so
       $w(t - x) = w(x + t) = 0$. Consequently,
       $$\operatorname{oddProfileCollarDiffSq}(a, w, t, x) = m_a(x)\,m_a(t - x)\,w(x)^2,$$
       $$\operatorname{oddProfileShiftJump}(a, w, t, x) = m_a(x)\,m_a(x + t)\,w(x)^2.$$
       Since $0 < t - x < x + t < t + R \le a$, strict monotonicity of $m_a$ on $[0, a]$
       (`strictMonoOn_oddProfile_Icc`) implies $m_a(t - x) < m_a(x + t)$, so
       $$\operatorname{oddProfileCollarDiffSq}(a, w, t, x) \le \operatorname{oddProfileShiftJump}(a, w, t, x)$$
       holds **pointwise on all of $(0, t/2)$** (`oddProfileCollarDiffSq_le_shiftJump_of_support_radius`).
   - Integrating over $(0, t/2)$ proves that for every prime power $d$ in the intermediate/high
     window $2R \le \log d \le a - R$, the origin-crossing collar is dominated **1-for-1** by the
     direct half-line prime jump with **zero archimedean cost**
     (`halfCollarIntegral_le_direct_of_support_radius`,
     `integral_oddProfileCollarDiffSq_le_two_Ioi_of_support_radius`,
     `integral_oddProfileShiftJump_ge_two_tail_of_support_radius`).

2. **Seamless Two-Regime Gluing Across All Prime Powers $\log d \le a - R$ with Cutoff-Free Archimedean Constant (§2):**
   - When $a \ge 3R + \delta + L$ ($\frac{1}{2}\log 2 \le \delta + L$), the low-prime regime
     $\log d < 2R$ automatically satisfies $\frac{3}{2}\log d + \delta + L < 3R + \delta + L \le a$,
     while the regime $2R \le \log d \le a - R$ requires zero archimedean budget.
   - The resulting two-regime collar-to-continuum ratio
     `supportTruncatedCollarArchRatio R δ L d` vanishes identically for $\log d \ge 2R$, so its
     von Mangoldt sum over **any** finite set $S$ of prime powers is bounded by the fixed,
     $S$-independent and $a$-independent constant
     $$C_{\mathrm{supp}}(R, \delta, L)
       := \sum_{d < \lfloor e^{2R} \rfloor + 1} \operatorname{vonMangoldtAtom}(d)\,\operatorname{primeCollarArchRatio}(\delta, L, d)$$
     (`sum_supportTruncatedCollarArchRatio_le_supportArchBudget`).

3. **All-Scale Comparison Against the Literal 2D Continuum Absorbed Archimedean Integral (§3):**
   - Bounding the global compact rectangle $\int_0^a \operatorname{absorbedArchSlice}(a, w, \delta, a, y)\,dy$
     above by the literal 2D continuum absorbed archimedean integral
     $$\int_{y \in (0, \infty)} \left(\int_{s \in (0, \infty)} (\omega(s) - \omega(2y + s))\,\operatorname{oddProfileShiftJump}(a, w, s, y)\,ds\right) dy$$
     yields the all-scale **Obstacle B** comparison for both the half-collar line integrals
     $\sum_{d \in S} \Lambda(d) d^{-1/2} \int_{2x+s=\log d} \operatorname{oddProfileShiftJump}(a, w, s, x)$
     and the full-line prime shift jumps (`sum_vonMangoldt_halfCollarIntegral_le_Ioi_add_continuum_absorbedArch`,
     `sum_vonMangoldt_fullLine_add_continuum_absorbedArch_ge_two_tail`).
-/

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.ThetaSourceWard _root_.RHTower.PhiDivisorEnergy

/-! ## Section 1: Zero-Archimedean-Cost Collar Domination Above Twice the Support Radius ($2R \le t \le a - R$) -/

/-- The 1D half-collar line integral along $2x + s = t$ ($s = t - 2x$, $x \in (0, t/2)$):
$$\operatorname{halfCollarIntegral}(a, w, t)
  = \int_{x \in (0, t/2)} \operatorname{oddProfileShiftJump}(a, w, t - 2x, x)\,dx.$$ -/
def halfCollarIntegral (a : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w (t - 2 * x) x

theorem halfCollarIntegral_eq_integral_oddProfileCollarDiffSq_half (a : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    halfCollarIntegral a w t = ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileCollarDiffSq a w t x :=
  setIntegral_congr_fun measurableSet_Ioo fun x _ =>
    (oddProfileCollarDiffSq_eq_oddProfileShiftJump a w t x).symm

/-- **Pointwise Half-Collar Domination Above Twice the Support Radius ($2R \le t \le a - R$):**
If $w : \mathbb{R} \to \mathbb{R}$ vanishes on $[R, \infty)$ ($R \ge 0$) and $2R \le t$ with
$t + R \le a$ ($a > 0$), then on the entire half-collar $x \in (0, t/2)$ both reflected/shifted
endpoints $t - x$ and $x + t$ lie in $[R, a]$ where $w$ vanishes and $m_a$ is strictly increasing,
so $\operatorname{oddProfileCollarDiffSq}(a, w, t, x) \le \operatorname{oddProfileShiftJump}(a, w, t, x)$
pointwise without any Schur residual. -/
theorem oddProfileCollarDiffSq_le_shiftJump_of_support_radius
    {a R t x : ℝ} (ha : 0 < a) (ht2R : 2 * R ≤ t) (hta : t + R ≤ a)
    {w : ℝ → ℝ} (hsupp : ∀ u, R ≤ u → w u = 0)
    (hx : x ∈ Ioo (0 : ℝ) (t / 2)) :
    oddProfileCollarDiffSq a w t x ≤ oddProfileShiftJump a w t x := by
  have hx0 : 0 < x := hx.1
  have hxt : x < t / 2 := hx.2
  have ht0 : 0 ≤ t := by linarith
  by_cases hxR : R ≤ x
  · have htxR : R ≤ t - x := by linarith
    have h0 : oddProfileCollarDiffSq a w t x = 0 := by
      unfold oddProfileCollarDiffSq
      rw [hsupp x hxR, hsupp (t - x) htxR]
      ring
    rw [h0]
    exact oddProfileShiftJump_nonneg_of_pos ha hx0 ht0 w
  · have hx_lt_R : x < R := not_le.mp hxR
    have htxR : R ≤ t - x := by linarith
    have hxtR : R ≤ x + t := by linarith
    have hcol_eq : oddProfileCollarDiffSq a w t x =
        oddProfile a x * oddProfile a (t - x) * w x ^ 2 := by
      unfold oddProfileCollarDiffSq
      rw [hsupp (t - x) htxR, sub_zero]
    have hdir_eq : oddProfileShiftJump a w t x =
        oddProfile a x * oddProfile a (x + t) * w x ^ 2 := by
      unfold oddProfileShiftJump
      rw [hsupp (x + t) hxtR, sub_zero]
    rw [hcol_eq, hdir_eq]
    have hmono : oddProfile a (t - x) ≤ oddProfile a (x + t) :=
      (strictMonoOn_oddProfile_Icc ha).monotoneOn
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    have hmx : 0 ≤ oddProfile a x := (oddProfile_pos ha hx0).le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hmx) (sq_nonneg _)

/-- **Half-Collar Line-Integral Domination Above Twice the Support Radius ($2R \le t \le a - R$):** -/
theorem halfCollarIntegral_le_direct_of_support_radius
    {a R t : ℝ} (ha : 0 < a) (ht2R : 2 * R ≤ t) (hta : t + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hsupp : ∀ u, R ≤ u → w u = 0) :
    halfCollarIntegral a w t ≤
      ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x := by
  rw [halfCollarIntegral_eq_integral_oddProfileCollarDiffSq_half]
  have hint_col : IntegrableOn (oddProfileCollarDiffSq a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileCollarDiffSq a t hw).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint_dir : IntegrableOn (oddProfileShiftJump a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileShiftJump_right a t hw).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  refine setIntegral_mono_on hint_col hint_dir measurableSet_Ioo fun x hx => ?_
  exact oddProfileCollarDiffSq_le_shiftJump_of_support_radius ha ht2R hta hsupp hx

/-- **Full-Collar Integral Domination by Twice the Half-Collar Direct Jump ($2R \le t \le a - R$):** -/
theorem integral_oddProfileCollarDiffSq_le_two_direct_of_support_radius
    {a R t : ℝ} (ha : 0 < a) (ht0 : 0 ≤ t) (ht2R : 2 * R ≤ t) (hta : t + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hsupp : ∀ u, R ≤ u → w u = 0) :
    (∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x) ≤
      2 * ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x := by
  rw [integral_oddProfileCollarDiffSq_eq_two_mul_half a hw ht0]
  have h := halfCollarIntegral_le_direct_of_support_radius ha ht2R hta hw hsupp
  unfold halfCollarIntegral at h
  linarith

/-- **Full-Collar Integral Domination by Twice the Half-Line Direct Jump ($2R \le t \le a - R$):** -/
theorem integral_oddProfileCollarDiffSq_le_two_Ioi_of_support_radius
    {a R t : ℝ} (ha : 0 < a) (ht0 : 0 ≤ t) (ht2R : 2 * R ≤ t) (hta : t + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hsupp : ∀ u, R ≤ u → w u = 0) :
    (∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x) ≤
      2 * ∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w t x := by
  have h1 := integral_oddProfileCollarDiffSq_le_two_direct_of_support_radius
    ha ht0 ht2R hta hw hsupp
  have hint : IntegrableOn (oddProfileShiftJump a w t) (Ioi (0 : ℝ)) := by
    have hsub : HasCompactSupport (fun x : ℝ => w x - w (x + t)) :=
      hwc.sub (hwc.comp_homeomorph (Homeomorph.addRight t))
    have hsub2 : HasCompactSupport (fun x : ℝ => (w x - w (x + t)) ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hsub ⊢
      filter_upwards [hsub] with x hx; simp [hx]
    exact ((continuous_oddProfileShiftJump_right a t hw).integrable_of_hasCompactSupport
      hsub2.mul_left).integrableOn
  have h2 : (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x) ≤
      ∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w t x := by
    refine setIntegral_mono_set hint ?_ (Eventually.of_forall fun x hx => hx.1)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact oddProfileShiftJump_nonneg_of_pos ha (mem_Ioi.mp hx) ht0 w
  linarith

/-- **Zero-Archimedean-Cost Full-Line Shift-Jump Positivity Above Twice the Support Radius ($2R \le t \le a - R$):**
For any even continuous compactly supported $w$ vanishing on $[R, \infty)$ and any shift
$2R \le t \le a - R$, the full-line shift jump $\int_{\mathbb{R}} \operatorname{oddProfileShiftJump}(a, w, t, x)\,dx$
dominates twice the tail jump $2 \int_{t/2}^\infty \operatorname{oddProfileShiftJump}(a, w, t, x)\,dx \ge 0$
on its own, requiring zero contribution from the archimedean integral. -/
theorem integral_oddProfileShiftJump_ge_two_tail_of_support_radius
    {a R t : ℝ} (ha : 0 < a) (ht0 : 0 ≤ t) (ht2R : 2 * R ≤ t) (hta : t + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) (hsupp : ∀ u, R ≤ u → w u = 0) :
    2 * (∫ x in Ioi (t / 2), oddProfileShiftJump a w t x) ≤
      ∫ x : ℝ, oddProfileShiftJump a w t x := by
  have hint_full : Integrable (oddProfileShiftJump a w t) := by
    have hsub : HasCompactSupport (fun x : ℝ => w x - w (x + t)) :=
      hwc.sub (hwc.comp_homeomorph (Homeomorph.addRight t))
    have hsub2 : HasCompactSupport (fun x : ℝ => (w x - w (x + t)) ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hsub ⊢
      filter_upwards [hsub] with x hx; simp [hx]
    exact (continuous_oddProfileShiftJump_right a t hw).integrable_of_hasCompactSupport hsub2.mul_left
  have hsplit_Ioi : (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w t x) =
      (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x) +
        (∫ x in Ioi (t / 2), oddProfileShiftJump a w t x) := by
    have hunion : Ioc (0 : ℝ) (t / 2) ∪ Ioi (t / 2) = Ioi (0 : ℝ) :=
      Ioc_union_Ioi_eq_Ioi (by linarith)
    have hdisj : Disjoint (Ioc (0 : ℝ) (t / 2)) (Ioi (t / 2)) := Ioc_disjoint_Ioi le_rfl
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioi
      hint_full.integrableOn hint_full.integrableOn, integral_Ioc_eq_integral_Ioo]
  have hfold := integral_oddProfileShiftJump_eq_halfLine_of_even a hw hwc heven ht0
  have hcol_eq : (∫ x in Ioo (0 : ℝ) t,
      oddProfile a x * oddProfile a (t - x) * (w x - w (t - x)) ^ 2) =
      ∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x := rfl
  rw [hcol_eq, hsplit_Ioi] at hfold
  have hdom := integral_oddProfileCollarDiffSq_le_two_direct_of_support_radius
    ha ht0 ht2R hta hw hsupp
  linarith

/-! ## Section 2: Seamless Two-Regime Gluing and Cutoff-Independent Archimedean Budget -/

/-- Support-truncated collar-to-continuum ratio: equals `primeCollarArchRatio δ L d` in the
low-prime regime $\log d < 2R$ and vanishes identically for $\log d \ge 2R$. -/
def supportTruncatedCollarArchRatio (R δ L : ℝ) (d : ℕ) : ℝ :=
  if Real.log d < 2 * R then primeCollarArchRatio δ L d else 0

theorem supportTruncatedCollarArchRatio_nonneg {R δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) (d : ℕ) :
    0 ≤ supportTruncatedCollarArchRatio R δ L d := by
  unfold supportTruncatedCollarArchRatio
  split_ifs
  · exact primeCollarArchRatio_nonneg hδ hL d
  · exact le_rfl

theorem supportTruncatedCollarArchRatio_le_primeCollarArchRatio
    {R δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) (d : ℕ) :
    supportTruncatedCollarArchRatio R δ L d ≤ primeCollarArchRatio δ L d := by
  unfold supportTruncatedCollarArchRatio
  split_ifs
  · exact le_rfl
  · exact primeCollarArchRatio_nonneg hδ hL d

theorem supportTruncatedCollarArchRatio_eq_zero_of_ge
    {R δ L : ℝ} {d : ℕ} (hd : 2 * R ≤ Real.log d) :
    supportTruncatedCollarArchRatio R δ L d = 0 := by
  unfold supportTruncatedCollarArchRatio
  exact if_neg (not_lt.mpr hd)

/-- Fixed, prime-cutoff-free and $a$-independent archimedean collar budget constant depending only
on the support radius $R$ and the bridge parameters $(\delta, L)$:
$$C_{\mathrm{supp}}(R, \delta, L)
  = \sum_{d < \lfloor e^{2R} \rfloor + 1} \operatorname{vonMangoldtAtom}(d)\,\operatorname{primeCollarArchRatio}(\delta, L, d).$$ -/
def supportArchBudget (R δ L : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (⌊Real.exp (2 * R)⌋₊ + 1),
    vonMangoldtAtom d * primeCollarArchRatio δ L d

theorem supportArchBudget_nonneg {R δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) :
    0 ≤ supportArchBudget R δ L := by
  unfold supportArchBudget
  exact Finset.sum_nonneg fun d _ =>
    mul_nonneg (vonMangoldtAtom_nonneg d) (primeCollarArchRatio_nonneg hδ hL d)

/-- **Uniform Cutoff-Independence of the Support-Truncated Archimedean Sum:**
For **every** finite set $S : \operatorname{Finset} \mathbb{N}$ of prime powers (regardless of how
large $S$ is), the sum of `vonMangoldtAtom d * supportTruncatedCollarArchRatio R δ L d` over $S$ is
bounded above by the fixed constant `supportArchBudget R δ L`. -/
theorem sum_supportTruncatedCollarArchRatio_le_supportArchBudget
    (R : ℝ) {δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) (S : Finset ℕ) :
    (∑ d ∈ S, vonMangoldtAtom d * supportTruncatedCollarArchRatio R δ L d) ≤
      supportArchBudget R δ L := by
  unfold supportArchBudget
  set N := ⌊Real.exp (2 * R)⌋₊ + 1
  have hsub : (∑ d ∈ S, vonMangoldtAtom d * supportTruncatedCollarArchRatio R δ L d) =
      ∑ d ∈ S.filter (· < N), vonMangoldtAtom d * supportTruncatedCollarArchRatio R δ L d := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun d hdS hnot => ?_
    rw [Finset.mem_filter, not_and] at hnot
    have hdN : N ≤ d := not_lt.mp (hnot hdS)
    have hfloor_lt : ⌊Real.exp (2 * R)⌋₊ < d := Nat.lt_of_succ_le hdN
    have hexp_le : Real.exp (2 * R) ≤ (d : ℝ) := ((Nat.floor_lt (Real.exp_pos _).le).mp hfloor_lt).le
    have hlog_ge : 2 * R ≤ Real.log (d : ℝ) := by
      rw [← Real.log_exp (2 * R)]
      exact Real.log_le_log (Real.exp_pos _) hexp_le
    rw [supportTruncatedCollarArchRatio_eq_zero_of_ge hlog_ge, mul_zero]
  rw [hsub]
  have hle1 : (∑ d ∈ S.filter (· < N),
        vonMangoldtAtom d * supportTruncatedCollarArchRatio R δ L d) ≤
      ∑ d ∈ S.filter (· < N), vonMangoldtAtom d * primeCollarArchRatio δ L d :=
    Finset.sum_le_sum fun d _ =>
      mul_le_mul_of_nonneg_left
        (supportTruncatedCollarArchRatio_le_primeCollarArchRatio hδ hL d)
        (vonMangoldtAtom_nonneg d)
  have hle2 : (∑ d ∈ S.filter (· < N), vonMangoldtAtom d * primeCollarArchRatio δ L d) ≤
      ∑ d ∈ Finset.range N, vonMangoldtAtom d * primeCollarArchRatio δ L d := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ =>
      mul_nonneg (vonMangoldtAtom_nonneg d) (primeCollarArchRatio_nonneg hδ hL d)
    intro d hd
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hd).2
  exact hle1.trans hle2

/-- **Two-Regime Per-Prime Collar Domination Across All Scales $\log d + R \le a$ ($a \ge 3R + \delta + L$):**
For any $d : \mathbb{N}$ with $\log d + R \le a$, combining the low-prime Schur-complement bridge
($\log d < 2R$) with the zero-cost support-disjointness bound ($\log d \ge 2R$) bounds the collar
integral with the truncated archimedean coefficient `supportTruncatedCollarArchRatio R δ L d`. -/
theorem vonMangoldt_oddProfileCollarDiffSq_le_two_Ioi_add_supportTruncated
    {a R δ L : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hL : 0 < L)
    (hδL : Real.log 2 / 2 ≤ δ + L) (haR : 3 * R + δ + L ≤ a)
    {d : ℕ} (hd_a : Real.log d + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hsupp : ∀ u, R ≤ u → w u = 0) :
    vonMangoldtAtom d *
        (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x) ≤
      2 * vonMangoldtAtom d *
        (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x) +
      (vonMangoldtAtom d * supportTruncatedCollarArchRatio R δ L d) *
        ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
  unfold supportTruncatedCollarArchRatio
  split_ifs with hlt
  · have hd_low : 3 * Real.log d / 2 + δ + L ≤ a := by linarith
    exact vonMangoldt_oddProfileCollarDiffSq_le_two_Ioi_add_global_absorbedArchSlice
      hδ hL hδL hd_low hw hwc
  · have hge : 2 * R ≤ Real.log d := not_lt.mp hlt
    have ha_pos : 0 < a := by linarith
    have hmid := integral_oddProfileCollarDiffSq_le_two_Ioi_of_support_radius
      ha_pos (Real.log_natCast_nonneg d) hge hd_a hw hwc hsupp
    have hmul := mul_le_mul_of_nonneg_left hmid (vonMangoldtAtom_nonneg d)
    linarith

/-- **Two-Regime Per-Prime Full-Line Shift-Jump Positivity Across All Scales $\log d + R \le a$:** -/
theorem vonMangoldt_fullLine_add_supportTruncated_ge_two_tail
    {a R δ L : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hL : 0 < L)
    (hδL : Real.log 2 / 2 ≤ δ + L) (haR : 3 * R + δ + L ≤ a)
    {d : ℕ} (hd_a : Real.log d + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) (hsupp : ∀ u, R ≤ u → w u = 0) :
    2 * vonMangoldtAtom d *
        (∫ x in Ioi (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x) ≤
      vonMangoldtAtom d *
        (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x) +
      (vonMangoldtAtom d * supportTruncatedCollarArchRatio R δ L d) *
        ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
  unfold supportTruncatedCollarArchRatio
  split_ifs with hlt
  · have hd_low : 3 * Real.log d / 2 + δ + L ≤ a := by linarith
    have h := sum_vonMangoldt_fullLine_add_global_absorbedArchSlice_ge_two_tail_unweighted
      (a := a) hδ hL hδL {d} (fun k hk => by rw [Finset.mem_singleton.mp hk]; exact hd_low)
      hw hwc heven
    simp only [Finset.sum_singleton] at h
    linarith
  · have hge : 2 * R ≤ Real.log d := not_lt.mp hlt
    have ha_pos : 0 < a := by linarith
    have hmid := integral_oddProfileShiftJump_ge_two_tail_of_support_radius
      ha_pos (Real.log_natCast_nonneg d) hge hd_a hw hwc heven hsupp
    have hmul := mul_le_mul_of_nonneg_left hmid (vonMangoldtAtom_nonneg d)
    linarith

/-- **All-Scale Summed Prime-Collar Domination with Cutoff-Free Support Budget (`supportArchBudget R δ L`):**
For any finite set $S$ of prime powers with $\forall d \in S,\, \log d + R \le a$ ($a \ge 3R + \delta + L$),
the unweighted von Mangoldt sum of prime-collar integrals over $S$ is bounded by twice the sum of
half-line prime shift jumps plus the **cutoff-free constant** `supportArchBudget R δ L` times the
global 2D absorbed archimedean integral. -/
theorem sum_vonMangoldt_oddProfileCollarDiffSq_le_two_Ioi_add_supportArchBudget
    {a R δ L : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hL : 0 < L)
    (hδL : Real.log 2 / 2 ≤ δ + L) (haR : 3 * R + δ + L ≤ a)
    (S : Finset ℕ) (hS : ∀ d ∈ S, Real.log d + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hsupp : ∀ u, R ≤ u → w u = 0) :
    (∑ d ∈ S, vonMangoldtAtom d *
        (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x)) ≤
      2 * (∑ d ∈ S, vonMangoldtAtom d *
        (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)) +
      supportArchBudget R δ L *
        ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
  have ha_pos : 0 < a := by linarith
  have hstep1 :
      (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x)) ≤
        2 * (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)) +
        (∑ d ∈ S, vonMangoldtAtom d * supportTruncatedCollarArchRatio R δ L d) *
          ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun d hd => ?_
    have h := vonMangoldt_oddProfileCollarDiffSq_le_two_Ioi_add_supportTruncated
      hR hδ hL hδL haR (hS d hd) hw hwc hsupp
    linarith
  have hbudget := sum_supportTruncatedCollarArchRatio_le_supportArchBudget R hδ hL S
  have hint_nonneg : 0 ≤ ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y :=
    setIntegral_nonneg measurableSet_Ioo fun y hy => absorbedArchSlice_nonneg ha_pos hδ hy.1 w
  exact hstep1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hbudget hint_nonneg))

/-! ## Section 3: Comparison Against the Literal 2D Continuum Absorbed Archimedean Integral on `(0, ∞)²` -/

/-- **Upper Bound on the Global 2D Compact Slice Integral by the Literal 2D Continuum Absorbed Archimedean Integral:**
Whenever $y \mapsto \int_{s \in Ioi 0} \operatorname{absorbedArchIntegrand}(a, w, s, y)\,ds$ is
integrable on $Ioi 0$ and each inner fiber is integrable on $Ioi 0$, the global compact slice
integral $\int_{y \in Ioo 0 a} \operatorname{absorbedArchSlice}(a, w, \delta, a, y)\,dy$ is bounded
above by the literal 2D continuum absorbed archimedean integral over $(0, \infty)^2$. -/
theorem integral_absorbedArchSlice_le_continuum_absorbedArch
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) {w : ℝ → ℝ} (hw : Continuous w)
    (hinner : ∀ y > 0, IntegrableOn (fun s : ℝ => absorbedArchIntegrand a w s y) (Ioi (0 : ℝ)))
    (houter : IntegrableOn
      (fun y : ℝ => ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s y) (Ioi (0 : ℝ))) :
    (∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y) ≤
      ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s y := by
  have hδa : δ ≤ a ∨ a < δ := le_or_gt δ a
  have hint_slice : IntegrableOn (absorbedArchSlice a w δ a) (Ioo (0 : ℝ) a) := by
    rcases hδa with hle | hgt
    · exact ((continuousOn_absorbedArchSlice_Ici a hδ hle hw).mono
        fun y hy => mem_Ici.mpr hy.1).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    · have hzero : EqOn (absorbedArchSlice a w δ a) 0 (Ioo (0 : ℝ) a) := fun y _ => by
        unfold absorbedArchSlice
        rw [Ioo_eq_empty (not_lt.mpr hgt.le), setIntegral_empty]
        rfl
      exact integrableOn_zero.congr_fun hzero.symm measurableSet_Ioo
  have hstep1 : (∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y) ≤
      ∫ y in Ioo (0 : ℝ) a, ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s y := by
    refine setIntegral_mono_on hint_slice (houter.mono_set fun y hy => hy.1)
      measurableSet_Ioo fun y hy => ?_
    exact absorbedArchSlice_le_integral_Ioi ha hδ hy.1 (hinner y hy.1)
  have hstep2 : (∫ y in Ioo (0 : ℝ) a, ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s y) ≤
      ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s y := by
    refine setIntegral_mono_set houter ?_ (Eventually.of_forall fun y hy => hy.1)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
    exact absorbedArchIntegrand_nonneg ha (mem_Ioi.mp hs) (mem_Ioi.mp hy) w
  exact hstep1.trans hstep2

/-- **Master All-Scale Obstacle B Comparison (Line-Integral Form vs. 2D Continuum Absorbed Archimedean + Half-Line Prime Jumps):**
For any even continuous compactly supported profile $w$ supported in $(-R, R)$, any $\delta, L > 0$
with $\frac{1}{2}\log 2 \le \delta + L$, any polar shift $a \ge 3R + \delta + L$, and **any**
finite set $S$ of prime powers with $\forall d \in S,\, \log d + R \le a$, twice the sum of the
discrete prime-collar line integrals
$\operatorname{halfCollarIntegral}(a, w, \log d) = \int_0^{\log d / 2} \operatorname{oddProfileShiftJump}(a, w, \log d - 2x, x)\,dx$
is bounded above by twice the sum of half-line prime shift jumps plus the cutoff-free constant
`supportArchBudget R δ L` times the 2D continuum absorbed archimedean integral on $(0, \infty)^2$. -/
theorem sum_vonMangoldt_halfCollarIntegral_le_Ioi_add_continuum_absorbedArch
    {a R δ L : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hL : 0 < L)
    (hδL : Real.log 2 / 2 ≤ δ + L) (haR : 3 * R + δ + L ≤ a)
    (S : Finset ℕ) (hS : ∀ d ∈ S, Real.log d + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hsupp : ∀ u, R ≤ u → w u = 0)
    (hinner : ∀ y > 0, IntegrableOn (fun s : ℝ => absorbedArchIntegrand a w s y) (Ioi (0 : ℝ)))
    (houter : IntegrableOn
      (fun y : ℝ => ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s y) (Ioi (0 : ℝ))) :
    2 * (∑ d ∈ S, vonMangoldtAtom d * halfCollarIntegral a w (Real.log d)) ≤
      2 * (∑ d ∈ S, vonMangoldtAtom d *
        (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)) +
      supportArchBudget R δ L *
        ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s y := by
  have ha_pos : 0 < a := by linarith
  have hlhs : 2 * (∑ d ∈ S, vonMangoldtAtom d * halfCollarIntegral a w (Real.log d)) =
      ∑ d ∈ S, vonMangoldtAtom d *
        (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_oddProfileCollarDiffSq_eq_two_mul_half a hw (Real.log_natCast_nonneg d)]
    unfold halfCollarIntegral
    ring
  rw [hlhs]
  have h1 := sum_vonMangoldt_oddProfileCollarDiffSq_le_two_Ioi_add_supportArchBudget
    hR hδ hL hδL haR S hS hw hwc hsupp
  have h2 := integral_absorbedArchSlice_le_continuum_absorbedArch ha_pos hδ hw hinner houter
  exact h1.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left h2 (supportArchBudget_nonneg hδ hL)))

/-- **Master All-Scale Full-Line Prime Shift Jump + 2D Continuum Absorbed Archimedean Positivity Law:**
Under the same hypotheses, the unweighted full-line prime shift-jump sum over $S$ plus
`supportArchBudget R δ L` times the 2D continuum absorbed archimedean integral on $(0, \infty)^2$
dominates twice the sum of non-negative tail prime jumps. -/
theorem sum_vonMangoldt_fullLine_add_continuum_absorbedArch_ge_two_tail
    {a R δ L : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hL : 0 < L)
    (hδL : Real.log 2 / 2 ≤ δ + L) (haR : 3 * R + δ + L ≤ a)
    (S : Finset ℕ) (hS : ∀ d ∈ S, Real.log d + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) (hsupp : ∀ u, R ≤ u → w u = 0)
    (hinner : ∀ y > 0, IntegrableOn (fun s : ℝ => absorbedArchIntegrand a w s y) (Ioi (0 : ℝ)))
    (houter : IntegrableOn
      (fun y : ℝ => ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s y) (Ioi (0 : ℝ))) :
    2 * (∑ d ∈ S, vonMangoldtAtom d *
        (∫ x in Ioi (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x)) ≤
      (∑ d ∈ S, vonMangoldtAtom d *
        (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x)) +
      supportArchBudget R δ L *
        ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s y := by
  have ha_pos : 0 < a := by linarith
  have hstep1 :
      2 * (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x in Ioi (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x)) ≤
        (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x)) +
        (∑ d ∈ S, vonMangoldtAtom d * supportTruncatedCollarArchRatio R δ L d) *
          ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun d hd => ?_
    have h := vonMangoldt_fullLine_add_supportTruncated_ge_two_tail
      hR hδ hL hδL haR (hS d hd) hw hwc heven hsupp
    linarith
  have hbudget := sum_supportTruncatedCollarArchRatio_le_supportArchBudget R hδ hL S
  have hint_nonneg : 0 ≤ ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y :=
    setIntegral_nonneg measurableSet_Ioo fun y hy => absorbedArchSlice_nonneg ha_pos hδ hy.1 w
  have hstep2 :
      (∑ d ∈ S, vonMangoldtAtom d * supportTruncatedCollarArchRatio R δ L d) *
          (∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y) ≤
        supportArchBudget R δ L *
          ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s y := by
    have h2 := integral_absorbedArchSlice_le_continuum_absorbedArch ha_pos hδ hw hinner houter
    exact (mul_le_mul_of_nonneg_right hbudget hint_nonneg).trans
      (mul_le_mul_of_nonneg_left h2 (supportArchBudget_nonneg hδ hL))
  exact hstep1.trans (add_le_add le_rfl hstep2)

end GaloisForLFunctions.TransHorizonIncidenceMechanics
