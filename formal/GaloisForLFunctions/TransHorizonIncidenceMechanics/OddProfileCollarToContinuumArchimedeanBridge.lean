import GaloisForLFunctions.RHTower.CHMDOddProfileArchAbsorptionAndPrimeChainBridge

/-!
# 1D-to-2D Prime-Collar to Continuum Archimedean Bridge (`OddProfileCollarToContinuumArchimedeanBridge`)

This module attacks **Obstacle B** of the CHMD closure programme
(`docs/reports/TransHorizonIncidenceMechanics/CHMD-programme.md`): comparing the 1D discrete
prime-collar line integrals
$$\sum_d \Lambda(d) d^{-1/2} \int_{2x + s = \log d} \operatorname{oddProfileShiftJump}(a, w, s, x)
  = \sum_d \Lambda(d) d^{-1/2} \int_0^{\log d} \operatorname{oddProfileCollarDiffSq}(a, w, \log d, x)\,dx$$
against the 2D continuum absorbed archimedean integral
$$\iint_{(0, \infty)^2} \bigl(\omega(s) - \omega(2y + s)\bigr)\,\operatorname{oddProfileShiftJump}(a, w, s, y)\,ds\,dy$$
plus the half-line prime jumps.

## Mathematical Overview & Resolution of the Two Core Obstructions

Comparing a 1D anti-diagonal prime-collar line integral $2x + s = t$ ($t = \log d$) against the 2D
continuum absorbed archimedean integral faces two structural obstructions:
1. **Order-of-vanishing mismatch at $x \to 0^+$:** On the half-collar $x \in (0, t/2)$,
   $\operatorname{oddProfileCollarDiffSq}(a, w, t, x) = m_a(x)\,m_a(t - x)\,(w(x) - w(t - x))^2$
   vanishes like $O(x)$ as $x \to 0^+$, whereas at fixed $s > 0$ the absorbed archimedean integrand
   $(\omega(s) - \omega(2x + s))\,m_a(x)\,m_a(x + s)\,(w(x) - w(x + s))^2$ vanishes like $O(x^2)$.
2. **Dimension mismatch (1D line vs. 2D area):** A 1D line segment in $(0, \infty)^2$ has 2D
   Lebesgue measure zero and cannot be controlled by a 2D integral without mediating across a
   continuum of intermediate points.

This module resolves both obstructions on the low-prime window $\frac{3}{2}t + \delta + L \le a$
(the exact complement of the high-prime monotone regime $t \ge \frac{2}{3}a$ established in
`CHMDOddMonotoneProfilePrimeSignLaw.lean`) via a two-step decomposition:

1. **Unconditional Strict Monotonicity of `oddProfile a` on `[0, a]` (§1):**
   Using `strictAntiOn_riemannKernelReal_Ici` and parity of $\Theta$, we prove that for every
   $a > 0$, $m_a = \operatorname{oddProfile} a$ is strictly increasing on $[0, a]$
   (`strictMonoOn_oddProfile_Icc`). Consequently, whenever $\frac{3}{2}t \le a$ and
   $x \in (0, t/2)$, all four evaluation points satisfy
   $$0 < m_a(x) < m_a(t - x) < m_a(t) < m_a(t + x).$$

2. **Exact Schur-Complement Direct-Minus-Collar Completion of Squares (§2):**
   At $x \to 0^+$, the direct half-line prime jump $\operatorname{oddProfileShiftJump}(a, w, t, x)$
   has the **exact same $O(x)$ leading coefficient** $m_a'(0)\,x\,m_a(t)\,(w(0) - w(t))^2$ as the
   collar jump $\operatorname{oddProfileCollarDiffSq}(a, w, t, x)$. We prove the exact algebraic
   Schur-complement identity (`oddProfile_direct_sub_collar_schur_identity`):
   $$\operatorname{oddProfileShiftJump}(a, w, t, x)
     - \operatorname{oddProfileCollarDiffSq}(a, w, t, x)
     + \frac{m_a(x)}{m_a(t + x) - m_a(t - x)}\,\operatorname{oddProfileAcrossJump}(a, w, t, x)$$
   $$= \frac{m_a(x)}{m_a(t + x) - m_a(t - x)}
     \Bigl(m_a(t + x)\bigl(w(x) - w(x + t)\bigr) - m_a(t - x)\bigl(w(x) - w(t - x)\bigr)\Bigr)^2 \ge 0,$$
   where $\operatorname{oddProfileAcrossJump}(a, w, t, x) := \operatorname{oddProfileShiftJump}(a, w, 2x, t - x)$
   jumps between $y_1 = t - x \in (t/2, t)$ and $y_2 = t + x \in (t, 3t/2)$ — **both strictly
   bounded away from the origin $0$ by at least $t/2$**. We also prove the weight-free anchor bound
   $\operatorname{oddProfileCollarDiffSq} \le 2\,\operatorname{oddProfileShiftJump} + 2\,\operatorname{oddProfileAcrossJump}$
   (`oddProfileCollarDiffSq_le_two_direct_add_two_across`).

3. **Exponential-Gap Lower Bound on `absorbedArchIntegrand` & Continuum Bridge (§3):**
   We prove the universal pointwise lower bound
   $\omega(s) - \omega(2y + s) \ge (1 - e^{-y})\,\omega(s)$ (`one_sub_exp_neg_mul_archLevyDensity_le_sub`).
   Mediating the across-$t$ jump $(w(t - x) - w(t + x))^2$ through a continuum bridge window
   $z \in (\frac{3}{2}t + \delta, \frac{3}{2}t + \delta + L) \subset (\frac{3}{2}t, a]$ uses
   $m_a(t - x) < m_a(t + x) < m_a(z)$ to bound $\operatorname{oddProfileAcrossJump}(a, w, t, x)$
   pointwise by `absorbedArchIntegrand` at $(t - x, z - (t - x))$ and $(t + x, z - (t + x))$
   (`oddProfileAcrossJump_mul_archGap_le_two_absorbed_legs`).

4. **Integrated 1D-to-2D Bridge and Full-Line Prime Shift-Jump Positivity (§4):**
   Integrating first over $z$ (at fixed $x$) and then over $x \in (0, t/2)$ folds the two bridge
   legs via reflection $y_1 = t - x \in (t/2, t)$ and translation $y_2 = t + x \in (t, 3t/2)$ onto
   the single disjoint union interval $y \in (t/2, 3t/2)$
   (`integral_absorbedArchSlice_sub_add_add_eq_Ioo`), yielding:
   - the unconditional 1D-to-2D collar bound (`integral_oddProfileCollarDiffSq_le_direct_add_absorbedArchSlice`),
   - the 1-for-1 Schur collar-minus-direct excess bound (`integral_oddProfileCollarDiffSq_sub_two_direct_le_absorbedArchSlice`),
   - the full-line prime shift-jump + 2D absorbed archimedean positivity law
     (`two_mul_integral_Ioi_half_le_fullLine_add_absorbedArchSlice`), and
   - the summed low-prime collar-to-archimedean comparison
     (`sum_vonMangoldt_oddProfileCollarDiffSq_le_direct_add_absorbedArchSlice`).
-/

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators
noncomputable section

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.ThetaSourceWard _root_.RHTower.PhiDivisorEnergy

/-! ## Section 1: Unconditional Strict Monotonicity of `oddProfile a` on `Icc 0 a` -/

/-- **Unconditional Strict Monotonicity of `oddProfile a` on `[0, a]`:**
For every $a > 0$, as $x \in [0, a]$ increases, $|x - a| = a - x$ strictly decreases on $[0, a]$
while $x + a$ strictly increases on $[a, 2a]$. Since $\Theta = \operatorname{riemannKernelReal}$ is
even and strictly decreasing on $[0, \infty)$, both $\Theta(x - a)$ and $-\Theta(x + a)$ are
strictly increasing on $[0, a]$, so $m_a(x) = \operatorname{oddProfile} a x$ is strictly increasing
on $[0, a]$. -/
theorem strictMonoOn_oddProfile_Icc {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (oddProfile a) (Icc (0 : ℝ) a) := by
  intro x hx y hy hxy
  unfold oddProfile
  have hsh : 0 < 2 * Real.sinh (a / 2) :=
    mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (half_pos ha))
  have h1 : riemannKernelReal (x - a) < riemannKernelReal (y - a) := by
    rw [show x - a = -(a - x) by ring, show y - a = -(a - y) by ring,
      WeilExcess.riemannKernelReal_neg, WeilExcess.riemannKernelReal_neg]
    exact strictAntiOn_riemannKernelReal_Ici
      (mem_Ici.mpr (by linarith [hy.2])) (mem_Ici.mpr (by linarith [hx.2])) (by linarith)
  have h2 : riemannKernelReal (y + a) < riemannKernelReal (x + a) :=
    strictAntiOn_riemannKernelReal_Ici
      (mem_Ici.mpr (by linarith [hx.1])) (mem_Ici.mpr (by linarith [hy.1])) (by linarith)
  exact div_lt_div_of_pos_right (by linarith) hsh

/-- **Four-Point Strict Ordering of `oddProfile a` Across the Half-Collar (`3t/2 ≤ a`):**
Whenever $a > 0$, $\frac{3}{2}t \le a$ (i.e. $t \le \frac{2}{3}a$, the low-prime complement of the
high-prime monotone threshold $t \ge \frac{2}{3}a$), and $x \in (0, t/2)$, we have
$$m_a(x) < m_a(t - x) < m_a(t) < m_a(t + x).$$ -/
theorem oddProfile_lt_of_mem_half {a t x : ℝ} (ha : 0 < a) (h3t : 3 * t / 2 ≤ a)
    (hx : x ∈ Ioo (0 : ℝ) (t / 2)) :
    oddProfile a x < oddProfile a (t - x) ∧
      oddProfile a (t - x) < oddProfile a t ∧
      oddProfile a t < oddProfile a (t + x) := by
  have hx_mem : x ∈ Icc (0 : ℝ) a := ⟨hx.1.le, by linarith [hx.1, hx.2]⟩
  have htx_mem : t - x ∈ Icc (0 : ℝ) a := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have ht_mem : t ∈ Icc (0 : ℝ) a := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have htx2_mem : t + x ∈ Icc (0 : ℝ) a := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  exact ⟨strictMonoOn_oddProfile_Icc ha hx_mem htx_mem (by linarith [hx.2]),
    strictMonoOn_oddProfile_Icc ha htx_mem ht_mem (by linarith [hx.1]),
    strictMonoOn_oddProfile_Icc ha ht_mem htx2_mem (by linarith [hx.1])⟩

/-! ## Section 2: Exact Schur-Complement Direct-Minus-Collar Completion of Squares -/

/-- The symmetric across-$t$ shift jump between the collar endpoint $t - x$ and the direct endpoint
$t + x$:
`oddProfileAcrossJump a w t x = oddProfileShiftJump a w (2x) (t - x) = m_a(t - x) m_a(t + x) (w(t - x) - w(t + x))²`. -/
def oddProfileAcrossJump (a : ℝ) (w : ℝ → ℝ) (t x : ℝ) : ℝ :=
  oddProfileShiftJump a w (2 * x) (t - x)

theorem oddProfileAcrossJump_eq (a : ℝ) (w : ℝ → ℝ) (t x : ℝ) :
    oddProfileAcrossJump a w t x =
      oddProfile a (t - x) * oddProfile a (t + x) * (w (t - x) - w (t + x)) ^ 2 := by
  unfold oddProfileAcrossJump oddProfileShiftJump
  rw [show t - x + 2 * x = t + x by ring]

theorem oddProfileAcrossJump_nonneg {a t x : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo (0 : ℝ) (t / 2)) (w : ℝ → ℝ) :
    0 ≤ oddProfileAcrossJump a w t x := by
  unfold oddProfileAcrossJump
  exact oddProfileShiftJump_nonneg_of_pos ha (by linarith [hx.1, hx.2]) (by linarith [hx.1]) w

/-- **Exact Schur-Complement Direct-Minus-Collar Completion-of-Squares Identity:**
For any $a, t, x \in \mathbb{R}$ with $m_a(t + x) \ne m_a(t - x)$, the difference between the
1D direct jump `oddProfileShiftJump a w t x` and the 1D collar jump `oddProfileCollarDiffSq a w t x`
(with matching unit coefficients!) plus the Schur-weighted across-$t$ jump equals an exact square. -/
theorem oddProfile_direct_sub_collar_schur_identity (a : ℝ) (w : ℝ → ℝ) (t x : ℝ)
    (hne : oddProfile a (t + x) ≠ oddProfile a (t - x)) :
    oddProfileShiftJump a w t x - oddProfileCollarDiffSq a w t x +
        (oddProfile a x / (oddProfile a (t + x) - oddProfile a (t - x))) *
          oddProfileAcrossJump a w t x =
      (oddProfile a x / (oddProfile a (t + x) - oddProfile a (t - x))) *
        (oddProfile a (t + x) * (w x - w (x + t)) -
          oddProfile a (t - x) * (w x - w (t - x))) ^ 2 := by
  have hsub : oddProfile a (t + x) - oddProfile a (t - x) ≠ 0 := sub_ne_zero.mpr hne
  rw [oddProfileAcrossJump_eq]
  unfold oddProfileShiftJump oddProfileCollarDiffSq
  rw [show x + t = t + x by ring]
  field_simp [hsub]
  ring

/-- **Pointwise 1-for-1 Schur Collar-Minus-Direct Excess Bound on `(0, t / 2)`:**
Whenever $a > 0$, $\frac{3}{2}t \le a$, and $x \in (0, t/2)$, subtracting the direct jump
`oddProfileShiftJump a w t x` from `oddProfileCollarDiffSq a w t x` cancels the $O(x)$ origin
singularity and is bounded above by the Schur-weighted across-$t$ jump. -/
theorem oddProfileCollarDiffSq_sub_direct_le_schur_across {a t x : ℝ} (ha : 0 < a)
    (h3t : 3 * t / 2 ≤ a) (hx : x ∈ Ioo (0 : ℝ) (t / 2)) (w : ℝ → ℝ) :
    oddProfileCollarDiffSq a w t x - oddProfileShiftJump a w t x ≤
      (oddProfile a x / (oddProfile a (t + x) - oddProfile a (t - x))) *
        oddProfileAcrossJump a w t x := by
  obtain ⟨_, h1, h2⟩ := oddProfile_lt_of_mem_half ha h3t hx
  have hlt : oddProfile a (t - x) < oddProfile a (t + x) := h1.trans h2
  have hpos : 0 < oddProfile a x / (oddProfile a (t + x) - oddProfile a (t - x)) :=
    div_pos (oddProfile_pos ha hx.1) (sub_pos.mpr hlt)
  have hid := oddProfile_direct_sub_collar_schur_identity a w t x hlt.ne'
  have hrhs : 0 ≤ (oddProfile a x / (oddProfile a (t + x) - oddProfile a (t - x))) *
      (oddProfile a (t + x) * (w x - w (x + t)) -
        oddProfile a (t - x) * (w x - w (t - x))) ^ 2 :=
    mul_nonneg hpos.le (sq_nonneg _)
  linarith

theorem oddProfileCollarDiffSq_sub_direct_le_of_ratio_bound {a t x κ : ℝ} (ha : 0 < a)
    (h3t : 3 * t / 2 ≤ a) (hx : x ∈ Ioo (0 : ℝ) (t / 2))
    (hκ : oddProfile a x ≤ κ * (oddProfile a (t + x) - oddProfile a (t - x))) (w : ℝ → ℝ) :
    oddProfileCollarDiffSq a w t x - oddProfileShiftJump a w t x ≤
      κ * oddProfileAcrossJump a w t x := by
  obtain ⟨_, h1, h2⟩ := oddProfile_lt_of_mem_half ha h3t hx
  have hlt : oddProfile a (t - x) < oddProfile a (t + x) := h1.trans h2
  have hdiv : oddProfile a x / (oddProfile a (t + x) - oddProfile a (t - x)) ≤ κ :=
    (div_le_iff₀ (sub_pos.mpr hlt)).mpr hκ
  exact (oddProfileCollarDiffSq_sub_direct_le_schur_across ha h3t hx w).trans
    (mul_le_mul_of_nonneg_right hdiv (oddProfileAcrossJump_nonneg ha hx w))

/-- **Unconditional Weight-Free Anchor Bound (`oddProfileCollarDiffSq ≤ 2 direct + 2 across`):**
Whenever $a > 0$, $\frac{3}{2}t \le a$, and $x \in (0, t/2)$, monotonicity $m_a(x) < m_a(t - x) < m_a(t + x)$
implies that both weight ratios in the anchor split across $t + x$ are strictly less than $1$:
$$\operatorname{oddProfileCollarDiffSq}(a, w, t, x)
  \le 2\,\operatorname{oddProfileShiftJump}(a, w, t, x)
    + 2\,\operatorname{oddProfileAcrossJump}(a, w, t, x).$$ -/
theorem oddProfileCollarDiffSq_le_two_direct_add_two_across {a t x : ℝ} (ha : 0 < a)
    (h3t : 3 * t / 2 ≤ a) (hx : x ∈ Ioo (0 : ℝ) (t / 2)) (w : ℝ → ℝ) :
    oddProfileCollarDiffSq a w t x ≤
      2 * oddProfileShiftJump a w t x + 2 * oddProfileAcrossJump a w t x := by
  obtain ⟨h0, h1, h2⟩ := oddProfile_lt_of_mem_half ha h3t hx
  have hm0 : 0 < oddProfile a x := oddProfile_pos ha hx.1
  have hm1 : 0 < oddProfile a (t - x) := oddProfile_pos ha (by linarith [hx.1, hx.2])
  have hlt12 : oddProfile a (t - x) ≤ oddProfile a (t + x) := (h1.trans h2).le
  have hlt02 : oddProfile a x ≤ oddProfile a (t + x) := (h0.trans (h1.trans h2)).le
  have hsq : (w x - w (t - x)) ^ 2 ≤ 2 * (w x - w (t + x)) ^ 2 + 2 * (w (t - x) - w (t + x)) ^ 2 := by
    have : 0 ≤ ((w x - w (t + x)) + (w (t - x) - w (t + x))) ^ 2 := sq_nonneg _
    linarith
  rw [oddProfileAcrossJump_eq]
  unfold oddProfileCollarDiffSq oddProfileShiftJump
  rw [show x + t = t + x by ring]
  have hmul1 : oddProfile a x * oddProfile a (t - x) * (w x - w (t + x)) ^ 2 ≤
      oddProfile a x * oddProfile a (t + x) * (w x - w (t + x)) ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlt12 hm0.le) (sq_nonneg _)
  have hmul2 : oddProfile a x * oddProfile a (t - x) * (w (t - x) - w (t + x)) ^ 2 ≤
      oddProfile a (t - x) * oddProfile a (t + x) * (w (t - x) - w (t + x)) ^ 2 := by
    have : oddProfile a x * oddProfile a (t - x) ≤ oddProfile a (t - x) * oddProfile a (t + x) := by
      nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hstep : oddProfile a x * oddProfile a (t - x) * (w x - w (t - x)) ^ 2 ≤
      oddProfile a x * oddProfile a (t - x) *
        (2 * (w x - w (t + x)) ^ 2 + 2 * (w (t - x) - w (t + x)) ^ 2) :=
    mul_le_mul_of_nonneg_left hsq (mul_nonneg hm0.le hm1.le)
  linarith

/-! ## Section 3: Exponential-Gap Lower Bound on `absorbedArchIntegrand` and Continuum Bridge -/

/-- **Exponential Contraction of Shifted `archLevyDensity`:**
For every $s > 0$ and $y \ge 0$, $\omega(2y + s) \le e^{-y}\,\omega(s)$. -/
theorem archLevyDensity_shift_le_exp_neg_mul {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) :
    archLevyDensity (2 * y + s) ≤ Real.exp (-y) * archLevyDensity s := by
  unfold archLevyDensity
  have hden_s : 0 < 1 - Real.exp (-2 * s) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hden_le : 1 - Real.exp (-2 * s) ≤ 1 - Real.exp (-2 * (2 * y + s)) :=
    sub_le_sub_left (Real.exp_le_exp.mpr (by linarith)) 1
  have hnum : Real.exp (-(2 * y + s) / 2) = Real.exp (-y) * Real.exp (-s / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hnum, ← mul_div_assoc]
  exact div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hden_s hden_le

/-- **Universal Exponential-Gap Lower Bound on $\omega(s) - \omega(2y + s)$:**
For every $s > 0$ and $y \ge 0$, $(1 - e^{-y})\,\omega(s) \le \omega(s) - \omega(2y + s)$. -/
theorem one_sub_exp_neg_mul_archLevyDensity_le_sub {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) :
    (1 - Real.exp (-y)) * archLevyDensity s ≤
      archLevyDensity s - archLevyDensity (2 * y + s) := by
  have h := archLevyDensity_shift_le_exp_neg_mul hs hy
  linarith

/-- **Pointwise Lower Bound on `absorbedArchIntegrand`:**
For every $a > 0$, $s > 0$, $y > 0$, and $w : \mathbb{R} \to \mathbb{R}$,
$$(1 - e^{-y})\,\omega(s)\,\operatorname{oddProfileShiftJump}(a, w, s, y)
  \le \operatorname{absorbedArchIntegrand}(a, w, s, y).$$ -/
theorem one_sub_exp_neg_mul_archLevyDensity_mul_shiftJump_le_absorbed {a s y : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hy : 0 < y) (w : ℝ → ℝ) :
    (1 - Real.exp (-y)) * archLevyDensity s * oddProfileShiftJump a w s y ≤
      absorbedArchIntegrand a w s y := by
  unfold absorbedArchIntegrand
  exact mul_le_mul_of_nonneg_right
    (one_sub_exp_neg_mul_archLevyDensity_le_sub hs hy.le)
    (oddProfileShiftJump_nonneg_of_pos ha hy hs.le w)

/-- **Uniform Strip Lower Bound on `absorbedArchIntegrand` (`y ≥ y₀ > 0`, `0 < s ≤ M`):** -/
theorem archGap_mul_oddProfileShiftJump_le_absorbed {a y₀ M s y : ℝ}
    (ha : 0 < a) (hy₀ : 0 < y₀) (hy : y₀ ≤ y) (hs0 : 0 < s) (hsM : s ≤ M) (w : ℝ → ℝ) :
    ((1 - Real.exp (-y₀)) * archLevyDensity M) * oddProfileShiftJump a w s y ≤
      absorbedArchIntegrand a w s y := by
  have hy_pos : 0 < y := hy₀.trans_le hy
  have hM_pos : 0 < M := hs0.trans_le hsM
  have hexp : 1 - Real.exp (-y₀) ≤ 1 - Real.exp (-y) :=
    sub_le_sub_left (Real.exp_le_exp.mpr (by linarith)) 1
  have hexp_pos : 0 < 1 - Real.exp (-y₀) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have harch : archLevyDensity M ≤ archLevyDensity s := by
    rcases eq_or_lt_of_le hsM with rfl | hlt
    · exact le_rfl
    · exact (strictAntiOn_archLevyDensity_Ioi (mem_Ioi.mpr hs0) (mem_Ioi.mpr hM_pos) hlt).le
  have hmul : (1 - Real.exp (-y₀)) * archLevyDensity M ≤ (1 - Real.exp (-y)) * archLevyDensity s :=
    mul_le_mul hexp harch (archLevyDensity_pos hM_pos).le (hexp_pos.le.trans hexp)
  exact (mul_le_mul_of_nonneg_right hmul
    (oddProfileShiftJump_nonneg_of_pos ha hy_pos hs0.le w)).trans
    (one_sub_exp_neg_mul_archLevyDensity_mul_shiftJump_le_absorbed ha hs0 hy_pos w)

/-- **Pointwise Continuum Bridge Bound for `oddProfileAcrossJump` (`z ∈ (3t/2, a]`):**
For any $x \in (0, t/2)$ and any intermediate bridge point $z \in (3t/2, a]$, strict monotonicity
$m_a(t - x) < m_a(t + x) < m_a(z)$ bounds `oddProfileAcrossJump a w t x` by twice the sum of the
forward shift jumps from $t - x$ to $z$ and from $t + x$ to $z$. -/
theorem oddProfileAcrossJump_le_two_bridge_legs {a t x z : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo (0 : ℝ) (t / 2)) (hz : z ∈ Ioc (3 * t / 2) a) (w : ℝ → ℝ) :
    oddProfileAcrossJump a w t x ≤
      2 * oddProfileShiftJump a w (z - (t - x)) (t - x) +
        2 * oddProfileShiftJump a w (z - (t + x)) (t + x) := by
  have htx_mem : t - x ∈ Icc (0 : ℝ) a :=
    ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2, hz.1, hz.2]⟩
  have htx2_mem : t + x ∈ Icc (0 : ℝ) a :=
    ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2, hz.1, hz.2]⟩
  have hz_mem : z ∈ Icc (0 : ℝ) a := ⟨by linarith [hx.1, hx.2, hz.1], hz.2⟩
  have hm1 : 0 < oddProfile a (t - x) := oddProfile_pos ha (by linarith [hx.1, hx.2])
  have hm2 : 0 < oddProfile a (t + x) := oddProfile_pos ha (by linarith [hx.1, hx.2])
  have hlt2z : oddProfile a (t + x) ≤ oddProfile a z :=
    (strictMonoOn_oddProfile_Icc ha htx2_mem hz_mem (by linarith [hx.2, hz.1])).le
  have hlt1z : oddProfile a (t - x) ≤ oddProfile a z :=
    (strictMonoOn_oddProfile_Icc ha htx_mem hz_mem (by linarith [hx.1, hx.2, hz.1])).le
  have hsq : (w (t - x) - w (t + x)) ^ 2 ≤
      2 * (w (t - x) - w z) ^ 2 + 2 * (w (t + x) - w z) ^ 2 := by
    have : 0 ≤ ((w (t - x) - w z) + (w (t + x) - w z)) ^ 2 := sq_nonneg _
    linarith
  rw [oddProfileAcrossJump_eq]
  unfold oddProfileShiftJump
  rw [show t - x + (z - (t - x)) = z by ring, show t + x + (z - (t + x)) = z by ring]
  have hmul1 : oddProfile a (t - x) * oddProfile a (t + x) * (w (t - x) - w z) ^ 2 ≤
      oddProfile a (t - x) * oddProfile a z * (w (t - x) - w z) ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlt2z hm1.le) (sq_nonneg _)
  have hmul2 : oddProfile a (t - x) * oddProfile a (t + x) * (w (t + x) - w z) ^ 2 ≤
      oddProfile a (t + x) * oddProfile a z * (w (t + x) - w z) ^ 2 := by
    have : oddProfile a (t - x) * oddProfile a (t + x) ≤ oddProfile a (t + x) * oddProfile a z := by
      nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hstep : oddProfile a (t - x) * oddProfile a (t + x) * (w (t - x) - w (t + x)) ^ 2 ≤
      oddProfile a (t - x) * oddProfile a (t + x) *
        (2 * (w (t - x) - w z) ^ 2 + 2 * (w (t + x) - w z) ^ 2) :=
    mul_le_mul_of_nonneg_left hsq (mul_nonneg hm1.le hm2.le)
  linarith

/-- **Pointwise Continuum Bridge into `absorbedArchIntegrand`:**
For any $x \in (0, t/2)$ and $z \in (\frac{3}{2}t + \delta, \frac{3}{2}t + \delta + L) \subset (\frac{3}{2}t, a]$,
both starting points $y_1 = t - x$ and $y_2 = t + x$ satisfy $y_i \ge t/2 > 0$ and both shifts
$s_i = z - y_i$ satisfy $0 < \delta < s_i \le t + \delta + L$, so `oddProfileAcrossJump` is bounded
directly by `absorbedArchIntegrand` at the two bridge legs. -/
theorem oddProfileAcrossJump_mul_archGap_le_two_absorbed_legs {a t δ L x z : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hL : 0 < L) (ha_le : 3 * t / 2 + δ + L ≤ a)
    (hx : x ∈ Ioo (0 : ℝ) (t / 2))
    (hz : z ∈ Ioo (3 * t / 2 + δ) (3 * t / 2 + δ + L)) (w : ℝ → ℝ) :
    ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        oddProfileAcrossJump a w t x ≤
      2 * absorbedArchIntegrand a w (z - (t - x)) (t - x) +
        2 * absorbedArchIntegrand a w (z - (t + x)) (t + x) := by
  have ht2 : 0 < t / 2 := hx.1.trans hx.2
  have hz_Ioc : z ∈ Ioc (3 * t / 2) a := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hbridge := oddProfileAcrossJump_le_two_bridge_legs ha hx hz_Ioc w
  have hc_pos : 0 ≤ (1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L) :=
    mul_nonneg (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).le
      (archLevyDensity_pos (by linarith)).le
  have hleg1 := archGap_mul_oddProfileShiftJump_le_absorbed ha ht2
    (by linarith [hx.2] : t / 2 ≤ t - x)
    (by linarith [hx.1, hx.2, hz.1] : 0 < z - (t - x))
    (by linarith [hx.1, hx.2, hz.2] : z - (t - x) ≤ t + δ + L) w
  have hleg2 := archGap_mul_oddProfileShiftJump_le_absorbed ha ht2
    (by linarith [hx.1, hx.2] : t / 2 ≤ t + x)
    (by linarith [hx.2, hz.1] : 0 < z - (t + x))
    (by linarith [hx.1, hx.2, hz.2] : z - (t + x) ≤ t + δ + L) w
  have hmul := mul_le_mul_of_nonneg_left hbridge hc_pos
  linarith

/-! ## Section 4: Integrated 1D-to-2D Continuum Bridge and Full-Line Prime Positivity -/

/-- The compact-strip 1D slice of the 2D absorbed archimedean integral at starting position $y$:
`absorbedArchSlice a w δ M y = ∫_{s ∈ (δ, M)} absorbedArchIntegrand a w s y`. -/
def absorbedArchSlice (a : ℝ) (w : ℝ → ℝ) (δ M y : ℝ) : ℝ :=
  ∫ s in Ioo δ M, absorbedArchIntegrand a w s y

private def clampedAbsorbedArchIntegrand (a : ℝ) (w : ℝ → ℝ) (δ y s : ℝ) : ℝ :=
  (archLevyDensity (max δ s) - archLevyDensity (max δ (2 * y + s))) *
    oddProfileShiftJump a w s y

private theorem continuous_uncurry_clampedAbsorbedArchIntegrand (a : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (Function.uncurry (clampedAbsorbedArchIntegrand a w δ)) := by
  have hden (g : ℝ × ℝ → ℝ) (hg : Continuous g) :
      Continuous (fun p : ℝ × ℝ => archLevyDensity (max δ (g p))) := by
    unfold archLevyDensity
    refine Continuous.div (by fun_prop) (by fun_prop) fun p => ?_
    have hle : δ ≤ max δ (g p) := le_max_left δ (g p)
    exact (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
  have h1 := hden Prod.snd continuous_snd
  have h2 := hden (fun p : ℝ × ℝ => 2 * p.1 + p.2) (by fun_prop)
  have hjump : Continuous (fun p : ℝ × ℝ => oddProfileShiftJump a w p.2 p.1) := by
    unfold oddProfileShiftJump
    exact (((continuous_oddProfile a).comp continuous_fst).mul
      ((continuous_oddProfile a).comp (continuous_fst.add continuous_snd))).mul
      (((hw.comp continuous_fst).sub (hw.comp (continuous_fst.add continuous_snd))).pow 2)
  exact (h1.sub h2).mul hjump

theorem continuousOn_absorbedArchSlice_Ici (a : ℝ) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    {w : ℝ → ℝ} (hw : Continuous w) :
    ContinuousOn (absorbedArchSlice a w δ M) (Ici (0 : ℝ)) := by
  have hc : Continuous (fun y : ℝ => ∫ s in δ..M, clampedAbsorbedArchIntegrand a w δ y s) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_uncurry_clampedAbsorbedArchIntegrand a hδ hw) δ M
  refine hc.continuousOn.congr fun y hy => ?_
  have hy0 : 0 ≤ y := mem_Ici.mp hy
  rw [absorbedArchSlice, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hδM]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hδM] at hs
  unfold absorbedArchIntegrand clampedAbsorbedArchIntegrand
  rw [max_eq_right hs.1, max_eq_right (by linarith [hs.1])]

theorem continuousOn_absorbedArchIntegrand_Icc {a δ M y : ℝ} (hδ : 0 < δ) (hy : 0 ≤ y)
    {w : ℝ → ℝ} (hw : Continuous w) :
    ContinuousOn (fun s : ℝ => absorbedArchIntegrand a w s y) (Icc δ M) := by
  have hpair : Continuous (fun s : ℝ => (y, s)) := continuous_const.prodMk continuous_id
  have hc := (continuous_uncurry_clampedAbsorbedArchIntegrand a hδ hw).comp hpair
  refine hc.continuousOn.congr fun s hs => ?_
  unfold absorbedArchIntegrand clampedAbsorbedArchIntegrand Function.uncurry
  dsimp
  rw [max_eq_right hs.1, max_eq_right (by linarith [hs.1])]

theorem integrableOn_absorbedArchIntegrand_Ioo {a δ M y : ℝ} (hδ : 0 < δ) (hy : 0 ≤ y)
    {w : ℝ → ℝ} (hw : Continuous w) :
    IntegrableOn (fun s : ℝ => absorbedArchIntegrand a w s y) (Ioo δ M) :=
  (continuousOn_absorbedArchIntegrand_Icc hδ hy hw).integrableOn_Icc.mono_set Ioo_subset_Icc_self

theorem absorbedArchSlice_nonneg {a δ M y : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hy : 0 < y)
    (w : ℝ → ℝ) :
    0 ≤ absorbedArchSlice a w δ M y :=
  setIntegral_nonneg measurableSet_Ioo fun _ hs =>
    absorbedArchIntegrand_nonneg ha (hδ.trans hs.1) hy w

/-- Whenever `s ↦ absorbedArchIntegrand a w s y` is integrable on `Ioi 0`, the compact-strip slice
`absorbedArchSlice a w δ M y` is bounded above by the full half-line absorbed archimedean integral. -/
theorem absorbedArchSlice_le_integral_Ioi {a δ M y : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hy : 0 < y)
    {w : ℝ → ℝ}
    (hint : IntegrableOn (fun s : ℝ => absorbedArchIntegrand a w s y) (Ioi 0)) :
    absorbedArchSlice a w δ M y ≤ ∫ s in Ioi (0 : ℝ), absorbedArchIntegrand a w s y := by
  unfold absorbedArchSlice
  refine setIntegral_mono_set hint ?_
    (Eventually.of_forall fun s hs => mem_Ioi.mpr (hδ.trans hs.1))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact absorbedArchIntegrand_nonneg ha (mem_Ioi.mp hs) hy w

theorem integral_bridge_leg_le_absorbedArchSlice {a t δ L y : ℝ}
    (ha : 0 < a) (hδ : 0 < δ)
    (hy : y ∈ Ioo (t / 2) (3 * t / 2)) {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ z in Ioo (3 * t / 2 + δ) (3 * t / 2 + δ + L),
        absorbedArchIntegrand a w (z - y) y) ≤
      absorbedArchSlice a w δ (t + δ + L) y := by
  have hy_pos : 0 < y := by linarith [hy.1, hy.2]
  have hmp : MeasurePreserving (fun s : ℝ => s + y) volume volume :=
    measurePreserving_add_right volume y
  have hemb : MeasurableEmbedding (fun s : ℝ => s + y) :=
    (Homeomorph.addRight y).measurableEmbedding
  have hpre : (fun s : ℝ => s + y) ⁻¹' Ioo (3 * t / 2 + δ) (3 * t / 2 + δ + L) =
      Ioo (3 * t / 2 + δ - y) (3 * t / 2 + δ + L - y) := by
    ext s
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith
  have htr := hmp.setIntegral_preimage_emb hemb
    (fun z : ℝ => absorbedArchIntegrand a w (z - y) y)
    (Ioo (3 * t / 2 + δ) (3 * t / 2 + δ + L))
  rw [hpre] at htr
  have hcongr : (∫ s in Ioo (3 * t / 2 + δ - y) (3 * t / 2 + δ + L - y),
      absorbedArchIntegrand a w (s + y - y) y) =
      ∫ s in Ioo (3 * t / 2 + δ - y) (3 * t / 2 + δ + L - y),
        absorbedArchIntegrand a w s y :=
    setIntegral_congr_fun measurableSet_Ioo fun s _ => by rw [add_sub_cancel_right]
  rw [← htr, hcongr]
  unfold absorbedArchSlice
  refine setIntegral_mono_set
    (integrableOn_absorbedArchIntegrand_Ioo hδ hy_pos.le hw)
    ?_
    (Eventually.of_forall fun s hs => ⟨by linarith [hs.1, hy.2], by linarith [hs.2, hy.1]⟩)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact absorbedArchIntegrand_nonneg ha (hδ.trans hs.1) hy_pos w

theorem integrableOn_bridge_leg {a t δ L y : ℝ} (hδ : 0 < δ)
    (hy : y ∈ Ioo (t / 2) (3 * t / 2)) {w : ℝ → ℝ} (hw : Continuous w) :
    IntegrableOn (fun z : ℝ => absorbedArchIntegrand a w (z - y) y)
      (Ioo (3 * t / 2 + δ) (3 * t / 2 + δ + L)) := by
  have hy_pos : 0 ≤ y := by linarith [hy.1, hy.2]
  have hc : ContinuousOn (fun s : ℝ => absorbedArchIntegrand a w s y)
      (Icc (3 * t / 2 + δ - y) (3 * t / 2 + δ + L - y)) :=
    (continuousOn_absorbedArchIntegrand_Icc hδ hy_pos hw).mono fun s hs =>
      ⟨by linarith [hs.1, hy.2], hs.2⟩
  have hcomp : ContinuousOn (fun z : ℝ => absorbedArchIntegrand a w (z - y) y)
      (Icc (3 * t / 2 + δ) (3 * t / 2 + δ + L)) :=
    hc.comp (continuous_id.sub continuous_const).continuousOn fun z hz =>
      ⟨by linarith [hz.1], by linarith [hz.2]⟩
  exact hcomp.integrableOn_Icc.mono_set Ioo_subset_Icc_self

/-- **Fixed-`x` Continuum Bridge Inequality:**
Integrating the pointwise continuum bridge over $z \in (\frac{3}{2}t + \delta, \frac{3}{2}t + \delta + L)$
at fixed $x \in (0, t/2)$ bounds `oddProfileAcrossJump a w t x` by the sum of the two absorbed
archimedean slices at $t - x$ and $t + x$. -/
theorem mul_oddProfileAcrossJump_le_two_mul_absorbedArchSlice_add {a t δ L x : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hL : 0 < L) (ha_le : 3 * t / 2 + δ + L ≤ a)
    (hx : x ∈ Ioo (0 : ℝ) (t / 2)) {w : ℝ → ℝ} (hw : Continuous w) :
    L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        oddProfileAcrossJump a w t x ≤
      2 * absorbedArchSlice a w δ (t + δ + L) (t - x) +
        2 * absorbedArchSlice a w δ (t + δ + L) (t + x) := by
  set z₀ := 3 * t / 2 + δ
  set c := ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
    oddProfileAcrossJump a w t x
  have hy1 : t - x ∈ Ioo (t / 2) (3 * t / 2) := ⟨by linarith [hx.2], by linarith [hx.1, hx.2]⟩
  have hy2 : t + x ∈ Ioo (t / 2) (3 * t / 2) := ⟨by linarith [hx.1, hx.2], by linarith [hx.2]⟩
  have hint1 := integrableOn_bridge_leg hδ hy1 hw (a := a) (L := L)
  have hint2 := integrableOn_bridge_leg hδ hy2 hw (a := a) (L := L)
  have hconst : IntegrableOn (fun _ : ℝ => c) (Ioo z₀ (z₀ + L)) :=
    integrableOn_const (by simp)
  have hmono : (∫ _ in Ioo z₀ (z₀ + L), c) ≤
      ∫ z in Ioo z₀ (z₀ + L),
        (2 * absorbedArchIntegrand a w (z - (t - x)) (t - x) +
          2 * absorbedArchIntegrand a w (z - (t + x)) (t + x)) := by
    refine setIntegral_mono_on hconst ((hint1.const_mul 2).add (hint2.const_mul 2))
      measurableSet_Ioo fun z hz => ?_
    exact oddProfileAcrossJump_mul_archGap_le_two_absorbed_legs ha hδ hL ha_le hx hz w
  have hlhs : (∫ _ in Ioo z₀ (z₀ + L), c) = L * c := by
    rw [setIntegral_const, Real.volume_real_Ioo, smul_eq_mul,
      show z₀ + L - z₀ = L by ring, max_eq_left hL.le]
  have hrhs : (∫ z in Ioo z₀ (z₀ + L),
      (2 * absorbedArchIntegrand a w (z - (t - x)) (t - x) +
        2 * absorbedArchIntegrand a w (z - (t + x)) (t + x))) =
      2 * (∫ z in Ioo z₀ (z₀ + L), absorbedArchIntegrand a w (z - (t - x)) (t - x)) +
        2 * (∫ z in Ioo z₀ (z₀ + L), absorbedArchIntegrand a w (z - (t + x)) (t + x)) := by
    rw [integral_add (hint1.const_mul 2) (hint2.const_mul 2),
      integral_const_mul, integral_const_mul]
  have hleg1 := integral_bridge_leg_le_absorbedArchSlice ha hδ hy1 hw (L := L)
  have hleg2 := integral_bridge_leg_le_absorbedArchSlice ha hδ hy2 hw (L := L)
  rw [hlhs, hrhs] at hmono
  dsimp [c] at hmono
  linarith

/-- **Disjoint Folding of the Reflected and Translated Bridge Legs (`(t/2, t) ∪ (t, 3t/2) = (t/2, 3t/2)`):**
As $x$ ranges over $(0, t/2)$, $t - x$ sweeps $(t/2, t)$ and $t + x$ sweeps $(t, 3t/2)$, so the
sum of their integrals equals the single integral over $(t/2, 3t/2)$. -/
theorem integral_absorbedArchSlice_sub_add_add_eq_Ioo (a : ℝ) {t δ M : ℝ}
    (ht : 0 ≤ t) (hδ : 0 < δ) (hδM : δ ≤ M) {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ x in Ioo (0 : ℝ) (t / 2), absorbedArchSlice a w δ M (t - x)) +
        (∫ x in Ioo (0 : ℝ) (t / 2), absorbedArchSlice a w δ M (t + x)) =
      ∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ M y := by
  set F := absorbedArchSlice a w δ M
  have hF : ContinuousOn F (Ici (0 : ℝ)) := continuousOn_absorbedArchSlice_Ici a hδ hδM hw
  have hintF : IntegrableOn F (Icc (t / 2) (3 * t / 2)) :=
    (hF.mono fun y hy => mem_Ici.mpr (by linarith [hy.1])).integrableOn_Icc
  have hrefl : (∫ x in Ioo (0 : ℝ) (t / 2), F (t - x)) = ∫ y in Ioo (t / 2) t, F y := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith)]
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t / 2) F t
    rw [sub_zero, show t - t / 2 = t / 2 by ring] at h
    exact h
  have htrans : (∫ x in Ioo (0 : ℝ) (t / 2), F (t + x)) = ∫ y in Ioo t (3 * t / 2), F y := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith)]
    have h := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := t / 2) F t
    rw [add_zero, show t + t / 2 = 3 * t / 2 by ring] at h
    exact h
  have hunion : Ioc (t / 2) t ∪ Ioc t (3 * t / 2) = Ioc (t / 2) (3 * t / 2) :=
    Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  have hdisj : Disjoint (Ioc (t / 2) t) (Ioc t (3 * t / 2)) :=
    Ioc_disjoint_Ioc_of_le le_rfl
  rw [hrefl, htrans, ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← hunion,
    setIntegral_union hdisj measurableSet_Ioc
      (hintF.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith))))
      (hintF.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith) le_rfl)))]

theorem continuous_oddProfileAcrossJump (a t : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (oddProfileAcrossJump a w t) := by
  have heq : oddProfileAcrossJump a w t = fun x =>
      oddProfile a (t - x) * oddProfile a (t + x) * (w (t - x) - w (t + x)) ^ 2 :=
    funext (oddProfileAcrossJump_eq a w t)
  rw [heq]
  exact (((continuous_oddProfile a).comp (continuous_const.sub continuous_id)).mul
    ((continuous_oddProfile a).comp (continuous_const.add continuous_id))).mul
    (((hw.comp (continuous_const.sub continuous_id)).sub
      (hw.comp (continuous_const.add continuous_id))).pow 2)

theorem continuous_oddProfileShiftJump_right (a t : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (oddProfileShiftJump a w t) := by
  unfold oddProfileShiftJump
  exact ((continuous_oddProfile a).mul
    ((continuous_oddProfile a).comp (continuous_id.add continuous_const))).mul
    ((hw.sub (hw.comp (continuous_id.add continuous_const))).pow 2)

theorem continuous_oddProfileCollarDiffSq (a t : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (oddProfileCollarDiffSq a w t) := by
  unfold oddProfileCollarDiffSq
  exact ((continuous_oddProfile a).mul
    ((continuous_oddProfile a).comp (continuous_const.sub continuous_id))).mul
    ((hw.sub (hw.comp (continuous_const.sub continuous_id))).pow 2)

/-- **Integrated Across-`t` Jump to 2D Continuum Absorbed Archimedean Bound:**
For any continuous $w : \mathbb{R} \to \mathbb{R}$ and $\frac{3}{2}t + \delta + L \le a$, the 1D
half-collar integral of `oddProfileAcrossJump a w t` is bounded directly by the 2D continuum
integral of `absorbedArchIntegrand` over $(y, s) \in (t/2, 3t/2) \times (\delta, t + \delta + L)$. -/
theorem integral_oddProfileAcrossJump_le_absorbedArchSlice {a t δ L : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hδ : 0 < δ) (hL : 0 < L)
    (ha_le : 3 * t / 2 + δ + L ≤ a) {w : ℝ → ℝ} (hw : Continuous w) :
    L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileAcrossJump a w t x) ≤
      2 * ∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ (t + δ + L) y := by
  set M := t + δ + L
  set C := L * ((1 - Real.exp (-(t / 2))) * archLevyDensity M)
  have hF : ContinuousOn (absorbedArchSlice a w δ M) (Ici (0 : ℝ)) :=
    continuousOn_absorbedArchSlice_Ici a hδ (by linarith) hw
  have hint_sub : IntegrableOn (fun x : ℝ => absorbedArchSlice a w δ M (t - x))
      (Ioo (0 : ℝ) (t / 2)) :=
    ((hF.comp (continuous_const.sub continuous_id).continuousOn fun x hx => by
      dsimp; exact mem_Ici.mpr (by linarith [hx.2])).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hint_add : IntegrableOn (fun x : ℝ => absorbedArchSlice a w δ M (t + x))
      (Ioo (0 : ℝ) (t / 2)) :=
    ((hF.comp (continuous_const.add continuous_id).continuousOn fun x hx => by
      dsimp; exact mem_Ici.mpr (by linarith [hx.1])).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hint_across : IntegrableOn (oddProfileAcrossJump a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileAcrossJump a t hw).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hmono : (∫ x in Ioo (0 : ℝ) (t / 2), C * oddProfileAcrossJump a w t x) ≤
      ∫ x in Ioo (0 : ℝ) (t / 2),
        (2 * absorbedArchSlice a w δ M (t - x) + 2 * absorbedArchSlice a w δ M (t + x)) := by
    refine setIntegral_mono_on (hint_across.const_mul C)
      ((hint_sub.const_mul 2).add (hint_add.const_mul 2)) measurableSet_Ioo fun x hx => ?_
    exact mul_oddProfileAcrossJump_le_two_mul_absorbedArchSlice_add ha hδ hL ha_le hx hw
  rw [integral_const_mul, integral_add (hint_sub.const_mul 2) (hint_add.const_mul 2),
    integral_const_mul, integral_const_mul, ← mul_add,
    integral_absorbedArchSlice_sub_add_add_eq_Ioo a ht hδ (by linarith) hw] at hmono
  exact hmono

/-- **Unconditional 1D-Collar-to-2D-Continuum Archimedean Comparison (`Obstacle B` Core Bound):**
For every $a > 0$, $t \ge 0$, $\delta > 0$, $L > 0$ with $\frac{3}{2}t + \delta + L \le a$ and every
continuous $w : \mathbb{R} \to \mathbb{R}$, the 1D origin-crossing collar integral
$\int_0^t \operatorname{oddProfileCollarDiffSq}(a, w, t, x)\,dx$ is bounded above by $4$ times the
half-collar direct shift jump plus $\frac{8}{L(1 - e^{-t/2})\omega(t + \delta + L)}$ times the 2D
continuum absorbed archimedean integral over $(t/2, 3t/2) \times (\delta, t + \delta + L)$. -/
theorem integral_oddProfileCollarDiffSq_le_direct_add_absorbedArchSlice {a t δ L : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hδ : 0 < δ) (hL : 0 < L)
    (ha_le : 3 * t / 2 + δ + L ≤ a) {w : ℝ → ℝ} (hw : Continuous w) :
    L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        (∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x) ≤
      4 * L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x) +
        8 * ∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ (t + δ + L) y := by
  have h3t : 3 * t / 2 ≤ a := by linarith
  have hint_col : IntegrableOn (oddProfileCollarDiffSq a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileCollarDiffSq a t hw).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint_dir : IntegrableOn (oddProfileShiftJump a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileShiftJump_right a t hw).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint_acr : IntegrableOn (oddProfileAcrossJump a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileAcrossJump a t hw).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hhalf_le : (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileCollarDiffSq a w t x) ≤
      2 * (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x) +
        2 * (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileAcrossJump a w t x) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hint_dir.const_mul 2) (hint_acr.const_mul 2)]
    exact setIntegral_mono_on hint_col ((hint_dir.const_mul 2).add (hint_acr.const_mul 2))
      measurableSet_Ioo fun x hx =>
        oddProfileCollarDiffSq_le_two_direct_add_two_across ha h3t hx w
  have hfold := integral_oddProfileCollarDiffSq_eq_two_mul_half a hw ht
  have hcongr : (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w (t - 2 * x) x) =
      ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileCollarDiffSq a w t x :=
    setIntegral_congr_fun measurableSet_Ioo fun x _ =>
      (oddProfileCollarDiffSq_eq_oddProfileShiftJump a w t x).symm
  rw [hcongr] at hfold
  set C := L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L))
  have hC : 0 ≤ C := by
    refine mul_nonneg hL.le (mul_nonneg ?_ (archLevyDensity_pos (by linarith)).le)
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hacr := integral_oddProfileAcrossJump_le_absorbedArchSlice ha ht hδ hL ha_le hw
  have hmul := mul_le_mul_of_nonneg_left hhalf_le hC
  rw [hfold]
  linarith

/-- **Schur 1-for-1 Collar-Minus-Direct Excess Bound via the 2D Absorbed Archimedean Integral:**
When $m_a(x) \le \kappa (m_a(t + x) - m_a(t - x))$ on $x \in (0, t/2)$, subtracting twice the
half-collar direct jump $2 \int_0^{t/2} \operatorname{oddProfileShiftJump}(a, w, t, x)\,dx$ from
$\int_0^t \operatorname{oddProfileCollarDiffSq}(a, w, t, x)\,dx$ cancels the direct jump 1-for-1
and is bounded **purely** by the 2D continuum absorbed archimedean integral. -/
theorem integral_oddProfileCollarDiffSq_sub_two_direct_le_absorbedArchSlice {a t δ L κ : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hδ : 0 < δ) (hL : 0 < L) (hκ0 : 0 ≤ κ)
    (ha_le : 3 * t / 2 + δ + L ≤ a)
    (hκ : ∀ x ∈ Ioo (0 : ℝ) (t / 2),
      oddProfile a x ≤ κ * (oddProfile a (t + x) - oddProfile a (t - x)))
    {w : ℝ → ℝ} (hw : Continuous w) :
    L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        ((∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x) -
          2 * (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x)) ≤
      4 * κ * ∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ (t + δ + L) y := by
  have h3t : 3 * t / 2 ≤ a := by linarith
  have hint_col : IntegrableOn (oddProfileCollarDiffSq a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileCollarDiffSq a t hw).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint_dir : IntegrableOn (oddProfileShiftJump a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileShiftJump_right a t hw).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint_acr : IntegrableOn (oddProfileAcrossJump a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileAcrossJump a t hw).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hsub_le : (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileCollarDiffSq a w t x) -
      (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x) ≤
      κ * (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileAcrossJump a w t x) := by
    rw [← integral_sub hint_col hint_dir, ← integral_const_mul]
    exact setIntegral_mono_on (hint_col.sub hint_dir) (hint_acr.const_mul κ)
      measurableSet_Ioo fun x hx =>
        oddProfileCollarDiffSq_sub_direct_le_of_ratio_bound ha h3t hx (hκ x hx) w
  have hfold := integral_oddProfileCollarDiffSq_eq_two_mul_half a hw ht
  have hcongr : (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w (t - 2 * x) x) =
      ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileCollarDiffSq a w t x :=
    setIntegral_congr_fun measurableSet_Ioo fun x _ =>
      (oddProfileCollarDiffSq_eq_oddProfileShiftJump a w t x).symm
  rw [hcongr] at hfold
  set C := L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L))
  have hC : 0 ≤ C := by
    refine mul_nonneg hL.le (mul_nonneg ?_ (archLevyDensity_pos (by linarith)).le)
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hacr := integral_oddProfileAcrossJump_le_absorbedArchSlice ha ht hδ hL ha_le hw
  have hmul1 := mul_le_mul_of_nonneg_left hsub_le hC
  have hmul2 := mul_le_mul_of_nonneg_left hacr hκ0
  rw [hfold]
  linarith

/-- **Full-Line Prime Shift Jump + 2D Continuum Absorbed Archimedean Positivity Law:**
For any even continuous compactly supported $w : \mathbb{R} \to \mathbb{R}$, the direct prime jump
on $(0, t/2)$ inside $\int_{\mathbb{R}} \operatorname{oddProfileShiftJump}(a, w, t, x)\,dx$ cancels
the direct component of the negative prime collar, so adding $4\kappa$ times the 2D continuum
absorbed archimedean integral dominates twice the non-negative tail prime jump
$2 \int_{t/2}^\infty \operatorname{oddProfileShiftJump}(a, w, t, x)\,dx \ge 0$. -/
theorem two_mul_integral_Ioi_half_le_fullLine_add_absorbedArchSlice {a t δ L κ : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hδ : 0 < δ) (hL : 0 < L) (hκ0 : 0 ≤ κ)
    (ha_le : 3 * t / 2 + δ + L ≤ a)
    (hκ : ∀ x ∈ Ioo (0 : ℝ) (t / 2),
      oddProfile a x ≤ κ * (oddProfile a (t + x) - oddProfile a (t - x)))
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    2 * L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        (∫ x in Ioi (t / 2), oddProfileShiftJump a w t x) ≤
      L * ((1 - Real.exp (-(t / 2))) * archLevyDensity (t + δ + L)) *
        (∫ x : ℝ, oddProfileShiftJump a w t x) +
        4 * κ * ∫ y in Ioo (t / 2) (3 * t / 2), absorbedArchSlice a w δ (t + δ + L) y := by
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
  have hfull := integral_oddProfileShiftJump_eq_halfLine_of_even a hw hwc heven ht
  have hcol : (∫ x in Ioo (0 : ℝ) t,
      oddProfile a x * oddProfile a (t - x) * (w x - w (t - x)) ^ 2) =
      ∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x := rfl
  rw [hcol, hsplit_Ioi] at hfull
  have hschur := integral_oddProfileCollarDiffSq_sub_two_direct_le_absorbedArchSlice
    ha ht hδ hL hκ0 ha_le hκ hw
  rw [hfull]
  linarith [hschur]

/-- **Summed Low-Prime Collar-to-Continuum Archimedean Comparison (`Obstacle B` Finite Sum):**
For any finite set $S$ of prime powers in the low-prime window $\frac{3}{2}\log d + \delta + L \le a$,
the discrete von Mangoldt-weighted prime-collar sum is bounded above by the half-collar direct
prime jumps plus the 2D continuum absorbed archimedean slices. -/
theorem sum_vonMangoldt_oddProfileCollarDiffSq_le_direct_add_absorbedArchSlice
    {a δ L : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hL : 0 < L)
    (S : Finset ℕ) (hS : ∀ d ∈ S, 3 * Real.log d / 2 + δ + L ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) :
    ∑ d ∈ S, vonMangoldtAtom d *
        (L * ((1 - Real.exp (-(Real.log d / 2))) * archLevyDensity (Real.log d + δ + L)) *
          (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x)) ≤
      ∑ d ∈ S, vonMangoldtAtom d *
        (4 * L * ((1 - Real.exp (-(Real.log d / 2))) * archLevyDensity (Real.log d + δ + L)) *
          (∫ x in Ioo (0 : ℝ) (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x) +
          8 * ∫ y in Ioo (Real.log d / 2) (3 * Real.log d / 2),
            absorbedArchSlice a w δ (Real.log d + δ + L) y) := by
  refine Finset.sum_le_sum fun d hd => ?_
  refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg d)
  exact integral_oddProfileCollarDiffSq_le_direct_add_absorbedArchSlice ha
    (Real.log_natCast_nonneg d) hδ hL (hS d hd) hw

end GaloisForLFunctions.TransHorizonIncidenceMechanics
