/-
The smoothed Perron kernel and its Mellin inversion.

The second-order smoothing weight `g(u) = max(1 − u, 0)` has Mellin transform
`∫₀¹ (1 − u) u^{s−1} du = 1/s − 1/(s+1) = 1/(s(s+1))` on the right half-plane `Re s > 0`.
Its inverse Mellin representation is the smoothed Perron formula: for `c > 0` and `y > 0`,

    (1/2π) ∫_{t∈ℝ} y^{c+it} / ((c+it)(c+it+1)) dt = max(1 − 1/y, 0),

the vertical integral converging absolutely because the kernel `1/(s(s+1))` is `O(|t|^{-2})`
on the line `Re s = c`.  The kernel is the analytic engine of a Perron-type summation: paired
with an absolutely convergent Dirichlet series it turns the vertical-line integral of
`L(s)·x^{s+1}/(s(s+1))` into the piecewise-linear partial sum `Σ aₙ·max(x − n, 0)`.

* `perronKernelG` — the smoothing weight `u ↦ max(1 − u, 0)` as a `ℂ`-valued function.
* `perronKernel_mellin` — the closed form `mellin perronKernelG s = 1/(s(s+1))` for `Re s > 0`.
* `perronKernel_mellinConvergent` — Mellin convergence of the weight at every real abscissa
  `c > 0` (the weight is continuous and compactly supported towards `+∞`).
* `perronKernel_verticalIntegrable` — absolute convergence of the inverse-Mellin vertical
  integral: `t ↦ 1/((c+it)(c+it+1))` is integrable, dominated by `(c²+t²)⁻¹`.
* `perronKernel_inversion` — the smoothed Perron formula:
  `(1/2π)·∫_t y^{c+it}/((c+it)(c+it+1)) dt = max(1 − 1/y, 0)` for `c > 0`, `y > 0`.

The second half of the file applies this Perron engine to prove **quiet-crossing rigidity**.
For `x₊ = n+½`, `x₀ = n`, `x₋ = n−½` the second difference of the smoothed partial sum
`A₁(x) = Σ aₘ·max(x−m,0)` collapses to a single kink: `A₁(x₊)+A₁(x₋)−2A₁(x₀) = ½·aₙ`.  On the
Mellin side this equals `(1/2π)∫ F(c+it)·N(c+it)/((c+it)(c+it+1)) dt` with the numerator
`N(s) = x₊^{s+1}+x₋^{s+1}−2x₀^{s+1}`.  Because `N(0)=N(−1)=0`, the ratio `N(s)/(s(s+1))` extends to
an entire function `perronE`, so `F·perronE` is entire and Cauchy's theorem lets the `Re s = c`
contour be pushed left to `Re s = −M`.  Fed a *quiet* sequence of heights `T_k` on which `F`'s
modulus grows slower than `T_k²`, the horizontal edges vanish as `k → ∞`, leaving `½·aₙ` bounded by
the left flank `∝ x₋^{1−M}`, which tends to `0` as `M → ∞`.  Hence `aₙ = 0` for every `n ≥ 2`.

* `perronKink` — the numerator `N(s) = (n+½)^{s+1}+(n−½)^{s+1}−2n^{s+1}`; entire, with `N(0)=N(−1)=0`.
* `perronE` — the entire regularization `N(s)/(s(s+1))` (a double `dslope` of `perronKink`).
* `perronKink_second_difference` — the kink identity `A₁(x₊)+A₁(x₋)−2A₁(x₀) = ½·aₙ`.
* `perronSecondDiff_integral` — the Mellin representation `½·aₙ = (1/2π)∫ F(c+it)·perronE(c+it) dt`.
* `quiet_crossing_rigidity` — a reflection-symmetric Dirichlet carrier that is quiet along a
  sequence of heights `T_k` (with `‖F‖ = o(T_k²)` across the closed critical strip) has all
  coefficients `aₙ = 0` for `n ≥ 2`.
-/
import Mathlib
import GaloisForLFunctions.RHTower.GammalessStripRigidity

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set

noncomputable section

namespace RHTower

/-- The second-order smoothing weight `g(u) = max(1 − u, 0)`, as a `ℂ`-valued function of a real
argument.  It is continuous, equals `1 − u` on `[0,1]`, and vanishes for `u ≥ 1`; its Mellin
transform is the smoothed Perron kernel `1/(s(s+1))`. -/
def perronKernelG (u : ℝ) : ℂ := ((max (1 - u) 0 : ℝ) : ℂ)

/-- The smoothing weight is continuous. -/
theorem continuous_perronKernelG : Continuous perronKernelG := by
  unfold perronKernelG; fun_prop

/-- **Mellin transform of the smoothing weight.**  For `Re s > 0`,
`mellin (u ↦ max(1 − u, 0)) s = 1/(s(s+1))`.  The weight is supported on `(0,1]`, where it equals
`1 − u`, so the Mellin integral collapses to `∫₀¹ (u^{s−1} − u^{s}) du = 1/s − 1/(s+1)`. -/
theorem perronKernel_mellin {s : ℂ} (hs : 0 < s.re) :
    mellin perronKernelG s = 1 / (s * (s + 1)) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have : (s + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at this; linarith
  rw [mellin]
  -- The integrand vanishes off `(0,1]`, so the Mellin integral collapses to `∫ over Ioc 0 1`.
  have hrestrict : ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1) • perronKernelG t
      = ∫ t in Ioc (0:ℝ) 1, (t:ℂ)^(s-1) • perronKernelG t := by
    rw [← MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (t := Ioi (0:ℝ)) (s := Ioc (0:ℝ) 1) measurableSet_Ioi Ioc_subset_Ioi_self ?_]
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    simp only [mem_Ioi] at hx0
    simp only [mem_Ioc, not_and, not_le] at hx1
    have hgt : 1 < x := hx1 hx0
    have hz : perronKernelG x = 0 := by
      simp only [perronKernelG]; rw [max_eq_right (by linarith)]; simp
    rw [hz, smul_zero]
  rw [hrestrict, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  -- On `[0,1]` the integrand is `u^{s−1} − u^{s}`.
  have hcongr : ∫ t in (0:ℝ)..1, (t:ℂ)^(s-1) • perronKernelG t
      = ∫ t in (0:ℝ)..1, ((t:ℂ)^(s-1) - (t:ℂ)^s) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    obtain ⟨ht0, ht1⟩ := ht
    dsimp only
    have hg : perronKernelG t = ((1 - t : ℝ) : ℂ) := by
      simp only [perronKernelG]; rw [max_eq_left (by linarith)]
    rw [hg, smul_eq_mul]
    push_cast
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · rw [← h0]
      simp only [Complex.ofReal_zero, sub_zero, mul_one, Complex.zero_cpow hs0, sub_zero]
    · have htne : (t:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h0
      have hcp : (t:ℂ)^s = (t:ℂ)^(s-1) * (t:ℂ) := by
        conv_lhs => rw [show s = (s-1) + 1 by ring]
        rw [Complex.cpow_add _ _ htne, Complex.cpow_one]
      rw [mul_sub, mul_one, hcp]
  rw [hcongr]
  have hi1 : IntervalIntegrable (fun t:ℝ => (t:ℂ)^(s-1)) volume 0 1 :=
    (intervalIntegrable_cpow' (by simp only [Complex.sub_re, Complex.one_re]; linarith)).symm
  have hi2 : IntervalIntegrable (fun t:ℝ => (t:ℂ)^s) volume 0 1 :=
    (intervalIntegrable_cpow' (by linarith)).symm
  rw [intervalIntegral.integral_sub hi1 hi2,
      integral_cpow (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith)),
      integral_cpow (Or.inl (by linarith))]
  have e1 : s - 1 + 1 = s := by ring
  rw [e1]
  simp only [Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero,
    Complex.zero_cpow hs0, Complex.zero_cpow hs1]
  field_simp
  ring

/-- **Mellin convergence of the smoothing weight.**  At every real abscissa `c > 0` the weight
`u ↦ max(1 − u, 0)` is Mellin convergent: it is continuous (hence locally integrable), it vanishes
identically near `+∞`, and it is bounded near `0`. -/
theorem perronKernel_mellinConvergent {c : ℝ} (hc : 0 < c) :
    MellinConvergent perronKernelG (↑c : ℂ) := by
  apply mellinConvergent_of_isBigO_rpow (a := c+1) (b := 0)
  · exact (continuous_perronKernelG.locallyIntegrable).locallyIntegrableOn _
  · have h0 : perronKernelG =ᶠ[atTop] (fun _ => (0:ℂ)) := by
      filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
      simp only [perronKernelG]; rw [max_eq_right (by linarith)]; simp
    exact h0.isBigO.trans (isBigO_zero _ _)
  · simp only [Complex.ofReal_re]; linarith
  · have h1 : (fun x:ℝ => x^(-(0:ℝ))) = (fun _ => (1:ℝ)) := by
      funext x; rw [neg_zero, Real.rpow_zero]
    rw [h1]
    exact ((continuous_perronKernelG.tendsto 0).mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  · simp only [Complex.ofReal_re]; exact hc

/-- The reciprocal quadratic `t ↦ (c²+t²)⁻¹` is Lebesgue integrable for `c > 0`; it is the
`c`-scaled Cauchy profile `c⁻²·(1+(t/c)²)⁻¹`. -/
private theorem inv_quad_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun t:ℝ => (c^2 + t^2)⁻¹) := by
  have hc0 : c⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hc)
  have h1 : Integrable (fun t:ℝ => (1 + (c⁻¹ * t)^2)⁻¹) :=
    (integrable_inv_one_add_sq).comp_mul_left' hc0
  have heq : (fun t:ℝ => (c^2 + t^2)⁻¹) = fun t => (c^2)⁻¹ * (1 + (c⁻¹ * t)^2)⁻¹ := by
    funext t; rw [← mul_inv]; congr 1; field_simp
  rw [heq]; exact h1.const_mul _

/-- The denominator `(c+it)(c+it+1)` never vanishes when `c > 0`: both factors have positive real
part. -/
private theorem kernel_den_ne {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (↑c + ↑t*I) * (↑c + ↑t*I + 1) ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.re h; simp at this; linarith

/-- The Perron kernel `t ↦ 1/((c+it)(c+it+1))` is continuous on the line `Re s = c > 0`. -/
private theorem kernel_continuous {c : ℝ} (hc : 0 < c) :
    Continuous (fun t:ℝ => ((↑c + ↑t*I) * (↑c + ↑t*I + 1))⁻¹) :=
  Continuous.inv₀ (by fun_prop) (kernel_den_ne hc)

/-- The Perron kernel is dominated by the reciprocal quadratic: `‖1/((c+it)(c+it+1))‖ ≤ (c²+t²)⁻¹`,
because `‖c+it‖ = √(c²+t²)` and `‖c+it+1‖ ≥ ‖c+it‖` (larger real part). -/
private theorem kernel_norm_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖((↑c + ↑t*I) * (↑c + ↑t*I + 1))⁻¹‖ ≤ (c^2 + t^2)⁻¹ := by
  set A : ℂ := (↑c + ↑t*I) with hA
  set B : ℂ := (↑c + ↑t*I + 1) with hB
  have hAnorm : ‖A‖ = Real.sqrt (c^2 + t^2) := by rw [hA, Complex.norm_add_mul_I]
  have hApos : 0 < ‖A‖ := by rw [hAnorm]; apply Real.sqrt_pos.mpr; positivity
  have hBge : ‖A‖ ≤ ‖B‖ := by
    have hBnorm : ‖B‖ = Real.sqrt ((c+1)^2 + t^2) := by
      rw [hB]
      have h : (↑c + ↑t*I + 1 : ℂ) = ↑(c+1) + ↑t*I := by push_cast; ring
      rw [h, Complex.norm_add_mul_I]
    rw [hAnorm, hBnorm]; apply Real.sqrt_le_sqrt; nlinarith
  have hBpos : 0 < ‖B‖ := lt_of_lt_of_le hApos hBge
  rw [norm_inv, norm_mul, inv_le_inv₀ (mul_pos hApos hBpos) (by positivity)]
  calc c^2 + t^2 = ‖A‖ * ‖A‖ := by rw [hAnorm, Real.mul_self_sqrt (by positivity)]
    _ ≤ ‖A‖ * ‖B‖ := mul_le_mul_of_nonneg_left hBge (le_of_lt hApos)

/-- **Absolute convergence of the inverse-Mellin vertical integral.**  On the line `Re s = c > 0`
the Perron kernel `t ↦ 1/((c+it)(c+it+1))` is integrable: its modulus is dominated by
`(c²+t²)⁻¹`, since `‖c+it‖ = √(c²+t²)` and `‖c+it+1‖ ≥ ‖c+it‖`. -/
theorem perronKernel_verticalIntegrable {c : ℝ} (hc : 0 < c) :
    VerticalIntegrable (mellin perronKernelG) c volume := by
  rw [VerticalIntegrable]
  -- On the vertical line the transform is the explicit kernel.
  have hval : (fun t : ℝ => mellin perronKernelG (↑c + ↑t * I))
      = fun t : ℝ => ((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹ := by
    funext t
    rw [perronKernel_mellin (by simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im]; simp; linarith), one_div]
  rw [hval]
  refine (inv_quad_integrable hc).mono' (kernel_continuous hc).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun t => kernel_norm_le hc t)

/-- **The smoothed Perron formula (Mellin inversion of the kernel).**  For `c > 0` and `y > 0`,

    (1/2π) ∫_{t∈ℝ} y^{c+it} / ((c+it)(c+it+1)) dt = max(1 − 1/y, 0).

This is Mellin inversion applied to `perronKernelG` at the point `1/y`: the transform is the
kernel `1/(s(s+1))`, the vertical integral converges absolutely (`O(|t|^{-2})`), and the weight is
continuous, so the inverse Mellin integral reproduces `perronKernelG (1/y) = max(1 − 1/y, 0)`.
The base change `(1/y)^{-(c+it)} = y^{c+it}` (valid for `y > 0`) rewrites the inversion integral
into the stated form. -/
theorem perronKernel_inversion {c : ℝ} (hc : 0 < c) {y : ℝ} (hy : 0 < y) :
    (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, (↑y : ℂ)^((c:ℂ) + ↑t * I) / (((c:ℂ) + ↑t * I) * ((c:ℂ) + ↑t * I + 1))
      = ((max (1 - 1/y) 0 : ℝ) : ℂ) := by
  -- Base change and kernel evaluation turn the integrand into the inversion integrand.
  have hintegrand : (fun t : ℝ => (↑y : ℂ)^((c:ℂ) + ↑t * I) / (((c:ℂ) + ↑t * I) * ((c:ℂ) + ↑t * I + 1)))
      = (fun t : ℝ => (↑(1/y) : ℂ)^(-((c:ℂ) + ↑t * I)) • mellin perronKernelG ((c:ℂ) + ↑t * I)) := by
    funext t
    have hre : 0 < ((c:ℂ) + ↑t * I).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im]; simp; linarith
    have hbase : (↑(1/y) : ℂ)^(-((c:ℂ) + ↑t * I)) = (↑y : ℂ)^((c:ℂ) + ↑t * I) := by
      rw [one_div, Complex.ofReal_inv,
        Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_pos.ne'.symm),
        Complex.cpow_neg, inv_inv]
    rw [perronKernel_mellin hre, smul_eq_mul, hbase, one_div, div_eq_mul_inv]
  rw [hintegrand]
  -- The transformed left side is exactly `mellinInv c (mellin perronKernelG) (1/y)`.
  have key : mellinInv c (mellin perronKernelG) (1/y) = perronKernelG (1/y) :=
    mellinInv_mellin_eq c perronKernelG (by positivity)
      (perronKernel_mellinConvergent hc) (perronKernel_verticalIntegrable hc)
      (continuous_perronKernelG.continuousAt)
  rw [show (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, (↑(1/y) : ℂ)^(-((c:ℂ) + ↑t * I)) • mellin perronKernelG ((c:ℂ) + ↑t * I)
      = mellinInv c (mellin perronKernelG) (1/y) from rfl, key]
  simp only [perronKernelG]

/-- Continuity in the height `t` of a single Dirichlet term `t ↦ aₙ·(n)^{-(c+it)}` restricted to
the vertical line `Re s = c`. -/
private theorem term_line_continuous (a : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    Continuous (fun t:ℝ => LSeries.term a (↑c + ↑t * I) n) := by
  rcases eq_or_ne n 0 with h | h
  · subst h; simp only [LSeries.term_zero]; exact continuous_const
  · have heq : (fun t:ℝ => LSeries.term a (↑c + ↑t * I) n)
        = fun t:ℝ => a n * (↑n:ℂ)^(-(↑c + (↑t:ℂ) * I)) := by
      funext t; rw [LSeries.term_of_ne_zero h, Complex.cpow_neg, div_eq_mul_inv]
    rw [heq]
    exact continuous_const.mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Nat.cast_ne_zero.mpr h)))

/-- **Smoothed Perron summation.**  For an absolutely convergent Dirichlet series `L(s) = Σ aₙ n^{-s}`
at a real abscissa `c > 0` and any `x > 0`,

    Σ_{n≥1} aₙ · max(x − n, 0)
      = (1/2π) ∫_{t∈ℝ} L(c+it) · x^{(c+it)+1} / ((c+it)(c+it+1)) dt.

The vertical integral is expanded as `Σₙ ∫ aₙ n^{-(c+it)} x^{(c+it)+1}/((c+it)(c+it+1)) dt`; the
sum and integral are interchanged by dominated convergence (each term is dominated by
`‖aₙ‖ n^{-c} x^{c+1} (c²+t²)⁻¹`, absolutely summable via `Σ ‖aₙ‖ n^{-c} < ∞`); and the smoothed
Perron kernel identity `(1/2π)∫ (x/n)^{c+it}/((c+it)(c+it+1)) dt = max(1 − n/x, 0)` evaluates each
term to `aₙ·x·max(1 − n/x, 0) = aₙ·max(x − n, 0)`.  The `n = 0` term is absent on both sides
(Dirichlet coefficients are `1`-indexed). -/
theorem smoothed_perron_sum {a : ℕ → ℂ} {c : ℝ} (hc : 0 < c) (hsum : LSeriesSummable a c)
    {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, (if n = 0 then (0:ℂ) else a n * ((max (x - n) 0 : ℝ) : ℂ))
      = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, LSeries a (↑c + ↑t * I) *
          ((↑x : ℂ) ^ ((↑c + ↑t * I) + 1) / ((↑c + ↑t * I) * ((↑c + ↑t * I) + 1))) := by
  have hxc : (↑x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  -- The per-term integrand.
  set F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term a (↑c + ↑t * I) n *
      ((↑x : ℂ) ^ ((↑c + ↑t * I) + 1) * ((↑c + ↑t * I) * ((↑c + ↑t * I) + 1))⁻¹) with hF
  have hre : ∀ t : ℝ, (↑c + ↑t * I : ℂ).re = c := by intro t; simp
  -- The per-term modulus bound: `‖Fₙ t‖ = Cₙ·‖kernel‖ ≤ Cₙ·(c²+t²)⁻¹`.
  set Cn : ℕ → ℝ := fun n => ‖LSeries.term a (↑c) n‖ * x ^ (c + 1) with hCn
  have hCn_nonneg : ∀ n, 0 ≤ Cn n := fun n =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx.le _)
  have hFnorm : ∀ n t, ‖F n t‖ = Cn n * ‖((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹‖ := by
    intro n t
    have h1 : ‖LSeries.term a (↑c + ↑t * I) n‖ = ‖LSeries.term a (↑c) n‖ := by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre, Complex.ofReal_re]
    have h2 : ‖(↑x : ℂ) ^ ((↑c + ↑t * I) + 1)‖ = x ^ (c + 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      congr 1
      rw [Complex.add_re, Complex.one_re, hre t]
    simp only [hF, hCn, norm_mul]
    rw [h1, h2]; ring
  have hFbound : ∀ n t, ‖F n t‖ ≤ Cn n * (c ^ 2 + t ^ 2)⁻¹ := by
    intro n t; rw [hFnorm n t]
    exact mul_le_mul_of_nonneg_left (kernel_norm_le hc t) (hCn_nonneg n)
  have hFcont : ∀ n, Continuous (F n) := by
    intro n
    simp only [hF]
    refine (term_line_continuous a c n).mul (Continuous.mul ?_ (kernel_continuous hc))
    exact Continuous.const_cpow (by fun_prop) (Or.inl hxc)
  have hFint : ∀ n, Integrable (F n) := fun n =>
    ((inv_quad_integrable hc).const_mul (Cn n)).mono'
      (hFcont n).aestronglyMeasurable (Filter.Eventually.of_forall (hFbound n))
  -- Absolute summability of the term integral norms.
  set M : ℝ := ∫ t : ℝ, ‖((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹‖ with hM
  have hSummable : Summable (fun n => ∫ t : ℝ, ‖F n t‖) := by
    have hCM : Summable (fun n => Cn n * M) := by
      have hbase : Summable (fun n => ‖LSeries.term a (↑c) n‖) := summable_norm_iff.mpr hsum
      have := hbase.mul_right (x ^ (c + 1) * M)
      refine this.congr (fun n => ?_)
      simp only [hCn]; ring
    refine hCM.congr (fun n => ?_)
    have : (fun t : ℝ => ‖F n t‖) = fun t : ℝ => Cn n * ‖((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹‖ := by
      funext t; exact hFnorm n t
    rw [this, MeasureTheory.integral_const_mul, ← hM]
  -- Expand the L-series, interchange sum and integral.
  have hExpand : ∀ t : ℝ,
      LSeries a (↑c + ↑t * I) *
          ((↑x : ℂ) ^ ((↑c + ↑t * I) + 1) / ((↑c + ↑t * I) * ((↑c + ↑t * I) + 1)))
        = ∑' n, F n t := by
    intro t
    rw [show LSeries a (↑c + ↑t * I) = ∑' n, LSeries.term a (↑c + ↑t * I) n from rfl,
      div_eq_mul_inv, ← tsum_mul_right]
  have hswap : ∫ t : ℝ, LSeries a (↑c + ↑t * I) *
        ((↑x : ℂ) ^ ((↑c + ↑t * I) + 1) / ((↑c + ↑t * I) * ((↑c + ↑t * I) + 1)))
      = ∑' n, ∫ t : ℝ, F n t := by
    simp_rw [hExpand]
    exact (integral_tsum_of_summable_integral_norm hFint hSummable).symm
  rw [hswap]
  have hIntSummable : Summable (fun n => ∫ t : ℝ, F n t) :=
    Summable.of_norm_bounded hSummable (fun n => norm_integral_le_integral_norm _)
  rw [← Summable.tsum_const_smul (1 / (2 * Real.pi) : ℝ) hIntSummable]
  -- Evaluate termwise.
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [if_pos rfl]
    simp only [hF, LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, smul_zero]
  · rw [if_neg hn]
    have hnpos : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    -- Rewrite the term integrand as `(aₙ·x)·((x/n)^{c+it}·kernel)`.
    have hpt : F n = fun t:ℝ =>
        (a n * ↑x) * ((↑(x/n):ℂ) ^ (↑c + ↑t * I) * ((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹) := by
      funext t
      have alg : (↑n:ℂ) ^ (-(↑c + (↑t:ℂ) * I)) * (↑x:ℂ) ^ ((↑c + (↑t:ℂ) * I) + 1)
          = ↑x * (↑(x/n):ℂ) ^ (↑c + (↑t:ℂ) * I) := by
        have harg : (↑(n:ℝ):ℂ).arg ≠ Real.pi := by
          rw [Complex.arg_ofReal_of_nonneg hnpos.le]; exact Real.pi_pos.ne'.symm
        have hdiv : (↑(x/n):ℂ) ^ (↑c + (↑t:ℂ) * I)
            = (↑x:ℂ) ^ (↑c + (↑t:ℂ) * I) * (↑n:ℂ) ^ (-(↑c + (↑t:ℂ) * I)) := by
          rw [Complex.ofReal_div, div_eq_mul_inv, ← Complex.ofReal_inv,
              Complex.mul_cpow_ofReal_nonneg hx.le (by positivity), Complex.ofReal_inv,
              Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, Complex.ofReal_natCast]
        rw [hdiv]
        have hx1 : (↑x:ℂ) ^ ((↑c + (↑t:ℂ) * I) + 1) = (↑x:ℂ) ^ (↑c + (↑t:ℂ) * I) * (↑x:ℂ) := by
          rw [Complex.cpow_add _ _ hxc, Complex.cpow_one]
        rw [hx1]; ring
      simp only [hF]
      rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
      rw [show a n * (↑n:ℂ) ^ (-(↑c + ↑t * I)) *
            ((↑x:ℂ) ^ ((↑c + ↑t * I) + 1) * ((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹)
          = a n * ((↑n:ℂ) ^ (-(↑c + ↑t * I)) * (↑x:ℂ) ^ ((↑c + ↑t * I) + 1)) *
            ((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹ by ring]
      rw [alg]; ring
    have hintFn : ∫ t : ℝ, F n t = (a n * ↑x) *
        ∫ t : ℝ, ((↑(x/n):ℂ) ^ (↑c + ↑t * I) * ((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹) := by
      rw [hpt, MeasureTheory.integral_const_mul]
    -- The term integral evaluates via the smoothed Perron kernel identity at `y = x/n`.
    have hJ : (1 / (2 * Real.pi) : ℝ) •
          ∫ t : ℝ, (↑(x/n):ℂ) ^ (↑c + ↑t * I) * ((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹
        = ((max (1 - 1 / (x / n)) 0 : ℝ) : ℂ) :=
      perronKernel_inversion hc (show (0:ℝ) < x / n by positivity)
    rw [hintFn, ← mul_smul_comm, hJ]
    -- Real identity `x·max(1 − 1/(x/n), 0) = max(x − n, 0)`.
    have hmax : x * max (1 - 1 / (x / n)) 0 = max (x - ↑n) 0 := by
      rw [mul_max_of_nonneg _ _ hx.le, mul_zero]
      congr 1
      field_simp
    rw [mul_assoc, ← Complex.ofReal_mul, hmax]

/-- The Perron **kink numerator** `N(s) = (n+½)^{s+1} + (n−½)^{s+1} − 2·n^{s+1}`.  Each summand is
an entire function of `s` (positive real base), and the second-difference weighting is chosen so
that `N(0) = (n+½)+(n−½)−2n = 0` and `N(−1) = 1+1−2 = 0`, killing the two poles `s = 0, −1` of the
smoothed Perron kernel `1/(s(s+1))`. -/
def perronKink (n : ℕ) (s : ℂ) : ℂ :=
    (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (s + 1) + (((n : ℝ) - 1 / 2 : ℝ) : ℂ) ^ (s + 1)
      - 2 * (((n : ℝ) : ℝ) : ℂ) ^ (s + 1)

/-- `N(0) = 0`: at `s = 0` the exponent is `1`, so the numerator is `(n+½)+(n−½)−2n = 0`. -/
theorem perronKink_zero (n : ℕ) : perronKink n 0 = 0 := by
  unfold perronKink
  rw [show (0 : ℂ) + 1 = 1 by ring, Complex.cpow_one, Complex.cpow_one, Complex.cpow_one]
  push_cast; ring

/-- `N(−1) = 0`: at `s = −1` the exponent is `0`, so each power is `1` and `1+1−2 = 0`. -/
theorem perronKink_negOne (n : ℕ) : perronKink n (-1) = 0 := by
  unfold perronKink
  rw [show (-1 : ℂ) + 1 = 0 by ring, Complex.cpow_zero, Complex.cpow_zero, Complex.cpow_zero]
  ring

/-- The kink numerator is entire: a sum of constant-base complex powers `c^{s+1}` with `c > 0`
(requiring `n ≥ 1` so that the base `n−½ ≥ ½` is positive). -/
theorem perronKink_differentiable {n : ℕ} (hn : 1 ≤ n) : Differentiable ℂ (perronKink n) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb1 : (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
    exact_mod_cast ne_of_gt this
  have hb2 : (((n : ℝ) - 1 / 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
    exact_mod_cast ne_of_gt this
  have hb3 : (((n : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast ne_of_gt this
  have d1 : Differentiable ℂ (fun s : ℂ => (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (s + 1)) :=
    fun s => (differentiableAt_id.add_const 1).const_cpow (Or.inl hb1)
  have d2 : Differentiable ℂ (fun s : ℂ => (((n : ℝ) - 1 / 2 : ℝ) : ℂ) ^ (s + 1)) :=
    fun s => (differentiableAt_id.add_const 1).const_cpow (Or.inl hb2)
  have d3 : Differentiable ℂ (fun s : ℂ => (((n : ℝ) : ℝ) : ℂ) ^ (s + 1)) :=
    fun s => (differentiableAt_id.add_const 1).const_cpow (Or.inl hb3)
  exact (d1.add d2).sub (d3.const_mul 2)

/-- The **entire regularization** `E(s) = N(s)/(s(s+1))`, realized as a double difference quotient
`dslope (dslope N 0) (−1)`.  Since `N(0) = 0` the inner `dslope … 0` removes the pole at `0`
(agreeing with `N(s)/s`), and since that quotient vanishes at `−1` the outer `dslope … (−1)`
removes the pole at `−1`; the result is entire wherever `N` is. -/
def perronE (n : ℕ) : ℂ → ℂ := dslope (dslope (perronKink n) 0) (-1)

/-- `E` is entire: complex `dslope` of an entire function is entire (removable singularity),
applied twice. -/
theorem perronE_differentiable {n : ℕ} (hn : 1 ≤ n) : Differentiable ℂ (perronE n) := by
  have g1 : Differentiable ℂ (dslope (perronKink n) 0) := by
    rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
    exact (perronKink_differentiable hn).differentiableOn
  unfold perronE
  rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
  exact g1.differentiableOn

/-- Away from the two removed poles, `E(s) = N(s)/(s(s+1))`.  Unfolding both difference quotients:
`dslope N 0 s = N(s)/s` (using `N(0)=0`) and `dslope (·) (−1) s = (that)/(s+1)` (using the inner
quotient's value `0` at `−1`), whose product denominator is `s(s+1)`. -/
theorem perronE_eq (n : ℕ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ -1) :
    perronE n s = perronKink n s / (s * (s + 1)) := by
  have e0 : dslope (perronKink n) 0 s = perronKink n s / s := by
    rw [dslope_of_ne _ h0, slope_def_field, perronKink_zero, sub_zero, sub_zero]
  have em1 : dslope (perronKink n) 0 (-1) = 0 := by
    rw [dslope_of_ne _ (by norm_num : (-1 : ℂ) ≠ 0), slope_def_field, perronKink_zero,
        perronKink_negOne, sub_zero, zero_div]
  unfold perronE
  rw [dslope_of_ne _ h1, slope_def_field, e0, em1, sub_zero, sub_neg_eq_add, div_div]

/-- Uniform triangle bound on the kink numerator: `‖N(s)‖ ≤ (n+½)^{σ+1} + (n−½)^{σ+1} + 2·n^{σ+1}`
where `σ = Re s`, since `‖c^{s+1}‖ = c^{Re s + 1}` for a positive real base `c`. -/
theorem perronKink_norm_le {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ‖perronKink n s‖ ≤ ((n : ℝ) + 1 / 2) ^ (s.re + 1) + ((n : ℝ) - 1 / 2) ^ (s.re + 1)
      + 2 * ((n : ℝ)) ^ (s.re + 1) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb1 : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hb2 : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hb3 : (0 : ℝ) < (n : ℝ) := by linarith
  have hre : (s + 1).re = s.re + 1 := by rw [Complex.add_re, Complex.one_re]
  have n1 : ‖(((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (s + 1)‖ = ((n : ℝ) + 1 / 2) ^ (s.re + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb1, hre]
  have n2 : ‖(((n : ℝ) - 1 / 2 : ℝ) : ℂ) ^ (s + 1)‖ = ((n : ℝ) - 1 / 2) ^ (s.re + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb2, hre]
  have n3 : ‖(((n : ℝ) : ℝ) : ℂ) ^ (s + 1)‖ = ((n : ℝ)) ^ (s.re + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb3, hre]
  unfold perronKink
  calc ‖(((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (s + 1) + (((n : ℝ) - 1 / 2 : ℝ) : ℂ) ^ (s + 1)
          - 2 * (((n : ℝ) : ℝ) : ℂ) ^ (s + 1)‖
      ≤ ‖(((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (s + 1) + (((n : ℝ) - 1 / 2 : ℝ) : ℂ) ^ (s + 1)‖
          + ‖2 * (((n : ℝ) : ℝ) : ℂ) ^ (s + 1)‖ := norm_sub_le _ _
    _ ≤ (‖(((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (s + 1)‖ + ‖(((n : ℝ) - 1 / 2 : ℝ) : ℂ) ^ (s + 1)‖)
          + ‖2 * (((n : ℝ) : ℝ) : ℂ) ^ (s + 1)‖ := by gcongr; exact norm_add_le _ _
    _ = ((n : ℝ) + 1 / 2) ^ (s.re + 1) + ((n : ℝ) - 1 / 2) ^ (s.re + 1)
          + 2 * ((n : ℝ)) ^ (s.re + 1) := by
        rw [norm_mul, n1, n2, n3]; simp only [Complex.norm_ofNat]

/-- **The kink identity.**  The smoothed partial sum `A₁(x) = Σₘ aₘ·max(x−m,0)` obeys, at the three
knots `x₊ = n+½`, `x₀ = n`, `x₋ = n−½`, the exact second difference
`A₁(x₊) + A₁(x₋) − 2·A₁(x₀) = ½·aₙ`.  Each sum truncates to `m ≤ n`; the pointwise weight
`max(x₊−m,0)+max(x₋−m,0)−2·max(x₀−m,0)` is affine and vanishes for `1 ≤ m ≤ n−1`, is `½` at `m = n`,
and vanishes for `m = 0`, so only the `m = n` term survives. -/
theorem perronKink_second_difference (a : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (∑' m : ℕ, (if m = 0 then (0 : ℂ) else a m * ((max (((n : ℝ) + 1 / 2) - m) 0 : ℝ) : ℂ)))
      + (∑' m : ℕ, (if m = 0 then (0 : ℂ) else a m * ((max (((n : ℝ) - 1 / 2) - m) 0 : ℝ) : ℂ)))
      - 2 * (∑' m : ℕ, (if m = 0 then (0 : ℂ) else a m * ((max ((n : ℝ) - m) 0 : ℝ) : ℂ)))
      = a n * (1 / 2) := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hvanish : ∀ (x : ℝ), x ≤ (n : ℝ) + 1 / 2 →
      ∀ m ∉ Finset.range (n + 1),
        (if m = 0 then (0 : ℂ) else a m * ((max (x - m) 0 : ℝ) : ℂ)) = 0 := by
    intro x hx m hm
    rw [Finset.mem_range, not_lt] at hm
    have hmn : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
    have hle : x - (m : ℝ) ≤ 0 := by linarith
    rw [max_eq_right hle]; simp
  rw [tsum_eq_sum (hvanish _ (by linarith)),
      tsum_eq_sum (hvanish _ (by linarith)),
      tsum_eq_sum (hvanish _ (by linarith))]
  rw [show (∑ m ∈ Finset.range (n + 1),
            (if m = 0 then (0 : ℂ) else a m * ((max (((n : ℝ) + 1 / 2) - m) 0 : ℝ) : ℂ)))
          + (∑ m ∈ Finset.range (n + 1),
            (if m = 0 then (0 : ℂ) else a m * ((max (((n : ℝ) - 1 / 2) - m) 0 : ℝ) : ℂ)))
          - 2 * (∑ m ∈ Finset.range (n + 1),
            (if m = 0 then (0 : ℂ) else a m * ((max ((n : ℝ) - m) 0 : ℝ) : ℂ)))
        = ∑ m ∈ Finset.range (n + 1),
            ((if m = 0 then (0 : ℂ) else a m * ((max (((n : ℝ) + 1 / 2) - m) 0 : ℝ) : ℂ))
              + (if m = 0 then (0 : ℂ) else a m * ((max (((n : ℝ) - 1 / 2) - m) 0 : ℝ) : ℂ))
              - 2 * (if m = 0 then (0 : ℂ) else a m * ((max ((n : ℝ) - m) 0 : ℝ) : ℂ)))
        from by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]]
  rw [Finset.sum_eq_single n]
  · rw [if_neg hn0, if_neg hn0, if_neg hn0]
    have e1 : ((n : ℝ) + 1 / 2) - n = 1 / 2 := by ring
    have e2 : ((n : ℝ) - 1 / 2) - n = -(1 / 2) := by ring
    have e3 : (n : ℝ) - n = 0 := by ring
    rw [e1, e2, e3, max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2),
        max_eq_right (by norm_num : (-(1 / 2) : ℝ) ≤ 0), max_self]
    push_cast; ring
  · intro m hmem hmn
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0; simp
    · have hmlt : m < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)) hmn
      have hmr : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmlt
      rw [if_neg hm0.ne', if_neg hm0.ne', if_neg hm0.ne',
          max_eq_left (by linarith : (0 : ℝ) ≤ ((n : ℝ) + 1 / 2) - m),
          max_eq_left (by linarith : (0 : ℝ) ≤ ((n : ℝ) - 1 / 2) - m),
          max_eq_left (by linarith : (0 : ℝ) ≤ (n : ℝ) - m)]
      push_cast; ring
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h

/-- Kernel decay on a horizontal segment: at any point `x + t·I` with `|t| ≥ T > 0`, the modulus of
`1/(s(s+1))` is at most `T^{-2}`, since `‖s‖ ≥ |Im s| = |t| ≥ T` and likewise `‖s+1‖ ≥ T`. -/
private theorem kernel_line_bound {t T : ℝ} (hT : 0 < T) (ht : T ≤ |t|) (x : ℝ) :
    ‖((↑x + ↑t * I) * (↑x + ↑t * I + 1))⁻¹‖ ≤ (T ^ 2)⁻¹ := by
  set s : ℂ := (↑x + ↑t * I : ℂ) with hs
  have him : s.im = t := by rw [hs]; simp
  have him1 : (s + 1).im = t := by rw [Complex.add_im, him, Complex.one_im, add_zero]
  have hA : T ≤ ‖s‖ := le_trans ht (by rw [← him]; exact Complex.abs_im_le_norm s)
  have hB : T ≤ ‖s + 1‖ := le_trans ht (by rw [← him1]; exact Complex.abs_im_le_norm (s + 1))
  have hge : T ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, sq]; exact mul_le_mul hA hB (le_of_lt hT) (le_trans hT.le hA)
  rw [norm_inv]; exact inv_anti₀ (by positivity) hge

/-- Kernel decay on the vertical line `Re s = −M` (with `M > 1`): `‖1/(s(s+1))‖ ≤ ((M−1)²+y²)⁻¹`,
since `‖s‖ = √(M²+y²) ≥ √((M−1)²+y²)` and `‖s+1‖ = √((M−1)²+y²)`. -/
private theorem kernel_left_bound {M y : ℝ} (hM : 1 < M) :
    ‖((↑(-M) + ↑y * I) * (↑(-M) + ↑y * I + 1))⁻¹‖ ≤ ((M - 1) ^ 2 + y ^ 2)⁻¹ := by
  have hAnorm : ‖(↑(-M) + ↑y * I : ℂ)‖ = Real.sqrt ((-M) ^ 2 + y ^ 2) := Complex.norm_add_mul_I _ _
  have hBeq : (↑(-M) + ↑y * I + 1 : ℂ) = ↑(1 - M) + ↑y * I := by push_cast; ring
  have hBnorm : ‖(↑(-M) + ↑y * I + 1 : ℂ)‖ = Real.sqrt ((1 - M) ^ 2 + y ^ 2) := by
    rw [hBeq, Complex.norm_add_mul_I]
  have hden : (0 : ℝ) < (M - 1) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y, sq_nonneg (M - 1)]
  have hAge : Real.sqrt ((M - 1) ^ 2 + y ^ 2) ≤ ‖(↑(-M) + ↑y * I : ℂ)‖ := by
    rw [hAnorm]; apply Real.sqrt_le_sqrt; nlinarith
  have hBge : Real.sqrt ((M - 1) ^ 2 + y ^ 2) ≤ ‖(↑(-M) + ↑y * I + 1 : ℂ)‖ := by
    rw [hBnorm]; apply Real.sqrt_le_sqrt; nlinarith
  have hge : (M - 1) ^ 2 + y ^ 2 ≤ ‖(↑(-M) + ↑y * I) * (↑(-M) + ↑y * I + 1)‖ := by
    rw [norm_mul]
    calc (M - 1) ^ 2 + y ^ 2
        = Real.sqrt ((M - 1) ^ 2 + y ^ 2) * Real.sqrt ((M - 1) ^ 2 + y ^ 2) := by
          rw [Real.mul_self_sqrt hden.le]
      _ ≤ ‖(↑(-M) + ↑y * I : ℂ)‖ * ‖(↑(-M) + ↑y * I + 1 : ℂ)‖ :=
          mul_le_mul hAge hBge (Real.sqrt_nonneg _) (le_trans (Real.sqrt_nonneg _) hAge)
  rw [norm_inv]; exact inv_anti₀ hden hge

/-- **Mellin representation of the kink.**  For a reflection-carrier `F` agreeing with the absolutely
convergent Dirichlet series `L(s) = Σ aₘ m^{−s}` on `Re s ≥ c > 0`,

    ½·aₙ = (1/2π) ∫_{t∈ℝ} F(c+it)·E(c+it) dt,       E = N/(s(s+1)),

obtained by applying smoothed Perron summation at the three knots `x₊,x₀,x₋`, combining by
linearity of the integral, and folding `x₊^{s+1}+x₋^{s+1}−2x₀^{s+1} = N(s)` with `L = F` on the
line.  Each single-knot integrand is dominated by `B·xᵢ^{c+1}·(c²+t²)⁻¹`, giving the integrability
needed for the linear combination. -/
theorem perronSecondDiff_integral {F : ℂ → ℂ} {a : ℕ → ℂ} {c : ℝ} (hc0 : 0 < c)
    (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s) {n : ℕ} (hn : 1 ≤ n) :
    a n * (1 / 2)
      = (1 / (2 * Real.pi) : ℝ) •
          ∫ t : ℝ, F ((c : ℂ) + ↑t * I) * perronE n ((c : ℂ) + ↑t * I) := by
  obtain ⟨B, hB⟩ := lseries_bounded_on_halfplane hsum
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxp : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hx₀ : (0 : ℝ) < (n : ℝ) := by linarith
  have hxm : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hrec : ∀ t : ℝ, ((c : ℂ) + ↑t * I).re = c := fun t => by simp
  have hle : ∀ t : ℝ, c ≤ ((c : ℂ) + ↑t * I).re := fun t => le_of_eq (hrec t).symm
  have hLF : ∀ t : ℝ, LSeries a ((c : ℂ) + ↑t * I) = F ((c : ℂ) + ↑t * I) := fun t =>
    (hFeq _ (hle t)).symm
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB ↑c (by rw [Complex.ofReal_re]))
  -- Integrability of each single-knot Perron integrand on the line `Re s = c`.
  have hIntKnot : ∀ x : ℝ, 0 < x → Integrable (fun t : ℝ =>
      LSeries a ((c : ℂ) + ↑t * I) *
        ((↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
          (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))) := by
    intro x hx
    have hxc : (↑x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
    have hcont : Continuous (fun t : ℝ =>
        LSeries a ((c : ℂ) + ↑t * I) *
          ((↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))) := by
      have heq : (fun t : ℝ => LSeries a ((c : ℂ) + ↑t * I) *
          ((↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1))))
          = fun t : ℝ => F ((c : ℂ) + ↑t * I) *
          ((↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1))) := by
        funext t; rw [hLF t]
      rw [heq]
      simp_rw [div_eq_mul_inv]
      exact (hF.continuous.comp (by fun_prop)).mul
        ((Continuous.const_cpow (by fun_prop) (Or.inl hxc)).mul (kernel_continuous hc0))
    have hbound : ∀ t : ℝ,
        ‖LSeries a ((c : ℂ) + ↑t * I) *
          ((↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))‖
          ≤ (B * x ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹ := by
      intro t
      rw [norm_mul, norm_div]
      have h1 : ‖LSeries a ((c : ℂ) + ↑t * I)‖ ≤ B := hB _ (hle t)
      have h2 : ‖(↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1)‖ = x ^ (c + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re, hrec]
      have h3 : ‖(((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1))‖⁻¹ ≤ (c ^ 2 + t ^ 2)⁻¹ := by
        rw [← norm_inv]; exact kernel_norm_le hc0 t
      calc ‖LSeries a ((c : ℂ) + ↑t * I)‖ *
              (‖(↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1)‖ /
                ‖(((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1))‖)
          = ‖LSeries a ((c : ℂ) + ↑t * I)‖ *
              (x ^ (c + 1) * ‖(((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1))‖⁻¹) := by
            rw [h2, div_eq_mul_inv]
        _ ≤ B * (x ^ (c + 1) * (c ^ 2 + t ^ 2)⁻¹) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hx.le _))
              (by positivity) hB0
        _ = (B * x ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹ := by ring
    exact ((inv_quad_integrable hc0).const_mul (B * x ^ (c + 1))).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall hbound)
  -- Pointwise: `F·E = integrand₊ + integrand₋ − 2·integrand₀` on the line.
  have hpt : ∀ t : ℝ, F ((c : ℂ) + ↑t * I) * perronE n ((c : ℂ) + ↑t * I)
      = LSeries a ((c : ℂ) + ↑t * I) *
          ((↑((n : ℝ) + 1 / 2) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))
        + LSeries a ((c : ℂ) + ↑t * I) *
          ((↑((n : ℝ) - 1 / 2) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))
        - 2 * (LSeries a ((c : ℂ) + ↑t * I) *
          ((↑((n : ℝ)) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))) := by
    intro t
    have hs0 : ((c : ℂ) + ↑t * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; rw [hrec] at this; simp at this; linarith
    have hs1 : ((c : ℂ) + ↑t * I) ≠ -1 := by
      intro h; have := congrArg Complex.re h; rw [hrec] at this; simp at this; linarith
    rw [← hLF t, perronE_eq n hs0 hs1]
    unfold perronKink
    ring
  -- Assemble.
  rw [← perronKink_second_difference a hn]
  rw [smoothed_perron_sum hc0 hsum hxp, smoothed_perron_sum hc0 hsum hxm,
      smoothed_perron_sum hc0 hsum hx₀]
  have hcomb : (∫ t : ℝ, F ((c : ℂ) + ↑t * I) * perronE n ((c : ℂ) + ↑t * I))
      = (∫ t : ℝ, LSeries a ((c : ℂ) + ↑t * I) *
            ((↑((n : ℝ) + 1 / 2) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
              (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1))))
        + (∫ t : ℝ, LSeries a ((c : ℂ) + ↑t * I) *
            ((↑((n : ℝ) - 1 / 2) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
              (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1))))
        - 2 * (∫ t : ℝ, LSeries a ((c : ℂ) + ↑t * I) *
            ((↑((n : ℝ)) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
              (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))) := by
    calc (∫ t : ℝ, F ((c : ℂ) + ↑t * I) * perronE n ((c : ℂ) + ↑t * I))
        = ∫ t : ℝ, (LSeries a ((c : ℂ) + ↑t * I) *
              ((↑((n : ℝ) + 1 / 2) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))
            + LSeries a ((c : ℂ) + ↑t * I) *
              ((↑((n : ℝ) - 1 / 2) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))
            - 2 * (LSeries a ((c : ℂ) + ↑t * I) *
              ((↑((n : ℝ)) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1))))) :=
          MeasureTheory.integral_congr_ae (Eventually.of_forall hpt)
      _ = (∫ t : ℝ, (LSeries a ((c : ℂ) + ↑t * I) *
              ((↑((n : ℝ) + 1 / 2) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))
            + LSeries a ((c : ℂ) + ↑t * I) *
              ((↑((n : ℝ) - 1 / 2) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))))
          - ∫ t : ℝ, 2 * (LSeries a ((c : ℂ) + ↑t * I) *
              ((↑((n : ℝ)) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))) :=
          MeasureTheory.integral_sub ((hIntKnot _ hxp).add (hIntKnot _ hxm))
            ((hIntKnot _ hx₀).const_mul 2)
      _ = _ := by
          rw [MeasureTheory.integral_add (hIntKnot _ hxp) (hIntKnot _ hxm),
              MeasureTheory.integral_const_mul]
  rw [hcomb]
  simp only [Complex.real_smul]
  ring

/-- **Quiet-crossing rigidity.**  Let `F` be entire, agree with an absolutely convergent Dirichlet
series `L(s) = Σ aₘ m^{−s}` on `Re s ≥ c` (with `½ ≤ c`), and satisfy the exact reflection symmetry
`F(s) = F(1−s)`.  Suppose there is a sequence of heights `T_k → ∞` along which `F` is *quiet* across
the closed critical strip `1−c ≤ σ ≤ c`: `‖F(σ ± iT_k)‖ ≤ q_k` with `q_k/T_k² → 0`.  Then `aₙ = 0`
for every `n ≥ 2`.

The Mellin representation `½·aₙ = (1/2π)∫ F(c+it)·E(c+it) dt` uses the entire regularization
`E = N/(s(s+1))`.  Since `F·E` is entire, Cauchy's theorem on the rectangle with corners
`(−M,−T_k)` and `(c,T_k)` moves the contour: the two horizontal edges are `≤ (B+q_k)·T_k^{-2}·const`
and vanish as `k → ∞` (this is exactly where quietness enters), while the left edge `Re s = −M` is
bounded uniformly in `k` by `4πB·(n−½)^{1−M}` using the right-flank bound `B` (carried left by
reflection) and `‖N(−M+iy)‖ ≤ 4(n−½)^{1−M}`.  Passing `k → ∞` gives `‖½·aₙ‖ ≤ 2B·(n−½)^{1−M}`, and
`(n−½) > 1` forces the right side to `0` as `M → ∞`. -/
theorem quiet_crossing_rigidity {F : ℂ → ℂ} {a : ℕ → ℂ} {c : ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hF : Differentiable ℂ F)
    (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hsym : ∀ s : ℂ, F s = F (1 - s))
    (hquiet : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ), Filter.Tendsto T Filter.atTop Filter.atTop ∧
      (∀ k, 0 < T k) ∧ Filter.Tendsto (fun k => q k / (T k) ^ 2) Filter.atTop (nhds 0) ∧
      ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
        ‖F (σ + (T k) * Complex.I)‖ ≤ q k ∧ ‖F (σ - (T k) * Complex.I)‖ ≤ q k) :
    ∀ n : ℕ, 2 ≤ n → a n = 0 := by
  intro n hn2
  have hn1 : 1 ≤ n := by omega
  obtain ⟨T, q, hTtop, hTpos, hqlim, hquietbd⟩ := hquiet
  obtain ⟨B, hB⟩ := lseries_bounded_on_halfplane hsum
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB ↑c (by rw [Complex.ofReal_re]))
  have hFB : ∀ s : ℂ, c ≤ s.re → ‖F s‖ ≤ B := fun s hs => by rw [hFeq s hs]; exact hB s hs
  have hFleft : ∀ s : ℂ, s.re ≤ 1 - c → ‖F s‖ ≤ B := by
    intro s hs; rw [hsym s]; exact hFB _ (by rw [Complex.sub_re, Complex.one_re]; linarith)
  have hEdiff : Differentiable ℂ (perronE n) := perronE_differentiable hn1
  -- Real facts about the three knots.
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hxppos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hxmpos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hxm1 : (1 : ℝ) ≤ (n : ℝ) - 1 / 2 := by linarith
  have hxmgt1 : (1 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hbase1p : (1 : ℝ) ≤ (n : ℝ) + 1 / 2 := by linarith
  -- The entire integrand `Hf = F·E`.
  set Hf : ℂ → ℂ := fun s => F s * perronE n s with hHf
  have hHfp : ∀ p : ℂ, Hf p = F p * perronE n p := fun p => by rw [hHf]
  have hHfdiff : Differentiable ℂ Hf := by rw [hHf]; exact hF.mul hEdiff
  have hHfcont : Continuous Hf := hHfdiff.continuous
  -- Numerator bound on the line `Re s ≤ c` (positive exponent regime).
  have hKink_c : ∀ p : ℂ, p.re ≤ c → ‖perronKink n p‖ ≤ 4 * ((n : ℝ) + 1 / 2) ^ (c + 1) := by
    intro p hpc
    have hb := perronKink_norm_le hn1 p
    have hc1 : (0 : ℝ) ≤ c + 1 := by linarith
    have hpc1 : p.re + 1 ≤ c + 1 := by linarith
    have t1 : ((n : ℝ) + 1 / 2) ^ (p.re + 1) ≤ ((n : ℝ) + 1 / 2) ^ (c + 1) :=
      Real.rpow_le_rpow_of_exponent_le hbase1p hpc1
    have t2 : ((n : ℝ) - 1 / 2) ^ (p.re + 1) ≤ ((n : ℝ) + 1 / 2) ^ (c + 1) :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hxm1 hpc1)
        (Real.rpow_le_rpow hxmpos.le (by linarith) hc1)
    have t3 : ((n : ℝ)) ^ (p.re + 1) ≤ ((n : ℝ) + 1 / 2) ^ (c + 1) :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hnR hpc1)
        (Real.rpow_le_rpow (by linarith) (by linarith) hc1)
    linarith [hb, t1, t2, t3]
  -- Numerator bound on the line `Re s = −M` (negative exponent regime).
  have hKink_M : ∀ (M : ℝ) (p : ℂ), 1 ≤ M → p.re = -M →
      ‖perronKink n p‖ ≤ 4 * ((n : ℝ) - 1 / 2) ^ (1 - M) := by
    intro M p hM hpre
    have hb := perronKink_norm_le hn1 p
    rw [hpre, show (-M + 1) = 1 - M by ring] at hb
    have hnp : (1 - M) ≤ 0 := by linarith
    have t1 : ((n : ℝ) + 1 / 2) ^ (1 - M) ≤ ((n : ℝ) - 1 / 2) ^ (1 - M) :=
      Real.rpow_le_rpow_of_nonpos hxmpos (by linarith) hnp
    have t3 : ((n : ℝ)) ^ (1 - M) ≤ ((n : ℝ) - 1 / 2) ^ (1 - M) :=
      Real.rpow_le_rpow_of_nonpos hxmpos (by linarith) hnp
    linarith [hb, t1, t3]
  -- The right-line integrand is integrable.
  have hRint : Integrable (fun t : ℝ => Hf (↑c + ↑t * I)) := by
    have hcont : Continuous (fun t : ℝ => Hf (↑c + ↑t * I)) := hHfcont.comp (by fun_prop)
    have hbd : ∀ t : ℝ, ‖Hf (↑c + ↑t * I)‖ ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * B) * (c ^ 2 + t ^ 2)⁻¹ := by
      intro t
      have hre : (↑c + ↑t * I : ℂ).re = c := by simp
      rw [hHfp, norm_mul]
      have hF' : ‖F (↑c + ↑t * I)‖ ≤ B := hFB _ (le_of_eq hre.symm)
      have h0 : (↑c + ↑t * I : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
      have h1 : (↑c + ↑t * I : ℂ) ≠ -1 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
      have hE' : ‖perronE n (↑c + ↑t * I)‖ ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹ := by
        rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
        exact mul_le_mul (hKink_c _ (le_of_eq hre)) (kernel_norm_le hc0 t) (norm_nonneg _)
          (by positivity)
      calc ‖F (↑c + ↑t * I)‖ * ‖perronE n (↑c + ↑t * I)‖
          ≤ B * ((4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹) :=
            mul_le_mul hF' hE' (norm_nonneg _) hB0
        _ = (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * B) * (c ^ 2 + t ^ 2)⁻¹ := by ring
    exact ((inv_quad_integrable hc0).const_mul _).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hbd)
  -- The bound at a fixed contour depth `M`.
  have keyM : ∀ M : ℕ, 2 ≤ M → (c : ℝ) ≤ (M : ℝ) →
      ‖∫ t : ℝ, Hf (↑c + ↑t * I)‖ ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
    intro M hM2 hMc
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hM1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
    have hM2R : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    have hMle : -(M : ℝ) ≤ 1 - c := by linarith
    have hMcle : -(M : ℝ) ≤ c := by linarith
    -- Left-line domination.
    have hleftbd : ∀ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
        ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
      intro y
      have hre : (↑(-(M : ℝ)) + ↑y * I : ℂ).re = -(M : ℝ) := by simp
      rw [hHfp, norm_mul]
      have hF' : ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ≤ B := hFleft _ (by rw [hre]; exact hMle)
      have h0 : (↑(-(M : ℝ)) + ↑y * I : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
      have h1 : (↑(-(M : ℝ)) + ↑y * I : ℂ) ≠ -1 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
      have hE' : ‖perronE n (↑(-(M : ℝ)) + ↑y * I)‖
          ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
        rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
        exact mul_le_mul (hKink_M (M : ℝ) _ hM1.le hre)
          (kernel_left_bound (M := (M : ℝ)) (y := y) hM1) (norm_nonneg _)
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hxmpos.le _))
      calc ‖F (↑(-(M : ℝ)) + ↑y * I)‖ * ‖perronE n (↑(-(M : ℝ)) + ↑y * I)‖
          ≤ B * ((4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹) :=
            mul_le_mul hF' hE' (norm_nonneg _) hB0
        _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by ring
    have hleftint : Integrable (fun y : ℝ => Hf (↑(-(M : ℝ)) + ↑y * I)) := by
      have hcont : Continuous (fun y : ℝ => Hf (↑(-(M : ℝ)) + ↑y * I)) := hHfcont.comp (by fun_prop)
      exact ((inv_quad_integrable (show (0 : ℝ) < (M : ℝ) - 1 from by linarith)).const_mul
        (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B)).mono' hcont.aestronglyMeasurable
        (Eventually.of_forall hleftbd)
    have hqle : ∫ y : ℝ, (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ ≤ Real.pi := by
      rw [← integral_univ_inv_one_add_sq]
      refine integral_mono (inv_quad_integrable (show (0 : ℝ) < (M : ℝ) - 1 from by linarith))
        integrable_inv_one_add_sq (fun y => ?_)
      refine inv_anti₀ (by positivity) ?_
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (M : ℝ) from hMnn) (show (0 : ℝ) ≤ (M : ℝ) - 2 from by linarith), sq_nonneg y]
    have hleftfull : ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
        ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
      have hdomint : Integrable (fun y : ℝ =>
          (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹) :=
        (inv_quad_integrable (show (0 : ℝ) < (M : ℝ) - 1 from by linarith)).const_mul _
      have hCnn : (0 : ℝ) ≤ 4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B :=
        mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hxmpos.le _)) hB0
      calc ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
          ≤ ∫ y : ℝ, (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ :=
            integral_mono hleftint.norm hdomint hleftbd
        _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * ∫ y : ℝ, (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ :=
            integral_const_mul _ _
        _ ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * Real.pi :=
            mul_le_mul_of_nonneg_left hqle hCnn
        _ = 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by ring
    have hleftk : ∀ k, ‖∫ y in (-(T k))..(T k), Hf (↑(-(M : ℝ)) + ↑y * I)‖
        ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
      intro k
      calc ‖∫ y in (-(T k))..(T k), Hf (↑(-(M : ℝ)) + ↑y * I)‖
          ≤ ∫ y in (-(T k))..(T k), ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith [hTpos k])
        _ = ∫ y in Set.Ioc (-(T k)) (T k), ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖ :=
            intervalIntegral.integral_of_le (by linarith [hTpos k])
        _ ≤ ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖ :=
            setIntegral_le_integral hleftint.norm (Eventually.of_forall (fun y => norm_nonneg _))
        _ ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := hleftfull
    -- Horizontal-edge domination and its decay.
    have hinvsq : Tendsto (fun k => ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
      have hTsq : Tendsto (fun k => (T k) ^ 2) atTop atTop := by
        simpa [pow_two] using hTtop.atTop_mul_atTop₀ hTtop
      exact hTsq.inv_tendsto_atTop
    have hcore : Tendsto (fun k => (B + q k) * ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
      have h1 : Tendsto (fun k => B * ((T k) ^ 2)⁻¹) atTop (nhds 0) := by simpa using hinvsq.const_mul B
      have h2 : Tendsto (fun k => q k * ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
        have := hqlim; simp_rw [div_eq_mul_inv] at this; exact this
      simpa [add_mul] using h1.add h2
    set d : ℕ → ℝ := fun k => (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * (c + (M : ℝ))) * ((B + q k) * ((T k) ^ 2)⁻¹) with hd
    have hd0 : Tendsto d atTop (nhds 0) := by
      simp only [hd]; simpa using hcore.const_mul (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * (c + (M : ℝ)))
    have hqk0 : ∀ k, (0 : ℝ) ≤ q k := fun k =>
      le_trans (norm_nonneg _) (hquietbd k c (by linarith) (le_refl c)).1
    -- Common per-edge norm-of-integrand const.
    have hedge : ∀ (k : ℕ) (t : ℝ), 0 < T k → |t| = T k →
        ∀ x : ℝ, -(M : ℝ) < x → x ≤ c → ‖F (↑x + ↑t * I)‖ ≤ B + q k →
        ‖Hf (↑x + ↑t * I)‖ ≤ (B + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) := by
      intro k t hTk habs x hx1 hx2 hFbd
      have hre : (↑x + ↑t * I : ℂ).re = x := by simp
      rw [hHfp, norm_mul]
      have h0 : (↑x + ↑t * I : ℂ) ≠ 0 := by
        intro hh; have := congrArg Complex.im hh; simp at this; rw [this] at habs
        simp at habs; linarith
      have h1 : (↑x + ↑t * I : ℂ) ≠ -1 := by
        intro hh; have := congrArg Complex.im hh; simp at this; rw [this] at habs
        simp at habs; linarith
      have hE' : ‖perronE n (↑x + ↑t * I)‖ ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * ((T k) ^ 2)⁻¹ := by
        rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
        exact mul_le_mul (hKink_c _ ((le_of_eq hre).trans hx2))
          (kernel_line_bound (t := t) (T := T k) hTk (le_of_eq habs.symm) x) (norm_nonneg _)
          (by positivity)
      exact mul_le_mul hFbd hE' (norm_nonneg _) (by linarith [hB0, hqk0 k])
    have htop : ∀ k, ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(T k) * I)‖ ≤ d k := by
      intro k
      have hconst : ∀ x ∈ Set.uIoc (-(M : ℝ)) c,
          ‖Hf (↑x + ↑(T k) * I)‖ ≤ (B + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) := by
        intro x hx
        rw [Set.uIoc_of_le hMcle] at hx
        obtain ⟨hx1, hx2⟩ := hx
        refine hedge k (T k) (hTpos k) (abs_of_pos (hTpos k)) x hx1 hx2 ?_
        rcases le_or_gt x (1 - c) with h | h
        · exact le_trans (hFleft _ (by simp; exact h)) (by linarith [hqk0 k])
        · exact le_trans (hquietbd k x (le_of_lt h) hx2).1 (by linarith [hB0])
      calc ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(T k) * I)‖
          ≤ ((B + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹)) * |c - -(M : ℝ)| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hconst
        _ = d k := by simp only [hd]; rw [abs_of_nonneg (by linarith)]; ring
    have hbot : ∀ k, ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(-(T k)) * I)‖ ≤ d k := by
      intro k
      have hconst : ∀ x ∈ Set.uIoc (-(M : ℝ)) c,
          ‖Hf (↑x + ↑(-(T k)) * I)‖ ≤ (B + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) := by
        intro x hx
        rw [Set.uIoc_of_le hMcle] at hx
        obtain ⟨hx1, hx2⟩ := hx
        have hpt : (↑x + ↑(-(T k)) * I : ℂ) = ↑x - ↑(T k) * I := by push_cast; ring
        refine hedge k (-(T k)) (hTpos k) (by rw [abs_neg, abs_of_pos (hTpos k)]) x hx1 hx2 ?_
        rcases le_or_gt x (1 - c) with h | h
        · exact le_trans (hFleft _ (by simp; exact h)) (by linarith [hqk0 k])
        · rw [hpt]; exact le_trans (hquietbd k x (le_of_lt h) hx2).2 (by linarith [hB0])
      calc ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(-(T k)) * I)‖
          ≤ ((B + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹)) * |c - -(M : ℝ)| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hconst
        _ = d k := by simp only [hd]; rw [abs_of_nonneg (by linarith)]; ring
    -- Right vertical integral converges to the full-line integral.
    have hrighttendsto : Tendsto (fun k => ∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)) atTop
        (nhds (∫ t : ℝ, Hf (↑c + ↑t * I))) :=
      intervalIntegral_tendsto_integral hRint (tendsto_neg_atBot_iff.mpr hTtop) hTtop
    have hnormtendsto : Tendsto (fun k => ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖) atTop
        (nhds ‖∫ t : ℝ, Hf (↑c + ↑t * I)‖) := hrighttendsto.norm
    -- Rectangle (Cauchy) bound: right edge ≤ tops + bottom + left.
    have hrectbd : ∀ k, ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖
        ≤ (d k + d k) + 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
      intro k
      set z : ℂ := ⟨-(M : ℝ), -(T k)⟩ with hz
      set w : ℂ := ⟨c, T k⟩ with hw
      have hrect := integral_boundary_rect_eq_zero_of_differentiableOn Hf z w hHfdiff.differentiableOn
      have hzre : z.re = -(M : ℝ) := rfl
      have hzim : z.im = -(T k) := rfl
      have hwre : w.re = c := rfl
      have hwim : w.im = T k := rfl
      rw [hzre, hzim, hwre, hwim] at hrect
      simp only [smul_eq_mul] at hrect
      set Itop := ∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(T k) * I) with hItop
      set Ibot := ∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(-(T k)) * I) with hIbot
      set Ilft := ∫ y in (-(T k))..(T k), Hf (↑(-(M : ℝ)) + ↑y * I) with hIlft
      have heqI : I * (∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)) = Itop - Ibot + I * Ilft := by
        linear_combination hrect
      have hInorm : ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖ = ‖Itop - Ibot + I * Ilft‖ := by
        rw [← heqI, norm_mul, Complex.norm_I, one_mul]
      rw [hInorm]
      have hb1 : ‖Itop - Ibot + I * Ilft‖ ≤ ‖Itop - Ibot‖ + ‖I * Ilft‖ := norm_add_le _ _
      have hb2 : ‖Itop - Ibot‖ ≤ ‖Itop‖ + ‖Ibot‖ := norm_sub_le _ _
      have hb3 : ‖I * Ilft‖ = ‖Ilft‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      rw [hb3] at hb1
      have h3 : ‖Itop‖ ≤ d k := htop k
      have h4 : ‖Ibot‖ ≤ d k := hbot k
      have h5 : ‖Ilft‖ ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := hleftk k
      linarith [hb1, hb2, h3, h4, h5]
    have hdb : Tendsto (fun k => (d k + d k) + 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
        atTop (nhds (4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))) := by
      simpa using (hd0.add hd0).add_const (4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
    exact le_of_tendsto_of_tendsto' hnormtendsto hdb hrectbd
  -- Send the contour to infinity.
  have hMtendsto : Tendsto (fun M : ℕ => 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
      atTop (nhds 0) := by
    have hbase : Tendsto (fun M : ℕ => ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) atTop (nhds 0) := by
      have h1 : (fun M : ℕ => ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
          = fun M : ℕ => ((n : ℝ) - 1 / 2) * (((n : ℝ) - 1 / 2)⁻¹) ^ M := by
        funext M
        rw [Real.rpow_sub hxmpos, Real.rpow_one, Real.rpow_natCast, div_eq_mul_inv, inv_pow]
      rw [h1]
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ ((n : ℝ) - 1 / 2)⁻¹)
        (by rw [inv_lt_one_iff₀]; right; exact hxmgt1)
      simpa using this.const_mul ((n : ℝ) - 1 / 2)
    simpa using hbase.const_mul (4 * Real.pi * B)
  have hbound_an : ‖a n * (1 / 2)‖ ≤ 0 := by
    have hR : a n * (1 / 2) = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, Hf (↑c + ↑t * I) := by
      rw [hHf]; exact perronSecondDiff_integral hc0 hsum hF hFeq hn1
    have hev : ∀ᶠ M : ℕ in atTop, ‖a n * (1 / 2)‖
        ≤ (1 / (2 * Real.pi)) * (4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) := by
      filter_upwards [eventually_ge_atTop (max 2 ⌈c⌉₊)] with M hM
      have hM2 : 2 ≤ M := le_trans (le_max_left _ _) hM
      have hMc : (c : ℝ) ≤ (M : ℝ) :=
        le_trans (Nat.le_ceil c) (by exact_mod_cast le_trans (le_max_right _ _) hM)
      rw [hR, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (keyM M hM2 hMc) (by positivity)
    have hlim : Tendsto (fun M : ℕ => (1 / (2 * Real.pi)) *
        (4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))) atTop (nhds 0) := by
      simpa using hMtendsto.const_mul (1 / (2 * Real.pi))
    exact ge_of_tendsto hlim hev
  have han2 : a n * (1 / 2) = 0 := norm_eq_zero.mp (le_antisymm hbound_an (norm_nonneg _))
  exact (mul_eq_zero.mp han2).resolve_right (by norm_num)

end RHTower

