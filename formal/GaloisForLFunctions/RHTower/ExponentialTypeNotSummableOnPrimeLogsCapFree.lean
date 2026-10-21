import GaloisForLFunctions.RHTower.ExponentialTypeNotSummableOnPrimeLogsNaturalRate
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Prime-log divergence of entire functions of exponential type, without the cap

Let `Φ ≢ 0` be entire with `‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}` and let `0 ≤ σ`.  Then the partial sums
`Σ_{p<N} p^{−σ} ‖Φ(log p)‖` over the primes are unbounded as soon as `ρ < 1 − σ`
(`exists_primeLogWeightedSum_gt_of_lt_one_sub_capFree`).  This removes the cap `2ρ < 5/12` of
`exists_primeLogWeightedSum_gt_of_lt_one_sub`, which came from measuring the variation of `Φ` on
real windows by the global type `ρ` while its size on the ray is only known at the worse rate
`e^{−(ρ+δ)t}`: windows of log-length `e^{−(2ρ+δ)t}` then need primes in intervals of length
`x^{1−2ρ−δ}`, and the `7/12` theorem caps `2ρ`.

The gain is to measure both the size and the variation of `Φ` at the same rate, the ray exponent
`a = h(0) = inf {a : ‖Φ(t)‖ ≤ e^{at} for all large t}` (`rayExponent`):

* **Two-ray floor** (`neg_le_rayExponent`): `a ≥ −ρ`, since an admissible exponent below `−ρ` makes
  `Φ(w) e^{(ρ+ε)w}` decay on both real rays, hence vanish (`eq_zero_of_two_ray_exponential_decay`).
* **Largeness at the ray exponent** (`exists_exp_rayExponent_sub_lt`): `‖Φ(t)‖ > e^{(a−δ)t}` at
  arbitrarily large `t`, by definition of the infimum.
* **Thin-strip bound** (`exists_thinStrip_bound`): `‖Φ(t + iy)‖ ≤ M₁ e^{(a+δ)t}` for `t ≥ 0`,
  `|y| ≤ 1`.  Damping by `e^{−(a+δ ∓ iρ)w}` makes `Φ` bounded on the positive real axis and on
  the positive, respectively negative, imaginary axis; Phragmén–Lindelöf in the first and fourth
  quadrants (`PhragmenLindelof.quadrant_I`, `quadrant_IV`) does the rest.
* **Lipschitz at the ray rate** (`norm_sub_le_of_thinStrip`): the Cauchy estimate on unit discs
  gives `‖Φ(v) − Φ(u)‖ ≤ M₁ e^{3|a+δ|} e^{(a+δ)x} (v − u)` on `[x, x+2]`.

Hence `Φ` stays above `½ e^{(a−δ)x}` on a window of log-length `e^{−3δx}`, the prime windows may
have log-length `e^{−6δx}`, i.e. intervals of length `x^{1−6δ}` covered by the `7/12` theorem for
every small `δ`, and the window contributes `≍ X^{1−σ+a−O(δ)}/log X ≥ X^{1−σ−ρ−O(δ)}/log X`, which
is unbounded exactly when `ρ < 1 − σ`.  The window assembly of the natural-rate module is reused
with an arbitrary Lipschitz constant (`primeWindow_sum_ge_of_window_value_lip`,
`exists_primeLogWeightedSum_gt_of_window_data_lip`).
-/

open Complex Filter Topology Set Finset Metric MeasureTheory
open scoped Real

noncomputable section

namespace RHTower

/-! ## 1. The ray exponent -/

/-- Admissible exponents on the positive ray: `‖Φ(t)‖ ≤ e^{a t}` for all large real `t`. -/
def rayExponentSet (Φ : ℂ → ℂ) : Set ℝ :=
  {a : ℝ | ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ‖Φ (t : ℂ)‖ ≤ Real.exp (a * t)}

/-- The ray exponent `h(0)`: the infimum of the admissible exponents. -/
def rayExponent (Φ : ℂ → ℂ) : ℝ := sInf (rayExponentSet Φ)

/-- Admissible exponents are upward closed. -/
theorem mem_rayExponentSet_of_le {Φ : ℂ → ℂ} {a b : ℝ} (ha : a ∈ rayExponentSet Φ)
    (hab : a ≤ b) : b ∈ rayExponentSet Φ := by
  obtain ⟨t₀, ht₀⟩ := ha
  refine ⟨max t₀ 0, fun t ht => ?_⟩
  have h1 := ht₀ t (le_trans (le_max_left _ _) ht)
  have h2 : 0 ≤ t := le_trans (le_max_right _ _) ht
  exact h1.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab h2))

/-- `ρ + 1` is admissible when `‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}` with `C > 0`. -/
theorem add_one_mem_rayExponentSet {Φ : ℂ → ℂ} {C ρ : ℝ} (hC : 0 < C)
    (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) : ρ + 1 ∈ rayExponentSet Φ := by
  refine ⟨max 0 (Real.log C), fun t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans (le_max_left _ _) ht
  have hlog : Real.log C ≤ t := le_trans (le_max_right _ _) ht
  have hCt : C ≤ Real.exp t := by
    rw [← Real.exp_log hC]
    exact Real.exp_le_exp.mpr hlog
  calc ‖Φ (t : ℂ)‖ ≤ C * Real.exp (ρ * ‖(t : ℂ)‖) := hgrow _
    _ = C * Real.exp (ρ * t) := by rw [Complex.norm_real, Real.norm_of_nonneg ht0]
    _ ≤ Real.exp t * Real.exp (ρ * t) := mul_le_mul_of_nonneg_right hCt (Real.exp_pos _).le
    _ = Real.exp ((ρ + 1) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **No admissible exponent lies below `−ρ`**: the two-ray theorem `h(0) + h(π) ≥ 0`.  An
exponent `a < −ρ` makes `Φ(w) e^{(ρ+ε)w}`, `ε = (−ρ − a)/2`, decay like `e^{−ε|t|}` on both real
rays, so it vanishes. -/
theorem neg_le_of_mem_rayExponentSet {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {C ρ : ℝ}
    (hC : 0 < C) (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) (hne : Φ ≠ 0)
    {a : ℝ} (ha : a ∈ rayExponentSet Φ) : -ρ ≤ a := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨t₀', ht₀'⟩ := ha
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = max t₀' 0 := ⟨_, rfl⟩
  have ht₀0 : 0 ≤ t₀ := by rw [ht₀]; exact le_max_right _ _
  have hup : ∀ t : ℝ, t₀ ≤ t → ‖Φ (t : ℂ)‖ ≤ Real.exp (a * t) := fun t ht =>
    ht₀' t (le_trans (by rw [ht₀]; exact le_max_left _ _) ht)
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (-ρ - a) / 2 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = ρ + ε := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; linarith
  -- the damped function
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = fun w => Φ w * cexp ((κ : ℂ) * w) := ⟨_, rfl⟩
  have hgd : Differentiable ℂ g := by
    rw [hg]
    exact hΦ.mul (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))
  have hgnorm : ∀ w : ℂ, ‖g w‖ = ‖Φ w‖ * Real.exp (κ * w.re) := fun w => by
    rw [hg]
    simp only [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max 1 (C * Real.exp ((ρ + κ + ε) * t₀)) := ⟨_, rfl⟩
  have hC'1 : 1 ≤ C' := by rw [hC']; exact le_max_left _ _
  have hCC' : C ≤ C' := by
    rw [hC']
    exact le_trans (le_mul_of_one_le_right hC.le (Real.one_le_exp (by positivity)))
      (le_max_right _ _)
  -- global growth of `g`
  have hgrow' : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp ((ρ + κ) * ‖z‖) := fun z => by
    rw [hgnorm]
    calc ‖Φ z‖ * Real.exp (κ * z.re) ≤ C * Real.exp (ρ * ‖z‖) * Real.exp (κ * ‖z‖) :=
          mul_le_mul (hgrow z)
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Complex.re_le_norm z) hκ0))
            (Real.exp_pos _).le (by positivity)
      _ = C * Real.exp ((ρ + κ) * ‖z‖) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  -- decay on the positive ray
  have hplus : ∀ x : ℝ, 0 ≤ x → ‖g (x : ℂ)‖ ≤ C' * Real.exp (-(ε * x)) := by
    intro x hx
    rw [hgnorm, Complex.ofReal_re]
    rcases le_or_gt t₀ x with hxt | hxt
    · calc ‖Φ (x : ℂ)‖ * Real.exp (κ * x) ≤ Real.exp (a * x) * Real.exp (κ * x) :=
            mul_le_mul_of_nonneg_right (hup x hxt) (Real.exp_pos _).le
        _ = Real.exp (-(ε * x)) := by
            rw [← Real.exp_add]
            congr 1
            rw [hκ, hε]
            ring
        _ ≤ C' * Real.exp (-(ε * x)) :=
            le_mul_of_one_le_left (Real.exp_pos _).le hC'1
    · have h1 : ‖Φ (x : ℂ)‖ ≤ C * Real.exp (ρ * x) := by
        have := hgrow (x : ℂ)
        rwa [Complex.norm_real, Real.norm_of_nonneg hx] at this
      calc ‖Φ (x : ℂ)‖ * Real.exp (κ * x) ≤ C * Real.exp (ρ * x) * Real.exp (κ * x) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = C * Real.exp ((ρ + κ + ε) * x) * Real.exp (-(ε * x)) := by
            rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
            congr 2
            ring
        _ ≤ C * Real.exp ((ρ + κ + ε) * t₀) * Real.exp (-(ε * x)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left hxt.le (by linarith))) hC.le) (Real.exp_pos _).le
        _ ≤ C' * Real.exp (-(ε * x)) := by
            rw [hC']
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  -- decay on the negative ray
  have hminus : ∀ x : ℝ, x ≤ 0 → ‖g (x : ℂ)‖ ≤ C' * Real.exp (ε * x) := by
    intro x hx
    rw [hgnorm, Complex.ofReal_re]
    have h1 : ‖Φ (x : ℂ)‖ ≤ C * Real.exp (ρ * (-x)) := by
      have := hgrow (x : ℂ)
      rwa [Complex.norm_real, Real.norm_of_nonpos hx] at this
    calc ‖Φ (x : ℂ)‖ * Real.exp (κ * x) ≤ C * Real.exp (ρ * (-x)) * Real.exp (κ * x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = C * Real.exp (ε * x) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          rw [hκ]
          ring
      _ ≤ C' * Real.exp (ε * x) := mul_le_mul_of_nonneg_right hCC' (Real.exp_pos _).le
  have hzero := eq_zero_of_two_ray_exponential_decay hgd hC.le (by linarith) hε0 hgrow' hplus
    hminus
  apply hne
  funext w
  have := congrFun hzero w
  rw [hg] at this
  simp only [Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, or_false] at this
  exact this

theorem rayExponentSet_nonempty {Φ : ℂ → ℂ} {C ρ : ℝ} (hC : 0 < C)
    (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) : (rayExponentSet Φ).Nonempty :=
  ⟨ρ + 1, add_one_mem_rayExponentSet hC hgrow⟩

theorem rayExponentSet_bddBelow {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {C ρ : ℝ} (hC : 0 < C)
    (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) (hne : Φ ≠ 0) :
    BddBelow (rayExponentSet Φ) :=
  ⟨-ρ, fun _ ha => neg_le_of_mem_rayExponentSet hΦ hC hρ hgrow hne ha⟩

/-- **The ray exponent is at least `−ρ`.** -/
theorem neg_le_rayExponent {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {C ρ : ℝ} (hC : 0 < C)
    (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) (hne : Φ ≠ 0) :
    -ρ ≤ rayExponent Φ :=
  le_csInf (rayExponentSet_nonempty hC hgrow)
    fun _ ha => neg_le_of_mem_rayExponentSet hΦ hC hρ hgrow hne ha

/-- **Upper bound at the ray exponent**: `‖Φ(t)‖ ≤ e^{(a+δ)t}` for all `t ≥ t₀`, `t₀ ≥ 0`. -/
theorem exists_forall_norm_le_exp_rayExponent_add {Φ : ℂ → ℂ} {C ρ : ℝ} (hC : 0 < C)
    (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ‖Φ (t : ℂ)‖ ≤ Real.exp ((rayExponent Φ + δ) * t) := by
  obtain ⟨a, ha, hlt⟩ := exists_lt_of_csInf_lt (rayExponentSet_nonempty hC hgrow)
    (show sInf (rayExponentSet Φ) < rayExponent Φ + δ by unfold rayExponent; linarith)
  obtain ⟨t₀, ht₀⟩ := mem_rayExponentSet_of_le ha hlt.le
  exact ⟨max t₀ 0, le_max_right _ _, fun t ht => ht₀ t (le_trans (le_max_left _ _) ht)⟩

/-- **Largeness at the ray exponent**: `‖Φ(t)‖ > e^{(a−δ)t}` at arbitrarily large `t`. -/
theorem exists_exp_rayExponent_sub_lt {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {C ρ : ℝ}
    (hC : 0 < C) (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) (hne : Φ ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ Real.exp ((rayExponent Φ - δ) * t) < ‖Φ (t : ℂ)‖ := by
  by_contra h
  push Not at h
  have hmem : rayExponent Φ - δ ∈ rayExponentSet Φ := ⟨T, h⟩
  have := csInf_le (rayExponentSet_bddBelow hΦ hC hρ hgrow hne) hmem
  unfold rayExponent at this
  linarith

/-! ## 2. The thin-strip bound by Phragmén–Lindelöf in two quadrants -/

/-- **First quadrant.**  If `‖Φ(t)‖ ≤ e^{at}` for `t ≥ t₀`, then on `Re z ≥ 0`, `Im z ≥ 0`:
`‖Φ z‖ ≤ K e^{a Re z + ρ Im z}`, `K = max(1, C e^{(ρ+|a|)t₀})`.  The damping `e^{−(a − iρ)z}`
bounds `Φ` by `K` on the positive real axis and by `C` on the positive imaginary axis. -/
theorem norm_le_exp_of_quadrant_I {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {C ρ : ℝ} (hC : 0 < C)
    (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) {a t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hup : ∀ t : ℝ, t₀ ≤ t → ‖Φ (t : ℂ)‖ ≤ Real.exp (a * t)) {z : ℂ} (hre : 0 ≤ z.re)
    (him : 0 ≤ z.im) :
    ‖Φ z‖ ≤ max 1 (C * Real.exp ((ρ + |a|) * t₀)) * Real.exp (a * z.re + ρ * z.im) := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (a : ℂ) - (ρ : ℂ) * I := ⟨_, rfl⟩
  have hre_cw : ∀ w : ℂ, (c * w).re = a * w.re + ρ * w.im := fun w => by
    rw [hc]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun w => Φ w * cexp (-(c * w)) := ⟨_, rfl⟩
  have hFnorm : ∀ w, ‖F w‖ = ‖Φ w‖ * Real.exp (-(a * w.re + ρ * w.im)) := fun w => by
    rw [hF]
    simp only [norm_mul, Complex.norm_exp, Complex.neg_re, hre_cw]
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max 1 (C * Real.exp ((ρ + |a|) * t₀)) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; exact le_max_left _ _
  have hKC : C ≤ K := by
    rw [hK]
    exact le_trans (le_mul_of_one_le_right hC.le (Real.one_le_exp (by positivity)))
      (le_max_right _ _)
  have hFd : Differentiable ℂ F := by
    rw [hF]
    exact hΦ.mul (Complex.differentiable_exp.comp
      ((differentiable_const _).mul differentiable_id).neg)
  -- the positive real axis
  have hreal : ∀ x : ℝ, 0 ≤ x → ‖F (x : ℂ)‖ ≤ K := by
    intro x hx
    rw [hFnorm, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
    rcases le_or_gt t₀ x with hxt | hxt
    · calc ‖Φ (x : ℂ)‖ * Real.exp (-(a * x)) ≤ Real.exp (a * x) * Real.exp (-(a * x)) :=
            mul_le_mul_of_nonneg_right (hup x hxt) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        _ ≤ K := hK1
    · have h1 : ‖Φ (x : ℂ)‖ ≤ C * Real.exp (ρ * x) := by
        have := hgrow (x : ℂ)
        rwa [Complex.norm_real, Real.norm_of_nonneg hx] at this
      calc ‖Φ (x : ℂ)‖ * Real.exp (-(a * x)) ≤ C * Real.exp (ρ * x) * Real.exp (-(a * x)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = C * Real.exp ((ρ - a) * x) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring
        _ ≤ C * Real.exp ((ρ + |a|) * t₀) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
            calc (ρ - a) * x ≤ (ρ + |a|) * x :=
                  mul_le_mul_of_nonneg_right (by linarith [neg_abs_le a]) hx
              _ ≤ (ρ + |a|) * t₀ := mul_le_mul_of_nonneg_left hxt.le (by positivity)
        _ ≤ K := by rw [hK]; exact le_max_right _ _
  -- the positive imaginary axis
  have himag : ∀ x : ℝ, 0 ≤ x → ‖F ((x : ℂ) * I)‖ ≤ K := by
    intro x hx
    rw [hFnorm]
    have hre' : ((x : ℂ) * I).re = 0 := by simp
    have him' : ((x : ℂ) * I).im = x := by simp
    have hn : ‖(x : ℂ) * I‖ = x := by
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg hx]
    rw [hre', him', mul_zero, zero_add]
    calc ‖Φ ((x : ℂ) * I)‖ * Real.exp (-(ρ * x))
        ≤ C * Real.exp (ρ * x) * Real.exp (-(ρ * x)) := by
          gcongr
          have := hgrow ((x : ℂ) * I)
          rwa [hn] at this
      _ = C := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ K := hKC
  -- order-one growth
  have hbig : ∃ e < (2 : ℝ), ∃ B : ℝ, F =O[Bornology.cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)]
      fun w => Real.exp (B * ‖w‖ ^ e) := by
    refine ⟨1, by norm_num, ρ + ‖c‖, Asymptotics.IsBigO.of_bound C
      (Eventually.of_forall fun w => ?_)⟩
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.rpow_one, hFnorm]
    have h1 : -(a * w.re + ρ * w.im) ≤ ‖c‖ * ‖w‖ := by
      rw [← hre_cw, ← norm_mul]
      have := Complex.abs_re_le_norm (c * w)
      linarith [(abs_le.mp this).1]
    calc ‖Φ w‖ * Real.exp (-(a * w.re + ρ * w.im))
        ≤ C * Real.exp (ρ * ‖w‖) * Real.exp (‖c‖ * ‖w‖) :=
          mul_le_mul (hgrow w) (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le (by positivity)
      _ = C * Real.exp ((ρ + ‖c‖) * ‖w‖) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hq := PhragmenLindelof.quadrant_I (f := F) (C := K) hFd.diffContOnCl hbig hreal himag
    hre him
  rw [hFnorm] at hq
  rw [← hK]
  calc ‖Φ z‖ = ‖Φ z‖ * Real.exp (-(a * z.re + ρ * z.im)) * Real.exp (a * z.re + ρ * z.im) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ K * Real.exp (a * z.re + ρ * z.im) :=
        mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le

/-- **Fourth quadrant.**  The mirror statement on `Re z ≥ 0`, `Im z ≤ 0`, with damping
`e^{−(a + iρ)z}`: `‖Φ z‖ ≤ K e^{a Re z − ρ Im z}`. -/
theorem norm_le_exp_of_quadrant_IV {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {C ρ : ℝ} (hC : 0 < C)
    (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) {a t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hup : ∀ t : ℝ, t₀ ≤ t → ‖Φ (t : ℂ)‖ ≤ Real.exp (a * t)) {z : ℂ} (hre : 0 ≤ z.re)
    (him : z.im ≤ 0) :
    ‖Φ z‖ ≤ max 1 (C * Real.exp ((ρ + |a|) * t₀)) * Real.exp (a * z.re - ρ * z.im) := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (a : ℂ) + (ρ : ℂ) * I := ⟨_, rfl⟩
  have hre_cw : ∀ w : ℂ, (c * w).re = a * w.re - ρ * w.im := fun w => by
    rw [hc]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun w => Φ w * cexp (-(c * w)) := ⟨_, rfl⟩
  have hFnorm : ∀ w, ‖F w‖ = ‖Φ w‖ * Real.exp (-(a * w.re - ρ * w.im)) := fun w => by
    rw [hF]
    simp only [norm_mul, Complex.norm_exp, Complex.neg_re, hre_cw]
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max 1 (C * Real.exp ((ρ + |a|) * t₀)) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; exact le_max_left _ _
  have hKC : C ≤ K := by
    rw [hK]
    exact le_trans (le_mul_of_one_le_right hC.le (Real.one_le_exp (by positivity)))
      (le_max_right _ _)
  have hFd : Differentiable ℂ F := by
    rw [hF]
    exact hΦ.mul (Complex.differentiable_exp.comp
      ((differentiable_const _).mul differentiable_id).neg)
  -- the positive real axis
  have hreal : ∀ x : ℝ, 0 ≤ x → ‖F (x : ℂ)‖ ≤ K := by
    intro x hx
    rw [hFnorm, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rcases le_or_gt t₀ x with hxt | hxt
    · calc ‖Φ (x : ℂ)‖ * Real.exp (-(a * x)) ≤ Real.exp (a * x) * Real.exp (-(a * x)) :=
            mul_le_mul_of_nonneg_right (hup x hxt) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        _ ≤ K := hK1
    · have h1 : ‖Φ (x : ℂ)‖ ≤ C * Real.exp (ρ * x) := by
        have := hgrow (x : ℂ)
        rwa [Complex.norm_real, Real.norm_of_nonneg hx] at this
      calc ‖Φ (x : ℂ)‖ * Real.exp (-(a * x)) ≤ C * Real.exp (ρ * x) * Real.exp (-(a * x)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = C * Real.exp ((ρ - a) * x) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring
        _ ≤ C * Real.exp ((ρ + |a|) * t₀) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
            calc (ρ - a) * x ≤ (ρ + |a|) * x :=
                  mul_le_mul_of_nonneg_right (by linarith [neg_abs_le a]) hx
              _ ≤ (ρ + |a|) * t₀ := mul_le_mul_of_nonneg_left hxt.le (by positivity)
        _ ≤ K := by rw [hK]; exact le_max_right _ _
  -- the negative imaginary axis
  have himag : ∀ x : ℝ, x ≤ 0 → ‖F ((x : ℂ) * I)‖ ≤ K := by
    intro x hx
    rw [hFnorm]
    have hre' : ((x : ℂ) * I).re = 0 := by simp
    have him' : ((x : ℂ) * I).im = x := by simp
    have hn : ‖(x : ℂ) * I‖ = -x := by
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonpos hx]
    rw [hre', him', mul_zero, zero_sub, neg_neg]
    calc ‖Φ ((x : ℂ) * I)‖ * Real.exp (ρ * x)
        ≤ C * Real.exp (ρ * (-x)) * Real.exp (ρ * x) := by
          gcongr
          have := hgrow ((x : ℂ) * I)
          rwa [hn] at this
      _ = C := by
          rw [mul_assoc, ← Real.exp_add]
          rw [show ρ * (-x) + ρ * x = 0 by ring, Real.exp_zero, mul_one]
      _ ≤ K := hKC
  -- order-one growth
  have hbig : ∃ e < (2 : ℝ), ∃ B : ℝ, F =O[Bornology.cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)]
      fun w => Real.exp (B * ‖w‖ ^ e) := by
    refine ⟨1, by norm_num, ρ + ‖c‖, Asymptotics.IsBigO.of_bound C
      (Eventually.of_forall fun w => ?_)⟩
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.rpow_one, hFnorm]
    have h1 : -(a * w.re - ρ * w.im) ≤ ‖c‖ * ‖w‖ := by
      rw [← hre_cw, ← norm_mul]
      have := Complex.abs_re_le_norm (c * w)
      linarith [(abs_le.mp this).1]
    calc ‖Φ w‖ * Real.exp (-(a * w.re - ρ * w.im))
        ≤ C * Real.exp (ρ * ‖w‖) * Real.exp (‖c‖ * ‖w‖) :=
          mul_le_mul (hgrow w) (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le (by positivity)
      _ = C * Real.exp ((ρ + ‖c‖) * ‖w‖) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hq := PhragmenLindelof.quadrant_IV (f := F) (C := K) hFd.diffContOnCl hbig hreal himag
    hre him
  rw [hFnorm] at hq
  rw [← hK]
  calc ‖Φ z‖ = ‖Φ z‖ * Real.exp (-(a * z.re - ρ * z.im)) * Real.exp (a * z.re - ρ * z.im) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ K * Real.exp (a * z.re - ρ * z.im) :=
        mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le

/-- **The thin-strip bound.**  If `‖Φ(t)‖ ≤ e^{at}` for `t ≥ t₀ ≥ 0`, then there is `M₁ > 0` with
`‖Φ z‖ ≤ M₁ e^{a Re z}` for all `z` with `Re z ≥ 0` and `|Im z| ≤ 1`. -/
theorem exists_thinStrip_bound {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {C ρ : ℝ} (hC : 0 < C)
    (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) {a t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hup : ∀ t : ℝ, t₀ ≤ t → ‖Φ (t : ℂ)‖ ≤ Real.exp (a * t)) :
    ∃ M₁ : ℝ, 0 < M₁ ∧ ∀ z : ℂ, 0 ≤ z.re → |z.im| ≤ 1 → ‖Φ z‖ ≤ M₁ * Real.exp (a * z.re) := by
  refine ⟨max 1 (C * Real.exp ((ρ + |a|) * t₀)) * Real.exp ρ, by positivity, fun z hre him => ?_⟩
  have hK0 : 0 ≤ max 1 (C * Real.exp ((ρ + |a|) * t₀)) := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨him1, him2⟩ := abs_le.mp him
  rcases le_or_gt 0 z.im with hz | hz
  · calc ‖Φ z‖ ≤ max 1 (C * Real.exp ((ρ + |a|) * t₀)) * Real.exp (a * z.re + ρ * z.im) :=
          norm_le_exp_of_quadrant_I hΦ hC hρ hgrow ht₀ hup hre hz
      _ ≤ max 1 (C * Real.exp ((ρ + |a|) * t₀)) * Real.exp ρ * Real.exp (a * z.re) := by
          rw [mul_assoc, ← Real.exp_add]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK0
          have := mul_le_mul_of_nonneg_left him2 hρ
          linarith
  · calc ‖Φ z‖ ≤ max 1 (C * Real.exp ((ρ + |a|) * t₀)) * Real.exp (a * z.re - ρ * z.im) :=
          norm_le_exp_of_quadrant_IV hΦ hC hρ hgrow ht₀ hup hre hz.le
      _ ≤ max 1 (C * Real.exp ((ρ + |a|) * t₀)) * Real.exp ρ * Real.exp (a * z.re) := by
          rw [mul_assoc, ← Real.exp_add]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK0
          have := mul_le_mul_of_nonneg_left (show -z.im ≤ 1 by linarith) hρ
          linarith

/-! ## 3. Lipschitz control at the ray rate -/

/-- **Lipschitz bound at the ray rate.**  From the thin-strip bound, the Cauchy estimate on unit
discs gives `‖Φ(v) − Φ(u)‖ ≤ M₁ e^{3|a|} e^{ax} (v − u)` for `1 ≤ x ≤ u ≤ v ≤ x + 2`. -/
theorem norm_sub_le_of_thinStrip {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {M₁ a : ℝ}
    (hM : 0 ≤ M₁) (hstrip : ∀ z : ℂ, 0 ≤ z.re → |z.im| ≤ 1 → ‖Φ z‖ ≤ M₁ * Real.exp (a * z.re))
    {x u v : ℝ} (hx : 1 ≤ x) (hu : x ≤ u) (huv : u ≤ v) (hv : v ≤ x + 2) :
    ‖Φ (v : ℂ) - Φ (u : ℂ)‖ ≤ M₁ * Real.exp (3 * |a|) * Real.exp (a * x) * (v - u) := by
  have hderiv : ∀ s : ℝ, x ≤ s → s ≤ x + 2 →
      ‖deriv Φ (s : ℂ)‖ ≤ M₁ * Real.exp (3 * |a|) * Real.exp (a * x) := by
    intro s hs1 hs2
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := (s : ℂ)) (R := 1)
      (C := M₁ * Real.exp (3 * |a|) * Real.exp (a * x)) one_pos hΦ.diffContOnCl fun z hz => ?_
    · simpa using h
    · rw [mem_sphere_iff_norm] at hz
      have hre := abs_le.mp (Complex.abs_re_le_norm (z - (s : ℂ)))
      have him := abs_le.mp (Complex.abs_im_le_norm (z - (s : ℂ)))
      rw [hz, Complex.sub_re, Complex.ofReal_re] at hre
      rw [hz, Complex.sub_im, Complex.ofReal_im, sub_zero] at him
      have hz_re : 0 ≤ z.re := by linarith
      have hz_im : |z.im| ≤ 1 := abs_le.mpr him
      calc ‖Φ z‖ ≤ M₁ * Real.exp (a * z.re) := hstrip z hz_re hz_im
        _ ≤ M₁ * Real.exp (3 * |a|) * Real.exp (a * x) := by
            rw [mul_assoc, ← Real.exp_add]
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
            have h1 : a * (z.re - x) ≤ |a| * |z.re - x| := by
              calc a * (z.re - x) ≤ |a * (z.re - x)| := le_abs_self _
                _ = |a| * |z.re - x| := abs_mul _ _
            have h2 : |z.re - x| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
            have h3 : |a| * |z.re - x| ≤ |a| * 3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
            linarith
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s : ℝ => Φ s)
    (f' := fun s : ℝ => deriv Φ s) (a := u) (b := v)
    (C := M₁ * Real.exp (3 * |a|) * Real.exp (a * x))
    (fun s _ => ((hΦ (s : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt)
    (fun s hs => hderiv s (by linarith [hs.1]) (by linarith [hs.2])) v ⟨huv, le_rfl⟩
  exact hmvt

/-! ## 4. The window assembly with an arbitrary Lipschitz constant -/

/-- **Prime mass of one logarithmic window, arbitrary Lipschitz constant.**  As
`primeWindow_sum_ge_of_window_value`, with the variation of `Φ` on `[x, x+2]` given by any
`D`: the primes `p ∈ (e^{x+kh}, e^{x+(k+1)h}]` contribute at least
`e^{−σ(x+1)} · max(0, ‖Φ(x+kh)‖ − hD) · (e^x h/4) / (x+1)`. -/
theorem primeWindow_sum_ge_of_window_value_lip (Φ : ℂ → ℂ) {σ : ℝ} (hσ : 0 ≤ σ) {x h : ℝ}
    (hx0 : 0 ≤ x) (hh0 : 0 < h) {k : ℕ} (hkh : k * h + h ≤ 1) {D : ℝ} (hD0 : 0 ≤ D)
    (hlip : ∀ u v : ℝ, x ≤ u → u ≤ v → v ≤ x + 2 → ‖Φ (v : ℂ) - Φ (u : ℂ)‖ ≤ D * (v - u))
    {α X₁ : ℝ}
    (hθ : ∀ y L : ℝ, X₁ ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y)
    (hα0 : 0 ≤ α) (hX₁ : X₁ ≤ Real.exp x) (hα : Real.exp (x + 1) ^ α ≤ Real.exp x * h / 2) :
    Real.exp (-(σ * (x + 1))) * max 0 (‖Φ ((x : ℂ) + ((k * h : ℝ) : ℂ))‖ - h * D) / (x + 1)
        * (Real.exp x * h / 4)
      ≤ ∑ p ∈ Finset.Ioc ⌊Real.exp (x + k * h)⌋₊ ⌊Real.exp (x + ((k + 1 : ℕ) : ℝ) * h)⌋₊,
          if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0 := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.exp x := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; exact Real.exp_pos x
  obtain ⟨Yk, hYk⟩ : ∃ Yk : ℝ, Yk = Real.exp (x + k * h) := ⟨_, rfl⟩
  obtain ⟨Yk1, hYk1⟩ : ∃ Yk1 : ℝ, Yk1 = Real.exp (x + ((k + 1 : ℕ) : ℝ) * h) := ⟨_, rfl⟩
  have hYk0 : 0 < Yk := by rw [hYk]; exact Real.exp_pos _
  have hYk10 : 0 < Yk1 := by rw [hYk1]; exact Real.exp_pos _
  have hYk1gt : 1 < Yk1 := by rw [hYk1]; exact Real.one_lt_exp_iff.mpr (by positivity)
  have hkh0 : 0 ≤ (k : ℝ) * h := by positivity
  have hYkge : y ≤ Yk := by
    rw [hy, hYk]; exact Real.exp_le_exp.mpr (le_add_of_nonneg_right hkh0)
  have hYk1le : Yk1 ≤ Real.exp (x + 1) := by
    rw [hYk1]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    linarith
  have hYsucc : Yk1 = Yk * Real.exp h := by
    rw [hYk1, hYk, ← Real.exp_add]
    congr 1
    push_cast
    ring
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Yk1 - Yk := ⟨_, rfl⟩
  have hLk : Yk * h ≤ L := by
    rw [hL, hYsucc]
    have h1 := Real.add_one_le_exp h
    nlinarith
  have hyhL : y * h ≤ L := le_trans (mul_le_mul_of_nonneg_right hYkge hh0.le) hLk
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hyhL
  have hYL : Yk + L = Yk1 := by rw [hL]; ring
  have hlogYk : Real.log Yk = x + k * h := by rw [hYk]; exact Real.log_exp _
  have hlogYk1 : Real.log Yk1 = x + k * h + h := by
    rw [hYk1, Real.log_exp]
    push_cast
    ring
  obtain ⟨mk, hmk⟩ : ∃ mk : ℝ, mk = max 0 (‖Φ ((x : ℂ) + ((k * h : ℝ) : ℂ))‖ - h * D) :=
    ⟨_, rfl⟩
  have hmk0 : 0 ≤ mk := by rw [hmk]; exact le_max_left _ _
  -- the values of `Φ` at the primes of the window
  have hlow : ∀ p : ℕ, p.Prime → Yk < p → (p : ℝ) ≤ Yk + L → mk ≤ ‖Φ (Real.log p)‖ := by
    intro p hp hp1 hp2
    rw [hYL] at hp2
    have hp0 : (0 : ℝ) < p := lt_trans hYk0 hp1
    have hlog1 : x + k * h ≤ Real.log p := by
      rw [← hlogYk]
      exact (Real.log_lt_log hYk0 hp1).le
    have hlog2 : Real.log p ≤ x + k * h + h := by
      rw [← hlogYk1]
      exact Real.log_le_log hp0 hp2
    have hsub := hlip (x + k * h) (Real.log p) (le_add_of_nonneg_right hkh0) hlog1
      (by linarith)
    rw [Complex.ofReal_add] at hsub
    rw [hmk]
    refine max_le (norm_nonneg _) ?_
    have h1 := norm_sub_norm_le (Φ ((x : ℂ) + ((k * h : ℝ) : ℂ))) (Φ (Real.log p))
    rw [norm_sub_rev] at h1
    have h2 : D * (Real.log p - (x + k * h)) ≤ D * h := by
      gcongr
      linarith
    linarith
  -- the Chebyshev mass of the window
  have hθwin : y * h / 4 ≤ Chebyshev.theta (Yk + L) - Chebyshev.theta Yk := by
    have h1 := hθ Yk L (le_trans (by rw [hy]; exact hX₁) hYkge) hL0.le
    have h2 : (Yk + L) ^ α ≤ L / 2 := by
      rw [hYL]
      calc Yk1 ^ α ≤ Real.exp (x + 1) ^ α := Real.rpow_le_rpow hYk10.le hYk1le hα0
        _ ≤ y * h / 2 := by rw [hy]; exact hα
        _ ≤ L / 2 := by linarith
    linarith
  -- assemble via the window lemma
  have hsum := window_sum_ge_theta_window Φ hσ (by rw [hYL]; exact hYk1gt) hL0.le hmk0 hlow
  rw [hYL] at hsum hθwin
  have hlogpos : 0 < Real.log Yk1 := by rw [hlogYk1]; positivity
  have hlogle : Real.log Yk1 ≤ x + 1 := by rw [hlogYk1]; linarith
  have hrp : Real.exp (-(σ * (x + 1))) ≤ Yk1 ^ (-σ) := by
    calc Real.exp (-(σ * (x + 1))) = Real.exp (x + 1) ^ (-σ) := by
          rw [← Real.exp_mul]
          congr 1
          ring
      _ ≤ Yk1 ^ (-σ) := Real.rpow_le_rpow_of_nonpos hYk10 hYk1le (by linarith)
  have hnum : Real.exp (-(σ * (x + 1))) * mk ≤ Yk1 ^ (-σ) * mk :=
    mul_le_mul_of_nonneg_right hrp hmk0
  have hnn : 0 ≤ Yk1 ^ (-σ) * mk := mul_nonneg (Real.rpow_nonneg hYk10.le _) hmk0
  have hA : Real.exp (-(σ * (x + 1))) * mk / (x + 1) ≤ Yk1 ^ (-σ) * mk / Real.log Yk1 :=
    calc Real.exp (-(σ * (x + 1))) * mk / (x + 1) ≤ Yk1 ^ (-σ) * mk / (x + 1) :=
          div_le_div_of_nonneg_right hnum (by linarith)
      _ ≤ Yk1 ^ (-σ) * mk / Real.log Yk1 := div_le_div_of_nonneg_left hnn hlogpos hlogle
  rw [← hmk, ← hy, ← hYk, ← hYk1]
  calc Real.exp (-(σ * (x + 1))) * mk / (x + 1) * (y * h / 4)
      ≤ Yk1 ^ (-σ) * mk / Real.log Yk1 * (y * h / 4) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ ≤ Yk1 ^ (-σ) * mk / Real.log Yk1 * (Chebyshev.theta Yk1 - Chebyshev.theta Yk) :=
        mul_le_mul_of_nonneg_left hθwin (div_nonneg hnn hlogpos.le)
    _ ≤ _ := hsum

/-- **Assembly with an arbitrary Lipschitz constant.**  As
`exists_primeLogWeightedSum_gt_of_window_data`, with the variation of `Φ` on `[x, x+2]` given by
any `D` with `hD ≤ m/4`. -/
theorem exists_primeLogWeightedSum_gt_of_window_data_lip {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {σ : ℝ} (hσ : 0 ≤ σ) {x h : ℝ} (hx0 : 0 ≤ x) (hh0 : 0 < h) {N : ℕ} (hN0 : 0 < N)
    (hNh : (N : ℝ) * h = 1) {D : ℝ} (hD0 : 0 ≤ D)
    (hlip : ∀ u v : ℝ, x ≤ u → u ≤ v → v ≤ x + 2 → ‖Φ (v : ℂ) - Φ (u : ℂ)‖ ≤ D * (v - u))
    {α X₁ : ℝ}
    (hθ : ∀ y L : ℝ, X₁ ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y)
    (hα0 : 0 ≤ α) (hX₁ : X₁ ≤ Real.exp x) (hα : Real.exp (x + 1) ^ α ≤ Real.exp x * h / 2)
    {m : ℝ} (hmint : m ≤ ∫ t in (0 : ℝ)..1, ‖Φ (x + t)‖) (hhD : h * D ≤ m / 4) {M : ℝ}
    (hM : M + 1 ≤ Real.exp (-(σ * (x + 1))) * Real.exp x / (4 * (x + 1)) * (m / 2)) :
    ∃ N' : ℕ, M < primeLogWeightedSum Φ σ N' := by
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, ∀ t : ℝ, f t = ‖Φ (x + t)‖ := ⟨_, fun _ => rfl⟩
  have hfc : Continuous f := by
    rw [show f = fun t : ℝ => ‖Φ (x + t)‖ from funext hfdef]
    exact (hΦ.continuous.comp (continuous_const.add continuous_ofReal)).norm
  have hmint' : m ≤ ∫ t in (0 : ℝ)..1, f t := by simpa only [hfdef] using hmint
  -- the Lipschitz property of `f` on `[0, 1]`
  have hlipf : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 → f v ≤ f u + D * (v - u) := by
    intro u v hu huv hv1
    have hsub := hlip (x + u) (x + v) (by linarith) (by linarith) (by linarith)
    rw [Complex.ofReal_add, Complex.ofReal_add] at hsub
    rw [hfdef, hfdef]
    calc ‖Φ (x + v)‖ ≤ ‖Φ (x + u)‖ + ‖Φ (x + v) - Φ (x + u)‖ := by
          have := norm_sub_norm_le (Φ (x + v)) (Φ (x + u))
          linarith
      _ ≤ ‖Φ (x + u)‖ + D * (x + v - (x + u)) := by gcongr
      _ = ‖Φ (x + u)‖ + D * (v - u) := by ring
  -- the lower Riemann sum
  have hriemann := integral_le_sum_window_values_add hfc hN0 hD0 hlipf
  have hh : h = 1 / N := by
    field_simp
    linarith
  rw [← hh] at hriemann
  -- the per-window lower bounds `m_k` and their weighted sum
  obtain ⟨mk, hmkdef⟩ : ∃ mk : ℕ → ℝ, ∀ k : ℕ, mk k = max 0 (f (k * h) - h * D) :=
    ⟨_, fun _ => rfl⟩
  have hmk0 : ∀ k, 0 ≤ mk k := fun k => by rw [hmkdef]; exact le_max_left _ _
  have hmksum : m / 2 ≤ ∑ k ∈ range N, h * mk k := by
    have h1 : ∑ k ∈ range N, h * (f (k * h) - h * D) ≤ ∑ k ∈ range N, h * mk k :=
      sum_le_sum fun k _ => by
        rw [hmkdef]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) hh0.le
    have h2 : ∑ k ∈ range N, h * (f (k * h) - h * D)
        = (∑ k ∈ range N, h * f (k * h)) - h * D := by
      simp only [mul_sub, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      rw [← mul_assoc, ← mul_assoc, hNh, one_mul]
    linarith
  clear hmint hmint' hriemann hlipf hfc
  -- the prime windows `(Y k, Y (k+1)]`
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ → ℝ, ∀ k : ℕ, Y k = Real.exp (x + k * h) := ⟨_, fun _ => rfl⟩
  have hYmono : Monotone Y := fun i j hij => by
    rw [hYdef, hYdef]
    exact Real.exp_le_exp.mpr
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hh0.le))
  -- the lower bound for each prime window
  have hwin : ∀ k ∈ range N,
      Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (Real.exp x * h / 4)
        ≤ ∑ p ∈ Finset.Ioc ⌊Y k⌋₊ ⌊Y (k + 1)⌋₊,
            if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0 := by
    intro k hk
    have hkh : (k : ℝ) * h + h ≤ 1 := by
      have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Finset.mem_range.mp hk
      calc (k : ℝ) * h + h = ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
        _ ≤ N * h := mul_le_mul_of_nonneg_right this hh0.le
        _ = 1 := hNh
    have h := primeWindow_sum_ge_of_window_value_lip Φ hσ hx0 hh0 hkh hD0 hlip hθ hα0 hX₁ hα
    rw [← hfdef, ← hmkdef, ← hYdef, ← hYdef] at h
    exact h
  -- the window sums merge into one prime sum
  have hmerge := sum_range_sum_Ioc_eq_sum_Ioc
    (f := fun p : ℕ => if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0)
    (b := fun k => ⌊Y k⌋₊) (fun i j hij => Nat.floor_le_floor (hYmono hij)) N
  have hchain : ∑ k ∈ range N, Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (Real.exp x * h / 4)
      ≤ primeLogWeightedSum Φ σ (⌊Y N⌋₊ + 1) := by
    calc ∑ k ∈ range N, Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (Real.exp x * h / 4)
        ≤ ∑ k ∈ range N, ∑ p ∈ Finset.Ioc ⌊Y k⌋₊ ⌊Y (k + 1)⌋₊,
            (if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0) := sum_le_sum hwin
      _ = ∑ p ∈ Finset.Ioc ⌊Y 0⌋₊ ⌊Y N⌋₊,
            (if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0) := hmerge
      _ ≤ primeLogWeightedSum Φ σ (⌊Y N⌋₊ + 1) := window_sum_le_primeLogWeightedSum Φ σ _ _
  refine ⟨⌊Y N⌋₊ + 1, lt_of_lt_of_le ?_ hchain⟩
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hfactor : ∑ k ∈ range N,
      Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (Real.exp x * h / 4)
      = Real.exp (-(σ * (x + 1))) * Real.exp x / (4 * (x + 1)) * ∑ k ∈ range N, h * mk k := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    field_simp
  rw [hfactor]
  calc M < M + 1 := by linarith
    _ ≤ Real.exp (-(σ * (x + 1))) * Real.exp x / (4 * (x + 1)) * (m / 2) := hM
    _ ≤ Real.exp (-(σ * (x + 1))) * Real.exp x / (4 * (x + 1)) * ∑ k ∈ range N, h * mk k :=
        mul_le_mul_of_nonneg_left hmksum (by positivity)

/-! ## 5. The prime sums are unbounded whenever `ρ < 1 − σ` -/

/-- **The prime-sum lower bound without the cap.**  For `Φ ≢ 0` entire with
`‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}`, `0 ≤ σ` and `ρ < 1 − σ`, the sums `Σ_{p<N} p^{−σ} ‖Φ(log p)‖` are
unbounded. -/
theorem exists_primeLogWeightedSum_gt_of_lt_one_sub_capFree {Φ : ℂ → ℂ}
    (hΦ : Differentiable ℂ Φ) {C ρ σ : ℝ} (hρ : 0 ≤ ρ)
    (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) (hne : Φ ≠ 0) (hσ : 0 ≤ σ)
    (hρσ : ρ < 1 - σ) (M : ℝ) :
    ∃ N : ℕ, M < primeLogWeightedSum Φ σ N := by
  -- the growth constant is positive, since `Φ ≢ 0`
  have hC : 0 < C := by
    by_contra hC
    simp only [not_lt] at hC
    apply hne
    funext ξ
    have h := hgrow ξ
    have h2 : C * Real.exp (ρ * ‖ξ‖) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le
    exact norm_le_zero_iff.mp (le_trans h h2)
  -- the small exponent `δ`
  obtain ⟨δ, hδ0, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ 8 * δ ≤ 1 - σ - ρ ∧ δ ≤ 1 / 20 :=
    ⟨min ((1 - σ - ρ) / 8) (1 / 20), lt_min (by linarith) (by norm_num),
      by linarith [min_le_left ((1 - σ - ρ) / 8) (1 / 20)], min_le_right _ _⟩
  -- the ray exponent `a ≥ −ρ` and the admissible exponent `a' = a + δ`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = rayExponent Φ := ⟨_, rfl⟩
  have ha_lo : -ρ ≤ a := by rw [ha]; exact neg_le_rayExponent hΦ hC hρ hgrow hne
  obtain ⟨t₀, ht₀0, hup⟩ := exists_forall_norm_le_exp_rayExponent_add hC hgrow hδ0
  rw [← ha] at hup
  -- the thin-strip bound and the Lipschitz constant `K₀ e^{(a+δ)x}`
  obtain ⟨M₁, hM₁0, hstrip⟩ := exists_thinStrip_bound hΦ hC hρ hgrow ht₀0 hup
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = M₁ * Real.exp (3 * |a + δ|) := ⟨_, rfl⟩
  have hK₀0 : 0 < K₀ := by rw [hK₀]; positivity
  have hlipK : ∀ x u v : ℝ, 1 ≤ x → x ≤ u → u ≤ v → v ≤ x + 2 →
      ‖Φ (v : ℂ) - Φ (u : ℂ)‖ ≤ K₀ * Real.exp ((a + δ) * x) * (v - u) := by
    intro x u v hx hu huv hv
    rw [hK₀]
    exact norm_sub_le_of_thinStrip hΦ hM₁0.le hstrip hx hu huv hv
  -- the window theorem at exponent `α = 1 − 7δ`
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 - 7 * δ := ⟨_, rfl⟩
  have hα7 : 7 / 12 < α := by rw [hαdef]; linarith
  have hα1 : α < 1 := by rw [hαdef]; linarith
  have hα0 : 0 ≤ α := by linarith
  obtain ⟨X₁, -, hθ⟩ := exists_theta_window_lower_seven_twelfths hα7 hα1
  -- the window-length constant `c₀ = 1/(8K₀ + 1)`
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 1 / (8 * K₀ + 1) := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  have hc₀1 : c₀ ≤ 1 := by
    rw [hc₀, div_le_one (by positivity)]
    linarith
  have hc₀K : c₀ * K₀ ≤ 1 / 8 := by
    rw [hc₀, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- the thresholds
  have hev : ∀ᶠ x : ℝ in atTop, t₀ ≤ x ∧ 1 ≤ x ∧ X₁ ≤ Real.exp x ∧
      2 * K₀ ≤ Real.exp (δ * x) ∧ 4 * Real.exp (1 - 7 * δ) / c₀ ≤ Real.exp (δ * x) ∧
      (M + 1) * 16 * Real.exp σ ≤ 2 * δ * Real.exp (2 * δ * x) := by
    have h1 : Tendsto (fun x : ℝ => Real.exp (δ * x)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hδ0)
    have h2 : Tendsto (fun x : ℝ => 2 * δ * Real.exp (2 * δ * x)) atTop atTop :=
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))).const_mul_atTop
        (by linarith)
    refine (eventually_ge_atTop t₀).and ((eventually_ge_atTop 1).and
      ((Real.tendsto_exp_atTop.eventually_ge_atTop X₁).and
      ((h1.eventually_ge_atTop _).and ((h1.eventually_ge_atTop _).and
      (h2.eventually_ge_atTop _)))))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  -- a large point where `Φ` is large at the ray exponent
  obtain ⟨x, hxT, hbig⟩ := exists_exp_rayExponent_sub_lt hΦ hC hρ hgrow hne hδ0 T
  rw [← ha] at hbig
  obtain ⟨hxt₀, hx1, hxX₁, hxK, hxc, hxM⟩ := hT x hxT
  have hx0 : 0 ≤ x := by linarith
  -- the Lipschitz constant on `[x, x+2]`
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = K₀ * Real.exp ((a + δ) * x) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hlip : ∀ u v : ℝ, x ≤ u → u ≤ v → v ≤ x + 2 →
      ‖Φ (v : ℂ) - Φ (u : ℂ)‖ ≤ D * (v - u) := fun u v hu huv hv => by
    rw [hD]; exact hlipK x u v hx1 hu huv hv
  -- the window `[x, x + ℓ]`, `ℓ = e^{−3δx}`, on which `Φ` stays above `½ e^{(a−δ)x}`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.exp (-(3 * δ * x)) := ⟨_, rfl⟩
  have hℓ0 : 0 < ℓ := by rw [hℓ]; exact Real.exp_pos _
  have hδx : 0 ≤ δ * x := mul_nonneg hδ0.le hx0
  have hℓ1 : ℓ ≤ 1 := by rw [hℓ]; exact Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : ℝ, v₀ = Real.exp ((a - δ) * x) := ⟨_, rfl⟩
  have hv₀0 : 0 < v₀ := by rw [hv₀]; exact Real.exp_pos _
  have hDℓ : D * ℓ ≤ v₀ / 2 := by
    rw [hD, hℓ, hv₀, mul_assoc, ← Real.exp_add]
    have h1 : Real.exp ((a + δ) * x + -(3 * δ * x)) = Real.exp ((a - δ) * x) * Real.exp (-(δ * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1]
    have h2 : K₀ * Real.exp (-(δ * x)) ≤ 1 / 2 := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    calc K₀ * (Real.exp ((a - δ) * x) * Real.exp (-(δ * x)))
        = (K₀ * Real.exp (-(δ * x))) * Real.exp ((a - δ) * x) := by ring
      _ ≤ 1 / 2 * Real.exp ((a - δ) * x) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp ((a - δ) * x) / 2 := by ring
  have hwindow : ∀ t : ℝ, 0 ≤ t → t ≤ ℓ → v₀ / 2 ≤ ‖Φ (x + t)‖ := by
    intro t ht0 htℓ
    have hsub := hlip x (x + t) le_rfl (by linarith) (by linarith)
    rw [Complex.ofReal_add] at hsub
    have h1 := norm_sub_norm_le (Φ (x : ℂ)) (Φ ((x : ℂ) + (t : ℂ)))
    rw [norm_sub_rev] at h1
    have h2 : D * (x + t - x) ≤ D * ℓ := by gcongr; linarith
    have h3 : v₀ < ‖Φ (x : ℂ)‖ := by rw [hv₀]; exact hbig
    linarith
  -- the window integral
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ℓ * (v₀ / 2) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  have hmint : m ≤ ∫ t in (0 : ℝ)..1, ‖Φ (x + t)‖ := by
    have hcont : Continuous fun t : ℝ => ‖Φ (x + t)‖ :=
      (hΦ.continuous.comp (continuous_const.add continuous_ofReal)).norm
    have hint1 : ∫ t in (0 : ℝ)..ℓ, ‖Φ (x + t)‖ ≤ ∫ t in (0 : ℝ)..1, ‖Φ (x + t)‖ :=
      intervalIntegral.integral_mono_interval le_rfl hℓ0.le hℓ1
        (Eventually.of_forall fun t => norm_nonneg _) (hcont.intervalIntegrable _ _)
    have hint2 : ∫ t in (0 : ℝ)..ℓ, v₀ / 2 ≤ ∫ t in (0 : ℝ)..ℓ, ‖Φ (x + t)‖ :=
      intervalIntegral.integral_mono_on hℓ0.le (continuous_const.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _) fun t ht => hwindow t ht.1 ht.2
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint2
    rw [hm]
    linarith
  -- the window count `N` and the window length `h = 1/N`
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = c₀ * Real.exp (-(6 * δ * x)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η ≤ 1 := by
    rw [hη]
    calc c₀ * Real.exp (-(6 * δ * x)) ≤ 1 * 1 :=
          mul_le_mul hc₀1 (Real.exp_le_one_iff.mpr (by linarith)) (Real.exp_pos _).le zero_le_one
      _ = 1 := mul_one 1
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈1 / η⌉₊ := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; exact Nat.ceil_pos.mpr (by positivity)
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 / N := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  have hNh : (N : ℝ) * h = 1 := by rw [hh]; field_simp
  have hhη : h ≤ η := by
    rw [hh, div_le_iff₀ (by positivity)]
    have h1 := Nat.le_ceil (1 / η)
    rw [← hN] at h1
    calc (1 : ℝ) = 1 / η * η := by field_simp
      _ ≤ N * η := mul_le_mul_of_nonneg_right h1 hη0.le
      _ = η * N := mul_comm _ _
  have hηh : η / 2 ≤ h := by
    rw [hh, le_div_iff₀ (by positivity)]
    have h1 : (N : ℝ) < 1 / η + 1 := by rw [hN]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) / η + 1 ≤ 2 / η := by
      rw [div_add_one hη0.ne', div_le_div_iff_of_pos_right hη0]
      linarith
    calc η / 2 * N ≤ η / 2 * (2 / η) := by gcongr; linarith
      _ = 1 := by field_simp
  -- the Lipschitz constraint `hD ≤ m/4`
  have hhD : h * D ≤ m / 4 := by
    calc h * D ≤ η * D := mul_le_mul_of_nonneg_right hhη hD0
      _ = c₀ * K₀ * (Real.exp (-(6 * δ * x)) * Real.exp ((a + δ) * x)) := by
          rw [hη, hD]; ring
      _ = c₀ * K₀ * (Real.exp (-(δ * x)) * Real.exp ((a - 4 * δ) * x)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
      _ ≤ 1 / 8 * (1 * Real.exp ((a - 4 * δ) * x)) := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by linarith)
      _ = m / 4 := by
          rw [hm, hℓ, hv₀, show Real.exp ((a - 4 * δ) * x)
            = Real.exp (-(3 * δ * x)) * Real.exp ((a - δ) * x) by
              rw [← Real.exp_add]; congr 1; ring]
          ring
  -- the short-interval condition `e^{(x+1)α} ≤ e^x h/2`
  have hα : Real.exp (x + 1) ^ α ≤ Real.exp x * h / 2 := by
    rw [← Real.exp_mul, hαdef]
    have h1 : Real.exp ((x + 1) * (1 - 7 * δ)) = Real.exp (1 - 7 * δ) * Real.exp x * Real.exp (-(7 * δ * x)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [h1]
    have h2 : Real.exp x * h / 2 ≥ Real.exp x * (η / 4) := by
      have := mul_le_mul_of_nonneg_left hηh (Real.exp_pos x).le
      linarith
    have h3 : Real.exp (1 - 7 * δ) * Real.exp (-(7 * δ * x)) ≤ c₀ / 4 * Real.exp (-(6 * δ * x)) := by
      have h4 : Real.exp (-(7 * δ * x)) = Real.exp (-(δ * x)) * Real.exp (-(6 * δ * x)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h4, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      rw [div_le_iff₀ hc₀0] at hxc
      linarith
    calc Real.exp (1 - 7 * δ) * Real.exp x * Real.exp (-(7 * δ * x))
        = Real.exp x * (Real.exp (1 - 7 * δ) * Real.exp (-(7 * δ * x))) := by ring
      _ ≤ Real.exp x * (c₀ / 4 * Real.exp (-(6 * δ * x))) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = Real.exp x * (η / 4) := by rw [hη]; ring
      _ ≤ Real.exp x * h / 2 := h2
  -- the size condition
  have hM : M + 1 ≤ Real.exp (-(σ * (x + 1))) * Real.exp x / (4 * (x + 1)) * (m / 2) := by
    have hx1' : (0 : ℝ) < x + 1 := by linarith
    have hm2 : m / 2 = 1 / 4 * Real.exp ((a - 4 * δ) * x) := by
      rw [hm, hℓ, hv₀, show Real.exp ((a - 4 * δ) * x)
        = Real.exp (-(3 * δ * x)) * Real.exp ((a - δ) * x) by
          rw [← Real.exp_add]; congr 1; ring]
      ring
    rw [hm2]
    have h1 : Real.exp (-(σ * (x + 1))) * Real.exp x * Real.exp ((a - 4 * δ) * x)
        = Real.exp (-σ) * Real.exp ((1 - σ + a - 4 * δ) * x) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (4 * δ * x) ≤ Real.exp ((1 - σ + a - 4 * δ) * x) := by
      refine Real.exp_le_exp.mpr ?_
      have := mul_nonneg (show 0 ≤ 1 - σ + a - 8 * δ by linarith) hx0
      linarith
    have h3 : 2 * δ * (x + 1) ≤ Real.exp (2 * δ * x) := by
      have := Real.add_one_le_exp (2 * δ * x)
      linarith
    have h4 : Real.exp (4 * δ * x) = Real.exp (2 * δ * x) * Real.exp (2 * δ * x) := by
      rw [← Real.exp_add]; congr 1; ring
    have h5 : (M + 1) * 16 * Real.exp σ * (x + 1) ≤ Real.exp (4 * δ * x) := by
      rw [h4]
      calc (M + 1) * 16 * Real.exp σ * (x + 1) ≤ 2 * δ * Real.exp (2 * δ * x) * (x + 1) :=
            mul_le_mul_of_nonneg_right hxM hx1'.le
        _ = Real.exp (2 * δ * x) * (2 * δ * (x + 1)) := by ring
        _ ≤ Real.exp (2 * δ * x) * Real.exp (2 * δ * x) :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    have hexpσ : Real.exp (-σ) * Real.exp σ = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hQ : Real.exp (-(σ * (x + 1))) * Real.exp x / (4 * (x + 1))
          * (1 / 4 * Real.exp ((a - 4 * δ) * x))
        = Real.exp (-σ) * Real.exp ((1 - σ + a - 4 * δ) * x) / (16 * (x + 1)) := by
      rw [← h1]
      field_simp
      ring
    rw [hQ, le_div_iff₀ (by positivity)]
    calc (M + 1) * (16 * (x + 1)) = Real.exp (-σ) * ((M + 1) * 16 * Real.exp σ * (x + 1)) := by
          rw [show Real.exp (-σ) * ((M + 1) * 16 * Real.exp σ * (x + 1))
              = (Real.exp (-σ) * Real.exp σ) * ((M + 1) * (16 * (x + 1))) by ring, hexpσ, one_mul]
      _ ≤ Real.exp (-σ) * Real.exp (4 * δ * x) :=
          mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
      _ ≤ Real.exp (-σ) * Real.exp ((1 - σ + a - 4 * δ) * x) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  exact exists_primeLogWeightedSum_gt_of_window_data_lip hΦ hσ hx0 hh0 hN0 hNh hD0 hlip hθ hα0
    hxX₁ hα hmint hhD hM

end RHTower
