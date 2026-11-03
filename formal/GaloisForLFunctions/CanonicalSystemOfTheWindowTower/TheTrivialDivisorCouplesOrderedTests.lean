import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm

/-!
# The trivial divisor couples ordered tests

Two real tests are **ordered at `a`** when `f` vanishes right of `a` and `g` vanishes left of `a`.
Weil's form `Q` couples them only through their cross-correlation `c(x) = ∫ f(u) g(u + x) du`,
which lives on `x ≥ 0`, and the coupling kernel is explicit:

`Q(f + g) = Q(f) + Q(g) + 2(∫_0^∞ κ(x) c(x) dx − Σ_n Λ(n) n^{−1/2} c(log n))`
(`weilQuad_add_of_ordered`), with the **collar kernel**

`κ(x) = 2cosh(x/2) − ω(x) = e^{x/2} − e^{−x/2}/(e^{2x} − 1)`   (`two_mul_cosh_sub_archLevyDensity`).

The kernel is the trivial divisor of `ζ` read at separation `x > 0`:
`κ(x) = e^{(1−½)x} − Σ_{k ≥ 1} e^{(−2k−½)x}` (`hasSum_collarKernel`) — the pole `s = 1` with sign `+`,
the trivial zeros `s = −2k` with sign `−`. The Gamma pole `s = 0` (the mode `e^{−x/2}` of the Lévy
density) cancels exactly against the decaying half of the pole term.

Consequently (`orderedCoupling_eq_moments`) the coupling factors through moments at the trivial
divisor: with `μ_s(f) = ∫ f(u) e^{(½ − s)u}` (left test) and `ν_s(g) = ∫ g(v) e^{(s − ½)v}`
(right test),

`∫_0^∞ κ c = μ_1(f) ν_1(g) − Σ_{k ≥ 1} μ_{−2k}(f) ν_{−2k}(g)`.

Across a separation containing no `log n`, the archimedean place transmits nothing but these
moments.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower
open scoped Real

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open SpacingScaleHarmonicAnalysis

/-! ### The collar kernel -/

/-- The **collar kernel** `κ(x) = e^{x/2} − e^{−x/2}/(e^{2x} − 1)`. -/
def collarKernel (x : ℝ) : ℝ := Real.exp (x / 2) - Real.exp (-x / 2) / (Real.exp (2 * x) - 1)

/-- `2cosh(x/2) − ω(x) = κ(x)` for `x > 0`. -/
theorem two_mul_cosh_sub_archLevyDensity {x : ℝ} (hx : 0 < x) :
    2 * Real.cosh (x / 2) - archLevyDensity x = collarKernel x := by
  set y := Real.exp (x / 2) with hy
  have hy1 : 1 < y := Real.one_lt_exp_iff.mpr (by linarith)
  have hy0 : 0 < y := by linarith
  have e1 : Real.exp (2 * x) = y ^ 4 := by
    rw [hy, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-x / 2) = y⁻¹ := by rw [neg_div, Real.exp_neg]
  have e3 : Real.exp (-2 * x) = (y ^ 4)⁻¹ := by
    rw [show -2 * x = -(2 * x) by ring, Real.exp_neg, e1]
  have h4 : 1 < y ^ 4 := one_lt_pow₀ hy1 (by norm_num)
  have h4' : y ^ 4 - 1 ≠ 0 := by linarith
  have h4'' : 1 - (y ^ 4)⁻¹ ≠ 0 := by
    have : (y ^ 4)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h4
    linarith
  unfold collarKernel archLevyDensity
  rw [Real.cosh_eq, e1, e2, e3, show -(x / 2) = -x / 2 by ring, e2]
  field_simp
  ring

/-- **The collar kernel is the trivial divisor of `ζ`**:
`κ(x) = e^{x/2} − Σ_{k ≥ 0} e^{−(2(k+1) + ½)x}` for `x > 0`. -/
theorem hasSum_collarKernel {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => Real.exp (-(2 * ((k : ℝ) + 1) + 1 / 2) * x))
      (Real.exp (x / 2) - collarKernel x) := by
  have hr : Real.exp (-(2 * x)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := (hasSum_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left (Real.exp (-(5 / 2 * x)))
  have hterm : (fun k : ℕ => Real.exp (-(5 / 2 * x)) * Real.exp (-(2 * x)) ^ k) =
      fun k : ℕ => Real.exp (-(2 * ((k : ℝ) + 1) + 1 / 2) * x) := by
    funext k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  rw [hterm] at hg
  have hval : Real.exp (-(5 / 2 * x)) * (1 - Real.exp (-(2 * x)))⁻¹ =
      Real.exp (x / 2) - collarKernel x := by
    set y := Real.exp (x / 2) with hy
    have hy1 : 1 < y := Real.one_lt_exp_iff.mpr (by linarith)
    have hy0 : 0 < y := by linarith
    have e1 : Real.exp (2 * x) = y ^ 4 := by
      rw [hy, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : Real.exp (-x / 2) = y⁻¹ := by rw [neg_div, Real.exp_neg]
    have e3 : Real.exp (-(2 * x)) = (y ^ 4)⁻¹ := by rw [Real.exp_neg, e1]
    have e5 : Real.exp (-(5 / 2 * x)) = (y ^ 5)⁻¹ := by
      rw [Real.exp_neg, hy, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    have h4 : 1 < y ^ 4 := one_lt_pow₀ hy1 (by norm_num)
    have h4' : y ^ 4 - 1 ≠ 0 := by linarith
    have h4'' : 1 - (y ^ 4)⁻¹ ≠ 0 := by
      have : (y ^ 4)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h4
      linarith
    rw [collarKernel, e1, e2, e3, e5]
    field_simp
    ring
  rw [hval] at hg
  exact hg

/-! ### Ordered tests -/

/-- `f` and `g` are **ordered at `a`**: `f` vanishes right of `a`, `g` vanishes left of `a`. -/
structure OrderedAt (a : ℝ) (f g : ℝ → ℝ) : Prop where
  left : ∀ u, a < u → f u = 0
  right : ∀ u, u < a → g u = 0

/-- The cross-correlation `c(x) = ∫ f(u) g(u + x) du`. -/
def crossCorr (f g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u, f u * g (u + x)

variable {a : ℝ} {f g : ℝ → ℝ}

namespace OrderedAt

/-- A continuous left test vanishes at the cut. -/
theorem left_at (h : OrderedAt a f g) (hf : Continuous f) : f a = 0 := by
  have hcl : IsClosed {u | f u = 0} := isClosed_eq hf continuous_const
  have hsub : Ioi a ⊆ {u | f u = 0} := fun u hu => h.left u hu
  have := hcl.closure_subset_iff.mpr hsub
  exact this (by rw [closure_Ioi]; exact self_mem_Ici)

/-- Ordered continuous tests have disjoint supports pointwise. -/
theorem mul_eq_zero (h : OrderedAt a f g) (hf : Continuous f) (u : ℝ) : f u * g u = 0 := by
  rcases lt_trichotomy u a with hu | hu | hu
  · rw [h.right u hu, mul_zero]
  · rw [hu, h.left_at hf, zero_mul]
  · rw [h.left u hu, zero_mul]

/-- A positive shift moves the right test off the left one in the wrong direction. -/
theorem shift_mul_eq_zero (h : OrderedAt a f g) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    f (u + x) * g u = 0 := by
  by_cases hu : u < a
  · rw [h.right u hu, mul_zero]
  · rw [h.left (u + x) (by linarith [not_lt.mp hu]), zero_mul]

/-- The cross-correlation vanishes at negative lags. -/
theorem mul_shift_eq_zero_of_neg (h : OrderedAt a f g) {x : ℝ} (hx : x < 0) (u : ℝ) :
    f u * g (u + x) = 0 := by
  by_cases hu : a < u
  · rw [h.left u hu, zero_mul]
  · rw [h.right (u + x) (by linarith [not_lt.mp hu]), mul_zero]

theorem crossCorr_eq_zero_of_neg (h : OrderedAt a f g) {x : ℝ} (hx : x < 0) :
    crossCorr f g x = 0 := by
  unfold crossCorr
  simp only [h.mul_shift_eq_zero_of_neg hx]
  exact integral_zero _ _

theorem crossCorr_zero (h : OrderedAt a f g) (hf : Continuous f) : crossCorr f g 0 = 0 := by
  unfold crossCorr
  simp only [add_zero, h.mul_eq_zero hf]
  exact integral_zero _ _

end OrderedAt

/-! ### Exponential moments of the cross-correlation -/

/-- The integrand `e^{λx} f(u) g(u + x)` on the product. -/
theorem integrable_prod_exp_mul (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (c : ℝ) :
    Integrable (fun p : ℝ × ℝ => Real.exp (c * p.1) * (f p.2 * g (p.2 + p.1)))
      (volume.prod volume) := by
  have hK : IsCompact ((fun p : ℝ × ℝ => (p.2 - p.1, p.1)) '' (tsupport f ×ˢ tsupport g)) :=
    (hfc.prod hgc).image (by fun_prop)
  have hcont : Continuous fun p : ℝ × ℝ => Real.exp (c * p.1) * (f p.2 * g (p.2 + p.1)) := by
    fun_prop
  have hsupp : HasCompactSupport fun p : ℝ × ℝ => Real.exp (c * p.1) * (f p.2 * g (p.2 + p.1)) := by
    refine HasCompactSupport.intro hK fun p hp => ?_
    by_contra hne
    apply hp
    have h1 : f p.2 ≠ 0 := fun h => hne (by simp [h])
    have h2 : g (p.2 + p.1) ≠ 0 := fun h => hne (by simp [h])
    exact ⟨(p.2, p.2 + p.1), ⟨subset_tsupport f h1, subset_tsupport g h2⟩, by simp⟩
  have : Integrable (fun p : ℝ × ℝ => Real.exp (c * p.1) * (f p.2 * g (p.2 + p.1))) volume :=
    hcont.integrable_of_hasCompactSupport hsupp
  rwa [Measure.volume_eq_prod] at this

/-- `x ↦ c(x) e^{λx}` is integrable. -/
theorem integrable_crossCorr_mul_exp (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (c : ℝ) :
    Integrable fun x => crossCorr f g x * Real.exp (c * x) := by
  have h := (integrable_prod_exp_mul hf hfc hg hgc c).integral_prod_left
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [crossCorr]
  rw [← integral_mul_const]
  congr 1; funext u; ring

/-- **Exponential moments factor**: `∫ c(x) e^{λx} dx = (∫ f(u) e^{−λu} du)(∫ g(v) e^{λv} dv)`. -/
theorem integral_crossCorr_mul_exp (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (c : ℝ) :
    ∫ x, crossCorr f g x * Real.exp (c * x) =
      (∫ u, f u * Real.exp (-(c * u))) * ∫ v, g v * Real.exp (c * v) := by
  have hint := integrable_prod_exp_mul hf hfc hg hgc c
  calc ∫ x, crossCorr f g x * Real.exp (c * x)
      = ∫ x, ∫ u, Real.exp (c * x) * (f u * g (u + x)) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [crossCorr]
        rw [← integral_mul_const]
        congr 1; funext u; ring
    _ = ∫ u, ∫ x, Real.exp (c * x) * (f u * g (u + x)) := integral_integral_swap hint
    _ = ∫ u, f u * Real.exp (-(c * u)) * ∫ v, g v * Real.exp (c * v) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only
        have hsub : ∫ x, Real.exp (c * x) * (f u * g (u + x)) =
            ∫ v, Real.exp (c * (v - u)) * (f u * g v) := by
          rw [← integral_add_right_eq_self (fun v => Real.exp (c * (v - u)) * (f u * g v)) u]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only
          rw [show x + u - u = x by ring, add_comm u x]
        rw [hsub, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        simp only
        rw [show c * (v - u) = c * v + -(c * u) by ring, Real.exp_add]
        ring
    _ = (∫ u, f u * Real.exp (-(c * u))) * ∫ v, g v * Real.exp (c * v) := by
        rw [integral_mul_const]

/-! ### The pieces of Weil's form on ordered tests -/

namespace OrderedAt

/-- The mixed Lévy integrand of ordered tests is `−ω(y) c(y)`. -/
theorem levyMixed_eq (h : OrderedAt a f g) (hf : Continuous f) {y : ℝ} (hy : 0 < y) :
    levyMixed f g y = -(archLevyDensity y * crossCorr f g y) := by
  unfold levyMixed crossCorr
  have e : ∀ u, (f u - f (u + y)) * (g u - g (u + y)) = -(f u * g (u + y)) := fun u => by
    have h1 := h.mul_eq_zero hf u
    have h2 := h.mul_eq_zero hf (u + y)
    have h3 := h.shift_mul_eq_zero hy u
    linear_combination h1 - h3 + h2
  simp_rw [e]
  rw [integral_neg]
  ring

/-- Ordered tests are orthogonal in `L²`. -/
theorem integral_sq_add (h : OrderedAt a f g) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ u, (f u + g u) ^ 2 = (∫ u, f u ^ 2) + ∫ u, g u ^ 2 := by
  have e : ∀ u, (f u + g u) ^ 2 = f u ^ 2 + g u ^ 2 := fun u => by
    have := h.mul_eq_zero hf u
    linear_combination 2 * this
  simp_rw [e]
  exact integral_add (integrable_sq_of_continuous hf hfc) (integrable_sq_of_continuous hg hgc)

/-- The cross-correlation of ordered tests lives on `(0, ∞)`. -/
theorem crossCorr_eq_zero_of_nonpos (h : OrderedAt a f g) (hf : Continuous f) {x : ℝ}
    (hx : x ≤ 0) : crossCorr f g x = 0 := by
  rcases hx.lt_or_eq with hx | hx
  · exact h.crossCorr_eq_zero_of_neg hx
  · rw [hx]; exact h.crossCorr_zero hf

end OrderedAt

/-! ### The pole plane -/

theorem integrable_mul_exp (hf : Continuous f) (hfc : HasCompactSupport f) (c : ℝ) :
    Integrable fun u => f u * Real.exp (c * u) :=
  (hf.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
    hfc.mul_right

theorem coshHalfMoment_eq (hf : Continuous f) (hfc : HasCompactSupport f) :
    coshHalfMoment f =
      ((∫ u, f u * Real.exp ((1 / 2) * u)) + ∫ u, f u * Real.exp (-(1 / 2) * u)) / 2 := by
  unfold coshHalfMoment
  rw [← integral_add (integrable_mul_exp hf hfc _) (integrable_mul_exp hf hfc _),
    ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [Real.cosh_eq, show u / 2 = 1 / 2 * u by ring, show -(1 / 2 * u) = -(1 / 2) * u by ring]
  ring

theorem sinhHalfMoment_eq (hf : Continuous f) (hfc : HasCompactSupport f) :
    sinhHalfMoment f =
      ((∫ u, f u * Real.exp ((1 / 2) * u)) - ∫ u, f u * Real.exp (-(1 / 2) * u)) / 2 := by
  unfold sinhHalfMoment
  rw [← integral_sub (integrable_mul_exp hf hfc _) (integrable_mul_exp hf hfc _),
    ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [Real.sinh_eq, show u / 2 = 1 / 2 * u by ring, show -(1 / 2 * u) = -(1 / 2) * u by ring]
  ring

/-- **The pole plane couples through `cosh`**: `C(f)C(g) − S(f)S(g) = ∫ c(x) cosh(x/2) dx`. -/
theorem cosh_mul_sub_sinh_mul_eq (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    coshHalfMoment f * coshHalfMoment g - sinhHalfMoment f * sinhHalfMoment g =
      ∫ x, crossCorr f g x * Real.cosh (x / 2) := by
  have e1 := integral_crossCorr_mul_exp hf hfc hg hgc (1 / 2)
  have e2 := integral_crossCorr_mul_exp hf hfc hg hgc (-(1 / 2))
  have hc : ∫ x, crossCorr f g x * Real.cosh (x / 2) =
      ((∫ x, crossCorr f g x * Real.exp (1 / 2 * x)) +
        ∫ x, crossCorr f g x * Real.exp (-(1 / 2) * x)) / 2 := by
    rw [← integral_add (integrable_crossCorr_mul_exp hf hfc hg hgc _)
      (integrable_crossCorr_mul_exp hf hfc hg hgc _), ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.cosh_eq, show x / 2 = 1 / 2 * x by ring, show -(1 / 2 * x) = -(1 / 2) * x by ring]
    ring
  have n1 : (fun u => f u * Real.exp (-(1 / 2 * u))) = fun u => f u * Real.exp (-(1 / 2) * u) := by
    funext u; rw [show -(1 / 2 * u) = -(1 / 2) * u by ring]
  have n2 : (fun u => f u * Real.exp (-(-(1 / 2) * u))) = fun u => f u * Real.exp (1 / 2 * u) := by
    funext u; rw [show -(-(1 / 2) * u) = 1 / 2 * u by ring]
  rw [n1] at e1
  rw [n2] at e2
  rw [hc, e1, e2, coshHalfMoment_eq hf hfc, coshHalfMoment_eq hg hgc, sinhHalfMoment_eq hf hfc,
    sinhHalfMoment_eq hg hgc]
  ring

theorem coshHalfMoment_add (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    coshHalfMoment (fun u => f u + g u) = coshHalfMoment f + coshHalfMoment g := by
  unfold coshHalfMoment
  have i1 : Integrable fun x => f x * Real.cosh (x / 2) :=
    (hf.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hfc.mul_right
  have i2 : Integrable fun x => g x * Real.cosh (x / 2) :=
    (hg.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hgc.mul_right
  rw [← integral_add i1 i2]
  congr 1; funext x; ring

theorem sinhHalfMoment_add (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    sinhHalfMoment (fun u => f u + g u) = sinhHalfMoment f + sinhHalfMoment g := by
  unfold sinhHalfMoment
  have i1 : Integrable fun x => f x * Real.sinh (x / 2) :=
    (hf.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hfc.mul_right
  have i2 : Integrable fun x => g x * Real.sinh (x / 2) :=
    (hg.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hgc.mul_right
  rw [← integral_add i1 i2]
  congr 1; funext x; ring

/-! ### The prime sum -/

/-- A compactly supported test is supported in some `[−R, R]`. -/
theorem exists_supportedIn (hfc : HasCompactSupport f) : ∃ R, 0 ≤ R ∧ SupportedIn R f := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun u hu => ?_⟩
  by_contra hne
  have := hR (subset_tsupport f hne)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_max_left R 0]

theorem supportedIn_mono {R R' : ℝ} (h : SupportedIn R f) (hRR : R ≤ R') : SupportedIn R' f :=
  fun u hu => h u (lt_of_le_of_lt hRR hu)

/-- One lag `L > 0` of ordered tests: the lag correlations of `f + g` gain `2c(L)`. -/
theorem lag_add_of_ordered (h : OrderedAt a f g) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) {L : ℝ} (hL : 0 < L) :
    ((∫ t, (f t + g t) * (f (t - L) + g (t - L))) + ∫ t, (f t + g t) * (f (t + L) + g (t + L))) =
      ((∫ t, f t * f (t - L)) + ∫ t, f t * f (t + L)) +
        ((∫ t, g t * g (t - L)) + ∫ t, g t * g (t + L)) + 2 * crossCorr f g L := by
  have p1 : ∀ t, (f t + g t) * (f (t - L) + g (t - L)) =
      f t * f (t - L) + g t * g (t - L) + f (t - L) * g t := fun t => by
    have := h.mul_shift_eq_zero_of_neg (x := -L) (by linarith) t
    rw [← sub_eq_add_neg] at this
    linear_combination this
  have p2 : ∀ t, (f t + g t) * (f (t + L) + g (t + L)) =
      f t * f (t + L) + g t * g (t + L) + f t * g (t + L) := fun t => by
    have := h.shift_mul_eq_zero hL t
    linear_combination this
  have i1 : Integrable fun t => f t * f (t - L) :=
    (hf.mul (hf.comp (continuous_sub_right L))).integrable_of_hasCompactSupport hfc.mul_right
  have i2 : Integrable fun t => g t * g (t - L) :=
    (hg.mul (hg.comp (continuous_sub_right L))).integrable_of_hasCompactSupport hgc.mul_right
  have i3 : Integrable fun t => f (t - L) * g t :=
    ((hf.comp (continuous_sub_right L)).mul hg).integrable_of_hasCompactSupport hgc.mul_left
  have j1 : Integrable fun t => f t * f (t + L) :=
    (hf.mul (hf.comp (continuous_add_const L))).integrable_of_hasCompactSupport hfc.mul_right
  have j2 : Integrable fun t => g t * g (t + L) :=
    (hg.mul (hg.comp (continuous_add_const L))).integrable_of_hasCompactSupport hgc.mul_right
  have j3 : Integrable fun t => f t * g (t + L) :=
    (hf.mul (hg.comp (continuous_add_const L))).integrable_of_hasCompactSupport hfc.mul_right
  have hsub : ∫ t, f (t - L) * g t = crossCorr f g L := by
    unfold crossCorr
    rw [← integral_add_right_eq_self (fun t => f (t - L) * g t) L]
    congr 1; funext u; simp only [add_sub_cancel_right]
  simp_rw [p1, p2]
  rw [integral_add (f := fun t => f t * f (t - L) + g t * g (t - L)) (g := fun t => f (t - L) * g t)
      (i1.add i2) i3, integral_add i1 i2,
    integral_add (f := fun t => f t * f (t + L) + g t * g (t + L)) (g := fun t => f t * g (t + L))
      (j1.add j2) j3, integral_add j1 j2, hsub]
  unfold crossCorr
  ring

theorem vonMangoldtAtom_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) : vonMangoldtAtom n = 0 := by
  unfold vonMangoldtAtom
  rw [if_neg (by omega)]

/-- **The prime sum of ordered tests**: `P(f + g) = P(f) + P(g) + 2Σ_n Λ(n)n^{−1/2} c(log n)`. -/
theorem primeSum_add_of_ordered (h : OrderedAt a f g) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    primeSum (fun u => f u + g u) = primeSum f + primeSum g +
      2 * ∑' n : ℕ, vonMangoldtAtom n * crossCorr f g (Real.log n) := by
  obtain ⟨R₁, -, hR₁⟩ := exists_supportedIn hfc
  obtain ⟨R₂, -, hR₂⟩ := exists_supportedIn hgc
  have hfR := supportedIn_mono hR₁ (le_max_left R₁ R₂)
  have hgR := supportedIn_mono hR₂ (le_max_right R₁ R₂)
  set R := max R₁ R₂
  have hsum : ∑' n : ℕ, vonMangoldtAtom n * crossCorr f g (Real.log n) =
      ∑ n ∈ Finset.range (lagRange R), vonMangoldtAtom n * crossCorr f g (Real.log n) := by
    refine tsum_eq_sum fun n hn => ?_
    have hn' : lagRange R ≤ n := by simpa using hn
    have hl := two_mul_lt_abs_log_of_lagRange_le hn'
    unfold crossCorr
    simp only [mul_shift_eq_zero_of_supportedIn hfR hgR hl, integral_zero, mul_zero]
  rw [primeSum_eq_sum_of_supportedIn (supportedIn_add hfR hgR), primeSum_eq_sum_of_supportedIn hfR,
    primeSum_eq_sum_of_supportedIn hgR, hsum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : 2 ≤ n
  · have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    rw [lag_add_of_ordered h hf hfc hg hgc hL]
    ring
  · rw [vonMangoldtAtom_eq_zero_of_lt_two (by omega)]
    ring

/-! ### Weil's form on ordered tests -/

/-- The **ordered coupling** `∫_0^∞ κ(x) c(x) dx − Σ_n Λ(n) n^{−1/2} c(log n)`. -/
def orderedCoupling (f g : ℝ → ℝ) : ℝ :=
  (∫ x in Ioi (0 : ℝ), collarKernel x * crossCorr f g x) -
    ∑' n : ℕ, vonMangoldtAtom n * crossCorr f g (Real.log n)

theorem integrable_crossCorr_mul_cosh (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable fun x => crossCorr f g x * Real.cosh (x / 2) := by
  have h := ((integrable_crossCorr_mul_exp hf hfc hg hgc (1 / 2)).add
    (integrable_crossCorr_mul_exp hf hfc hg hgc (-(1 / 2)))).div_const 2
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  rw [Real.cosh_eq, show x / 2 = 1 / 2 * x by ring, show -(1 / 2 * x) = -(1 / 2) * x by ring]
  ring

theorem OrderedAt.integrableOn_archLevyDensity_mul_crossCorr (h : OrderedAt a f g)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    IntegrableOn (fun x => archLevyDensity x * crossCorr f g x) (Ioi 0) :=
  (integrableOn_levyMixed hf hfc hg hgc).neg.congr_fun
    (fun y hy => by simp only [Pi.neg_apply, h.levyMixed_eq hf.continuous hy, neg_neg])
    measurableSet_Ioi

/-- `∫_0^∞ κ c = 2∫_0^∞ c cosh(x/2) − ∫_0^∞ ω c`. -/
theorem OrderedAt.integral_collarKernel_mul (h : OrderedAt a f g) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∫ x in Ioi (0 : ℝ), collarKernel x * crossCorr f g x =
      2 * (∫ x in Ioi (0 : ℝ), crossCorr f g x * Real.cosh (x / 2)) -
        ∫ x in Ioi (0 : ℝ), archLevyDensity x * crossCorr f g x := by
  have i1 := (integrable_crossCorr_mul_cosh hf.continuous hfc hg.continuous hgc).integrableOn
    (s := Ioi (0 : ℝ))
  have i2 := h.integrableOn_archLevyDensity_mul_crossCorr hf hfc hg hgc
  rw [← integral_const_mul, ← integral_sub (i1.const_mul 2) i2]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [← two_mul_cosh_sub_archLevyDensity hx]
  ring

/-- **Weil's form on ordered tests**: `Q(f + g) = Q(f) + Q(g) + 2(∫_0^∞ κ c − Σ_n Λ(n)n^{−1/2} c(log n))`. -/
theorem weilQuad_add_of_ordered (h : OrderedAt a f g) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    weilQuad (fun u => f u + g u) = weilQuad f + weilQuad g + 2 * orderedCoupling f g := by
  have hfg : ContDiff ℝ 2 (fun u => f u + g u) := hf.add hg
  have hfgc : HasCompactSupport (fun u => f u + g u) := hfc.add hgc
  rw [weilQuad_eq hfg hfgc, weilQuad_eq hf hfc, weilQuad_eq hg hgc]
  have hL2 := h.integral_sq_add hf.continuous hfc hg.continuous hgc
  have hlev : levyEnergy (fun u => f u + g u) =
      levyEnergy f + levyEnergy g + 2 * ∫ y in Ioi 0, levyMixed f g y := by
    have := levyEnergy_smul_add hf hfc hg hgc 1
    simp only [one_mul] at this
    rw [this]; ring
  have hmix : ∫ y in Ioi 0, levyMixed f g y =
      -∫ y in Ioi 0, archLevyDensity y * crossCorr f g y := by
    rw [← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun y hy => h.levyMixed_eq hf.continuous hy
  have hpr := primeSum_add_of_ordered h hf.continuous hfc hg.continuous hgc
  have hC := coshHalfMoment_add hf.continuous hfc hg.continuous hgc
  have hS := sinhHalfMoment_add hf.continuous hfc hg.continuous hgc
  have hpole := cosh_mul_sub_sinh_mul_eq hf.continuous hfc hg.continuous hgc
  have hcosh : ∫ x, crossCorr f g x * Real.cosh (x / 2) =
      ∫ x in Ioi (0 : ℝ), crossCorr f g x * Real.cosh (x / 2) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    rw [h.crossCorr_eq_zero_of_nonpos hf.continuous (not_lt.mp hx), zero_mul]
  have hker := h.integral_collarKernel_mul hf hfc hg hgc
  unfold orderedCoupling
  rw [hL2, hlev, hmix, hpr, hC, hS, hker]
  linear_combination 4 * hpole + 4 * hcosh

/-! ### Transmission through the trivial divisor -/

/-- The **left moment** `∫ f(u) e^{−σu} du` of a test lying left of a cut. -/
def leftMoment (f : ℝ → ℝ) (σ : ℝ) : ℝ := ∫ u, f u * Real.exp (-(σ * u))

/-- The **right moment** `∫ g(v) e^{σv} dv` of a test lying right of a cut. -/
def rightMoment (g : ℝ → ℝ) (σ : ℝ) : ℝ := ∫ v, g v * Real.exp (σ * v)

/-- The exponent `σ = s − ½` of the trivial zero `s = −2(k + 1)`. -/
def trivialExponent (k : ℕ) : ℝ := -(2 * ((k : ℝ) + 1) + 1 / 2)

/-- Exponential moments of the cross-correlation of ordered tests live on the half-line. -/
theorem OrderedAt.setIntegral_exp_mul_crossCorr (h : OrderedAt a f g) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) (σ : ℝ) :
    ∫ x in Ioi (0 : ℝ), Real.exp (σ * x) * crossCorr f g x = leftMoment f σ * rightMoment g σ := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [h.crossCorr_eq_zero_of_nonpos hf (not_lt.mp hx), mul_zero])]
  rw [leftMoment, rightMoment, ← integral_crossCorr_mul_exp hf hfc hg hgc σ]
  congr 1; funext x; ring

/-- `Σ_k e^{σ_k x} = ω(x) − e^{−x/2}` for `x > 0`: the Lévy density without its Gamma-pole mode. -/
theorem hasSum_trivialExponent {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => Real.exp (trivialExponent k * x))
      (archLevyDensity x - Real.exp (-(1 / 2) * x)) := by
  have hs := hasSum_collarKernel hx
  have hval : Real.exp (x / 2) - collarKernel x = archLevyDensity x - Real.exp (-(1 / 2) * x) := by
    rw [← two_mul_cosh_sub_archLevyDensity hx, Real.cosh_eq,
      show -(x / 2) = -(1 / 2) * x by ring]
    ring
  rw [hval] at hs
  exact hs

/-- **Transmission theorem.** Across a cut, the archimedean place and the pole couple ordered
tests only through their moments at the trivial divisor of `ζ`:
`∫_0^∞ κ(x) c(x) dx = μ_{1}(f) ν_{1}(g) − Σ_{k ≥ 1} μ_{−2k}(f) ν_{−2k}(g)`. -/
theorem OrderedAt.integral_collarKernel_mul_eq_moments (h : OrderedAt a f g) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∫ x in Ioi (0 : ℝ), collarKernel x * crossCorr f g x =
      leftMoment f (1 / 2) * rightMoment g (1 / 2) -
        ∑' k : ℕ, leftMoment f (trivialExponent k) * rightMoment g (trivialExponent k) := by
  have hfC := hf.continuous
  have hgC := hg.continuous
  set c := crossCorr f g
  have hint : ∀ σ : ℝ, Integrable fun x => Real.exp (σ * x) * c x := fun σ =>
    (integrable_crossCorr_mul_exp hfC hfc hgC hgc σ).congr
      (Eventually.of_forall fun x => by simp only [c]; ring)
  have hω := h.integrableOn_archLevyDensity_mul_crossCorr hf hfc hg hgc
  -- the trivial-zero part of the kernel, pointwise on the half-line
  have hB : ∀ x ∈ Ioi (0 : ℝ), ∑' k : ℕ, Real.exp (trivialExponent k * x) * c x =
      archLevyDensity x * c x - Real.exp (-(1 / 2) * x) * c x := by
    intro x hx
    rw [((hasSum_trivialExponent hx).mul_right (c x)).tsum_eq]
    ring
  have hpt : ∀ x ∈ Ioi (0 : ℝ), collarKernel x * c x =
      Real.exp (1 / 2 * x) * c x - ∑' k : ℕ, Real.exp (trivialExponent k * x) * c x := by
    intro x hx
    rw [hB x hx, ← two_mul_cosh_sub_archLevyDensity hx, Real.cosh_eq,
      show x / 2 = 1 / 2 * x by ring, show -(1 / 2 * x) = -(1 / 2) * x by ring]
    ring
  have hBint : IntegrableOn (fun x => ∑' k : ℕ, Real.exp (trivialExponent k * x) * c x) (Ioi 0) :=
    (hω.sub (hint (-(1 / 2))).integrableOn).congr_fun (fun x hx => (hB x hx).symm)
      measurableSet_Ioi
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable (fun x => Real.exp (trivialExponent k * x) * c x)
      (volume.restrict (Ioi 0)) := fun k => (hint _).aestronglyMeasurable.restrict
  have hfin : ∑' k : ℕ, ∫⁻ x in Ioi (0 : ℝ), ‖Real.exp (trivialExponent k * x) * c x‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun k => (hmeas k).aemeasurable.enorm]
    refine ne_top_of_le_ne_top hω.2.ne (setLIntegral_mono' measurableSet_Ioi fun x hx => ?_)
    have hx0 : 0 < x := hx
    have hsumm : Summable fun k : ℕ => Real.exp (trivialExponent k * x) * |c x| :=
      ((hasSum_trivialExponent hx0).mul_right |c x|).summable
    have e1 : ∀ k : ℕ, ‖Real.exp (trivialExponent k * x) * c x‖ₑ =
        ENNReal.ofReal (Real.exp (trivialExponent k * x) * |c x|) := fun k => by
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    simp_rw [e1]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
      hsumm, ((hasSum_trivialExponent hx0).mul_right |c x|).tsum_eq, Real.enorm_eq_ofReal_abs,
      abs_mul, abs_of_pos (archLevyDensity_pos hx0)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (by linarith [Real.exp_pos (-(1 / 2) * x)]) (abs_nonneg _))
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub (hint _).integrableOn hBint,
    integral_tsum hmeas hfin, h.setIntegral_exp_mul_crossCorr hfC hfc hgC hgc]
  congr 1
  exact tsum_congr fun k => h.setIntegral_exp_mul_crossCorr hfC hfc hgC hgc _

/-- **Prime-free transmission.** If no `log n` separates the tests (their cross-correlation
vanishes at every `log n`), Weil's form couples them only through their trivial-divisor moments. -/
theorem weilQuad_add_of_ordered_of_primeFree (h : OrderedAt a f g) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hfree : ∀ n : ℕ, 2 ≤ n → crossCorr f g (Real.log n) = 0) :
    weilQuad (fun u => f u + g u) = weilQuad f + weilQuad g +
      2 * (leftMoment f (1 / 2) * rightMoment g (1 / 2) -
        ∑' k : ℕ, leftMoment f (trivialExponent k) * rightMoment g (trivialExponent k)) := by
  rw [weilQuad_add_of_ordered h hf hfc hg hgc, orderedCoupling,
    h.integral_collarKernel_mul_eq_moments hf hfc hg hgc]
  have : ∑' n : ℕ, vonMangoldtAtom n * crossCorr f g (Real.log n) = 0 := by
    refine (tsum_congr fun n => ?_).trans tsum_zero
    by_cases hn : 2 ≤ n
    · rw [hfree n hn, mul_zero]
    · rw [vonMangoldtAtom_eq_zero_of_lt_two (by omega), zero_mul]
  rw [this, sub_zero]

/-- Tests at total spread below `log 2` see no fold: the cross-correlation vanishes at every
`log n`, `n ≥ 2`. -/
theorem crossCorr_log_eq_zero_of_spread {s t : ℝ} (hfs : ∀ u, u < a - s → f u = 0)
    (hgt : ∀ v, a + t < v → g v = 0) (h : OrderedAt a f g) (hst : s + t < Real.log 2) {n : ℕ}
    (hn : 2 ≤ n) : crossCorr f g (Real.log n) = 0 := by
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  unfold crossCorr
  have e : ∀ u, f u * g (u + Real.log n) = 0 := fun u => by
    by_cases hu : u < a - s
    · rw [hfs u hu, zero_mul]
    · by_cases hu' : a < u
      · rw [h.left u hu', zero_mul]
      · rw [hgt (u + Real.log n) (by push Not at hu hu'; linarith), mul_zero]
  simp only [e, integral_zero]

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
