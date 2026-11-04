import GaloisForLFunctions.ZeroConfigurationGeometry.ShallowPairsAreNearCollisions

/-!
# Resolution is uniform in depth

`ShallowPairsAreNearCollisions` resolves FE pairs through the pair gap `A(2δ) − A(0) ≍ δ²`, which
degenerates for shallow pairs. The degeneration is an artifact of the basis `e^{±δv}`. Writing a
pair as `p e^{δv} + q e^{−δv} = P cosh(δv) + R sinh(δv)/δ`, `P = p + q`, `R = δ(p − q)`, the Gram
block becomes uniform in `δ`.

* **The diagonal is uniform** (`diag_cosh_ge`, `diag_depthSine_ge`, `diag_cross_eq_zero`). With the
  weight `cos(av)`, `a = π/(2V)`, the two profiles are orthogonal (one is even, one odd), and
  `∫ cos(av) cosh² ≥ 2/a`, `∫ cos(av) (sinh(δv)/δ)² ≥ ∫ cos(av) v² = 2V²/a − 4/a³ > 0`.
* **Off-diagonal entries decay like `1/x²`** (`norm_integral_ofReal_mul_cexp_le`,
  `norm_integral_cos_mul_mul_cexp_le`). Two integrations by parts against `e^{ixv}` give the bound
  `B/x²`, the boundary terms of the first vanishing since `cos(aV) = 0`.

The shallow-pair alternative therefore disappears from the near-collision constraint
(`eq_of_weil_eq_of_heightSeparated`, `exists_near_pair_of_mimic`): two different tempered
configurations with one image at aperture `a > V/2` contain two points of different FE orbits at
height distance `< g`, or a point deeper than `s`, as soon as `2π² B(V, s) < 3 D(V) g²`. The scale
`g` depends on the aperture and the depth budget, not on how shallow the pairs are.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open SquareRootThreshold Zeta23 _root_.RHTower

/-! ### The two profiles of a pair -/

/-- The antialigned profile `sinh(δv)/δ` of an FE pair, equal to `v` at `δ = 0`. -/
def depthSine (δ v : ℝ) : ℝ := if δ = 0 then v else Real.sinh (δ * v) / δ

theorem hasDerivAt_cosh_mul (δ v : ℝ) :
    HasDerivAt (fun v => Real.cosh (δ * v)) (δ * Real.sinh (δ * v)) v := by
  exact (((hasDerivAt_id' v).const_mul δ).cosh).congr_deriv (by ring)

theorem hasDerivAt_mul_sinh_mul (δ v : ℝ) :
    HasDerivAt (fun v => δ * Real.sinh (δ * v)) (δ ^ 2 * Real.cosh (δ * v)) v := by
  exact ((((hasDerivAt_id' v).const_mul δ).sinh).const_mul δ).congr_deriv (by ring)

theorem hasDerivAt_depthSine (δ v : ℝ) : HasDerivAt (depthSine δ) (Real.cosh (δ * v)) v := by
  by_cases h : δ = 0
  · subst h
    have e : depthSine 0 = fun v => v := funext fun v => by simp [depthSine]
    rw [e]
    simpa using hasDerivAt_id' v
  · have e : depthSine δ = fun v => Real.sinh (δ * v) / δ :=
      funext fun v => by simp [depthSine, h]
    rw [e]
    exact ((((hasDerivAt_id' v).const_mul δ).sinh).div_const δ).congr_deriv (by field_simp)

theorem depthSine_neg (δ v : ℝ) : depthSine δ (-v) = -depthSine δ v := by
  by_cases h : δ = 0
  · simp [depthSine, h]
  · simp only [depthSine, h, if_false, mul_neg, Real.sinh_neg, neg_div]

/-- `|sinh(δv)/δ| ≥ |v|`. -/
theorem sq_le_depthSine_sq (δ v : ℝ) : v ^ 2 ≤ depthSine δ v ^ 2 := by
  by_cases h : δ = 0
  · simp [depthSine, h]
  · simp only [depthSine, h, if_false, div_pow]
    rw [le_div_iff₀ (by positivity)]
    have hs : |δ * v| ≤ |Real.sinh (δ * v)| := by
      rcases le_total 0 (δ * v) with hy | hy
      · rw [abs_of_nonneg hy, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hy)]
        exact Real.self_le_sinh_iff.mpr hy
      · rw [abs_of_nonpos hy, abs_of_nonpos (Real.sinh_nonpos_iff.mpr hy)]
        have := Real.self_le_sinh_iff.mpr (neg_nonneg.mpr hy)
        rw [Real.sinh_neg] at this
        linarith
    have := pow_le_pow_left₀ (abs_nonneg _) hs 2
    rw [sq_abs, sq_abs, mul_pow] at this
    linarith

theorem abs_sinh_le_cosh (y : ℝ) : |Real.sinh y| ≤ Real.cosh y := by
  rw [abs_le]
  constructor
  · have := Real.cosh_add_sinh y
    have := Real.exp_pos y
    linarith
  · have := Real.cosh_sub_sinh y
    have := Real.exp_pos (-y)
    linarith

/-- The profile `b` of a pair of depth `δ`: `cosh(δv)` for `b = true`, `sinh(δv)/δ` otherwise. -/
def pairProfile (δ : ℝ) (b : Bool) (v : ℝ) : ℝ := if b then Real.cosh (δ * v) else depthSine δ v

/-- Its derivative. -/
def pairProfile1 (δ : ℝ) (b : Bool) (v : ℝ) : ℝ :=
  if b then δ * Real.sinh (δ * v) else Real.cosh (δ * v)

/-- Its second derivative. -/
def pairProfile2 (δ : ℝ) (b : Bool) (v : ℝ) : ℝ :=
  if b then δ ^ 2 * Real.cosh (δ * v) else δ * Real.sinh (δ * v)

theorem hasDerivAt_pairProfile (δ : ℝ) (b : Bool) (v : ℝ) :
    HasDerivAt (pairProfile δ b) (pairProfile1 δ b v) v := by
  cases b
  · have e : pairProfile δ false = depthSine δ := funext fun v => by simp [pairProfile]
    rw [e]
    simpa [pairProfile1] using hasDerivAt_depthSine δ v
  · have e : pairProfile δ true = fun v => Real.cosh (δ * v) :=
      funext fun v => by simp [pairProfile]
    rw [e]
    simpa [pairProfile1] using hasDerivAt_cosh_mul δ v

theorem hasDerivAt_pairProfile1 (δ : ℝ) (b : Bool) (v : ℝ) :
    HasDerivAt (pairProfile1 δ b) (pairProfile2 δ b v) v := by
  cases b
  · have e : pairProfile1 δ false = fun v => Real.cosh (δ * v) :=
      funext fun v => by simp [pairProfile1]
    rw [e]
    simpa [pairProfile2] using hasDerivAt_cosh_mul δ v
  · have e : pairProfile1 δ true = fun v => δ * Real.sinh (δ * v) :=
      funext fun v => by simp [pairProfile1]
    rw [e]
    simpa [pairProfile2] using hasDerivAt_mul_sinh_mul δ v

theorem continuous_pairProfile2 (δ : ℝ) (b : Bool) : Continuous (pairProfile2 δ b) := by
  cases b
  · have e : pairProfile2 δ false = fun v => δ * Real.sinh (δ * v) :=
      funext fun v => by simp [pairProfile2]
    rw [e]; fun_prop
  · have e : pairProfile2 δ true = fun v => δ ^ 2 * Real.cosh (δ * v) :=
      funext fun v => by simp [pairProfile2]
    rw [e]; fun_prop

theorem continuous_pairProfile (δ : ℝ) (b : Bool) : Continuous (pairProfile δ b) :=
  continuous_iff_continuousAt.mpr fun v => (hasDerivAt_pairProfile δ b v).continuousAt

/-- `E₀ = (1 + V) cosh(sV)` bounds both profiles on `[−V, V]`. -/
def profileBound0 (V s : ℝ) : ℝ := (1 + V) * Real.cosh (s * V)

/-- `E₁ = (1 + s) cosh(sV)` bounds their derivatives. -/
def profileBound1 (V s : ℝ) : ℝ := (1 + s) * Real.cosh (s * V)

/-- `E₂ = (s + s²) cosh(sV)` bounds their second derivatives. -/
def profileBound2 (V s : ℝ) : ℝ := (s + s ^ 2) * Real.cosh (s * V)

theorem cosh_mul_le {δ s v V : ℝ} (hδ : |δ| ≤ s) (hv : v ∈ Icc (-V) V) :
    Real.cosh (δ * v) ≤ Real.cosh (s * V) := by
  have hV : 0 ≤ V := by linarith [hv.1, hv.2]
  have hs : 0 ≤ s := (abs_nonneg δ).trans hδ
  rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hV]
  exact mul_le_mul hδ (abs_le.mpr hv) (abs_nonneg v) hs

theorem pairProfile_bounds {δ s V v : ℝ} (hδ : |δ| ≤ s) (hv : v ∈ Icc (-V) V) (b : Bool) :
    |pairProfile δ b v| ≤ profileBound0 V s ∧ |pairProfile1 δ b v| ≤ profileBound1 V s ∧
      |pairProfile2 δ b v| ≤ profileBound2 V s := by
  have hV : 0 ≤ V := by linarith [hv.1, hv.2]
  have hs : 0 ≤ s := (abs_nonneg δ).trans hδ
  have hc := cosh_mul_le hδ hv
  have hc0 : 0 < Real.cosh (s * V) := Real.cosh_pos _
  have hsh : |Real.sinh (δ * v)| ≤ Real.cosh (s * V) := (abs_sinh_le_cosh _).trans hc
  have hcabs : |Real.cosh (δ * v)| ≤ Real.cosh (s * V) := by
    rw [abs_of_pos (Real.cosh_pos _)]; exact hc
  have hδsh : |δ * Real.sinh (δ * v)| ≤ s * Real.cosh (s * V) := by
    rw [abs_mul]; exact mul_le_mul hδ hsh (abs_nonneg _) hs
  unfold profileBound0 profileBound1 profileBound2
  cases b
  · -- the antialigned profile `sinh(δv)/δ`
    have hS : |depthSine δ v| ≤ V * Real.cosh (s * V) := by
      have hmvt := (convex_Icc (-V) V).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := depthSine δ) (f' := fun v => Real.cosh (δ * v)) (C := Real.cosh (s * V))
        (fun x _ => (hasDerivAt_depthSine δ x).hasDerivWithinAt)
        (fun x (hx : x ∈ Icc (-V) V) => show ‖Real.cosh (δ * x)‖ ≤ Real.cosh (s * V) by
          rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]; exact cosh_mul_le hδ hx)
        (show (0 : ℝ) ∈ Icc (-V) V from ⟨by linarith, hV⟩) hv
      have h0 : depthSine δ 0 = 0 := by simp [depthSine]
      rw [h0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
      calc |depthSine δ v| ≤ Real.cosh (s * V) * |v| := hmvt
        _ ≤ Real.cosh (s * V) * V := mul_le_mul_of_nonneg_left (abs_le.mpr hv) hc0.le
        _ = V * Real.cosh (s * V) := by ring
    simp only [pairProfile, pairProfile1, pairProfile2, Bool.false_eq_true, if_false]
    refine ⟨by nlinarith, by nlinarith, by nlinarith [sq_nonneg s]⟩
  · simp only [pairProfile, pairProfile1, pairProfile2, if_true]
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    rw [abs_mul, abs_of_nonneg (sq_nonneg δ)]
    have hδ2 : δ ^ 2 ≤ s ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg δ) hδ 2
    nlinarith [mul_le_mul hδ2 hcabs (abs_nonneg _) (sq_nonneg s)]

/-! ### Off-diagonal decay -/

/-- **Two integrations by parts.** If `g(±V) = 0`, then
`‖∫_{−V}^{V} g(v) e^{ixv} dv‖ ≤ (|g'(V)| + |g'(−V)| + ∫|g''|)/x²`. -/
theorem norm_integral_ofReal_mul_cexp_le {g g1 g2 : ℝ → ℝ} {V x : ℝ} (hV : 0 ≤ V) (hx : x ≠ 0)
    (hg : ∀ v, HasDerivAt g (g1 v) v) (hg1 : ∀ v, HasDerivAt g1 (g2 v) v) (hg2 : Continuous g2)
    (h1 : g V = 0) (h2 : g (-V) = 0) :
    ‖∫ v in -V..V, (g v : ℂ) * cexp (I * x * v)‖ ≤
      (|g1 V| + |g1 (-V)| + ∫ v in -V..V, |g2 v|) / x ^ 2 := by
  have hIx : (I * x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hx)
  have hEc : Continuous fun v : ℝ => cexp (I * x * v) := by fun_prop
  have hFd : ∀ v : ℝ, HasDerivAt (fun v : ℝ => cexp (I * x * v) / (I * x)) (cexp (I * x * v)) v := by
    intro v
    refine ((((hasDerivAt_id' v).ofReal_comp).const_mul (I * (x : ℂ))).cexp.div_const
      (I * x)).congr_deriv ?_
    rw [Complex.ofReal_one, mul_one, mul_div_assoc, div_self hIx, mul_one]
  have hg1c : Continuous g1 := continuous_iff_continuousAt.mpr fun v => (hg1 v).continuousAt
  have I1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -V) (b := V)
    (u := fun v => (g v : ℂ)) (u' := fun v => (g1 v : ℂ))
    (fun v _ => (hg v).ofReal_comp) (fun v _ => hFd v)
    ((Complex.continuous_ofReal.comp hg1c).intervalIntegrable _ _) (hEc.intervalIntegrable _ _)
  have I2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -V) (b := V)
    (u := fun v => (g1 v : ℂ)) (u' := fun v => (g2 v : ℂ))
    (fun v _ => (hg1 v).ofReal_comp) (fun v _ => hFd v)
    ((Complex.continuous_ofReal.comp hg2).intervalIntegrable _ _) (hEc.intervalIntegrable _ _)
  have hdiv : ∀ h : ℝ → ℝ, (∫ v in -V..V, (h v : ℂ) * (cexp (I * x * v) / (I * x))) =
      (∫ v in -V..V, (h v : ℂ) * cexp (I * x * v)) / (I * x) := by
    intro h
    rw [← intervalIntegral.integral_div]
    congr 1
    funext v
    ring
  have key : (∫ v in -V..V, (g v : ℂ) * cexp (I * x * v)) =
      -(((g1 V : ℂ) * (cexp (I * x * V) / (I * x)) -
        (g1 (-V) : ℂ) * (cexp (I * x * (-V : ℝ)) / (I * x)) -
          (∫ v in -V..V, (g2 v : ℂ) * cexp (I * x * v)) / (I * x)) / (I * x)) := by
    rw [I1, h1, h2, hdiv g1, I2, hdiv g2]
    push_cast
    ring
  have hIxn : ‖(I * x : ℂ)‖ = |x| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hEn : ∀ v : ℝ, ‖cexp (I * x * v)‖ = 1 := fun v => by
    rw [show I * (x : ℂ) * (v : ℂ) = ((x * v : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hx0 : 0 < |x| := abs_pos.mpr hx
  have hA : ∀ y : ℝ, ‖(g1 y : ℂ) * (cexp (I * x * y) / (I * x))‖ = |g1 y| / |x| := fun y => by
    rw [norm_mul, norm_div, hEn, hIxn, Complex.norm_real, Real.norm_eq_abs]
    ring
  have hint : ‖∫ v in -V..V, (g2 v : ℂ) * cexp (I * x * v)‖ ≤ ∫ v in -V..V, |g2 v| := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans (le_of_eq ?_)
    congr 1
    funext v
    rw [norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hC : ‖(∫ v in -V..V, (g2 v : ℂ) * cexp (I * x * v)) / (I * x)‖ ≤
      (∫ v in -V..V, |g2 v|) / |x| := by
    rw [norm_div, hIxn]
    exact div_le_div_of_nonneg_right hint hx0.le
  rw [key, norm_neg, norm_div, hIxn]
  have hsum : ‖(g1 V : ℂ) * (cexp (I * x * V) / (I * x)) -
      (g1 (-V) : ℂ) * (cexp (I * x * (-V : ℝ)) / (I * x)) -
        (∫ v in -V..V, (g2 v : ℂ) * cexp (I * x * v)) / (I * x)‖ ≤
      |g1 V| / |x| + |g1 (-V)| / |x| + (∫ v in -V..V, |g2 v|) / |x| := by
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) hC)
    rw [hA, hA]
  calc _ ≤ (|g1 V| / |x| + |g1 (-V)| / |x| + (∫ v in -V..V, |g2 v|) / |x|) / |x| :=
        div_le_div_of_nonneg_right hsum hx0.le
    _ = (|g1 V| + |g1 (-V)| + ∫ v in -V..V, |g2 v|) / x ^ 2 := by
        rw [← sq_abs x]
        field_simp

theorem abs_mul_le_of_le {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- The off-diagonal constant `B = 2aE₀² + 2V(a²E₀² + 4aE₀E₁ + 2E₀E₂ + 2E₁²)`. -/
def offDiagConst (a V E0 E1 E2 : ℝ) : ℝ :=
  2 * a * E0 ^ 2 + 2 * V * (a ^ 2 * E0 ^ 2 + 4 * a * E0 * E1 + 2 * E0 * E2 + 2 * E1 ^ 2)

/-- **Off-diagonal entries decay like `1/x²`.** For profiles `u, w` with values, derivatives and
second derivatives bounded by `E₀, E₁, E₂` on `[−V, V]`, and `aV = π/2`,
`‖∫_{−V}^{V} cos(av) u(v) w(v) e^{ixv} dv‖ ≤ B/x²`. -/
theorem norm_integral_cos_mul_mul_cexp_le {u u1 u2 w w1 w2 : ℝ → ℝ} {a V x E0 E1 E2 : ℝ}
    (hV : 0 ≤ V) (ha : 0 ≤ a) (haV : a * V = π / 2) (hx : x ≠ 0)
    (hu : ∀ v, HasDerivAt u (u1 v) v) (hu1 : ∀ v, HasDerivAt u1 (u2 v) v) (hu2 : Continuous u2)
    (hw : ∀ v, HasDerivAt w (w1 v) v) (hw1 : ∀ v, HasDerivAt w1 (w2 v) v) (hw2 : Continuous w2)
    (bu : ∀ v ∈ Icc (-V) V, |u v| ≤ E0 ∧ |u1 v| ≤ E1 ∧ |u2 v| ≤ E2)
    (bw : ∀ v ∈ Icc (-V) V, |w v| ≤ E0 ∧ |w1 v| ≤ E1 ∧ |w2 v| ≤ E2) :
    ‖∫ v in -V..V, ((Real.cos (a * v) * (u v * w v) : ℝ) : ℂ) * cexp (I * x * v)‖ ≤
      offDiagConst a V E0 E1 E2 / x ^ 2 := by
  have hc : ∀ v, HasDerivAt (fun v => Real.cos (a * v)) (-(a * Real.sin (a * v))) v := fun v =>
    (((hasDerivAt_id' v).const_mul a).cos).congr_deriv (by ring)
  have hs : ∀ v, HasDerivAt (fun v => Real.sin (a * v)) (a * Real.cos (a * v)) v := fun v =>
    (((hasDerivAt_id' v).const_mul a).sin).congr_deriv (by ring)
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun v => (hu v).continuousAt
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun v => (hw v).continuousAt
  have hu1c : Continuous u1 := continuous_iff_continuousAt.mpr fun v => (hu1 v).continuousAt
  have hw1c : Continuous w1 := continuous_iff_continuousAt.mpr fun v => (hw1 v).continuousAt
  have hg : ∀ v, HasDerivAt (fun v => Real.cos (a * v) * (u v * w v))
      (-(a * Real.sin (a * v)) * (u v * w v) + Real.cos (a * v) * (u1 v * w v + u v * w1 v)) v :=
    fun v => (hc v).mul ((hu v).mul (hw v))
  have hg1 : ∀ v, HasDerivAt
      (fun v => -(a * Real.sin (a * v)) * (u v * w v) + Real.cos (a * v) * (u1 v * w v + u v * w1 v))
      (-(a ^ 2 * Real.cos (a * v) * (u v * w v)) -
        2 * a * Real.sin (a * v) * (u1 v * w v + u v * w1 v) +
          Real.cos (a * v) * (u2 v * w v + 2 * (u1 v * w1 v) + u v * w2 v)) v := by
    intro v
    refine ((((hs v).const_mul a).neg.mul ((hu v).mul (hw v))).add
      ((hc v).mul (((hu1 v).mul (hw v)).add ((hu v).mul (hw1 v))))).congr_deriv ?_
    simp only [Pi.mul_apply, Pi.neg_apply, Pi.add_apply]
    ring
  have hg2c : Continuous fun v => -(a ^ 2 * Real.cos (a * v) * (u v * w v)) -
      2 * a * Real.sin (a * v) * (u1 v * w v + u v * w1 v) +
        Real.cos (a * v) * (u2 v * w v + 2 * (u1 v * w1 v) + u v * w2 v) := by fun_prop
  have hcosV : Real.cos (a * V) = 0 := by rw [haV, Real.cos_pi_div_two]
  have hcosV' : Real.cos (a * -V) = 0 := by rw [mul_neg, Real.cos_neg, hcosV]
  have hsinV : Real.sin (a * V) = 1 := by rw [haV, Real.sin_pi_div_two]
  have hsinV' : Real.sin (a * -V) = -1 := by rw [mul_neg, Real.sin_neg, hsinV]
  have hIBP := norm_integral_ofReal_mul_cexp_le hV hx hg hg1 hg2c
    (by simp only [hcosV, zero_mul]) (by simp only [hcosV', zero_mul])
  refine hIBP.trans (div_le_div_of_nonneg_right ?_ (sq_nonneg x))
  have hVmem : V ∈ Icc (-V) V := ⟨by linarith, le_rfl⟩
  have hVmem' : -V ∈ Icc (-V) V := ⟨le_rfl, by linarith⟩
  have hE0 : 0 ≤ E0 := (abs_nonneg _).trans (bu V hVmem).1
  have hb1 : |-(a * Real.sin (a * V)) * (u V * w V) + Real.cos (a * V) * (u1 V * w V + u V * w1 V)|
      ≤ a * E0 ^ 2 := by
    rw [hsinV, hcosV, zero_mul, add_zero, mul_one, sq]
    rw [abs_mul, abs_neg, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (abs_mul_le_of_le (bu V hVmem).1 (bw V hVmem).1) ha
  have hb1' : |-(a * Real.sin (a * -V)) * (u (-V) * w (-V)) +
      Real.cos (a * -V) * (u1 (-V) * w (-V) + u (-V) * w1 (-V))| ≤ a * E0 ^ 2 := by
    rw [hsinV', hcosV', zero_mul, add_zero, mul_neg_one, neg_neg, sq]
    rw [abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (abs_mul_le_of_le (bu _ hVmem').1 (bw _ hVmem').1) ha
  set K := a ^ 2 * E0 ^ 2 + 4 * a * E0 * E1 + 2 * E0 * E2 + 2 * E1 ^ 2 with hK
  have hpt : ∀ v ∈ Icc (-V) V, |-(a ^ 2 * Real.cos (a * v) * (u v * w v)) -
      2 * a * Real.sin (a * v) * (u1 v * w v + u v * w1 v) +
        Real.cos (a * v) * (u2 v * w v + 2 * (u1 v * w1 v) + u v * w2 v)| ≤ K := by
    intro v hv
    obtain ⟨u0, u1b, u2b⟩ := bu v hv
    obtain ⟨w0, w1b, w2b⟩ := bw v hv
    have hca : |a ^ 2 * Real.cos (a * v)| ≤ a ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
      exact mul_le_of_le_one_right (sq_nonneg a) (Real.abs_cos_le_one _)
    have hsa : |2 * a * Real.sin (a * v)| ≤ 2 * a := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a)]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
    have hP0 : |u v * w v| ≤ E0 * E0 := abs_mul_le_of_le u0 w0
    have hP1 : |u1 v * w v + u v * w1 v| ≤ E1 * E0 + E0 * E1 :=
      (abs_add_le _ _).trans (add_le_add (abs_mul_le_of_le u1b w0) (abs_mul_le_of_le u0 w1b))
    have hP2 : |u2 v * w v + 2 * (u1 v * w1 v) + u v * w2 v| ≤ E2 * E0 + 2 * (E1 * E1) + E0 * E2 := by
      have h11 : |2 * (u1 v * w1 v)| ≤ 2 * (E1 * E1) := by
        rw [abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left (abs_mul_le_of_le u1b w1b) (by norm_num)
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_mul_le_of_le u2b w0) h11)) (abs_mul_le_of_le u0 w2b))
    have hA := abs_mul_le_of_le hca hP0
    have hB := abs_mul_le_of_le hsa hP1
    have hC := abs_mul_le_of_le (Real.abs_cos_le_one (a * v)) hP2
    set A := a ^ 2 * Real.cos (a * v) * (u v * w v)
    set B := 2 * a * Real.sin (a * v) * (u1 v * w v + u v * w1 v)
    set C := Real.cos (a * v) * (u2 v * w v + 2 * (u1 v * w1 v) + u v * w2 v)
    have : |-A - B + C| ≤ |A| + |B| + |C| := by
      rw [abs_le]
      constructor <;> linarith [le_abs_self A, neg_abs_le A, le_abs_self B, neg_abs_le B,
        le_abs_self C, neg_abs_le C]
    nlinarith [this, hA, hB, hC]
  have hint : (∫ v in -V..V, |-(a ^ 2 * Real.cos (a * v) * (u v * w v)) -
      2 * a * Real.sin (a * v) * (u1 v * w v + u v * w1 v) +
        Real.cos (a * v) * (u2 v * w v + 2 * (u1 v * w1 v) + u v * w2 v)|) ≤ 2 * V * K := by
    calc _ ≤ ∫ _v in -V..V, K := intervalIntegral.integral_mono_on (by linarith)
          (hg2c.abs.intervalIntegrable _ _) intervalIntegrable_const hpt
      _ = 2 * V * K := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  unfold offDiagConst
  rw [← hK]
  linarith

/-! ### The diagonal -/

theorem cos_mul_nonneg {a V v : ℝ} (ha : 0 ≤ a) (haV : a * V = π / 2) (hv : v ∈ Icc (-V) V) :
    0 ≤ Real.cos (a * v) := by
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> nlinarith [hv.1, hv.2]

/-- `∫_{−V}^{V} cos(av) dv = 2/a`. -/
theorem integral_cos_mul_eq {a V : ℝ} (ha : 0 < a) (haV : a * V = π / 2) :
    ∫ v in -V..V, Real.cos (a * v) = 2 / a := by
  have h : ∀ v ∈ uIcc (-V) V, HasDerivAt (fun v => Real.sin (a * v) / a) (Real.cos (a * v)) v :=
    fun v _ => ((((hasDerivAt_id' v).const_mul a).sin).div_const a).congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((by fun_prop : Continuous fun v => Real.cos (a * v)).intervalIntegrable _ _)]
  rw [mul_neg, haV, Real.sin_neg, Real.sin_pi_div_two]
  ring

/-- `∫_{−V}^{V} cos(av) v² dv = 2V²/a − 4/a³`. -/
theorem integral_cos_mul_sq_eq {a V : ℝ} (ha : 0 < a) (haV : a * V = π / 2) :
    ∫ v in -V..V, Real.cos (a * v) * v ^ 2 = 2 * V ^ 2 / a - 4 / a ^ 3 := by
  have hc : ∀ v, HasDerivAt (fun v => Real.cos (a * v)) (-(a * Real.sin (a * v))) v := fun v =>
    (((hasDerivAt_id' v).const_mul a).cos).congr_deriv (by ring)
  have hs : ∀ v, HasDerivAt (fun v => Real.sin (a * v)) (a * Real.cos (a * v)) v := fun v =>
    (((hasDerivAt_id' v).const_mul a).sin).congr_deriv (by ring)
  have h : ∀ v ∈ uIcc (-V) V, HasDerivAt
      (fun v => v ^ 2 * Real.sin (a * v) / a + 2 * v * Real.cos (a * v) / a ^ 2 -
        2 * Real.sin (a * v) / a ^ 3) (Real.cos (a * v) * v ^ 2) v := by
    intro v _
    refine (((((hasDerivAt_pow 2 v).mul (hs v)).div_const a).add
      ((((hasDerivAt_id' v).const_mul 2).mul (hc v)).div_const (a ^ 2))).sub
      (((hs v).const_mul 2).div_const (a ^ 3))).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((by fun_prop : Continuous fun v => Real.cos (a * v) * v ^ 2).intervalIntegrable _ _)]
  rw [mul_neg, haV, Real.sin_neg, Real.cos_neg, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

/-- The aligned profile: `∫ cos(av) cosh²(δv) ≥ 2/a`. -/
theorem diag_cosh_ge {a V δ : ℝ} (ha : 0 < a) (haV : a * V = π / 2) :
    2 / a ≤ ∫ v in -V..V, Real.cos (a * v) * (Real.cosh (δ * v) * Real.cosh (δ * v)) := by
  have hV : 0 ≤ V := by
    by_contra h; push Not at h; nlinarith [Real.pi_pos]
  rw [← integral_cos_mul_eq ha haV]
  refine intervalIntegral.integral_mono_on (by linarith)
    ((by fun_prop : Continuous fun v => Real.cos (a * v)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun v =>
      Real.cos (a * v) * (Real.cosh (δ * v) * Real.cosh (δ * v))).intervalIntegrable _ _)
    fun v hv => ?_
  have h1 : 1 ≤ Real.cosh (δ * v) * Real.cosh (δ * v) := by
    nlinarith [Real.one_le_cosh (δ * v)]
  have h0 := cos_mul_nonneg ha.le haV hv
  nlinarith

/-- The antialigned profile: `∫ cos(av) (sinh(δv)/δ)² ≥ 2V²/a − 4/a³`. -/
theorem diag_depthSine_ge {a V δ : ℝ} (ha : 0 < a) (haV : a * V = π / 2) :
    2 * V ^ 2 / a - 4 / a ^ 3 ≤ ∫ v in -V..V, Real.cos (a * v) * (depthSine δ v * depthSine δ v) := by
  have hV : 0 ≤ V := by
    by_contra h; push Not at h; nlinarith [Real.pi_pos]
  rw [← integral_cos_mul_sq_eq ha haV]
  have hc : Continuous (depthSine δ) :=
    continuous_iff_continuousAt.mpr fun v => (hasDerivAt_depthSine δ v).continuousAt
  refine intervalIntegral.integral_mono_on (by linarith)
    ((by fun_prop : Continuous fun v => Real.cos (a * v) * v ^ 2).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun v =>
      Real.cos (a * v) * (depthSine δ v * depthSine δ v)).intervalIntegrable _ _)
    fun v hv => ?_
  have h1 := sq_le_depthSine_sq δ v
  have h0 := cos_mul_nonneg ha.le haV hv
  rw [← sq]
  exact mul_le_mul_of_nonneg_left h1 h0

/-- The two profiles are orthogonal for the weight `cos(av)`: the product is odd. -/
theorem diag_cross_eq_zero (a V δ : ℝ) :
    ∫ v in -V..V, Real.cos (a * v) * (Real.cosh (δ * v) * depthSine δ v) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -V) (b := V)
    (fun v => Real.cos (a * v) * (Real.cosh (δ * v) * depthSine δ v))
  simp only [neg_neg, mul_neg, Real.cos_neg, Real.cosh_neg, depthSine_neg] at h
  rw [intervalIntegral.integral_neg] at h
  linarith

/-! ### The depth-uniform block inequality -/

/-- Expansion of the weighted mean square of a sum of profiled exponentials. -/
theorem integral_cos_mul_normSq_profileSum {J : Type*} [Fintype J] (γ : J → ℝ) (u : J → ℝ → ℝ)
    (hu : ∀ j, Continuous (u j)) (c : J → ℂ) (a V : ℝ) :
    ∫ v in -V..V, Real.cos (a * v) * ‖∑ j, c j * (cexp (I * γ j * v) * (u j v : ℂ))‖ ^ 2 =
      (∑ j, ∑ l, c j * conj (c l) *
        ∫ v in -V..V, ((Real.cos (a * v) * (u j v * u l v) : ℝ) : ℂ) *
          cexp (I * ((γ j - γ l : ℝ) : ℂ) * v)).re := by
  set G : ℝ → ℂ := fun v => ∑ j, ∑ l, c j * conj (c l) *
    (((Real.cos (a * v) * (u j v * u l v) : ℝ) : ℂ) * cexp (I * ((γ j - γ l : ℝ) : ℂ) * v))
    with hG
  have hpt : ∀ v : ℝ, Real.cos (a * v) * ‖∑ j, c j * (cexp (I * γ j * v) * (u j v : ℂ))‖ ^ 2 =
      (G v).re := by
    intro v
    have hn : ‖∑ j, c j * (cexp (I * γ j * v) * (u j v : ℂ))‖ ^ 2 =
        ((∑ j, c j * (cexp (I * γ j * v) * (u j v : ℂ))) *
          conj (∑ j, c j * (cexp (I * γ j * v) * (u j v : ℂ)))).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hn, ← Complex.re_ofReal_mul, hG, map_sum, Finset.sum_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul, ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal]
    rw [show cexp (I * ((γ j - γ l : ℝ) : ℂ) * v) = cexp (I * γ j * v) * cexp (-I * γ l * v) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    push_cast
    ring
  have hcont : Continuous G := by
    rw [hG]
    have := hu
    fun_prop
  rw [intervalIntegral.integral_congr (fun v _ => hpt v),
    show (∫ v in -V..V, (G v).re) = (∫ v in -V..V, G v).re from
      intervalIntegral.intervalIntegral_re (hcont.intervalIntegrable _ _), hG]
  congr 1
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    (by have := hu; fun_prop : Continuous fun v : ℝ => ∑ l, c j * conj (c l) *
      (((Real.cos (a * v) * (u j v * u l v) : ℝ) : ℂ) *
        cexp (I * ((γ j - γ l : ℝ) : ℂ) * v))).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum fun l _ =>
    (by have := hu; fun_prop : Continuous fun v : ℝ => c j * conj (c l) *
      (((Real.cos (a * v) * (u j v * u l v) : ℝ) : ℂ) *
        cexp (I * ((γ j - γ l : ℝ) : ℂ) * v))).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_const_mul]

/-- The diagonal constant `D(V) = min(2/a, 2V²/a − 4/a³)`, `a = π/(2V)`. -/
def uniformDiag (V : ℝ) : ℝ := min (2 / inghamA V) (2 * V ^ 2 / inghamA V - 4 / inghamA V ^ 3)

/-- The off-diagonal constant `B(V, s)` of the profiles of depth `≤ s`. -/
def uniformB (V s : ℝ) : ℝ :=
  offDiagConst (inghamA V) V (profileBound0 V s) (profileBound1 V s) (profileBound2 V s)

theorem inghamA_mul {V : ℝ} (hV : 0 < V) : inghamA V * V = π / 2 := by
  unfold inghamA; field_simp

theorem uniformDiag_pos {V : ℝ} (hV : 0 < V) : 0 < uniformDiag V := by
  have ha : 0 < inghamA V := by unfold inghamA; positivity
  have haV := inghamA_mul hV
  refine lt_min (by positivity) ?_
  -- `2V²/a − 4/a³ = (4V³/π)(1 − 8/π²)`
  have hpi : (8 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hV' : V = π / 2 / inghamA V := by field_simp; linarith
  rw [sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
  have : (4 : ℝ) * inghamA V < 2 * V ^ 2 * inghamA V ^ 3 := by
    have e : 2 * V ^ 2 * inghamA V ^ 3 = (π ^ 2 / 2) * inghamA V := by
      rw [show 2 * V ^ 2 * inghamA V ^ 3 = 2 * (inghamA V * V) ^ 2 * inghamA V by ring, haV]
      ring
    rw [e]
    nlinarith
  linarith

theorem uniformB_nonneg {V s : ℝ} (hV : 0 < V) (hs : 0 ≤ s) : 0 ≤ uniformB V s := by
  have ha : 0 < inghamA V := by unfold inghamA; positivity
  have h0 := Real.cosh_pos (s * V)
  unfold uniformB offDiagConst profileBound0 profileBound1 profileBound2
  positivity

/-- **The depth-uniform block inequality.** For `g`-separated heights `γ_k`, depths `|δ_k| ≤ s`
and coefficients `P_k, R_k`,
`(D − 2π²B/(3g²)) Σ_k (|P_k|² + |R_k|²) ≤ ∫_{−V}^{V} |Σ_k e^{iγ_k v}(P_k cosh(δ_k v) + R_k sinh(δ_k v)/δ_k)|²`,
with `D = D(V)` and `B = B(V, s)` independent of the depths. -/
theorem uniform_block_inequality {ι : Type*} [Fintype ι] [DecidableEq ι] (γ δ : ι → ℝ)
    (P R : ι → ℂ) {g V s : ℝ} (hg : 0 < g) (hV : 0 < V) (hs : 0 ≤ s) (hδ : ∀ k, |δ k| ≤ s)
    (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) :
    (uniformDiag V - 2 * (π ^ 2 / 3 * uniformB V s / g ^ 2)) * ∑ k, (‖P k‖ ^ 2 + ‖R k‖ ^ 2) ≤
      ∫ v in -V..V, ‖∑ k, cexp (I * γ k * v) *
        (P k * Real.cosh (δ k * v) + R k * depthSine (δ k) v)‖ ^ 2 := by
  classical
  set a := inghamA V with ha_def
  have ha : 0 < a := by rw [ha_def]; unfold inghamA; positivity
  have haV : a * V = π / 2 := inghamA_mul hV
  set B := uniformB V s with hB
  have hB0 : 0 ≤ B := uniformB_nonneg hV hs
  set D := uniformDiag V with hD
  set Rr := π ^ 2 / 3 * B / g ^ 2 with hRr
  have hRr0 : 0 ≤ Rr := by positivity
  -- the sum over profiles
  set c' : ι × Bool → ℂ := fun x => if x.2 then P x.1 else R x.1 with hc'
  set γ' : ι × Bool → ℝ := fun x => γ x.1 with hγ'
  set u : ι × Bool → ℝ → ℝ := fun x => pairProfile (δ x.1) x.2 with hu
  have huc : ∀ x, Continuous (u x) := fun x => continuous_pairProfile _ _
  have hF : ∀ v : ℝ, (∑ k, cexp (I * γ k * v) *
      (P k * Real.cosh (δ k * v) + R k * depthSine (δ k) v)) =
        ∑ x, c' x * (cexp (I * γ' x * v) * (u x v : ℂ)) := by
    intro v
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_bool]
    simp only [hc', hγ', hu, pairProfile, if_true, Bool.false_eq_true, if_false]
    ring
  set f : ℝ → ℂ := fun v => ∑ x, c' x * (cexp (I * γ' x * v) * (u x v : ℂ)) with hf
  have hfc : Continuous fun v => ‖f v‖ ^ 2 := by
    rw [hf]
    have := huc
    fun_prop
  have h1 : ∫ v in -V..V, Real.cos (a * v) * ‖f v‖ ^ 2 ≤ ∫ v in -V..V, ‖f v‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith)
      ((show Continuous fun v : ℝ => Real.cos (a * v) * ‖f v‖ ^ 2 from
        (by fun_prop : Continuous fun v : ℝ => Real.cos (a * v)).mul hfc).intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _) fun v _ =>
        mul_le_of_le_one_left (by positivity) (Real.cos_le_one _)
  have hQ := integral_cos_mul_normSq_profileSum γ' u huc c' a V
  have hint : (∫ v in -V..V, ‖∑ k, cexp (I * γ k * v) *
      (P k * Real.cosh (δ k * v) + R k * depthSine (δ k) v)‖ ^ 2) = ∫ v in -V..V, ‖f v‖ ^ 2 := by
    congr 1 with v
    rw [hF v]
  rw [hint]
  refine le_trans ?_ (hQ ▸ h1)
  -- blocks
  set J : ι × Bool → ι × Bool → ℂ := fun x y =>
    ∫ v in -V..V, ((Real.cos (a * v) * (u x v * u y v) : ℝ) : ℂ) *
      cexp (I * ((γ' x - γ' y : ℝ) : ℂ) * v) with hJ
  set blk : ι → ι → ℂ := fun k l => ∑ b : Bool, ∑ b' : Bool,
    c' (k, b) * conj (c' (l, b')) * J (k, b) (l, b') with hblk
  have hsplit : (∑ x, ∑ y, c' x * conj (c' y) * J x y) = ∑ k, ∑ l, blk k l := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fintype.sum_prod_type, hblk]
    rw [Finset.sum_comm]
  rw [show (∑ x, ∑ y, c' x * conj (c' y) *
      ∫ v in -V..V, ((Real.cos (a * v) * (u x v * u y v) : ℝ) : ℂ) *
        cexp (I * ((γ' x - γ' y : ℝ) : ℂ) * v)) = ∑ x, ∑ y, c' x * conj (c' y) * J x y from rfl,
    hsplit, Complex.re_sum]
  set w : ι → ℝ := fun k => ‖P k‖ + ‖R k‖ with hw
  set S : ι → ℝ := fun k => ‖P k‖ ^ 2 + ‖R k‖ ^ 2 with hS
  -- the diagonal block
  have hdiag : ∀ k, D * S k ≤ (blk k k).re := by
    intro k
    have hJd : ∀ b b' : Bool, J (k, b) (k, b') =
        ((∫ v in -V..V, Real.cos (a * v) * (pairProfile (δ k) b v * pairProfile (δ k) b' v) : ℝ) : ℂ) := by
      intro b b'
      simp only [hJ, hγ', hu, sub_self, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
        mul_one]
      exact intervalIntegral.integral_ofReal
    have hTT := diag_cosh_ge (δ := δ k) ha haV
    have hFF := diag_depthSine_ge (δ := δ k) ha haV
    have hTF := diag_cross_eq_zero a V (δ k)
    have hFT : ∫ v in -V..V, Real.cos (a * v) * (depthSine (δ k) v * Real.cosh (δ k * v)) = 0 := by
      rw [← hTF]; congr 1 with v; ring
    have hblkk : blk k k = ((‖P k‖ ^ 2 * ∫ v in -V..V, Real.cos (a * v) *
        (Real.cosh (δ k * v) * Real.cosh (δ k * v)) : ℝ) : ℂ) +
        ((‖R k‖ ^ 2 * ∫ v in -V..V, Real.cos (a * v) * (depthSine (δ k) v * depthSine (δ k) v) : ℝ) : ℂ) := by
      simp only [hblk, Fintype.sum_bool, hJd]
      simp only [hc', pairProfile, if_true, Bool.false_eq_true, if_false, hTF, hFT,
        Complex.ofReal_zero, mul_zero, add_zero, zero_add]
      rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hblkk, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
    have hD1 : D ≤ 2 / a := min_le_left _ _
    have hD2 : D ≤ 2 * V ^ 2 / a - 4 / a ^ 3 := min_le_right _ _
    have hP2 := sq_nonneg ‖P k‖
    have hR2 := sq_nonneg ‖R k‖
    simp only [hS]
    nlinarith [mul_le_mul_of_nonneg_left (hD1.trans hTT) hP2,
      mul_le_mul_of_nonneg_left (hD2.trans hFF) hR2]
  -- the off-diagonal blocks
  have hoff : ∀ k l, k ≠ l → ‖blk k l‖ ≤ w k * w l * (B / |γ k - γ l| ^ 2) := by
    intro k l hkl
    have hx : γ k - γ l ≠ 0 := by
      intro h0
      have := hsep k l hkl
      rw [h0, abs_zero] at this
      linarith
    have hJo : ∀ b b' : Bool, ‖J (k, b) (l, b')‖ ≤ B / |γ k - γ l| ^ 2 := by
      intro b b'
      rw [sq_abs]
      exact norm_integral_cos_mul_mul_cexp_le hV.le ha.le haV hx
        (hasDerivAt_pairProfile _ _) (hasDerivAt_pairProfile1 _ _) (continuous_pairProfile2 _ _)
        (hasDerivAt_pairProfile _ _) (hasDerivAt_pairProfile1 _ _) (continuous_pairProfile2 _ _)
        (fun v hv => pairProfile_bounds (hδ k) hv b) (fun v hv => pairProfile_bounds (hδ l) hv b')
    have hψ0 : 0 ≤ B / |γ k - γ l| ^ 2 := by positivity
    calc ‖blk k l‖ ≤ ∑ b : Bool, ∑ b' : Bool, ‖c' (k, b)‖ * ‖c' (l, b')‖ * (B / |γ k - γ l| ^ 2) := by
          simp only [hblk]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left (hJo b b') (by positivity)
      _ = w k * w l * (B / |γ k - γ l| ^ 2) := by
          simp only [Fintype.sum_bool, hc', if_true, Bool.false_eq_true, if_false, hw]
          ring
  -- the row sums
  have hrow : ∀ k, ∑ l ∈ Finset.univ.filter (· ≠ k), B / |γ k - γ l| ^ 2 ≤ Rr := by
    intro k
    have hbasel := _root_.RHTower.hasSum_inv_add_one_sq
    have hψn : ∀ n : ℕ, B / (((n : ℝ) + 1) * g) ^ 2 = B / g ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ := by
      intro n
      rw [mul_pow]
      field_simp
    have hψs : Summable fun n : ℕ => B / (((n : ℝ) + 1) * g) ^ 2 := by
      rw [show (fun n : ℕ => B / (((n : ℝ) + 1) * g) ^ 2) =
        fun n : ℕ => B / g ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ from funext hψn]
      exact hbasel.summable.mul_left _
    have h := sum_offDiag_le_two_tsum γ hg hsep (ψ := fun x => B / x ^ 2)
      (fun x hx => by positivity)
      (fun x y hx hxy => div_le_div_of_nonneg_left hB0 (pow_pos (by linarith) 2)
        (pow_le_pow_left₀ (by linarith) hxy 2)) hψs k
    refine h.trans (le_of_eq ?_)
    rw [tsum_congr hψn, tsum_mul_left, hbasel.tsum_eq, hRr]
    ring
  -- assemble
  have hrowk : ∀ k, D * S k - ∑ l ∈ Finset.univ.filter (· ≠ k),
      w k * w l * (B / |γ k - γ l| ^ 2) ≤ (∑ l, blk k l).re := by
    intro k
    rw [Finset.filter_ne', ← Finset.add_sum_erase _ _ (Finset.mem_univ k), Complex.add_re,
      Complex.re_sum (Finset.univ.erase k) (blk k)]
    have hlow : ∀ l ∈ Finset.univ.erase k, -(w k * w l * (B / |γ k - γ l| ^ 2)) ≤
        (blk k l).re := fun l hl => by
      have hne : k ≠ l := (Finset.ne_of_mem_erase hl).symm
      have h := (abs_le.mp (Complex.abs_re_le_norm (blk k l))).1
      linarith [hoff k l hne]
    have := Finset.sum_le_sum hlow
    rw [Finset.sum_neg_distrib] at this
    linarith [hdiag k]
  have hschur := schur_offDiag_le w (fun k l => B / |γ k - γ l| ^ 2)
    (fun k l _ => by positivity) (fun k l => by simp only [abs_sub_comm]) hrow
  have hw2 : ∑ k, w k ^ 2 ≤ 2 * ∑ k, S k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by
      simp only [hw, hS]; nlinarith [sq_nonneg (‖P k‖ - ‖R k‖)]
  have hsumk := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hrowk k
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsumk
  have := mul_le_mul_of_nonneg_left hw2 hRr0
  nlinarith

end GaloisForLFunctions.ZeroConfigurationGeometry
