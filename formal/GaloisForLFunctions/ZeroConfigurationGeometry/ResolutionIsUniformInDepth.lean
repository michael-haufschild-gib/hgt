import GaloisForLFunctions.ZeroConfigurationGeometry.ShallowPairsAreNearCollisions

/-!
# Resolution is uniform in depth

`ShallowPairsAreNearCollisions` resolves FE pairs through the pair gap `A(2δ) − A(0) ≍ δ²`, which
degenerates for shallow pairs. The degeneration is an artifact of the basis `e^{±δv}`. On `[−V, V]`
write a pair as `p e^{δv} + q e^{−δv} = P cosh(δv) + R sinh(δv)/(δV)`, with `P = p + q` and
`R = Vδ(p − q)`. In this basis the Gram block is uniform in `δ`.

* **The diagonal is uniform** (`diag_cosh_ge`, `diag_depthSine_ge`, `diag_cross_eq_zero`). For the
  weight `cos(av)`, `a = π/(2V)`, the two profiles are orthogonal (one even, one odd), and
  `∫ cos(av) cosh² ≥ 2/a` and `∫ cos(av) (sinh(δv)/δ)² ≥ ∫ cos(av) v² = 2V²/a − 4/a³`. So the
  diagonal is at least `D(V) = (4V/π)(1 − 8/π²) > 0`.
* **Off-diagonal entries decay like `1/x²`** (`norm_integral_ofReal_mul_cexp_le`,
  `norm_integral_cos_mul_mul_cexp_le`). Two integrations by parts against `e^{ixv}` give `B/x²`.
  The first boundary term vanishes since `cos(aV) = 0`. With the normalized profiles,
  `B(V, s) = O(1/V)` for `s ≤ 1/V`.
* **The block inequality** (`uniform_block_inequality`). For `g`-separated heights,
  `(D − 2π²B/(3g²)) Σ (|P_k|² + |R_k|²) ≤ ∫_{−V}^{V} |Σ_k e^{iγ_k v}(P_k cosh + R_k sinh/(δV))|²`.

The shallow-pair alternative therefore disappears from the near-collision constraint
(`eq_of_weil_eq_of_heightSeparated`, `exists_near_pair_of_mimic`). Two different tempered
configurations with one image at aperture `a > V/2` contain two points of different FE orbits at
height distance `< g`, or a point deeper than `s`, as soon as `D(V) > 2π²B(V, s)/(3g²)`. For
`s ≤ 1/V` this holds at every `g ≥ 90/V` (`exists_near_pair_of_mimic_of_le`): the resolution scale
has the Nyquist order of the aperture and does not depend on how shallow the pairs are.
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

/-- The profile `b` of a pair of depth `δ` on `[−V, V]`: `cosh(δv)` for `b = true`, and the
normalized antialigned profile `sinh(δv)/(δV)` otherwise. -/
def pairProfile (V δ : ℝ) (b : Bool) (v : ℝ) : ℝ :=
  if b then Real.cosh (δ * v) else depthSine δ v / V

/-- Its derivative. -/
def pairProfile1 (V δ : ℝ) (b : Bool) (v : ℝ) : ℝ :=
  if b then δ * Real.sinh (δ * v) else Real.cosh (δ * v) / V

/-- Its second derivative. -/
def pairProfile2 (V δ : ℝ) (b : Bool) (v : ℝ) : ℝ :=
  if b then δ ^ 2 * Real.cosh (δ * v) else δ * Real.sinh (δ * v) / V

theorem hasDerivAt_pairProfile (V δ : ℝ) (b : Bool) (v : ℝ) :
    HasDerivAt (pairProfile V δ b) (pairProfile1 V δ b v) v := by
  cases b
  · have e : pairProfile V δ false = fun v => depthSine δ v / V :=
      funext fun v => by simp [pairProfile]
    rw [e]
    simpa [pairProfile1] using (hasDerivAt_depthSine δ v).div_const V
  · have e : pairProfile V δ true = fun v => Real.cosh (δ * v) :=
      funext fun v => by simp [pairProfile]
    rw [e]
    simpa [pairProfile1] using hasDerivAt_cosh_mul δ v

theorem hasDerivAt_pairProfile1 (V δ : ℝ) (b : Bool) (v : ℝ) :
    HasDerivAt (pairProfile1 V δ b) (pairProfile2 V δ b v) v := by
  cases b
  · have e : pairProfile1 V δ false = fun v => Real.cosh (δ * v) / V :=
      funext fun v => by simp [pairProfile1]
    rw [e]
    simpa [pairProfile2] using (hasDerivAt_cosh_mul δ v).div_const V
  · have e : pairProfile1 V δ true = fun v => δ * Real.sinh (δ * v) :=
      funext fun v => by simp [pairProfile1]
    rw [e]
    simpa [pairProfile2] using hasDerivAt_mul_sinh_mul δ v

theorem continuous_pairProfile2 (V δ : ℝ) (b : Bool) : Continuous (pairProfile2 V δ b) := by
  cases b
  · have e : pairProfile2 V δ false = fun v => δ * Real.sinh (δ * v) / V :=
      funext fun v => by simp [pairProfile2]
    rw [e]; fun_prop
  · have e : pairProfile2 V δ true = fun v => δ ^ 2 * Real.cosh (δ * v) :=
      funext fun v => by simp [pairProfile2]
    rw [e]; fun_prop

theorem continuous_pairProfile (V δ : ℝ) (b : Bool) : Continuous (pairProfile V δ b) :=
  continuous_iff_continuousAt.mpr fun v => (hasDerivAt_pairProfile V δ b v).continuousAt

/-- `E₀ = cosh(sV)` bounds both profiles on `[−V, V]`. -/
def profileBound0 (V s : ℝ) : ℝ := Real.cosh (s * V)

/-- `E₁ = (s + 1/V) cosh(sV)` bounds their derivatives. -/
def profileBound1 (V s : ℝ) : ℝ := (s + 1 / V) * Real.cosh (s * V)

/-- `E₂ = (s² + s/V) cosh(sV)` bounds their second derivatives. -/
def profileBound2 (V s : ℝ) : ℝ := (s ^ 2 + s / V) * Real.cosh (s * V)

theorem cosh_mul_le {δ s v V : ℝ} (hδ : |δ| ≤ s) (hv : v ∈ Icc (-V) V) :
    Real.cosh (δ * v) ≤ Real.cosh (s * V) := by
  have hV : 0 ≤ V := by linarith [hv.1, hv.2]
  have hs : 0 ≤ s := (abs_nonneg δ).trans hδ
  rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hV]
  exact mul_le_mul hδ (abs_le.mpr hv) (abs_nonneg v) hs

/-- `|sinh(δv)/δ| ≤ V cosh(sV)` on `[−V, V]`, by the mean value theorem. -/
theorem abs_depthSine_le {δ s V v : ℝ} (hδ : |δ| ≤ s) (hv : v ∈ Icc (-V) V) :
    |depthSine δ v| ≤ V * Real.cosh (s * V) := by
  have hV : 0 ≤ V := by linarith [hv.1, hv.2]
  have hc0 : 0 < Real.cosh (s * V) := Real.cosh_pos _
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

theorem pairProfile_bounds {δ s V v : ℝ} (hV : 0 < V) (hδ : |δ| ≤ s) (hv : v ∈ Icc (-V) V)
    (b : Bool) :
    |pairProfile V δ b v| ≤ profileBound0 V s ∧ |pairProfile1 V δ b v| ≤ profileBound1 V s ∧
      |pairProfile2 V δ b v| ≤ profileBound2 V s := by
  have hs : 0 ≤ s := (abs_nonneg δ).trans hδ
  have hc := cosh_mul_le hδ hv
  have hc0 : 0 < Real.cosh (s * V) := Real.cosh_pos _
  have hsh : |Real.sinh (δ * v)| ≤ Real.cosh (s * V) := (abs_sinh_le_cosh _).trans hc
  have hcabs : |Real.cosh (δ * v)| ≤ Real.cosh (s * V) := by
    rw [abs_of_pos (Real.cosh_pos _)]; exact hc
  have hδsh : |δ * Real.sinh (δ * v)| ≤ s * Real.cosh (s * V) := by
    rw [abs_mul]; exact mul_le_mul hδ hsh (abs_nonneg _) hs
  have hV1 : 0 < 1 / V := by positivity
  unfold profileBound0 profileBound1 profileBound2
  cases b
  · simp only [pairProfile, pairProfile1, pairProfile2, Bool.false_eq_true, if_false]
    have hS := abs_depthSine_le hδ hv
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hV, div_le_iff₀ hV]; linarith
    · rw [abs_div, abs_of_pos hV, div_le_iff₀ hV]
      rw [show (s + 1 / V) * Real.cosh (s * V) * V = s * V * Real.cosh (s * V) +
        Real.cosh (s * V) by field_simp]
      nlinarith [mul_nonneg (mul_nonneg hs hV.le) hc0.le]
    · rw [abs_div, abs_of_pos hV, div_le_iff₀ hV]
      rw [show (s ^ 2 + s / V) * Real.cosh (s * V) * V = s ^ 2 * V * Real.cosh (s * V) +
        s * Real.cosh (s * V) by field_simp]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg s) hV.le) hc0.le]
  · simp only [pairProfile, pairProfile1, pairProfile2, if_true]
    refine ⟨hcabs, by nlinarith, ?_⟩
    rw [abs_mul, abs_of_nonneg (sq_nonneg δ)]
    have hδ2 : δ ^ 2 ≤ s ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg δ) hδ 2
    have hsV : 0 ≤ s / V := by positivity
    nlinarith [mul_le_mul hδ2 hcabs (abs_nonneg _) (sq_nonneg s), mul_nonneg hsV hc0.le]

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

/-- The diagonal constant `D(V) = 2/a − 4/(a³V²) = (4V/π)(1 − 8/π²)`, `a = π/(2V)`. -/
def uniformDiag (V : ℝ) : ℝ := 2 / inghamA V - 4 / (inghamA V ^ 3 * V ^ 2)

/-- The off-diagonal constant `B(V, s)` of the profiles of depth `≤ s`. -/
def uniformB (V s : ℝ) : ℝ :=
  offDiagConst (inghamA V) V (profileBound0 V s) (profileBound1 V s) (profileBound2 V s)

theorem inghamA_mul {V : ℝ} (hV : 0 < V) : inghamA V * V = π / 2 := by
  unfold inghamA; field_simp

theorem uniformDiag_pos {V : ℝ} (hV : 0 < V) : 0 < uniformDiag V := by
  have ha : 0 < inghamA V := by unfold inghamA; positivity
  have haV := inghamA_mul hV
  have hpi : (8 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three]
  unfold uniformDiag
  rw [sub_pos, div_lt_div_iff₀ (by positivity) ha]
  -- `4a < 2a³V² = (π²/2) a`
  have e : 2 * (inghamA V ^ 3 * V ^ 2) = (π ^ 2 / 2) * inghamA V := by
    rw [show 2 * (inghamA V ^ 3 * V ^ 2) = 2 * (inghamA V * V) ^ 2 * inghamA V by ring, haV]
    ring
  rw [e]
  nlinarith

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
        (P k * Real.cosh (δ k * v) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ))‖ ^ 2 := by
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
  set u : ι × Bool → ℝ → ℝ := fun x => pairProfile V (δ x.1) x.2 with hu
  have huc : ∀ x, Continuous (u x) := fun x => continuous_pairProfile _ _ _
  have hF : ∀ v : ℝ, (∑ k, cexp (I * γ k * v) *
      (P k * Real.cosh (δ k * v) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ))) =
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
      (P k * Real.cosh (δ k * v) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ))‖ ^ 2) = ∫ v in -V..V, ‖f v‖ ^ 2 := by
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
        ((∫ v in -V..V, Real.cos (a * v) * (pairProfile V (δ k) b v * pairProfile V (δ k) b' v) : ℝ) :
          ℂ) := by
      intro b b'
      simp only [hJ, hγ', hu, sub_self, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
        mul_one]
      exact intervalIntegral.integral_ofReal
    have hTT := diag_cosh_ge (δ := δ k) ha haV
    have hV0 : V ≠ 0 := hV.ne'
    have hFF : 2 / a - 4 / (a ^ 3 * V ^ 2) ≤ ∫ v in -V..V, Real.cos (a * v) *
        (depthSine (δ k) v / V * (depthSine (δ k) v / V)) := by
      have h := diag_depthSine_ge (δ := δ k) ha haV
      rw [show (fun v => Real.cos (a * v) * (depthSine (δ k) v / V * (depthSine (δ k) v / V))) =
        fun v => Real.cos (a * v) * (depthSine (δ k) v * depthSine (δ k) v) / V ^ 2 from
          funext fun v => by field_simp, intervalIntegral.integral_div, le_div_iff₀ (by positivity)]
      have e : (2 / a - 4 / (a ^ 3 * V ^ 2)) * V ^ 2 = 2 * V ^ 2 / a - 4 / a ^ 3 := by
        field_simp
      linarith
    have hTF : ∫ v in -V..V, Real.cos (a * v) * (Real.cosh (δ k * v) * (depthSine (δ k) v / V)) =
        0 := by
      rw [show (fun v => Real.cos (a * v) * (Real.cosh (δ k * v) * (depthSine (δ k) v / V))) =
        fun v => Real.cos (a * v) * (Real.cosh (δ k * v) * depthSine (δ k) v) / V from
          funext fun v => by ring, intervalIntegral.integral_div, diag_cross_eq_zero, zero_div]
    have hFT : ∫ v in -V..V, Real.cos (a * v) * (depthSine (δ k) v / V * Real.cosh (δ k * v)) =
        0 := by
      rw [← hTF]; congr 1 with v; ring
    have hblkk : blk k k = ((‖P k‖ ^ 2 * ∫ v in -V..V, Real.cos (a * v) *
        (Real.cosh (δ k * v) * Real.cosh (δ k * v)) : ℝ) : ℂ) +
        ((‖R k‖ ^ 2 * ∫ v in -V..V, Real.cos (a * v) *
          (depthSine (δ k) v / V * (depthSine (δ k) v / V)) : ℝ) : ℂ) := by
      simp only [hblk, Fintype.sum_bool, hJd]
      simp only [hc', pairProfile, if_true, Bool.false_eq_true, if_false, hTF, hFT,
        Complex.ofReal_zero, mul_zero, add_zero, zero_add]
      rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hblkk, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
    have hD1 : D ≤ 2 / a := by
      rw [hD, uniformDiag, ← ha_def]
      have : 0 ≤ 4 / (a ^ 3 * V ^ 2) := by positivity
      linarith
    have hD2 : D ≤ 2 / a - 4 / (a ^ 3 * V ^ 2) := by rw [hD, uniformDiag, ← ha_def]
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
        (hasDerivAt_pairProfile _ _ _) (hasDerivAt_pairProfile1 _ _ _) (continuous_pairProfile2 _ _ _)
        (hasDerivAt_pairProfile _ _ _) (hasDerivAt_pairProfile1 _ _ _) (continuous_pairProfile2 _ _ _)
        (fun v hv => pairProfile_bounds hV (hδ k) hv b)
        (fun v hv => pairProfile_bounds hV (hδ l) hv b')
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

/-! ### Resolution uniform in depth -/

/-- A pair in the profile basis: `p e^{δv} + q e^{−δv} = (p + q) cosh(δv) + δ(p − q) sinh(δv)/δ`. -/
theorem pair_eq_profiles (p q : ℂ) (δ v : ℝ) :
    p * cexp ((δ : ℂ) * v) + q * cexp (-(δ : ℂ) * v) =
      (p + q) * (Real.cosh (δ * v) : ℂ) + ((δ : ℂ) * (p - q)) * (depthSine δ v : ℂ) := by
  by_cases h : δ = 0
  · subst h
    simp [depthSine]
  · have hδ : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
    have hc : ((Real.cosh (δ * v) : ℝ) : ℂ) = (cexp ((δ : ℂ) * v) + cexp (-(δ : ℂ) * v)) / 2 := by
      rw [Complex.ofReal_cosh, Complex.cosh]
      push_cast
      ring_nf
    have hs : ((depthSine δ v : ℝ) : ℂ) = (cexp ((δ : ℂ) * v) - cexp (-(δ : ℂ) * v)) / 2 / δ := by
      simp only [depthSine, h, if_false]
      rw [Complex.ofReal_div, Complex.ofReal_sinh, Complex.sinh]
      push_cast
      ring_nf
    rw [hc, hs]
    field_simp
    ring

theorem profile_rescale (c : ℂ) (δ V v : ℝ) (hV : V ≠ 0) :
    ((V * δ : ℝ) : ℂ) * c * ((depthSine δ v / V : ℝ) : ℂ) = (δ : ℂ) * c * (depthSine δ v : ℂ) := by
  have hV' : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV
  push_cast
  field_simp

/-- **Vanishing profile sums.** A summable sum of profiled exponentials at `g`-separated heights,
vanishing on `[−V, V]`, has all coefficients zero once `D(V) > 2π²B(V, s)/(3g²)`. -/
theorem eq_zero_of_profileSum_eq_zero {κ : Type*} (γ δ : κ → ℝ) (P R : κ → ℂ) {g V s : ℝ}
    (hg : 0 < g) (hV : 0 < V) (hs : 0 ≤ s) (hδ : ∀ k, |δ k| ≤ s)
    (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|)
    (hpos : 0 < uniformDiag V - 2 * (π ^ 2 / 3 * uniformB V s / g ^ 2))
    (hsum : Summable fun k => ‖P k‖ + ‖R k‖)
    (hzero : ∀ v ∈ Set.Icc (-V) V, ∑' k, cexp (I * γ k * v) *
      (P k * Real.cosh (δ k * v) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ)) = 0) :
    ∀ k, P k = 0 ∧ R k = 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨k₀, hk₀⟩ := hne
  set C := uniformDiag V - 2 * (π ^ 2 / 3 * uniformB V s / g ^ 2) with hC
  set M := ‖P k₀‖ ^ 2 + ‖R k₀‖ ^ 2 with hM
  have hM0 : 0 < M := by
    by_cases hp : P k₀ = 0
    · have := norm_pos_iff.mpr (hk₀ hp)
      rw [hM]; positivity
    · have := norm_pos_iff.mpr hp
      rw [hM]; positivity
  set E := profileBound0 V s with hE
  have hE0 : 0 < E := by
    rw [hE, profileBound0]; have := Real.cosh_pos (s * V); positivity
  have hterm : ∀ k, ∀ v ∈ Set.Icc (-V) V, ‖cexp (I * γ k * v) *
      (P k * Real.cosh (δ k * v) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ))‖ ≤ E * (‖P k‖ + ‖R k‖) := by
    intro k v hv
    have hb1 := (pairProfile_bounds hV (hδ k) hv true).1
    have hb2 := (pairProfile_bounds hV (hδ k) hv false).1
    simp only [pairProfile, if_true, Bool.false_eq_true, if_false] at hb1 hb2
    have h0 : ‖cexp (I * γ k * v)‖ = 1 := by
      rw [show I * (γ k : ℂ) * (v : ℂ) = ((γ k * v : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, h0, one_mul]
    calc ‖P k * (Real.cosh (δ k * v) : ℂ) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ)‖
        ≤ ‖P k‖ * |Real.cosh (δ k * v)| + ‖R k‖ * |depthSine (δ k) v / V| := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ ‖P k‖ * E + ‖R k‖ * E := by gcongr
      _ = E * (‖P k‖ + ‖R k‖) := by ring
  set ε := Real.sqrt (C * M / (2 * V * E ^ 2 + 1)) with hε
  have hε0 : 0 < ε := Real.sqrt_pos.mpr (by have := mul_pos hpos hM0; positivity)
  have hε2 : 2 * V * (E * ε) ^ 2 < C * M := by
    have hCM : 0 < C * M := mul_pos hpos hM0
    rw [mul_pow, hε, Real.sq_sqrt (by positivity)]
    rw [show 2 * V * (E ^ 2 * (C * M / (2 * V * E ^ 2 + 1))) =
      (2 * V * E ^ 2) / (2 * V * E ^ 2 + 1) * (C * M) by ring]
    have : (2 * V * E ^ 2) / (2 * V * E ^ 2 + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    nlinarith
  obtain ⟨F, hF₀, hFtail⟩ : ∃ F : Finset κ, k₀ ∈ F ∧
      ∑' x : {x // x ∉ F}, (‖P x‖ + ‖R x‖) < ε := by
    have h := (tendsto_tsum_compl_atTop_zero (fun k => ‖P k‖ + ‖R k‖)).eventually
      (gt_mem_nhds hε0)
    obtain ⟨F, hF⟩ := (h.and (Filter.eventually_ge_atTop {k₀})).exists
    exact ⟨F, hF.2 (Finset.mem_singleton_self _), hF.1⟩
  have hsmall : ∀ v ∈ Set.Icc (-V) V, ‖∑ k ∈ F, cexp (I * γ k * v) *
      (P k * Real.cosh (δ k * v) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ))‖ ≤ E * ε := by
    intro v hv
    set u : κ → ℂ := fun k => cexp (I * γ k * v) *
      (P k * Real.cosh (δ k * v) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ)) with hu
    have husum : Summable u :=
      Summable.of_norm_bounded (hsum.mul_left E) fun k => hterm k v hv
    have hsplit := husum.sum_add_tsum_subtype_compl F
    rw [hzero v hv] at hsplit
    have htn : Summable fun x : {x // x ∉ F} => ‖P x‖ + ‖R x‖ :=
      hsum.comp_injective Subtype.val_injective
    rw [show ∑ k ∈ F, u k = -∑' x : {x // x ∉ F}, u x by linear_combination hsplit, norm_neg]
    calc ‖∑' x : {x // x ∉ F}, u x‖ ≤ ∑' x : {x // x ∉ F}, E * (‖P x‖ + ‖R x‖) :=
          tsum_of_norm_bounded (htn.mul_left E).hasSum fun x => hterm x v hv
      _ = E * ∑' x : {x // x ∉ F}, (‖P x‖ + ‖R x‖) := tsum_mul_left
      _ ≤ E * ε := mul_le_mul_of_nonneg_left hFtail.le hE0.le
  have hblock := uniform_block_inequality (ι := F) (fun k => γ k) (fun k => δ k)
    (fun k => P k) (fun k => R k) hg hV hs (fun k => hδ k)
    (fun j l hjl => hsep j l fun h => hjl (Subtype.ext h))
  rw [← hC] at hblock
  have hrw : ∀ v : ℝ, ∑ k : F, cexp (I * ((γ k : ℝ) : ℂ) * v) *
      (P k * ((Real.cosh (δ k * v) : ℝ) : ℂ) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ)) =
        ∑ k ∈ F, cexp (I * γ k * v) *
          (P k * Real.cosh (δ k * v) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ)) := fun v =>
    Finset.sum_coe_sort F (fun k => cexp (I * γ k * v) *
      (P k * Real.cosh (δ k * v) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ)))
  simp_rw [hrw] at hblock
  have hint : ∫ v in -V..V, ‖∑ k ∈ F, cexp (I * γ k * v) *
      (P k * Real.cosh (δ k * v) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ))‖ ^ 2 ≤ 2 * V * (E * ε) ^ 2 := by
    have hcont : Continuous fun v : ℝ => ‖∑ k ∈ F, cexp (I * γ k * v) *
        (P k * Real.cosh (δ k * v) + R k * ((depthSine (δ k) v / V : ℝ) : ℂ))‖ ^ 2 := by
      refine (continuous_norm.comp (continuous_finsetSum _ fun k _ => ?_)).pow 2
      have hd : Continuous (depthSine (δ k)) :=
        continuous_iff_continuousAt.mpr fun v => (hasDerivAt_depthSine _ v).continuousAt
      fun_prop
    calc _ ≤ ∫ _v in -V..V, (E * ε) ^ 2 := intervalIntegral.integral_mono_on (by linarith)
          (hcont.intervalIntegrable _ _) intervalIntegrable_const fun v hv =>
            pow_le_pow_left₀ (norm_nonneg _) (hsmall v hv) 2
      _ = 2 * V * (E * ε) ^ 2 := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hsq : M ≤ ∑ k : F, (‖P k‖ ^ 2 + ‖R k‖ ^ 2) := by
    rw [Finset.sum_coe_sort F (fun k => ‖P k‖ ^ 2 + ‖R k‖ ^ 2)]
    exact Finset.single_le_sum (f := fun k => ‖P k‖ ^ 2 + ‖R k‖ ^ 2)
      (fun _ _ => by positivity) hF₀
  have : C * M ≤ 2 * V * (E * ε) ^ 2 :=
    (mul_le_mul_of_nonneg_left hsq hpos.le).trans (hblock.trans hint)
  linarith

/-- **Resolution is uniform in depth.** Tempered configurations with depths `≤ s`, whose union has
`g`-separated heights apart from FE partners, are determined by their Weil forms on `C²` tests
supported in `[−a, a]`, `a > V/2`, as soon as `D(V) > 2π²B(V, s)/(3g²)`. No lower bound on the
depths of the off-line points is needed. -/
theorem eq_of_weil_eq_of_heightSeparated (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {g V s a : ℝ} (hg : 0 < g) (hV : 0 < V) (hs : 0 ≤ s)
    (hdepth : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, |ρ.re - 1 / 2| ≤ s)
    (hsep : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, ∀ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ →
      ρ' ≠ reflect ρ → g ≤ |ρ.im - ρ'.im|)
    (hpos : 0 < uniformDiag V - 2 * (π ^ 2 / 3 * uniformB V s / g ^ 2)) (ha : V / 2 < a)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  classical
  set w := a - V / 2 with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  refine eq_of_multDiff_eq_zero fun ρ₀ => ?_
  by_contra hc
  obtain ⟨t₀, ht₀re, hct₀⟩ := exists_site_of_multDiff_ne_zero hc
  set γ₀ := t₀.im
  have hzero := pairSum_vanishes_of_weil_eq Z Z' hZ hZ' (V := V) hw0
    (le_of_eq (by rw [hw]; ring)) γ₀ hW
  have hsum := summable_site Z Z' hZ hZ' hw0 γ₀
  set K := pairSites Z Z'
  set δ : K → ℝ := fun k => (k : ℂ).re - 1 / 2 with hδ
  set p : K → ℂ := fun k => siteP Z Z' w γ₀ k with hp
  set q : K → ℂ := fun k => siteQ Z Z' w γ₀ k with hq
  have hδs : ∀ k : K, |δ k| ≤ s := fun k => hdepth k k.2.1
  have hV0 : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  have hzero' : ∀ v ∈ Icc (-V) V, ∑' k : K, cexp (I * (k : ℂ).im * v) *
      ((p k + q k) * Real.cosh (δ k * v) +
        (((V * δ k : ℝ) : ℂ) * (p k - q k)) * ((depthSine (δ k) v / V : ℝ) : ℂ)) = 0 := by
    intro v hv
    rw [← hzero v hv]
    refine tsum_congr fun k => ?_
    rw [pair_eq_profiles, profile_rescale _ _ _ _ hV.ne']
  have hsum' : Summable fun k : K => ‖p k + q k‖ + ‖((V * δ k : ℝ) : ℂ) * (p k - q k)‖ := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (hsum.mul_left (1 + V * s))
    have h1 := norm_add_le (p k) (q k)
    have h2 : ‖((V * δ k : ℝ) : ℂ) * (p k - q k)‖ ≤ V * s * (‖p k‖ + ‖q k‖) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hV]
      have h := mul_le_mul (hδs k) (norm_sub_le (p k) (q k)) (norm_nonneg _) hs
      nlinarith [mul_le_mul_of_nonneg_left h hV.le]
    simp only [hp, hq] at h1 h2 ⊢
    nlinarith
  have hres := eq_zero_of_profileSum_eq_zero (fun k : K => (k : ℂ).im) δ
    (fun k => p k + q k) (fun k => ((V * δ k : ℝ) : ℂ) * (p k - q k)) hg hV hs hδs
    (sites_sep hsep) hpos hsum' hzero'
  obtain ⟨hP, hR⟩ := hres ⟨t₀, mem_carrier_of_multDiff_ne_zero hct₀, ht₀re⟩
  -- the coefficient of `e^{δv}` at `t₀` vanishes
  have hp0 : siteP Z Z' w γ₀ t₀ = 0 := by
    by_cases hk : t₀.re = 1 / 2
    · have hq0 : siteQ Z Z' w γ₀ t₀ = 0 := by simp [siteQ, hk]
      simp only [hp, hq, hq0, add_zero] at hP
      exact hP
    · have hδ0 : ((V * δ ⟨t₀, mem_carrier_of_multDiff_ne_zero hct₀, ht₀re⟩ : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (mul_ne_zero hV.ne' (sub_ne_zero.mpr hk))
      have hpq := sub_eq_zero.mp ((mul_eq_zero.mp hR).resolve_left hδ0)
      simp only [hp, hq] at hP hpq
      rw [hpq] at hP
      have : (2 : ℂ) * siteQ Z Z' w γ₀ t₀ = 0 := by rw [two_mul]; exact hP
      rw [hpq]
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  simp only [siteP] at hp0
  exact hct₀ ((mul_eq_zero.mp hp0).resolve_right (pairWeight_modScaledBump_ne_zero hw0 γ₀ _))

/-- **Hiding needs a near-collision in height or a deep point.** Two tempered configurations with
different carriers and one image at aperture `a > V/2` contain two points of different FE orbits
at height distance `< g`, or a point of depth `> s`, whenever `D(V) > 2π²B(V, s)/(3g²)`. Shallow
pairs are no obstruction. -/
theorem exists_near_pair_of_mimic {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') (hne : Z.carrier ≠ Z'.carrier) {g V s a : ℝ} (hg : 0 < g)
    (hV : 0 < V) (hs : 0 ≤ s)
    (hpos : 0 < uniformDiag V - 2 * (π ^ 2 / 3 * uniformB V s / g ^ 2)) (ha : V / 2 < a)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) :
    (∃ ρ ∈ Z.carrier ∪ Z'.carrier, ∃ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ ∧ ρ' ≠ reflect ρ ∧
        |ρ.im - ρ'.im| < g) ∨
      ∃ ρ ∈ Z.carrier ∪ Z'.carrier, s < |ρ.re - 1 / 2| := by
  by_contra h
  simp only [not_or, not_exists, not_and, not_lt] at h
  obtain ⟨hnear, hdeep⟩ := h
  exact hne (eq_of_weil_eq_of_heightSeparated Z Z' hZ hZ' hg hV hs hdeep
    (fun ρ hρ ρ' hρ' h1 h2 => hnear ρ hρ ρ' hρ' h1 h2) hpos ha hW).1

/-! ### The explicit scale -/

theorem uniformDiag_eq {V : ℝ} (hV : 0 < V) : uniformDiag V = (4 / π - 32 / π ^ 3) * V := by
  unfold uniformDiag inghamA
  field_simp
  ring

/-- `D(V) ≥ V/5`. -/
theorem uniformDiag_ge {V : ℝ} (hV : 0 < V) : V / 5 ≤ uniformDiag V := by
  rw [uniformDiag_eq hV]
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  have hpi : 0 < π := Real.pi_pos
  have key : 1 / 5 ≤ 4 / π - 32 / π ^ 3 := by
    rw [div_sub_div _ _ hpi.ne' (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [mul_pos hpi hpi, mul_pos (mul_pos hpi hpi) hpi]
  nlinarith

theorem cosh_le_two {x : ℝ} (hx : |x| ≤ 1) : Real.cosh x ≤ 2 := by
  have h1 : Real.cosh x ≤ Real.cosh 1 := by
    rw [Real.cosh_le_cosh, abs_one]; exact hx
  have h2 : Real.cosh 1 ≤ 2 := by
    rw [Real.cosh_eq]
    have := Real.exp_one_lt_d9
    have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  linarith

/-- `B(V, s) ≤ 230/V` for depths `s ≤ 1/V`. -/
theorem uniformB_le {V s : ℝ} (hV : 0 < V) (hs : 0 ≤ s) (hsV : s * V ≤ 1) :
    uniformB V s ≤ 230 / V := by
  have ha : 0 < inghamA V := by unfold inghamA; positivity
  have hc0 := Real.cosh_pos (s * V)
  have hc2 : Real.cosh (s * V) ≤ 2 :=
    cosh_le_two (by rw [abs_of_nonneg (by positivity)]; exact hsV)
  have hsV' : s ≤ 1 / V := by rw [le_div_iff₀ hV]; exact hsV
  have hE0 : profileBound0 V s ≤ 2 := hc2
  have hE1 : profileBound1 V s ≤ 4 / V := by
    unfold profileBound1
    calc (s + 1 / V) * Real.cosh (s * V) ≤ (2 / V) * 2 := by
          apply mul_le_mul _ hc2 hc0.le (by positivity)
          rw [show 2 / V = 1 / V + 1 / V by ring]; linarith
      _ = 4 / V := by ring
  have hE2 : profileBound2 V s ≤ 4 / V ^ 2 := by
    unfold profileBound2
    have hs2 : s ^ 2 ≤ 1 / V ^ 2 := by
      rw [show 1 / V ^ 2 = (1 / V) ^ 2 by ring]; exact pow_le_pow_left₀ hs hsV' 2
    have hsv : s / V ≤ 1 / V ^ 2 := by
      rw [show 1 / V ^ 2 = (1 / V) / V by ring]
      exact div_le_div_of_nonneg_right hsV' hV.le
    calc (s ^ 2 + s / V) * Real.cosh (s * V) ≤ (2 / V ^ 2) * 2 := by
          apply mul_le_mul _ hc2 hc0.le (by positivity)
          rw [show 2 / V ^ 2 = 1 / V ^ 2 + 1 / V ^ 2 by ring]; linarith
      _ = 4 / V ^ 2 := by ring
  have hE0n : 0 ≤ profileBound0 V s := hc0.le
  have hE1n : 0 ≤ profileBound1 V s := by unfold profileBound1; positivity
  have hE2n : 0 ≤ profileBound2 V s := by unfold profileBound2; positivity
  have hmono : uniformB V s ≤ offDiagConst (inghamA V) V 2 (4 / V) (4 / V ^ 2) := by
    unfold uniformB offDiagConst
    gcongr
  have hval : offDiagConst (inghamA V) V 2 (4 / V) (4 / V ^ 2) = (36 * π + 2 * π ^ 2 + 96) / V := by
    unfold offDiagConst inghamA
    field_simp
    ring
  have h2 := Real.pi_lt_d2
  have hnum : 36 * π + 2 * π ^ 2 + 96 ≤ 230 := by nlinarith [Real.pi_pos]
  calc uniformB V s ≤ (36 * π + 2 * π ^ 2 + 96) / V := hmono.trans_eq hval
    _ ≤ 230 / V := div_le_div_of_nonneg_right hnum hV.le

/-- **The explicit scale.** For depths `s ≤ 1/V` the depth-uniform constraint holds at every
separation `g ≥ 90/V`: two tempered configurations with different carriers and one image at
aperture `a > V/2` contain two points of different FE orbits at height distance `< g`, or a point of
depth `> s`. The scale is of the Nyquist order `1/V` of the aperture. -/
theorem exists_near_pair_of_mimic_of_le {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') (hne : Z.carrier ≠ Z'.carrier) {g V s a : ℝ} (hV : 0 < V)
    (hs : 0 ≤ s) (hsV : s * V ≤ 1) (hgV : 90 ≤ g * V) (ha : V / 2 < a)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) :
    (∃ ρ ∈ Z.carrier ∪ Z'.carrier, ∃ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ ∧ ρ' ≠ reflect ρ ∧
        |ρ.im - ρ'.im| < g) ∨
      ∃ ρ ∈ Z.carrier ∪ Z'.carrier, s < |ρ.re - 1 / 2| := by
  have hg : 0 < g := by
    by_contra h; push Not at h; nlinarith
  refine exists_near_pair_of_mimic hZ hZ' hne hg hV hs ?_ ha hW
  have hD := uniformDiag_ge hV
  have hB := uniformB_le hV hs hsV
  have h2 := Real.pi_lt_d2
  have hpi2 : π ^ 2 < 10 := by nlinarith [Real.pi_pos]
  have hg2 : 8100 ≤ (g * V) ^ 2 := by nlinarith
  -- `2(π²/3) B/g² ≤ (460π²/3)/(V g²) < V/5`
  have hB' : 2 * (π ^ 2 / 3 * uniformB V s / g ^ 2) ≤ 2 * (π ^ 2 / 3 * (230 / V) / g ^ 2) := by
    gcongr
  have hlt : 2 * (π ^ 2 / 3 * (230 / V) / g ^ 2) < V / 5 := by
    rw [show 2 * (π ^ 2 / 3 * (230 / V) / g ^ 2) = 460 * π ^ 2 * V / (3 * (g * V) ^ 2) by
      field_simp; ring]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_pos hV (by positivity : (0 : ℝ) < π ^ 2)]
  linarith

end GaloisForLFunctions.ZeroConfigurationGeometry
