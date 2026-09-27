import GaloisForLFunctions.RHTower.WeightedInterpolationContour
import GaloisForLFunctions.RHTower.CosineTranslatedWeilTests
import GaloisForLFunctions.RHTower.SubNyquistHodgeExclusion

/-!
# The localized finite-level resolution law

Let `Z` be a zero configuration with local count `N(t, t+1] ≤ A₀ log(|t| + 3)` and let `ρ₀` be a
zero of depth `δ = |β₀ - ½| > 0` at height `|γ₀| ≥ 103`.  Let `n_δ` be the number of zeros of depth
`≥ δ/8` with ordinate in `(γ₀ - 100, γ₀ + 100]`.  If the level-`a` Hodge index holds, then

> `δ a < 12((4 n_δ + 2) log(10⁶/δ) + log(A₀ log(|γ₀| + 3)) + 18)`

(`resolution_law_of_hodgeIndex`, and `zeta_resolution_law_of_hodgeIndex` for `ζ`).

A deep zero that the level-`a` Hodge index cannot see is therefore hidden in one of two ways:
either by the density of the other zeros (`δ a ≲ log(A₀ log |γ₀|)`: the zeros of small depth,
critical ones included, are not killed and still dominate), or by a crowd of `≳ δ a/log(1/δ)` zeros
of depth `≥ δ/8` within ordinate distance `100`.  The first regime is the finite-level resolution
`β - ½ ≲ log log γ/a`; the corpus companion law (`IsolatedDeepZeroHodgeIndex`) needed isolation
up to ordinate distance `e^a`.

**The test.**  Its transform is `cos(c x) Ŵ(x)^N Q(x)/lc(Q)` in the window coordinate
`x = γ - γ₀ - i(β - ½)` (`CosineTranslatedWeilTests`), where `Q = P·p` interpolates
`±i/(P cos(c·) Ŵ^N)` at the nodes, the window values of depth `≥ δ/8` inside
`[-X, X] × ±(y₀, 1)`, and `P` kills the other values of depth `≥ δ/8` and the polar point
(`WeightedInterpolationContour`).  Every node contributes `-m_ρ/lc(Q)²`.

* The window zeros of depth `< δ/8` are left alone: the contour formula at distance `≥ δ/8` bounds
  them by `e^{-cδ/8}` times constants to the power `n_δ`, since `|cos(c t)| ≥ sinh(c y₀)` on the
  contour while `|cos(c x)| ≤ cosh(cδ/8)` at them (`norm_wProfile_window_le`).
* The zeros outside the window are bounded by the decay of `Ŵ^N` (`norm_sq_wProfile_far_le`).
* The contour sides are chosen by the forward-difference product selection among the `n_δ` deep
  values only (`resolution_selection`).
-/

open Complex MeasureTheory Real Set Filter Topology Polynomial Lagrange
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23 HTGeometry

/-! ### The cosine factor -/

theorem norm_cos_sq (z : ℂ) : ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have hre : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    rw [Complex.cos_eq]; simp [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
      ← Complex.ofReal_sinh]
  have him : (Complex.cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
    rw [Complex.cos_eq]; simp [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
      ← Complex.ofReal_sinh]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  have h1 := Real.cosh_sq z.im
  have h2 := Real.sin_sq_add_cos_sq z.re
  nlinarith [h1, h2]

/-- `|cos z| ≥ |sinh(Im z)|`. -/
theorem abs_sinh_im_le_norm_cos (z : ℂ) : |Real.sinh z.im| ≤ ‖Complex.cos z‖ := by
  have h := norm_cos_sq z
  have h0 : 0 ≤ ‖Complex.cos z‖ := norm_nonneg _
  rw [← Real.sqrt_sq h0, h, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Real.cos z.re)])

/-- `|cos z| ≤ cosh(Im z)`. -/
theorem norm_cos_le_cosh_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  have h := norm_cos_sq z
  have h0 : 0 ≤ ‖Complex.cos z‖ := norm_nonneg _
  have hc := Real.cosh_sq z.im
  have hcos := Real.cos_sq_le_one z.re
  have hpos := Real.cosh_pos z.im
  nlinarith [sq_nonneg (‖Complex.cos z‖ - Real.cosh z.im)]

/-! ### The unit weight at a point -/

/-- `∫ (1 - u²)₊^{5/2} = Ŵ(0)`. -/
def unitMass : ℝ := ∫ u, sinhTestWeight 1 u

theorem unitWeightFloor_le_unitMass : unitWeightFloor ≤ unitMass := by
  have h := unitWeightFloor_le 0
  simp only [zero_mul, Real.cosh_zero, mul_one] at h
  exact h

theorem unitMass_pos : 0 < unitMass :=
  lt_of_lt_of_le unitWeightFloor_pos unitWeightFloor_le_unitMass

theorem integrable_unitWeight_mul_cosh (y : ℝ) :
    Integrable (fun u => sinhTestWeight 1 u * Real.cosh (y * u)) := by
  refine Continuous.integrable_of_hasCompactSupport ((sinhTestWeight_contDiff 1).continuous.mul
    (Real.continuous_cosh.comp (continuous_const.mul continuous_id))) ?_
  exact (hasCompactSupport_of_support_subset_abs (sinhTestWeight_supp zero_le_one)).mul_right

theorem unitMass_le_integral_cosh (y : ℝ) :
    unitMass ≤ ∫ u, sinhTestWeight 1 u * Real.cosh (y * u) := by
  unfold unitMass
  refine integral_mono ((sinhTestWeight_contDiff 1).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_support_subset_abs (sinhTestWeight_supp zero_le_one)))
    (integrable_unitWeight_mul_cosh y) fun u => ?_
  exact le_mul_of_one_le_right (sinhTestWeight_nonneg 1 u) (Real.one_le_cosh _)

/-- `Re Ŵ(t) ≥ cos θ · Ŵ(0)` for `|Re t| ≤ θ ≤ π/2`, at every height. -/
theorem re_unitHat_ge_mass {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.pi / 2) {t : ℂ}
    (ht : |t.re| ≤ θ) : Real.cos θ * unitMass ≤ (unitHat t).re := by
  set w := sinhTestWeight 1
  have hwc : Continuous w := (sinhTestWeight_contDiff 1).continuous
  have hws : HasCompactSupport w := hasCompactSupport_of_support_subset_abs
    (sinhTestWeight_supp zero_le_one)
  have hint : Integrable (fun u : ℝ => (w u : ℂ) * cexp (I * t * u)) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact (hasCompactSupport_ofReal_of_abs (sinhTestWeight_supp zero_le_one)).mul_right
  have hre : (unitHat t).re = ∫ u, w u * (Real.exp (-(t.im * u)) * Real.cos (t.re * u)) := by
    unfold unitHat
    rw [paperFT_def]
    have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [Complex.re_ofReal_mul, Complex.exp_re]
    congr 2
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
  have hcos : ∀ u, w u * (Real.exp (-(t.im * u)) * Real.cos θ) ≤
      w u * (Real.exp (-(t.im * u)) * Real.cos (t.re * u)) := by
    intro u
    by_cases hu : |u| ≤ 1
    · have hw0 := sinhTestWeight_nonneg 1 u
      have hc : Real.cos θ ≤ Real.cos (t.re * u) := by
        rw [← Real.cos_abs (t.re * u)]
        apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
        rw [abs_mul]
        calc |t.re| * |u| ≤ θ * 1 := mul_le_mul ht hu (abs_nonneg _) hθ0
          _ = θ := mul_one θ
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) hw0
    · have : w u = 0 := sinhTestWeight_eq_zero zero_le_one (lt_of_not_ge hu)
      simp [this]
  have hi1 : Integrable (fun u => w u * (Real.exp (-(t.im * u)) * Real.cos θ)) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact hws.mul_right
  have hi2 : Integrable (fun u => w u * (Real.exp (-(t.im * u)) * Real.cos (t.re * u))) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact hws.mul_right
  have hmono := integral_mono hi1 hi2 hcos
  have hint' : Integrable (fun u : ℝ => (w u : ℂ) * cexp (I * (I * t.im) * u)) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact (hasCompactSupport_ofReal_of_abs (sinhTestWeight_supp zero_le_one)).mul_right
  have hre2 : (unitHat (I * t.im)).re = ∫ u, w u * Real.exp (-(t.im * u)) := by
    unfold unitHat
    rw [paperFT_def]
    have h := integral_re hint'
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [Complex.re_ofReal_mul, Complex.exp_re]
    simp [Complex.mul_re, Complex.mul_im]
  have hval : unitHat (I * t.im) = ((∫ u, sinhTestWeight 1 u * Real.cosh (-t.im * u) : ℝ) : ℂ) := by
    have h := paperFT_unitWeight_neg_I_mul (-t.im)
    rw [show -(I * ((-t.im : ℝ) : ℂ)) = I * t.im by push_cast; ring] at h
    exact h
  have hfloor : unitMass ≤ ∫ u, w u * Real.exp (-(t.im * u)) := by
    rw [← hre2, hval, Complex.ofReal_re]
    exact unitMass_le_integral_cosh (-t.im)
  have hθc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos]) hθ
  have hpull : ∫ u, w u * (Real.exp (-(t.im * u)) * Real.cos θ) =
      Real.cos θ * ∫ u, w u * Real.exp (-(t.im * u)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    ring
  rw [hre]
  calc Real.cos θ * unitMass ≤ Real.cos θ * ∫ u, w u * Real.exp (-(t.im * u)) :=
        mul_le_mul_of_nonneg_left hfloor hθc
    _ = ∫ u, w u * (Real.exp (-(t.im * u)) * Real.cos θ) := hpull.symm
    _ ≤ _ := hmono

/-- `|Ŵ(x)| ≤ Ŵ(0) e^{|Im x|}`. -/
theorem norm_unitHat_le_mass (x : ℂ) : ‖unitHat x‖ ≤ unitMass * Real.exp |x.im| := by
  unfold unitHat unitMass
  rw [paperFT_def]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_mul_const]
  have hws := hasCompactSupport_of_support_subset_abs (sinhTestWeight_supp zero_le_one)
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) ?_
    (Eventually.of_forall fun u => ?_)
  · exact ((sinhTestWeight_contDiff 1).continuous.integrable_of_hasCompactSupport hws).mul_const _
  · simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sinhTestWeight_nonneg 1 u),
      Complex.norm_exp]
    by_cases hu : |u| ≤ 1
    · have : (I * x * (u : ℂ)).re = -(x.im * u) := by simp [Complex.mul_re]
      rw [this]
      have h1 : -(x.im * u) ≤ |x.im| := by
        have := abs_mul x.im u
        have h2 : |x.im| * |u| ≤ |x.im| := mul_le_of_le_one_right (abs_nonneg _) hu
        have h3 := neg_abs_le (x.im * u)
        linarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) (sinhTestWeight_nonneg 1 u)
    · have : sinhTestWeight 1 u = 0 := sinhTestWeight_eq_zero zero_le_one (lt_of_not_ge hu)
      simp [this]

/-! ### The weight `cos(c x) Ŵ(x)^N` -/

/-- The weight `Ψ(x) = cos(c x) Ŵ(x)^N`. -/
def cosShiftWeight (c : ℝ) (N : ℕ) (x : ℂ) : ℂ := Complex.cos (c * x) * unitHat x ^ N

theorem differentiable_cosShiftWeight (c : ℝ) (N : ℕ) : Differentiable ℂ (cosShiftWeight c N) := by
  unfold cosShiftWeight
  exact (Complex.differentiable_cos.comp (differentiable_const _ |>.mul differentiable_id)).mul
    (differentiable_unitHat.pow N)

theorem conj_cosShiftWeight_conj (c : ℝ) (N : ℕ) (z : ℂ) :
    conj (cosShiftWeight c N (conj z)) = cosShiftWeight c N z := by
  unfold cosShiftWeight
  rw [map_mul, map_pow, conj_unitHat_conj, ← Complex.cos_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_conj]

/-- On `|Re t| ≤ X ≤ 1`, `|Im t| ≥ y`: `|Ψ(t)| ≥ sinh(c y)(cos X · Ŵ(0))^N`. -/
theorem norm_cosShiftWeight_ge {c X y : ℝ} {N : ℕ} (hc : 0 ≤ c) (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hy : 0 ≤ y) {t : ℂ} (hre : |t.re| ≤ X) (him : y ≤ |t.im|) :
    Real.sinh (c * y) * (Real.cos X * unitMass) ^ N ≤ ‖cosShiftWeight c N t‖ := by
  unfold cosShiftWeight
  rw [norm_mul, norm_pow]
  have h1 : Real.sinh (c * y) ≤ ‖Complex.cos (c * t)‖ := by
    refine le_trans ?_ (abs_sinh_im_le_norm_cos _)
    have : (↑c * t).im = c * t.im := by simp
    rw [this, abs_sinh, abs_mul, abs_of_nonneg hc]
    exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left him hc)
  have hXπ : X ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have h2 : Real.cos X * unitMass ≤ ‖unitHat t‖ :=
    (re_unitHat_ge_mass hX0 hXπ hre).trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hcX : 0 ≤ Real.cos X := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos]) hXπ
  have hs0 : 0 ≤ Real.sinh (c * y) := Real.sinh_nonneg_iff.mpr (mul_nonneg hc hy)
  exact mul_le_mul h1 (pow_le_pow_left₀ (mul_nonneg hcX unitMass_pos.le) h2 N)
    (pow_nonneg (mul_nonneg hcX unitMass_pos.le) N) (norm_nonneg _)

theorem cosShiftWeight_ne_zero {c X : ℝ} {N : ℕ} (hc : 0 < c) (hX0 : 0 ≤ X) (hX : X ≤ 1) {t : ℂ}
    (hre : |t.re| ≤ X) (him : t.im ≠ 0) : cosShiftWeight c N t ≠ 0 := by
  have hy : 0 < |t.im| := abs_pos.mpr him
  have h := norm_cosShiftWeight_ge (y := |t.im|) hc.le hX0 hX (abs_nonneg _) hre le_rfl (N := N)
  have hs : 0 < Real.sinh (c * |t.im|) := Real.sinh_pos_iff.mpr (mul_pos hc hy)
  have hcX : 0 < Real.cos X := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three],
    by linarith [Real.pi_gt_three]⟩
  have hp : 0 < Real.sinh (c * |t.im|) * (Real.cos X * unitMass) ^ N := by
    have := unitMass_pos; positivity
  intro h0
  rw [h0, norm_zero] at h
  linarith

/-! ### Products on the contour -/

/-- On the sides of `[-X, X] × ±[y₀, 1]`, `Π_D |t - v| ≥ b^{|D|}`, given the one-dimensional
products at `X` and `y₀` with bases `≥ b`, and `b ≤ ½`. -/
theorem prod_norm_sub_ge_on_sides_gen {D : Finset ℂ} {X y₀ b bX bY : ℝ} (hb0 : 0 ≤ b)
    (hbX : b ≤ bX) (hbY : b ≤ bY) (hb2 : b ≤ 1 / 2) (hD : ∀ v ∈ D, |v.im| ≤ 1 / 2)
    (hXp : bX ^ D.card ≤ ∏ v ∈ D, abs (X - |v.re|))
    (hyp : bY ^ D.card ≤ ∏ v ∈ D, abs (y₀ - |v.im|))
    {t : ℂ} (ht : (|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
      (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1))) :
    b ^ D.card ≤ ∏ v ∈ D, ‖t - v‖ := by
  rcases ht with ⟨hre, -, -⟩ | ⟨-, him | him⟩
  · refine le_trans (pow_le_pow_left₀ hb0 hbX _) (hXp.trans ?_)
    refine Finset.prod_le_prod (fun v _ => abs_nonneg _) fun v _ => ?_
    rw [← hre]
    refine (abs_abs_sub_abs_le_abs_sub t.re v.re).trans ?_
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  · refine le_trans (pow_le_pow_left₀ hb0 hbY _) (hyp.trans ?_)
    refine Finset.prod_le_prod (fun v _ => abs_nonneg _) fun v _ => ?_
    rw [← him]
    refine (abs_abs_sub_abs_le_abs_sub t.im v.im).trans ?_
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  · rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun v _ => hb0) fun v hv => ?_
    have h1 : |t.im| - |v.im| ≤ ‖t - v‖ := by
      refine (le_abs_self _).trans ((abs_abs_sub_abs_le_abs_sub t.im v.im).trans ?_)
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    linarith [hD v hv]

/-- **The border bound with the polar factor.**  With the deep window values `D` split into nodes
`S` and conjugation-closed killed values `Kw`, a polar point `p` with `|Re p| ≥ H + 2`, and the side
products `≥ b^{|D|}`, `|P(t) ω(t)| ≥ (|Re p| - 1)² (b²/4)^k` on the sides, `P = P_{Kw ∪ {p}}`. -/
theorem border_lower_bound_polar {D S Kw : Finset ℂ} {X y₀ H b : ℝ} {p : ℂ} {k : ℕ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hX : X ≤ 3 / 4) (hy₀ : y₀ ≤ 1) (hH : 0 ≤ H)
    (hDSK : D = S ∪ Kw) (hdisj : Disjoint S Kw) (hKc : ∀ r ∈ Kw, conj r ∈ Kw)
    (hS : ∀ s ∈ S, |s.re| < X ∧ |s.im| ≤ 1 / 2) (hDre : ∀ v ∈ D, |v.re| ≤ H)
    (hp : H + 2 ≤ |p.re|) (hcard : D.card ≤ k)
    (hside : ∀ t : ℂ, ((|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
        (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1))) → b ^ D.card ≤ ∏ v ∈ D, ‖t - v‖)
    (t : ℂ) (ht : (|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
        (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1))) :
    (|p.re| - 1) ^ 2 * (b ^ 2 / 4) ^ k ≤
      ‖(killPoly (insert p Kw)).eval t‖ * ‖eval t (nodal S id)‖ := by
  have htre : |t.re| ≤ X := by
    rcases ht with h | h
    · exact h.1.le
    · exact h.1
  have htim : |t.im| ≤ 1 := by
    rcases ht with h | ⟨-, h | h⟩
    · exact h.2.2
    · rw [h]; exact hy₀
    · rw [h]
  have hSR : ∀ s ∈ S, ‖t - s‖ ≤ 4 := by
    intro s hs
    have h1 := Complex.norm_le_abs_re_add_abs_im (t - s)
    rw [Complex.sub_re, Complex.sub_im] at h1
    have h2 := abs_sub t.re s.re
    have h3 := abs_sub t.im s.im
    linarith [(hS s hs).1, (hS s hs).2]
  have hsq := sq_prod_le_killPoly_nodal hDSK hdisj hKc (by norm_num : (1 : ℝ) ≤ 4) hSR
  have hlow := hside t ht
  have hpow : (b ^ D.card) ^ 2 ≤ (∏ v ∈ D, ‖t - v‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlow 2
  have hpK : p ∉ Kw := by
    intro h
    have := hDre p (by rw [hDSK]; exact Finset.mem_union_right _ h)
    linarith
  have hPins : ‖(killPoly (insert p Kw)).eval t‖ =
      ‖t - p‖ * ‖t - conj p‖ * ‖(killPoly Kw).eval t‖ := by
    rw [norm_eval_killPoly, norm_eval_killPoly, Finset.prod_insert hpK]
  have hfar : ∀ q : ℂ, |q.re| = |p.re| → |p.re| - 1 ≤ ‖t - q‖ := by
    intro q hq
    have h1 := Complex.abs_re_le_norm (t - q)
    rw [Complex.sub_re] at h1
    have h2 := abs_sub_abs_le_abs_sub q.re t.re
    rw [abs_sub_comm] at h2
    linarith
  have hp1 := hfar p rfl
  have hp2 := hfar (conj p) (by rw [Complex.conj_re])
  have hp0 : 0 ≤ |p.re| - 1 := by linarith
  have hb4 : b ^ 2 / 4 ≤ 1 := by nlinarith
  have h4 : (0 : ℝ) < 4 ^ D.card := by positivity
  have hPKw : (b ^ 2 / 4) ^ k ≤ ‖(killPoly Kw).eval t‖ * ‖eval t (nodal S id)‖ := by
    calc (b ^ 2 / 4) ^ k ≤ (b ^ 2 / 4) ^ D.card :=
          pow_le_pow_of_le_one (by positivity) hb4 hcard
      _ = (b ^ D.card) ^ 2 / 4 ^ D.card := by
          rw [div_pow, ← pow_mul, ← pow_mul, mul_comm D.card 2]
      _ ≤ (∏ v ∈ D, ‖t - v‖) ^ 2 / 4 ^ D.card := div_le_div_of_nonneg_right hpow h4.le
      _ ≤ _ := by rw [div_le_iff₀ h4]; linarith
  rw [hPins]
  have hn0 : 0 ≤ ‖(killPoly Kw).eval t‖ * ‖eval t (nodal S id)‖ := by positivity
  calc (|p.re| - 1) ^ 2 * (b ^ 2 / 4) ^ k
      ≤ (‖t - p‖ * ‖t - conj p‖) * (‖(killPoly Kw).eval t‖ * ‖eval t (nodal S id)‖) := by
        rw [sq]
        exact mul_le_mul (mul_le_mul hp1 hp2 hp0 (norm_nonneg _)) hPKw (by positivity)
          (by positivity)
    _ = _ := by ring

/-- Upper bound for `|P_{Kw ∪ {p}}(x) ω_S(x)|`. -/
theorem killPoly_insert_nodal_le {S Kw : Finset ℂ} {p x : ℂ} {B Bp : ℝ} {k : ℕ} (hB : 1 ≤ B)
    (hBp : 0 ≤ Bp) (hK : ∀ r ∈ Kw, ‖x - r‖ ≤ B ∧ ‖x - conj r‖ ≤ B)
    (hS : ∀ s ∈ S, ‖x - s‖ ≤ B) (hcard : Kw.card + S.card ≤ k) (hpK : p ∉ Kw)
    (hxp : ‖x - p‖ ≤ Bp) (hxp' : ‖x - conj p‖ ≤ Bp) :
    ‖(killPoly (insert p Kw)).eval x‖ * ‖eval x (nodal S id)‖ ≤ Bp ^ 2 * B ^ (2 * k) := by
  have h := killPoly_nodal_le hB hK hS hcard
  have hPins : ‖(killPoly (insert p Kw)).eval x‖ =
      ‖x - p‖ * ‖x - conj p‖ * ‖(killPoly Kw).eval x‖ := by
    rw [norm_eval_killPoly, norm_eval_killPoly, Finset.prod_insert hpK]
  rw [hPins, mul_assoc, sq]
  exact mul_le_mul (mul_le_mul hxp hxp' (norm_nonneg _) hBp) h (by positivity) (by positivity)

/-! ### Summation -/

/-- **Summation with a positive window part.**  As `re_W_neg_of_window_profile`, but the window
zeros other than the deep pair may contribute up to `m C_u²/q²` each. -/
theorem re_W_neg_of_window_profile_gen (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {H : ℝ} (hH : 0 < H) {Wn : Finset ℂ}
    (hWn : ∀ ρ, ρ ∈ Wn ↔ ρ ∈ Z.carrier ∧ ρ₀.im - H < ρ.im ∧ ρ.im ≤ ρ₀.im + H)
    {f : ℝ → ℂ} {Φ : ℂ → ℂ} {q : ℝ} (hq : q ≠ 0)
    (hre_s : ∀ ρ : ℂ, (Z.Wsummand f f ρ).re = (Z.mult ρ : ℝ) * (Φ ρ ^ 2).re / q ^ 2)
    (hnorm_s : ∀ ρ : ℂ, ‖Z.Wsummand f f ρ‖ = (Z.mult ρ : ℝ) * ‖Φ ρ‖ ^ 2 / q ^ 2)
    {Cu : ℝ} (hwin : ∀ ρ ∈ Wn, (Φ ρ ^ 2).re ≤ Cu ^ 2 ∧ ‖Φ ρ‖ ^ 2 ≤ 1 + Cu ^ 2)
    {C₁ : ℝ} {E : ℕ} (hC₁0 : 0 ≤ C₁)
    (hfar : ∀ ρ ∈ Z.carrier, ρ ∉ Wn →
      H ≤ |ρ.im - ρ₀.im| ∧ ‖Φ ρ‖ ^ 2 * (1 + |ρ.im - ρ₀.im|) ^ (3 + E) ≤ C₁)
    (hΦ₀ : Φ ρ₀ ^ 2 = -1) (hΦ₁ : Φ (Zeta23.reflect ρ₀) ^ 2 = -1)
    (hbig : (C₁ / (1 + H) ^ E + Cu ^ 2 * (1 + H) ^ 3) * (24 * A₀ * Real.log (|ρ₀.im| + 3)) < 2) :
    (Z.W f f).re < 0 := by
  classical
  set γ₀ := ρ₀.im with hγ₀
  obtain ⟨hwsum, hwle⟩ := window_tsum_le Z hA₀ hloc γ₀
  have hH1 : 0 < 1 + H := by linarith
  have hq2 : 0 < q ^ 2 := by positivity
  have hHE : 0 < (1 + H) ^ E := by positivity
  have hCu2 : 0 ≤ Cu ^ 2 := sq_nonneg _
  have hρ₁W : Zeta23.reflect ρ₀ ∈ Wn :=
    (hWn _).mpr ⟨Z.reflect_mem ρ₀ hρ₀, by rw [reflect_im']; linarith,
      by rw [reflect_im']; linarith⟩
  have hwinD : ∀ ρ : ℂ, ρ ∈ Wn → 1 + |ρ.im - γ₀| ≤ 1 + H := by
    intro ρ hρ
    obtain ⟨-, h1, h2⟩ := (hWn _).mp hρ
    have := abs_le.mpr (⟨by linarith, by linarith⟩ : -H ≤ ρ.im - γ₀ ∧ ρ.im - γ₀ ≤ H)
    linarith
  have hbound : ∀ ρ : Z.carrier, ‖Z.Wsummand f f ρ‖ ≤
      (C₁ + (1 + Cu ^ 2) * (1 + H) ^ 3) / q ^ 2 *
        ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) := by
    intro ρ
    rw [hnorm_s]
    have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
    obtain ⟨D, hD⟩ : ∃ D, D = 1 + |(ρ : ℂ).im - γ₀| := ⟨_, rfl⟩
    rw [← hD]
    have hD1 : 1 ≤ D := by rw [hD]; linarith [abs_nonneg ((ρ : ℂ).im - γ₀)]
    have hD3 : 0 < D ^ 3 := by positivity
    have key : ‖Φ ρ‖ ^ 2 ≤ (C₁ + (1 + Cu ^ 2) * (1 + H) ^ 3) / D ^ 3 := by
      rw [le_div_iff₀ hD3]
      by_cases hW : (ρ : ℂ) ∈ Wn
      · have hDH : D ≤ 1 + H := by rw [hD]; exact hwinD _ hW
        have h3 := (hwin _ hW).2
        have h4 : D ^ 3 ≤ (1 + H) ^ 3 := pow_le_pow_left₀ (by linarith) hDH 3
        calc ‖Φ ρ‖ ^ 2 * D ^ 3 ≤ (1 + Cu ^ 2) * (1 + H) ^ 3 :=
              mul_le_mul h3 h4 (by positivity) (by positivity)
          _ ≤ C₁ + (1 + Cu ^ 2) * (1 + H) ^ 3 := by linarith
      · obtain ⟨-, hb⟩ := hfar _ ρ.2 hW
        rw [← hD] at hb
        have : ‖Φ ρ‖ ^ 2 * D ^ 3 ≤ ‖Φ ρ‖ ^ 2 * D ^ (3 + E) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD1 (by omega)) (by positivity)
        have : (0 : ℝ) ≤ (1 + Cu ^ 2) * (1 + H) ^ 3 := by positivity
        linarith
    calc (Z.mult (ρ : ℂ) : ℝ) * ‖Φ ρ‖ ^ 2 / q ^ 2
        ≤ (Z.mult (ρ : ℂ) : ℝ) * ((C₁ + (1 + Cu ^ 2) * (1 + H) ^ 3) / D ^ 3) / q ^ 2 := by
          gcongr
      _ = _ := by ring
  have hsum := Summable.of_norm_bounded
    (hwsum.mul_left ((C₁ + (1 + Cu ^ 2) * (1 + H) ^ 3) / q ^ 2)) hbound
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (C₁ / (1 + H) ^ E + Cu ^ 2 * (1 + H) ^ 3) / q ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hunit : ∀ ρ : Z.carrier, 0 ≤ (Z.mult (ρ : ℂ) : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 :=
    fun ρ => div_nonneg (Nat.cast_nonneg _) (by positivity)
  obtain ⟨T, hT⟩ : ∃ T : Z.carrier → ℝ, ∀ ρ, T ρ =
      c * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) :=
    ⟨fun ρ => c * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3), fun ρ => rfl⟩
  have hT0 : ∀ ρ, 0 ≤ T ρ := fun ρ => by rw [hT]; exact mul_nonneg hc0 (hunit ρ)
  have hTsum : Summable T := (hwsum.mul_left c).congr fun ρ => (hT ρ).symm
  set ρ₀ₛ : Z.carrier := ⟨ρ₀, hρ₀⟩ with hρ₀ₛ
  set ρ₁ₛ : Z.carrier := ⟨Zeta23.reflect ρ₀, Z.reflect_mem ρ₀ hρ₀⟩ with hρ₁ₛ
  have hne : ρ₁ₛ ≠ ρ₀ₛ := by
    intro h
    have := congrArg (fun x : Z.carrier => (x : ℂ).re) h
    simp only [hρ₀ₛ, hρ₁ₛ, reflect_re', hre] at this
    linarith
  have hm₀ : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ hρ₀
  have hdeep : ∀ ρ' : ℂ, Φ ρ' ^ 2 = -1 → (1 : ℝ) ≤ Z.mult ρ' →
      (Z.mult ρ' : ℝ) * (Φ ρ' ^ 2).re / q ^ 2 ≤ -(1 / q ^ 2) := by
    intro ρ' h hm
    rw [h, Complex.neg_re, Complex.one_re, mul_neg, mul_one, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_right hm hq2.le)
  have hpt : ∀ ρ : Z.carrier, (Z.Wsummand f f ρ).re ≤
      (if ρ = ρ₀ₛ then -(1 / q ^ 2) else 0) + (if ρ = ρ₁ₛ then -(1 / q ^ 2) else 0) + T ρ := by
    intro ρ
    rw [hre_s]
    have hTρ := hT0 ρ
    by_cases h0 : ρ = ρ₀ₛ
    · have h1 : ρ ≠ ρ₁ₛ := fun h => hne (h ▸ h0)
      rw [if_pos h0, if_neg h1, add_zero]
      have := hdeep ρ₀ hΦ₀ hm₀
      have e : (ρ : ℂ) = ρ₀ := by rw [h0]
      rw [e]
      linarith
    by_cases h1 : ρ = ρ₁ₛ
    · rw [if_neg h0, if_pos h1, zero_add]
      have := hdeep _ hΦ₁ (by rw [Z.mult_reflect ρ₀ hρ₀]; exact hm₀)
      have e : (ρ : ℂ) = Zeta23.reflect ρ₀ := by rw [h1]
      rw [e]
      linarith
    rw [if_neg h0, if_neg h1, zero_add, zero_add, hT, hc]
    have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
    obtain ⟨D, hD⟩ : ∃ D, D = 1 + |(ρ : ℂ).im - γ₀| := ⟨_, rfl⟩
    rw [← hD]
    have hD1 : 1 ≤ D := by rw [hD]; linarith [abs_nonneg ((ρ : ℂ).im - γ₀)]
    have hD0 : 0 < D := by linarith
    by_cases hW : (ρ : ℂ) ∈ Wn
    · have hDH : D ≤ 1 + H := by rw [hD]; exact hwinD _ hW
      have h3 := (hwin _ hW).1
      have hD3 : D ^ 3 ≤ (1 + H) ^ 3 := pow_le_pow_left₀ hD0.le hDH 3
      have key : (Z.mult (ρ : ℂ) : ℝ) * (Φ ρ ^ 2).re ≤
          (Z.mult (ρ : ℂ) : ℝ) * (Cu ^ 2 * (1 + H) ^ 3 / D ^ 3) := by
        refine mul_le_mul_of_nonneg_left (h3.trans ?_) hm
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      calc (Z.mult (ρ : ℂ) : ℝ) * (Φ ρ ^ 2).re / q ^ 2
          ≤ (Z.mult (ρ : ℂ) : ℝ) * (Cu ^ 2 * (1 + H) ^ 3 / D ^ 3) / q ^ 2 :=
            div_le_div_of_nonneg_right key hq2.le
        _ = Cu ^ 2 * (1 + H) ^ 3 / q ^ 2 * ((Z.mult (ρ : ℂ) : ℝ) / D ^ 3) := by
            field_simp
        _ ≤ (C₁ / (1 + H) ^ E + Cu ^ 2 * (1 + H) ^ 3) / q ^ 2 * ((Z.mult (ρ : ℂ) : ℝ) / D ^ 3) := by
            have hmD : 0 ≤ (Z.mult (ρ : ℂ) : ℝ) / D ^ 3 := by positivity
            have : 0 ≤ C₁ / (1 + H) ^ E / q ^ 2 := by positivity
            rw [add_div, add_mul]
            nlinarith
    · obtain ⟨hfarH, hb⟩ := hfar _ ρ.2 hW
      rw [← hD] at hb
      have hDH : 1 + H ≤ D := by rw [hD]; linarith
      have hDE : (1 + H) ^ E * D ^ 3 ≤ D ^ (3 + E) := by
        rw [pow_add, mul_comm]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH1.le hDH E) (by positivity)
      have hF : ‖Φ ρ‖ ^ 2 ≤ C₁ / ((1 + H) ^ E * D ^ 3) := by
        rw [le_div_iff₀ (by positivity)]
        exact (mul_le_mul_of_nonneg_left hDE (by positivity)).trans hb
      have hre_le : (Φ ρ ^ 2).re ≤ ‖Φ ρ‖ ^ 2 := by
        rw [← norm_pow]; exact Complex.re_le_norm _
      calc (Z.mult (ρ : ℂ) : ℝ) * (Φ ρ ^ 2).re / q ^ 2
          ≤ (Z.mult (ρ : ℂ) : ℝ) * (C₁ / ((1 + H) ^ E * D ^ 3)) / q ^ 2 := by
            gcongr; exact hre_le.trans hF
        _ = C₁ / (1 + H) ^ E / q ^ 2 * ((Z.mult (ρ : ℂ) : ℝ) / D ^ 3) := by field_simp
        _ ≤ (C₁ / (1 + H) ^ E + Cu ^ 2 * (1 + H) ^ 3) / q ^ 2 * ((Z.mult (ρ : ℂ) : ℝ) / D ^ 3) := by
            have hmD : 0 ≤ (Z.mult (ρ : ℂ) : ℝ) / D ^ 3 := by positivity
            have : 0 ≤ Cu ^ 2 * (1 + H) ^ 3 / q ^ 2 := by positivity
            rw [add_div]
            nlinarith
  have hW := re_W_le_of_pointwise Z f hsum ρ₀ₛ ρ₁ₛ (1 / q ^ 2) hTsum hpt
  have hTle' : ∑' ρ, T ρ ≤ c * (24 * A₀ * Real.log (|γ₀| + 3)) := by
    rw [tsum_congr hT, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hwle hc0
  have hkey : c * (24 * A₀ * Real.log (|γ₀| + 3)) < 2 * (1 / q ^ 2) := by
    calc c * (24 * A₀ * Real.log (|γ₀| + 3))
        = (C₁ / (1 + H) ^ E + Cu ^ 2 * (1 + H) ^ 3) * (24 * A₀ * Real.log (|γ₀| + 3)) / q ^ 2 := by
          rw [hc]; ring
      _ < 2 / q ^ 2 := div_lt_div_of_pos_right hbig hq2
      _ = 2 * (1 / q ^ 2) := by ring
  linarith

/-! ### The profile at the zeros -/

/-- In the strip, `|Ŵ(x)| (1 + |Re x|)² ≤ 168 e^{1/2}`. -/
theorem norm_unitHat_mul_sq_le {x : ℂ} (hx : |x.im| ≤ 1 / 2) :
    ‖unitHat x‖ * (1 + |x.re|) ^ 2 ≤ Real.exp (1 / 2) * 168 := by
  have h := norm_unitHat_div_le hx
  have hc := unitHatFloor_pos
  have hD : 0 < (1 + |x.re|) ^ 2 := by positivity
  unfold unitDecayRatio at h
  rw [div_le_div_iff₀ hc hD] at h
  have e : Real.exp (1 / 2) * 168 / unitHatFloor * unitHatFloor = Real.exp (1 / 2) * 168 := by
    field_simp
  nlinarith

/-- The side conditions shared by the two per-zero bounds. -/
def OnSides (X y₀ : ℝ) (t : ℂ) : Prop :=
  (|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨ (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1))

theorem OnSides.re_le {X y₀ : ℝ} {t : ℂ} (h : OnSides X y₀ t) : |t.re| ≤ X := by
  rcases h with h | h
  · exact h.1.le
  · exact h.1

theorem OnSides.im_ge {X y₀ : ℝ} {t : ℂ} (hy : y₀ ≤ 1) (h : OnSides X y₀ t) :
    y₀ ≤ |t.im| ∧ |t.im| ≤ 1 := by
  rcases h with h | ⟨-, h | h⟩
  · exact h.2
  · rw [h]; exact ⟨le_rfl, hy⟩
  · rw [h]; exact ⟨hy, le_rfl⟩

/-- **The window zeros left unkilled.**  At a window value `x` of depth `< δ/8`, the profile is at
most `C_u`: the contour is at distance `≥ δ/8` and the weight gains `sinh(c y₀)/cosh(cδ/8)`. -/
theorem norm_wProfile_window_le {S Kw : Finset ℂ} {p x : ℂ} {X y₀ δ H c lam cΨ : ℝ} {N k : ℕ}
    (hX0 : 0 < X) (hX : X ≤ 3 / 4) (hy0 : 0 < y₀) (hy : y₀ ≤ 1 / 2) (hδ : 0 < δ)
    (hy₀δ : δ / 4 ≤ y₀) (hc : 0 < c) (hH : 0 ≤ H)
    (hS : ∀ s ∈ S, |s.re| < X ∧ y₀ < |s.im| ∧ |s.im| ≤ 1 / 2)
    (hKw : ∀ r ∈ Kw, (X < |r.re| ∨ |r.im| < y₀) ∧ |r.re| ≤ H ∧ |r.im| ≤ 1 / 2)
    (hKc : ∀ r ∈ Kw, conj r ∈ Kw) (hSH : ∀ s ∈ S, |s.re| ≤ H)
    (hp : X < |p.re|) (hpim : |p.im| ≤ 1 / 2) (hpK : p ∉ Kw) (hcard : Kw.card + S.card ≤ k)
    (hlam : 0 < lam) (hcΨ : 0 < cΨ)
    (hlamS : ∀ t, OnSides X y₀ t → lam ≤ ‖(killPoly (insert p Kw)).eval t‖ * ‖eval t (nodal S id)‖)
    (hΨ : ∀ t, OnSides X y₀ t → cΨ ≤ ‖cosShiftWeight c N t‖)
    (hx : |x.re| ≤ H) (hxi : |x.im| < δ / 8) :
    ‖wProfile (insert p Kw) S (cosShiftWeight c N) x‖ ≤
      2 * ((|p.re| + H + 1) ^ 2 * (2 * H + 2) ^ (2 * k) / (lam * (δ / 8)) *
        (Real.cosh (c * (δ / 8)) * (unitMass * Real.exp (δ / 8)) ^ N / cΨ)) := by
  have hKmem : ∀ r ∈ insert p Kw, X < |r.re| ∨ |r.im| < y₀ ∨ 1 < |r.im| := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Or.inl hp
    · rcases (hKw r hr).1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hδ8 : 0 < δ / 8 := by positivity
  have hM := killPoly_insert_nodal_le (S := S) (Kw := Kw) (p := p) (x := x)
    (B := 2 * H + 2) (Bp := |p.re| + H + 1) (k := k) (by linarith) (by positivity)
    (fun r hr => by
      have hr' := hKw r hr
      have hrc := hKw _ (hKc r hr)
      constructor
      · have h1 := Complex.norm_le_abs_re_add_abs_im (x - r)
        rw [Complex.sub_re, Complex.sub_im] at h1
        have h2 := abs_sub x.re r.re
        have h3 := abs_sub x.im r.im
        linarith [hr'.2.1, hr'.2.2]
      · have h1 := Complex.norm_le_abs_re_add_abs_im (x - conj r)
        rw [Complex.sub_re, Complex.sub_im] at h1
        have h2 := abs_sub x.re (conj r).re
        have h3 := abs_sub x.im (conj r).im
        linarith [hrc.2.1, hrc.2.2])
    (fun s hs => by
      have h1 := Complex.norm_le_abs_re_add_abs_im (x - s)
      rw [Complex.sub_re, Complex.sub_im] at h1
      have h2 := abs_sub x.re s.re
      have h3 := abs_sub x.im s.im
      linarith [hSH s hs, (hS s hs).2.2])
    hcard hpK
    (by
      have h1 := Complex.norm_le_abs_re_add_abs_im (x - p)
      rw [Complex.sub_re, Complex.sub_im] at h1
      have h2 := abs_sub x.re p.re
      have h3 := abs_sub x.im p.im
      linarith)
    (by
      have h1 := Complex.norm_le_abs_re_add_abs_im (x - conj p)
      rw [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im] at h1
      have h2 := abs_sub x.re p.re
      have h3 := abs_sub x.im (-p.im)
      rw [abs_neg] at h3
      linarith)
  have hbound := norm_wProfile_le (K := insert p Kw) (S := S) (Ψ := cosShiftWeight c N) (X := X)
    (y₀ := y₀) (lam := lam) (M := (|p.re| + H + 1) ^ 2 * (2 * H + 2) ^ (2 * k)) (c := cΨ)
    (d := δ / 8) (x := x) hX0 hX hy0 hy
    (fun s hs => ⟨(hS s hs).1, (hS s hs).2.1, by linarith [(hS s hs).2.2]⟩) hKmem
    (Or.inr (Or.inl (by linarith))) (differentiable_cosShiftWeight c N)
    (fun t htr hti _ => cosShiftWeight_ne_zero (N := N) hc hX0.le (by linarith) htr (by
          intro h0; rw [h0, abs_zero] at hti; linarith))
    hcΨ hlam hδ8
    (fun t ht => ⟨hlamS t ht, hΨ t ht, by
      have hti := (OnSides.im_ge (X := X) (by linarith) ht).1
      have h1 := Complex.abs_im_le_norm (x - t)
      rw [Complex.sub_im] at h1
      have h2 := abs_sub_abs_le_abs_sub t.im x.im
      rw [abs_sub_comm] at h2
      linarith⟩)
    hM
  refine hbound.trans ?_
  have hΨx : ‖cosShiftWeight c N x‖ ≤
      Real.cosh (c * (δ / 8)) * (unitMass * Real.exp (δ / 8)) ^ N := by
    unfold cosShiftWeight
    rw [norm_mul, norm_pow]
    have h1 : ‖Complex.cos (c * x)‖ ≤ Real.cosh (c * (δ / 8)) := by
      refine (norm_cos_le_cosh_im _).trans ?_
      have : (↑c * x).im = c * x.im := by simp
      rw [this]
      refine Real.cosh_le_cosh.mpr ?_
      rw [abs_mul, abs_of_pos hc, abs_of_nonneg (by positivity : 0 ≤ c * (δ / 8))]
      exact mul_le_mul_of_nonneg_left hxi.le hc.le
    have h2 : ‖unitHat x‖ ≤ unitMass * Real.exp (δ / 8) :=
      (norm_unitHat_le_mass x).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hxi.le) unitMass_pos.le)
    exact mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) h2 N) (by positivity)
      (Real.cosh_pos _).le
  have hMd : 0 ≤ (|p.re| + H + 1) ^ 2 * (2 * H + 2) ^ (2 * k) / (lam * (δ / 8)) := by positivity
  gcongr

/-- **The zeros outside the window.**  For `|Re x| ≥ H`, `|Im x| ≤ ½`,
`|Φ(x)|² (1 + |Re x|)^{4N-4k-4} ≤ 4 ((|Re p| + 1)² (H + 1)^{2k}/λ · cosh(c/2)/c_Ψ)²
(168 e^{1/2})^{2N}`. -/
theorem norm_sq_wProfile_far_le {S Kw : Finset ℂ} {p x : ℂ} {X y₀ H c lam cΨ : ℝ} {N k : ℕ}
    (hX0 : 0 < X) (hX : X ≤ 3 / 4) (hy0 : 0 < y₀) (hy : y₀ ≤ 1 / 2) (hc : 0 < c) (hH : 2 ≤ H)
    (hS : ∀ s ∈ S, |s.re| < X ∧ y₀ < |s.im| ∧ |s.im| ≤ 1 / 2)
    (hKw : ∀ r ∈ Kw, (X < |r.re| ∨ |r.im| < y₀) ∧ |r.re| ≤ H ∧ |r.im| ≤ 1 / 2)
    (hKc : ∀ r ∈ Kw, conj r ∈ Kw) (hSH : ∀ s ∈ S, |s.re| ≤ H)
    (hp : X < |p.re|) (hpim : |p.im| ≤ 1 / 2) (hpK : p ∉ Kw) (hcard : Kw.card + S.card ≤ k)
    (hlam : 0 < lam) (hcΨ : 0 < cΨ)
    (hlamS : ∀ t, OnSides X y₀ t → lam ≤ ‖(killPoly (insert p Kw)).eval t‖ * ‖eval t (nodal S id)‖)
    (hΨ : ∀ t, OnSides X y₀ t → cΨ ≤ ‖cosShiftWeight c N t‖)
    (hNk : 2 * k + 2 ≤ N) (hx : H ≤ |x.re|) (hxi : |x.im| ≤ 1 / 2) :
    ‖wProfile (insert p Kw) S (cosShiftWeight c N) x‖ ^ 2 * (1 + |x.re|) ^ (4 * N - 4 * k - 4) ≤
      4 * ((|p.re| + 1) ^ 2 * (H + 1) ^ (2 * k) / lam * (Real.cosh (c / 2) / cΨ)) ^ 2 *
        (Real.exp (1 / 2) * 168) ^ (2 * N) := by
  set D := 1 + |x.re| with hD
  have hD1 : 1 ≤ D := by linarith [abs_nonneg x.re]
  have hD0 : 0 < D := by linarith
  have hKmem : ∀ r ∈ insert p Kw, X < |r.re| ∨ |r.im| < y₀ ∨ 1 < |r.im| := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Or.inl hp
    · rcases (hKw r hr).1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hnear : ∀ v : ℂ, |v.re| ≤ H → |v.im| ≤ 1 / 2 → ‖x - v‖ ≤ (H + 1) * D := by
    intro v hv1 hv2
    have h1 := Complex.norm_le_abs_re_add_abs_im (x - v)
    rw [Complex.sub_re, Complex.sub_im] at h1
    have h2 := abs_sub x.re v.re
    have h3 := abs_sub x.im v.im
    nlinarith [abs_nonneg x.re]
  have hpolar : ∀ q : ℂ, |q.re| = |p.re| → |q.im| ≤ 1 / 2 → ‖x - q‖ ≤ (|p.re| + 1) * D := by
    intro q hq hqi
    have h1 := Complex.norm_le_abs_re_add_abs_im (x - q)
    rw [Complex.sub_re, Complex.sub_im] at h1
    have h2 := abs_sub x.re q.re
    have h3 := abs_sub x.im q.im
    nlinarith [abs_nonneg x.re, abs_nonneg p.re]
  have hM := killPoly_insert_nodal_le (S := S) (Kw := Kw) (p := p) (x := x)
    (B := (H + 1) * D) (Bp := (|p.re| + 1) * D) (k := k) (by nlinarith) (by positivity)
    (fun r hr => ⟨hnear r (hKw r hr).2.1 (hKw r hr).2.2,
      hnear _ (hKw _ (hKc r hr)).2.1 (hKw _ (hKc r hr)).2.2⟩)
    (fun s hs => hnear s (hSH s hs) (hS s hs).2.2) hcard hpK (hpolar p rfl hpim)
    (hpolar _ (by rw [Complex.conj_re]) (by rw [Complex.conj_im, abs_neg]; exact hpim))
  have hbound := norm_wProfile_le (K := insert p Kw) (S := S) (Ψ := cosShiftWeight c N) (X := X)
    (y₀ := y₀) (lam := lam) (M := ((|p.re| + 1) * D) ^ 2 * ((H + 1) * D) ^ (2 * k)) (c := cΨ)
    (d := 1) (x := x) hX0 hX hy0 hy
    (fun s hs => ⟨(hS s hs).1, (hS s hs).2.1, by linarith [(hS s hs).2.2]⟩) hKmem
    (Or.inl (by linarith)) (differentiable_cosShiftWeight c N)
    (fun t htr hti _ => cosShiftWeight_ne_zero (N := N) hc hX0.le (by linarith) htr (by
          intro h0; rw [h0, abs_zero] at hti; linarith))
    hcΨ hlam one_pos
    (fun t ht => ⟨hlamS t ht, hΨ t ht, by
      have htr := OnSides.re_le (y₀ := y₀) ht
      have h1 := Complex.abs_re_le_norm (x - t)
      rw [Complex.sub_re] at h1
      have h2 := abs_sub_abs_le_abs_sub x.re t.re
      linarith⟩)
    hM
  -- the weight at `x`
  have hW := norm_unitHat_mul_sq_le hxi
  have hΨx : ‖cosShiftWeight c N x‖ * D ^ (2 * N) ≤
      Real.cosh (c / 2) * (Real.exp (1 / 2) * 168) ^ N := by
    unfold cosShiftWeight
    rw [norm_mul, norm_pow]
    have h1 : ‖Complex.cos (c * x)‖ ≤ Real.cosh (c / 2) := by
      refine (norm_cos_le_cosh_im _).trans ?_
      have : (↑c * x).im = c * x.im := by simp
      rw [this]
      refine Real.cosh_le_cosh.mpr ?_
      rw [abs_mul, abs_of_pos hc, abs_of_pos (by positivity : 0 < c / 2)]
      nlinarith
    have h2 : (‖unitHat x‖ * D ^ 2) ^ N ≤ (Real.exp (1 / 2) * 168) ^ N :=
      pow_le_pow_left₀ (by positivity) hW N
    calc ‖Complex.cos (↑c * x)‖ * ‖unitHat x‖ ^ N * D ^ (2 * N)
        = ‖Complex.cos (↑c * x)‖ * (‖unitHat x‖ * D ^ 2) ^ N := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ Real.cosh (c / 2) * (Real.exp (1 / 2) * 168) ^ N :=
          mul_le_mul h1 h2 (by positivity) (Real.cosh_pos _).le
  set A := (|p.re| + 1) ^ 2 * (H + 1) ^ (2 * k) / lam * (Real.cosh (c / 2) / cΨ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hstep : ‖wProfile (insert p Kw) S (cosShiftWeight c N) x‖ * D ^ (2 * N) ≤
      2 * A * (Real.exp (1 / 2) * 168) ^ N * D ^ (2 * k + 2) := by
    have e1 : ((|p.re| + 1) * D) ^ 2 * ((H + 1) * D) ^ (2 * k) / (lam * 1) =
        (|p.re| + 1) ^ 2 * (H + 1) ^ (2 * k) / lam * D ^ (2 * k + 2) := by
      rw [mul_pow, mul_pow, pow_add]; field_simp
    calc ‖wProfile (insert p Kw) S (cosShiftWeight c N) x‖ * D ^ (2 * N)
        ≤ 2 * (((|p.re| + 1) * D) ^ 2 * ((H + 1) * D) ^ (2 * k) / (lam * 1) *
            (‖cosShiftWeight c N x‖ / cΨ)) * D ^ (2 * N) :=
          mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = 2 * ((|p.re| + 1) ^ 2 * (H + 1) ^ (2 * k) / lam / cΨ) * D ^ (2 * k + 2) *
            (‖cosShiftWeight c N x‖ * D ^ (2 * N)) := by rw [e1]; ring
      _ ≤ 2 * ((|p.re| + 1) ^ 2 * (H + 1) ^ (2 * k) / lam / cΨ) * D ^ (2 * k + 2) *
            (Real.cosh (c / 2) * (Real.exp (1 / 2) * 168) ^ N) := by gcongr
      _ = 2 * A * (Real.exp (1 / 2) * 168) ^ N * D ^ (2 * k + 2) := by rw [hA]; ring
  have hsq : ‖wProfile (insert p Kw) S (cosShiftWeight c N) x‖ ^ 2 * D ^ (4 * N) ≤
      4 * A ^ 2 * (Real.exp (1 / 2) * 168) ^ (2 * N) * D ^ (4 * k + 4) := by
    have := pow_le_pow_left₀ (by positivity) hstep 2
    calc ‖wProfile (insert p Kw) S (cosShiftWeight c N) x‖ ^ 2 * D ^ (4 * N)
        = (‖wProfile (insert p Kw) S (cosShiftWeight c N) x‖ * D ^ (2 * N)) ^ 2 := by ring
      _ ≤ (2 * A * (Real.exp (1 / 2) * 168) ^ N * D ^ (2 * k + 2)) ^ 2 := this
      _ = 4 * A ^ 2 * (Real.exp (1 / 2) * 168) ^ (2 * N) * D ^ (4 * k + 4) := by ring
  have hsplit : D ^ (4 * N) = D ^ (4 * N - 4 * k - 4) * D ^ (4 * k + 4) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, ← mul_assoc] at hsq
  exact le_of_mul_le_mul_right hsq (by positivity)

/-! ### Selection and classification -/

/-- **Contour selection among the deep values.**  Let `D` be the window values of depth
`≥ δ/8`.  There are `X ∈ [√δ/8, √δ/4]` and `y₀ ∈ [δ/4, δ/2]`, attained by no `|Re v|`, resp.
`|Im v|`, `v ∈ D`, with `Π_D |t - v| ≥ (δ/(16e))^{|D|}` on the sides of `[-X, X] × ±[y₀, 1]`. -/
theorem resolution_selection {D : Finset ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : ∀ v ∈ D, |v.im| ≤ 1 / 2) :
    ∃ X y₀ : ℝ, Real.sqrt δ / 8 ≤ X ∧ X ≤ Real.sqrt δ / 4 ∧ δ / 4 ≤ y₀ ∧ y₀ ≤ δ / 2 ∧
      (∀ v ∈ D, |v.re| ≠ X ∧ |v.im| ≠ y₀) ∧
      ∀ t : ℂ, OnSides X y₀ t → (δ / (16 * Real.exp 1)) ^ D.card ≤ ∏ v ∈ D, ‖t - v‖ := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  obtain ⟨X, ⟨hX1, hX2⟩, hXp⟩ := exists_mem_Icc_prod_abs_sub_ge D (fun v => |v.re|)
    (Real.sqrt δ / 8) (L := Real.sqrt δ / 8) (by positivity)
  obtain ⟨y₀, ⟨hy1, hy2⟩, hyp⟩ := exists_mem_Icc_prod_abs_sub_ge D (fun v => |v.im|) (δ / 4)
    (L := δ / 4) (by positivity)
  have hne : ∀ {f : ℂ → ℝ} {b : ℝ}, 0 < b → b ^ D.card ≤ ∏ v ∈ D, f v → ∀ v ∈ D, f v ≠ 0 := by
    intro f b hb h
    have hpos : 0 < ∏ v ∈ D, f v := lt_of_lt_of_le (pow_pos hb _) h
    exact Finset.prod_ne_zero_iff.mp hpos.ne'
  have hXn := hne (by positivity) hXp
  have hyn := hne (by positivity) hyp
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hsδ : δ ≤ Real.sqrt δ := by
    have := Real.sqrt_le_sqrt hδ1
    rw [Real.sqrt_one] at this
    nlinarith [Real.sq_sqrt hδ.le]
  refine ⟨X, y₀, hX1, by linarith, hy1, by linarith, fun v hv => ⟨?_, ?_⟩, fun t ht =>
    prod_norm_sub_ge_on_sides_gen (bX := Real.sqrt δ / 8 / (2 * Real.exp 1))
      (bY := δ / 4 / (2 * Real.exp 1)) (by positivity) ?_ ?_ ?_ hD hXp hyp ht⟩
  · intro h; apply hXn v hv; rw [h, sub_self, abs_zero]
  · intro h; apply hyn v hv; rw [h, sub_self, abs_zero]
  · rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have := Real.add_one_le_exp 1
    nlinarith

/-! ### The resolution law -/

/-- **The test and its Weil form.**  Given contour data and the classification of the window values
into nodes `S` (conjugation-closed, inside `[-X, X] × ±(y₀, ½]`), killed values `Kw` and shallow
values of depth `< δ/8`, the cosine-translated interpolation test has negative Weil form under the
size condition. -/
theorem resolution_test_negative (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {H a c : ℝ} (hH : 2 ≤ H) (hγ : H + 3 ≤ |ρ₀.im|) (hc : 0 < c) {N k : ℕ}
    (hNa : (N : ℝ) + c ≤ a) (hNk : 2 * k + 2 ≤ N) {Wn : Finset ℂ}
    (hWn : ∀ ρ, ρ ∈ Wn ↔ ρ ∈ Z.carrier ∧ ρ₀.im - H < ρ.im ∧ ρ.im ≤ ρ₀.im + H)
    {S Kw : Finset ℂ} {X y₀ lam cΨ : ℝ}
    (hX0 : 0 < X) (hX34 : X ≤ 3 / 4) (hy0 : 0 < y₀) (hy : y₀ ≤ 1 / 2) (hy1 : δ / 4 ≤ y₀)
    (hSg : ∀ s ∈ S, |s.re| < X ∧ y₀ < |s.im| ∧ |s.im| ≤ 1 / 2)
    (hKg : ∀ r ∈ Kw, (X < |r.re| ∨ |r.im| < y₀) ∧ |r.re| ≤ H ∧ |r.im| ≤ 1 / 2)
    (hKc : ∀ r ∈ Kw, conj r ∈ Kw) (hSc : ∀ s ∈ S, conj s ∈ S) (hSH : ∀ s ∈ S, |s.re| ≤ H)
    (hx₀S : -(I * (δ : ℂ)) ∈ S) (hcardSK : Kw.card + S.card ≤ k)
    (hlam : 0 < lam) (hcΨ : 0 < cΨ)
    (hlamS : ∀ t, OnSides X y₀ t → lam ≤
      ‖(killPoly (insert (⟨-ρ₀.im, 1 / 2⟩ : ℂ) Kw)).eval t‖ * ‖eval t (nodal S id)‖)
    (hΨside : ∀ t, OnSides X y₀ t → cΨ ≤ ‖cosShiftWeight c N t‖)
    (hclass : ∀ ρ ∈ Wn, gammaOf ρ - ρ₀.im ∈ S ∨ gammaOf ρ - ρ₀.im ∈ Kw ∨
      |(gammaOf ρ - ρ₀.im).im| < δ / 8)
    (hbig : (4 * ((|ρ₀.im| + 1) ^ 2 * (H + 1) ^ (2 * k) / lam * (Real.cosh (c / 2) / cΨ)) ^ 2 *
          (Real.exp (1 / 2) * 168) ^ (2 * N) / (1 + H) ^ (4 * N - 4 * k - 7) +
        (2 * ((|ρ₀.im| + H + 1) ^ 2 * (2 * H + 2) ^ (2 * k) / (lam * (δ / 8)) *
          (Real.cosh (c * (δ / 8)) * (unitMass * Real.exp (δ / 8)) ^ N / cΨ))) ^ 2 *
          (1 + H) ^ 3) * (24 * A₀ * Real.log (|ρ₀.im| + 3)) < 2) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0 ∧ (Z.W f f).re < 0 := by
  classical
  have hH0 : 0 ≤ H := by linarith
  obtain ⟨p, hpdef⟩ : ∃ p : ℂ, p = ⟨-ρ₀.im, 1 / 2⟩ := ⟨_, rfl⟩
  rw [← hpdef] at hlamS
  have hpre : |p.re| = |ρ₀.im| := by rw [hpdef]; simp
  have hpim : |p.im| ≤ 1 / 2 := by rw [hpdef]; simp
  have hpK : p ∉ Kw := by
    intro h
    have := (hKg p h).2.1
    linarith
  have hξre : ∀ ρ : ℂ, (gammaOf ρ - ρ₀.im).re = ρ.im - ρ₀.im := fun ρ => by
    simp [WeilEF.gammaOf_re]
  have hξim : ∀ ρ : ℂ, (gammaOf ρ - ρ₀.im).im = 1 / 2 - ρ.re := fun ρ => by
    simp [WeilEF.gammaOf_im]
  have hξrefl : ∀ ρ : ℂ, gammaOf (Zeta23.reflect ρ) - ρ₀.im = conj (gammaOf ρ - ρ₀.im) := by
    intro ρ
    apply Complex.ext
    · rw [hξre, Complex.conj_re, hξre, reflect_im']
    · rw [hξim, Complex.conj_im, hξim, reflect_re']; ring
  have hx₀ : gammaOf ρ₀ - ρ₀.im = -(I * δ) :=
    (gammaOf_sub_of_re_im (ρ := ρ₀) (γ₀ := ρ₀.im) rfl hre).1
  have hwinb : ∀ ρ ∈ Wn, |(gammaOf ρ - ρ₀.im).re| ≤ H ∧ |(gammaOf ρ - ρ₀.im).im| ≤ 1 / 2 := by
    intro ρ hρ
    obtain ⟨hρZ, h1, h2⟩ := (hWn ρ).mp hρ
    have hs := Z.strip ρ hρZ
    rw [hξre, hξim]
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hconjabs : ∀ v : ℂ, |(conj v).re| = |v.re| ∧ |(conj v).im| = |v.im| := fun v => by
    rw [Complex.conj_re, Complex.conj_im, abs_neg]; exact ⟨rfl, rfl⟩
  have hSim : ∀ s ∈ S, s.im ≠ 0 := by
    intro s hs h
    have := (hSg s hs).2.1
    rw [h, abs_zero] at this
    linarith
  have hSne : S.Nonempty := ⟨_, hx₀S⟩
  -- the profile at the nodes and the killed values
  have hKcard : (insert p Kw).card = Kw.card + 1 := Finset.card_insert_of_notMem hpK
  have hPs : ∀ s ∈ S, (killPoly (insert p Kw)).eval s ≠ 0 := by
    intro s hs
    obtain ⟨h1, h2, -⟩ := hSg s hs
    have hfar : ∀ q : ℂ, (X < |q.re| ∨ |q.im| < y₀) → s ≠ q := by
      intro q hq hsq
      rw [← hsq] at hq
      rcases hq with h | h <;> linarith
    refine killPoly_eval_ne_zero fun r hr => ?_
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ⟨hfar _ (Or.inl (by rw [hpre]; linarith)),
        hfar _ (Or.inl (by rw [(hconjabs _).1, hpre]; linarith))⟩
    · exact ⟨hfar r (hKg r hr).1,
        hfar _ (by rw [(hconjabs r).1, (hconjabs r).2]; exact (hKg r hr).1)⟩
  have hΨs : ∀ s ∈ S, cosShiftWeight c N s ≠ 0 := fun s hs =>
    cosShiftWeight_ne_zero hc hX0.le (by linarith) (hSg s hs).1.le (hSim s hs)
  have hnodeval : ∀ s ∈ S, wProfile (insert p Kw) S (cosShiftWeight c N) s =
      if s.im < 0 then I else -I :=
    fun s hs => wProfile_node hs (hPs s hs) (hΨs s hs)
  have hnodesq : ∀ s ∈ S, wProfile (insert p Kw) S (cosShiftWeight c N) s ^ 2 = -1 := by
    intro s hs
    rw [hnodeval s hs]
    split_ifs
    · rw [sq, Complex.I_mul_I]
    · rw [neg_sq, sq, Complex.I_mul_I]
  have hkill : ∀ r ∈ Kw, wProfile (insert p Kw) S (cosShiftWeight c N) r = 0 :=
    fun r hr => (wProfile_killed _ S _ (Finset.mem_insert_of_mem hr)).1
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = wQ (insert p Kw) S (cosShiftWeight c N) := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := by
    intro h
    have hv := hnodeval _ hx₀S
    rw [wProfile, ← hQdef, h, eval_zero, mul_zero] at hv
    have him : (-(I * (δ : ℂ))).im < 0 := by simp; linarith
    rw [if_pos him] at hv
    exact Complex.I_ne_zero hv.symm
  have hdeg : Q.natDegree + 1 ≤ N := by
    have : Q.natDegree < 2 * (insert p Kw).card + S.card := by
      rw [hQdef]; exact natDegree_wQ_lt _ S _ hSne
    rw [hKcard] at this
    omega
  have hQreal : ∀ n, conj (Q.coeff n) = Q.coeff n := by
    rw [hQdef]; exact wQ_real (conj_cosShiftWeight_conj c N) hSc hSim
  obtain ⟨q, hqℓ⟩ : ∃ q : ℝ, (q : ℂ) = Q.leadingCoeff :=
    ⟨_, Complex.conj_eq_iff_re.mp (hQreal Q.natDegree)⟩
  have hq0 : q ≠ 0 := by
    intro h; apply leadingCoeff_ne_zero.mpr hQ0; rw [← hqℓ, h, Complex.ofReal_zero]
  have hprof : ∀ x, Complex.cos (c * x) * polyProfile (sinhTestWeight 1) N Q x =
      wProfile (insert p Kw) S (cosShiftWeight c N) x / q := by
    intro x
    rw [polyProfile_eq _ N hQ0, wProfile, ← hQdef, cosShiftWeight, hqℓ]
    unfold unitHat
    ring
  -- the test
  obtain ⟨hfc, hfs, hff⟩ := cosPolyTest_props (sinhTestWeight_contDiff 1) (sinhTestWeight_even 1)
    (sinhTestWeight_supp zero_le_one) ρ₀.im hc.le hdeg
  have hpolar : Q.eval p = 0 ∧ Q.eval (conj p) = 0 := by
    rw [hQdef, wQ, eval_mul, eval_mul, eval_killPoly, eval_killPoly]
    constructor
    · rw [Finset.prod_eq_zero (Finset.mem_insert_self p Kw) (by ring), zero_mul]
    · rw [Finset.prod_eq_zero (Finset.mem_insert_self p Kw) (by rw [sub_self, mul_zero]),
        zero_mul]
  refine ⟨cosPolyTest ρ₀.im c (sinhTestWeight 1) N Q, hfc, ?_, ?_, ?_, ?_⟩
  · refine tsupport_subset_of_support_subset_abs fun u hu => ?_
    have := hfs u hu
    linarith
  · refine cosPolyTest_polar_zero (sinhTestWeight_contDiff 1) (sinhTestWeight_even 1)
      (sinhTestWeight_supp zero_le_one) ρ₀.im hc.le hQ0 hdeg ?_
    have e : I / 2 - (ρ₀.im : ℂ) = p := by rw [hpdef]; apply Complex.ext <;> simp
    rw [e]; exact hpolar.1
  · refine cosPolyTest_polar_zero (sinhTestWeight_contDiff 1) (sinhTestWeight_even 1)
      (sinhTestWeight_supp zero_le_one) ρ₀.im hc.le hQ0 hdeg ?_
    have e : -(I / 2) - (ρ₀.im : ℂ) = conj p := by rw [hpdef]; apply Complex.ext <;> simp
    rw [e]; exact hpolar.2
  -- the Weil form
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ → ℂ, ∀ ρ, Φ ρ = wProfile (insert p Kw) S (cosShiftWeight c N)
      (gammaOf ρ - ρ₀.im) := ⟨_, fun ρ => rfl⟩
  have hWs : ∀ ρ : ℂ, Z.Wsummand (cosPolyTest ρ₀.im c (sinhTestWeight 1) N Q)
      (cosPolyTest ρ₀.im c (sinhTestWeight 1) N Q) ρ =
        (Z.mult ρ : ℂ) * (Φ ρ / q) ^ 2 := by
    intro ρ
    rw [Wsummand_cosPolyTest (sinhTestWeight_contDiff 1) (sinhTestWeight_even 1)
      (sinhTestWeight_supp zero_le_one) Z ρ₀.im hc.le hQ0 hQreal hdeg ρ, hprof, hΦ]
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0
  have hre_s : ∀ ρ : ℂ, (Z.Wsummand (cosPolyTest ρ₀.im c (sinhTestWeight 1) N Q)
      (cosPolyTest ρ₀.im c (sinhTestWeight 1) N Q) ρ).re =
        (Z.mult ρ : ℝ) * (Φ ρ ^ 2).re / q ^ 2 := by
    intro ρ
    have e : (Z.mult ρ : ℂ) * (Φ ρ / q) ^ 2 = (((Z.mult ρ : ℝ) / q ^ 2 : ℝ) : ℂ) * Φ ρ ^ 2 := by
      push_cast; field_simp
    rw [hWs, e, Complex.re_ofReal_mul]; ring
  have hnorm_s : ∀ ρ : ℂ, ‖Z.Wsummand (cosPolyTest ρ₀.im c (sinhTestWeight 1) N Q)
      (cosPolyTest ρ₀.im c (sinhTestWeight 1) N Q) ρ‖ =
        (Z.mult ρ : ℝ) * ‖Φ ρ‖ ^ 2 / q ^ 2 := by
    intro ρ
    rw [hWs, norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, div_pow, sq_abs]
    ring
  obtain ⟨Cu, hCudef⟩ : ∃ Cu : ℝ, Cu = 2 * ((|ρ₀.im| + H + 1) ^ 2 * (2 * H + 2) ^ (2 * k) /
      (lam * (δ / 8)) * (Real.cosh (c * (δ / 8)) * (unitMass * Real.exp (δ / 8)) ^ N / cΨ)) :=
    ⟨_, rfl⟩
  rw [← hCudef] at hbig
  have hwin : ∀ ρ ∈ Wn, (Φ ρ ^ 2).re ≤ Cu ^ 2 ∧ ‖Φ ρ‖ ^ 2 ≤ 1 + Cu ^ 2 := by
    intro ρ hρ
    rcases hclass ρ hρ with hvS | hvK | hshallow
    · have h := hnodesq _ hvS
      rw [hΦ, h]
      refine ⟨by simp; nlinarith [sq_nonneg Cu], ?_⟩
      rw [← norm_pow, h, norm_neg, norm_one]
      nlinarith [sq_nonneg Cu]
    · have h := hkill _ hvK
      rw [hΦ, h]
      refine ⟨by simp; positivity, by simp; positivity⟩
    · have hb := norm_wProfile_window_le (S := S) (Kw := Kw) (p := p)
        (x := gammaOf ρ - ρ₀.im) (N := N) (k := k) hX0 hX34 hy0 hy hδ hy1 hc hH0 hSg hKg hKc
        hSH (by rw [hpre]; linarith) hpim hpK hcardSK hlam hcΨ hlamS hΨside (hwinb ρ hρ).1
        hshallow
      rw [hpre, ← hCudef] at hb
      rw [← hΦ] at hb
      have hn0 : 0 ≤ ‖Φ ρ‖ := norm_nonneg _
      have hsq : ‖Φ ρ‖ ^ 2 ≤ Cu ^ 2 := pow_le_pow_left₀ hn0 hb 2
      refine ⟨?_, by linarith⟩
      calc (Φ ρ ^ 2).re ≤ ‖Φ ρ ^ 2‖ := Complex.re_le_norm _
        _ = ‖Φ ρ‖ ^ 2 := norm_pow _ _
        _ ≤ Cu ^ 2 := hsq
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁ : ℝ, C₁ = 4 * ((|ρ₀.im| + 1) ^ 2 * (H + 1) ^ (2 * k) / lam *
      (Real.cosh (c / 2) / cΨ)) ^ 2 * (Real.exp (1 / 2) * 168) ^ (2 * N) := ⟨_, rfl⟩
  rw [← hC₁def] at hbig
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁def]; positivity
  have hE3 : 4 * N - 4 * k - 4 = 3 + (4 * N - 4 * k - 7) := by omega
  have hfar : ∀ ρ ∈ Z.carrier, ρ ∉ Wn →
      H ≤ |ρ.im - ρ₀.im| ∧ ‖Φ ρ‖ ^ 2 * (1 + |ρ.im - ρ₀.im|) ^ (3 + (4 * N - 4 * k - 7)) ≤ C₁ := by
    intro ρ hρZ hρW
    have hfarH : H ≤ |ρ.im - ρ₀.im| := by
      have hnot : ¬ (ρ₀.im - H < ρ.im ∧ ρ.im ≤ ρ₀.im + H) :=
        fun h => hρW ((hWn _).mpr ⟨hρZ, h⟩)
      rw [not_and_or, not_lt, not_le] at hnot
      rcases hnot with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    refine ⟨hfarH, ?_⟩
    have hs := Z.strip ρ hρZ
    have hxi : |(gammaOf ρ - ρ₀.im).im| ≤ 1 / 2 := by
      rw [hξim]; exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hb := norm_sq_wProfile_far_le (S := S) (Kw := Kw) (p := p) (x := gammaOf ρ - ρ₀.im)
      (N := N) (k := k) hX0 hX34 hy0 hy hc hH hSg hKg hKc hSH (by rw [hpre]; linarith) hpim hpK
      hcardSK hlam hcΨ hlamS hΨside hNk (by rw [hξre]; exact hfarH) hxi
    rw [hξre, hE3, hpre, ← hC₁def, ← hΦ] at hb
    exact hb
  have hΦ₀ : Φ ρ₀ ^ 2 = -1 := by
    rw [hΦ, hx₀]; exact hnodesq _ hx₀S
  have hΦ₁ : Φ (Zeta23.reflect ρ₀) ^ 2 = -1 := by
    rw [hΦ, hξrefl, hx₀]; exact hnodesq _ (hSc _ hx₀S)
  exact re_W_neg_of_window_profile_gen Z hA₀ hloc hρ₀ hδ hre (by linarith) hWn hq0
    hre_s hnorm_s hwin hC₁0 hfar hΦ₀ hΦ₁ hbig

/-- The constant of the zeros outside the window. -/
def resolutionFarConstant (γ₀ δ H c : ℝ) (N k : ℕ) : ℝ :=
  4 * ((|γ₀| + 1) ^ 2 * (H + 1) ^ (2 * k) /
      ((|γ₀| - 1) ^ 2 * (δ / (32 * Real.exp 1)) ^ (2 * k)) *
    (Real.cosh (c / 2) /
      (Real.sinh (c * (δ / 4)) * (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N))) ^ 2 *
    (Real.exp (1 / 2) * 168) ^ (2 * N)

/-- The bound for the window zeros left unkilled. -/
def resolutionWindowConstant (γ₀ δ H c : ℝ) (N k : ℕ) : ℝ :=
  2 * ((|γ₀| + H + 1) ^ 2 * (2 * H + 2) ^ (2 * k) /
      ((|γ₀| - 1) ^ 2 * (δ / (32 * Real.exp 1)) ^ (2 * k) * (δ / 8)) *
    (Real.cosh (c * (δ / 8)) * (unitMass * Real.exp (δ / 8)) ^ N /
      (Real.sinh (c * (δ / 4)) * (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N)))

/-- **The localized resolution law.**  Let `Z` have local count `N(t, t+1] ≤ A₀ log(|t| + 3)` and
let `ρ₀ = ½ + δ + iγ₀` be a zero with `|γ₀| ≥ H + 3`, `H ≥ 2`.  If at most `k` zeros of the window
`γ₀ - H < γ ≤ γ₀ + H` have depth `≥ δ/8`, `2k + 2 ≤ N`, `N + c ≤ a`, and
`(C_far/(1 + H)^{4N-4k-7} + C_win² (1 + H)³) · 24 A₀ log(|γ₀| + 3) < 2`, then the level-`a` Hodge
index fails. -/
theorem exists_hodge_violation_resolution (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {H a c : ℝ} (hH : 2 ≤ H) (hγ : H + 3 ≤ |ρ₀.im|) (hc : 0 < c) {N k : ℕ}
    (hNa : (N : ℝ) + c ≤ a)
    (hk : ((Z.finite_window (ρ₀.im - H) (ρ₀.im + H)).toFinset.filter
      (fun ρ => δ / 8 ≤ |ρ.re - 1 / 2|)).card ≤ k) (hNk : 2 * k + 2 ≤ N)
    (hbig : (resolutionFarConstant ρ₀.im δ H c N k / (1 + H) ^ (4 * N - 4 * k - 7) +
        resolutionWindowConstant ρ₀.im δ H c N k ^ 2 * (1 + H) ^ 3) *
      (24 * A₀ * Real.log (|ρ₀.im| + 3)) < 2) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0 ∧ (Z.W f f).re < 0 := by
  classical
  set γ₀ := ρ₀.im with hγ₀
  have hst := Z.strip ρ₀ hρ₀
  have hδ2 : δ ≤ 1 / 2 := by linarith [hst.2]
  have hH0 : 0 ≤ H := by linarith
  set Wn := (Z.finite_window (γ₀ - H) (γ₀ + H)).toFinset with hWndef
  have hWn : ∀ ρ, ρ ∈ Wn ↔ ρ ∈ Z.carrier ∧ γ₀ - H < ρ.im ∧ ρ.im ≤ γ₀ + H := by
    intro ρ; rw [hWndef, Set.Finite.mem_toFinset]; rfl
  have hξre : ∀ ρ : ℂ, (gammaOf ρ - γ₀).re = ρ.im - γ₀ := fun ρ => by
    simp [WeilEF.gammaOf_re]
  have hξim : ∀ ρ : ℂ, (gammaOf ρ - γ₀).im = 1 / 2 - ρ.re := fun ρ => by
    simp [WeilEF.gammaOf_im]
  have hξrefl : ∀ ρ : ℂ, gammaOf (Zeta23.reflect ρ) - γ₀ = conj (gammaOf ρ - γ₀) := by
    intro ρ
    apply Complex.ext
    · rw [hξre, Complex.conj_re, hξre, reflect_im']
    · rw [hξim, Complex.conj_im, hξim, reflect_re']; ring
  -- the deep window values
  set D := (Wn.image (fun ρ => gammaOf ρ - γ₀)).filter (fun v => δ / 8 ≤ |v.im|) with hDdef
  have hDmem : ∀ v, v ∈ D ↔ (∃ ρ ∈ Wn, gammaOf ρ - γ₀ = v) ∧ δ / 8 ≤ |v.im| := by
    intro v; rw [hDdef, Finset.mem_filter, Finset.mem_image]
  have hconjabs : ∀ v : ℂ, |(conj v).re| = |v.re| ∧ |(conj v).im| = |v.im| := fun v => by
    rw [Complex.conj_re, Complex.conj_im, abs_neg]; exact ⟨rfl, rfl⟩
  have hDc : ∀ v ∈ D, conj v ∈ D := by
    intro v hv
    obtain ⟨⟨ρ, hρ, rfl⟩, hdeep⟩ := (hDmem v).mp hv
    obtain ⟨hρZ, h1, h2⟩ := (hWn ρ).mp hρ
    refine (hDmem _).mpr ⟨⟨Zeta23.reflect ρ, (hWn _).mpr ⟨Z.reflect_mem ρ hρZ, ?_, ?_⟩,
      hξrefl ρ⟩, by rw [(hconjabs _).2]; exact hdeep⟩
    · rw [reflect_im']; exact h1
    · rw [reflect_im']; exact h2
  have hwinb : ∀ ρ ∈ Wn, |(gammaOf ρ - γ₀).re| ≤ H ∧ |(gammaOf ρ - γ₀).im| ≤ 1 / 2 := by
    intro ρ hρ
    obtain ⟨hρZ, h1, h2⟩ := (hWn ρ).mp hρ
    have hs := Z.strip ρ hρZ
    rw [hξre, hξim]
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hDb : ∀ v ∈ D, |v.re| ≤ H ∧ |v.im| ≤ 1 / 2 := by
    intro v hv
    obtain ⟨⟨ρ, hρ, rfl⟩, -⟩ := (hDmem v).mp hv
    exact hwinb ρ hρ
  have hDcard : D.card ≤ k := by
    refine le_trans ?_ hk
    refine le_trans (Finset.card_le_card (t := (Wn.filter (fun ρ => δ / 8 ≤ |ρ.re - 1 / 2|)).image
      (fun ρ => gammaOf ρ - γ₀)) ?_) Finset.card_image_le
    · intro v hv
      obtain ⟨⟨ρ, hρ, rfl⟩, hdeep⟩ := (hDmem v).mp hv
      refine Finset.mem_image.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hρ, ?_⟩, rfl⟩
      rw [hξim, abs_sub_comm] at hdeep
      exact hdeep
  have hρ₀W : ρ₀ ∈ Wn := (hWn ρ₀).mpr ⟨hρ₀, by linarith, by linarith⟩
  have hx₀ : gammaOf ρ₀ - γ₀ = -(I * δ) :=
    (gammaOf_sub_of_re_im (ρ := ρ₀) (γ₀ := γ₀) rfl hre).1
  have hx₀D : -(I * (δ : ℂ)) ∈ D := by
    refine (hDmem _).mpr ⟨⟨ρ₀, hρ₀W, hx₀⟩, ?_⟩
    simp [abs_of_pos hδ]; linarith
  -- the contour
  obtain ⟨X, y₀, hX1, hX2, hy1, hy2, hDne, hside⟩ :=
    resolution_selection (D := D) hδ (by linarith) (fun v hv => (hDb v hv).2)
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hsδ1 : Real.sqrt δ ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  have hX0 : 0 < X := by linarith
  have hX34 : X ≤ 3 / 4 := by linarith
  have hy0 : 0 < y₀ := by linarith
  set S := D.filter (fun v => |v.re| < X ∧ y₀ < |v.im|) with hSdef
  set Kw := D.filter (fun v => ¬ (|v.re| < X ∧ y₀ < |v.im|)) with hKwdef
  have hDSK : D = S ∪ Kw := (Finset.filter_union_filter_not_eq _ D).symm
  have hdisj : Disjoint S Kw := Finset.disjoint_filter_filter_not D D _
  have hKc : ∀ r ∈ Kw, conj r ∈ Kw := by
    intro r hr
    rw [hKwdef, Finset.mem_filter] at hr ⊢
    rw [(hconjabs r).1, (hconjabs r).2]
    exact ⟨hDc r hr.1, hr.2⟩
  have hSc : ∀ s ∈ S, conj s ∈ S := by
    intro s hs
    rw [hSdef, Finset.mem_filter] at hs ⊢
    rw [(hconjabs s).1, (hconjabs s).2]
    exact ⟨hDc s hs.1, hs.2⟩
  have hSg : ∀ s ∈ S, |s.re| < X ∧ y₀ < |s.im| ∧ |s.im| ≤ 1 / 2 := by
    intro s hs
    rw [hSdef, Finset.mem_filter] at hs
    exact ⟨hs.2.1, hs.2.2, (hDb s hs.1).2⟩
  have hSH : ∀ s ∈ S, |s.re| ≤ H := by
    intro s hs; rw [hSdef, Finset.mem_filter] at hs; exact (hDb s hs.1).1
  have hKg : ∀ r ∈ Kw, (X < |r.re| ∨ |r.im| < y₀) ∧ |r.re| ≤ H ∧ |r.im| ≤ 1 / 2 := by
    intro r hr
    rw [hKwdef, Finset.mem_filter] at hr
    obtain ⟨hne1, hne2⟩ := hDne r hr.1
    refine ⟨?_, hDb r hr.1⟩
    have h := hr.2
    rw [not_and_or, not_lt, not_lt] at h
    rcases h with h | h
    · exact Or.inl (lt_of_le_of_ne h (Ne.symm hne1))
    · exact Or.inr (lt_of_le_of_ne h hne2)
  have hSim : ∀ s ∈ S, s.im ≠ 0 := by
    intro s hs h
    have := (hSg s hs).2.1
    rw [h, abs_zero] at this
    linarith
  have hx₀S : -(I * (δ : ℂ)) ∈ S := by
    rw [hSdef, Finset.mem_filter]
    refine ⟨hx₀D, ?_, ?_⟩
    · simp; linarith
    · simp [abs_of_pos hδ]; linarith
  have hSne : S.Nonempty := ⟨_, hx₀S⟩
  have hcardSK : Kw.card + S.card ≤ k := by
    have := Finset.card_union_of_disjoint hdisj
    rw [← hDSK] at this
    omega
  -- the polar point
  set p : ℂ := ⟨-γ₀, 1 / 2⟩ with hpdef
  have hpre : |p.re| = |γ₀| := by simp [hpdef]
  have hp : H + 2 ≤ |p.re| := by rw [hpre]; linarith
  have hpim : |p.im| ≤ 1 / 2 := by simp [hpdef]
  have hpK : p ∉ Kw := by
    intro h
    have := (hKg p h).2.1
    linarith
  set K := insert p Kw with hKdef
  -- the weight and the side bounds
  set Ψ := cosShiftWeight c N with hΨdef
  set lam := (|γ₀| - 1) ^ 2 * (δ / (32 * Real.exp 1)) ^ (2 * k) with hlamdef
  have hlam : 0 < lam := by
    rw [hlamdef]
    have : 0 < |γ₀| - 1 := by linarith
    positivity
  have hlamS : ∀ t, OnSides X y₀ t →
      lam ≤ ‖(killPoly (insert p Kw)).eval t‖ * ‖eval t (nodal S id)‖ := by
    intro t ht
    have h := border_lower_bound_polar (D := D) (S := S) (Kw := Kw) (X := X) (y₀ := y₀) (H := H)
      (b := δ / (16 * Real.exp 1)) (p := p) (k := k) (by positivity) (by
        rw [div_le_one (by positivity)]
        have := Real.add_one_le_exp 1
        linarith) hX34 (by linarith) hH0 hDSK hdisj hKc
      (fun s hs => ⟨(hSg s hs).1, (hSg s hs).2.2⟩) (fun v hv => (hDb v hv).1) hp hDcard
      hside t ht
    refine le_trans (le_of_eq ?_) h
    rw [hlamdef, hpre]
    congr 1
    rw [pow_mul]
    congr 1
    field_simp
    ring
  set cΨ := Real.sinh (c * (δ / 4)) * (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N with hcΨdef
  have hcos0 : 0 < Real.cos (Real.sqrt δ / 4) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  have hcΨ : 0 < cΨ := by
    rw [hcΨdef]
    have := unitMass_pos
    have : 0 < Real.sinh (c * (δ / 4)) := Real.sinh_pos_iff.mpr (by positivity)
    positivity
  have hΨside : ∀ t, OnSides X y₀ t → cΨ ≤ ‖Ψ t‖ := by
    intro t ht
    have htr := OnSides.re_le (y₀ := y₀) ht
    have hti := (OnSides.im_ge (X := X) (by linarith) ht).1
    have h := norm_cosShiftWeight_ge (N := N) hc.le hX0.le (by linarith) hy0.le htr hti
    refine le_trans ?_ h
    rw [hcΨdef]
    have hs1 : Real.sinh (c * (δ / 4)) ≤ Real.sinh (c * y₀) :=
      Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hy1 hc.le)
    have hc1 : Real.cos (Real.sqrt δ / 4) ≤ Real.cos X :=
      Real.cos_le_cos_of_nonneg_of_le_pi hX0.le (by linarith [Real.pi_gt_three]) hX2
    have hm := unitMass_pos
    have : 0 ≤ Real.sinh (c * (δ / 4)) := (Real.sinh_pos_iff.mpr (by positivity)).le
    gcongr
  have hclass : ∀ ρ ∈ Wn, gammaOf ρ - ρ₀.im ∈ S ∨ gammaOf ρ - ρ₀.im ∈ Kw ∨
      |(gammaOf ρ - ρ₀.im).im| < δ / 8 := by
    intro ρ hρ
    by_cases hvD : gammaOf ρ - γ₀ ∈ D
    · rw [hDSK, Finset.mem_union] at hvD
      rcases hvD with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · right; right
      by_contra hge
      exact hvD ((hDmem _).mpr ⟨⟨ρ, hρ, rfl⟩, le_of_not_gt hge⟩)
  refine resolution_test_negative Z hA₀ hloc hρ₀ hδ hre hH hγ hc hNa hNk hWn hX0 hX34 hy0
    (by linarith) hy1 hSg hKg hKc hSc hSH hx₀S hcardSK hlam hcΨ hlamS hΨside hclass ?_
  unfold resolutionFarConstant resolutionWindowConstant at hbig
  rw [hlamdef, hcΨdef]
  exact hbig

/-! ### The size condition -/

theorem cosh_le_exp_abs' (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
    have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
    linarith
  · rw [abs_of_nonpos h]
    have : Real.exp x ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    linarith

theorem exp_div_four_le_sinh_of_half {y : ℝ} (hy : 1 / 2 ≤ y) : Real.exp y / 4 ≤ Real.sinh y := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have h2 : 2 ≤ Real.exp y * Real.exp y := by
    rw [← Real.exp_add]
    have := Real.add_one_le_exp (y + y)
    linarith
  have hpos := Real.exp_pos y
  have h3 : Real.exp (-y) ≤ Real.exp y / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  linarith

theorem exp_neg_le_cos_sqrt {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    Real.exp (-(δ / 16)) ≤ Real.cos (Real.sqrt δ / 4) := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt δ / 4)
  rw [div_pow, Real.sq_sqrt hδ0] at h1
  have h2 : Real.exp (-(δ / 16)) ≤ 1 - δ / 32 := by
    have h3 := Real.add_one_le_exp (δ / 16)
    have h4 : Real.exp (-(δ / 16)) * Real.exp (δ / 16) = 1 := by rw [← Real.exp_add]; simp
    have h5 := Real.exp_pos (-(δ / 16))
    nlinarith
  linarith

theorem unitMass_ge : (48 / 100 : ℝ) ≤ unitMass :=
  unitWeightFloor_ge.trans unitWeightFloor_le_unitMass

theorem resolutionWindowConstant_le {γ δ c : ℝ} {N k : ℕ} (hγ : 103 ≤ |γ|) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hc : 2 ≤ c * δ) :
    resolutionWindowConstant γ δ 100 c N k ≤
      256 / δ * (2 * 10 ^ 4 / δ) ^ (2 * k) *
        Real.exp (-(c * δ / 8) + 3 * N * δ / 16) := by
  unfold resolutionWindowConstant
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hm := unitMass_ge
  have hm0 : 0 < unitMass := by linarith
  have hγ1 : 0 < |γ| - 1 := by linarith
  have hcos := exp_neg_le_cos_sqrt hδ.le hδ2
  have hcos0 : 0 < Real.cos (Real.sqrt δ / 4) := lt_of_lt_of_le (Real.exp_pos _) hcos
  have X1 : (|γ| + 100 + 1) ^ 2 ≤ 4 * (|γ| - 1) ^ 2 := by nlinarith
  have X2 : (2 * 100 + 2 : ℝ) ^ (2 * k) ≤
      (2 * 10 ^ 4 / δ) ^ (2 * k) * (δ / (32 * Real.exp 1)) ^ (2 * k) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by norm_num) ?_ _
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    nlinarith
  have hsinh := exp_div_four_le_sinh_of_half (show 1 / 2 ≤ c * (δ / 4) by nlinarith)
  have hcosh := cosh_le_exp_abs' (c * (δ / 8))
  rw [abs_of_nonneg (by nlinarith)] at hcosh
  have X4 : Real.cosh (c * (δ / 8)) ≤ 4 * Real.exp (-(c * δ / 8)) * Real.sinh (c * (δ / 4)) := by
    have e : Real.exp (c * (δ / 8)) =
        4 * Real.exp (-(c * δ / 8)) * (Real.exp (c * (δ / 4)) / 4) := by
      rw [show 4 * Real.exp (-(c * δ / 8)) * (Real.exp (c * (δ / 4)) / 4) =
        Real.exp (-(c * δ / 8)) * Real.exp (c * (δ / 4)) by ring, ← Real.exp_add]
      congr 1; ring
    calc Real.cosh (c * (δ / 8)) ≤ Real.exp (c * (δ / 8)) := hcosh
      _ = 4 * Real.exp (-(c * δ / 8)) * (Real.exp (c * (δ / 4)) / 4) := e
      _ ≤ 4 * Real.exp (-(c * δ / 8)) * Real.sinh (c * (δ / 4)) := by gcongr
  have X5 : (unitMass * Real.exp (δ / 8)) ^ N ≤
      Real.exp (3 * N * δ / 16) * (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N := by
    have e3 : Real.exp (3 * N * δ / 16) = Real.exp (3 * δ / 16) ^ N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [e3, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    have h1 : Real.exp (δ / 8) = Real.exp (3 * δ / 16) * Real.exp (-(δ / 16)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1]
    have : 0 < Real.exp (3 * δ / 16) := Real.exp_pos _
    calc unitMass * (Real.exp (3 * δ / 16) * Real.exp (-(δ / 16)))
        = Real.exp (3 * δ / 16) * (Real.exp (-(δ / 16)) * unitMass) := by ring
      _ ≤ Real.exp (3 * δ / 16) * (Real.cos (Real.sqrt δ / 4) * unitMass) := by gcongr
  have hs0 : 0 < Real.sinh (c * (δ / 4)) := Real.sinh_pos_iff.mpr (by nlinarith)
  have hden : 0 < (|γ| - 1) ^ 2 * (δ / (32 * Real.exp 1)) ^ (2 * k) * (δ / 8) := by positivity
  have hden2 : 0 < Real.sinh (c * (δ / 4)) * (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N := by
    positivity
  have hA : (|γ| + 100 + 1) ^ 2 * (2 * 100 + 2) ^ (2 * k) /
      ((|γ| - 1) ^ 2 * (δ / (32 * Real.exp 1)) ^ (2 * k) * (δ / 8)) ≤
        4 * (2 * 10 ^ 4 / δ) ^ (2 * k) * (8 / δ) := by
    rw [div_le_iff₀ hden]
    calc (|γ| + 100 + 1) ^ 2 * (2 * 100 + 2 : ℝ) ^ (2 * k)
        ≤ (4 * (|γ| - 1) ^ 2) * ((2 * 10 ^ 4 / δ) ^ (2 * k) * (δ / (32 * Real.exp 1)) ^ (2 * k)) :=
          mul_le_mul X1 X2 (by positivity) (by positivity)
      _ = 4 * (2 * 10 ^ 4 / δ) ^ (2 * k) * (8 / δ) *
          ((|γ| - 1) ^ 2 * (δ / (32 * Real.exp 1)) ^ (2 * k) * (δ / 8)) := by
          field_simp
  have hB : Real.cosh (c * (δ / 8)) * (unitMass * Real.exp (δ / 8)) ^ N /
      (Real.sinh (c * (δ / 4)) * (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N) ≤
        4 * Real.exp (-(c * δ / 8)) * Real.exp (3 * N * δ / 16) := by
    rw [div_le_iff₀ hden2]
    calc Real.cosh (c * (δ / 8)) * (unitMass * Real.exp (δ / 8)) ^ N
        ≤ (4 * Real.exp (-(c * δ / 8)) * Real.sinh (c * (δ / 4))) *
          (Real.exp (3 * N * δ / 16) * (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N) :=
          mul_le_mul X4 X5 (by positivity) (by positivity)
      _ = _ := by ring
  have hA0 : 0 ≤ (|γ| + 100 + 1) ^ 2 * (2 * 100 + 2 : ℝ) ^ (2 * k) /
      ((|γ| - 1) ^ 2 * (δ / (32 * Real.exp 1)) ^ (2 * k) * (δ / 8)) := by positivity
  calc 2 * ((|γ| + 100 + 1) ^ 2 * (2 * 100 + 2) ^ (2 * k) /
        ((|γ| - 1) ^ 2 * (δ / (32 * Real.exp 1)) ^ (2 * k) * (δ / 8)) *
        (Real.cosh (c * (δ / 8)) * (unitMass * Real.exp (δ / 8)) ^ N /
          (Real.sinh (c * (δ / 4)) * (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N)))
      ≤ 2 * ((4 * (2 * 10 ^ 4 / δ) ^ (2 * k) * (8 / δ)) *
          (4 * Real.exp (-(c * δ / 8)) * Real.exp (3 * N * δ / 16))) := by
        gcongr
    _ = 256 / δ * (2 * 10 ^ 4 / δ) ^ (2 * k) * Real.exp (-(c * δ / 8) + 3 * N * δ / 16) := by
        rw [Real.exp_add]; field_simp; ring

theorem exp_half_le : Real.exp (1 / 2) ≤ 165 / 100 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

theorem resolutionFarConstant_div_le {γ δ c : ℝ} {N k : ℕ} (hγ : 103 ≤ |γ|) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hc : 2 ≤ c * δ) (hNk : 2 * k + 2 ≤ N) :
    resolutionFarConstant γ δ 100 c N k / (1 + 100) ^ (4 * N - 4 * k - 7) ≤
      1024 * 101 ^ 7 * (10 ^ 6 / δ) ^ (4 * k) * Real.exp (c - 5 * N) := by
  unfold resolutionFarConstant
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hm := unitMass_ge
  have hm0 : 0 < unitMass := by linarith
  have hγ1 : 0 < |γ| - 1 := by linarith
  have hcos := exp_neg_le_cos_sqrt hδ.le hδ2
  have hcos1 : (96 / 100 : ℝ) ≤ Real.cos (Real.sqrt δ / 4) := by
    refine le_trans ?_ hcos
    have := Real.add_one_le_exp (-(δ / 16))
    linarith
  have hcos0 : 0 < Real.cos (Real.sqrt δ / 4) := by linarith
  have hc0 : 0 < c := by
    by_contra h; push Not at h; nlinarith
  -- the pieces
  have hsinh := exp_div_four_le_sinh_of_half (show 1 / 2 ≤ c * (δ / 4) by nlinarith)
  have hs0 : 0 < Real.sinh (c * (δ / 4)) := Real.sinh_pos_iff.mpr (by nlinarith)
  have hcosh := cosh_le_exp_abs' (c / 2)
  rw [abs_of_pos (by positivity)] at hcosh
  have hsinh1 : 1 / 4 ≤ Real.sinh (c * (δ / 4)) := by
    have := Real.one_le_exp (show 0 ≤ c * (δ / 4) by nlinarith)
    linarith
  set A := (|γ| + 1) ^ 2 * (100 + 1 : ℝ) ^ (2 * k) /
      ((|γ| - 1) ^ 2 * (δ / (32 * Real.exp 1)) ^ (2 * k)) with hAdef
  set B := Real.cosh (c / 2) / (Real.sinh (c * (δ / 4)) *
      (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N) with hBdef
  have hA : A ≤ 4 * (101 * 32 * Real.exp 1 / δ) ^ (2 * k) := by
    rw [hAdef, div_le_iff₀ (by positivity)]
    have X1 : (|γ| + 1) ^ 2 ≤ 4 * (|γ| - 1) ^ 2 := by nlinarith
    have X2 : (100 + 1 : ℝ) ^ (2 * k) =
        (101 * 32 * Real.exp 1 / δ) ^ (2 * k) * (δ / (32 * Real.exp 1)) ^ (2 * k) := by
      rw [← mul_pow]; congr 1; field_simp; ring
    rw [X2]
    calc (|γ| + 1) ^ 2 * ((101 * 32 * Real.exp 1 / δ) ^ (2 * k) * (δ / (32 * Real.exp 1)) ^ (2 * k))
        ≤ (4 * (|γ| - 1) ^ 2) * ((101 * 32 * Real.exp 1 / δ) ^ (2 * k) *
          (δ / (32 * Real.exp 1)) ^ (2 * k)) := by gcongr
      _ = _ := by ring
  have hB : B ≤ 4 * Real.exp (c / 2) / (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N := by
    rw [hBdef, div_le_div_iff₀ (by positivity) (by positivity)]
    calc Real.cosh (c / 2) * (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N
        ≤ Real.exp (c / 2) * (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N := by gcongr
      _ ≤ 4 * Real.exp (c / 2) * (Real.sinh (c * (δ / 4)) *
          (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N) := by
          have : 0 ≤ Real.exp (c / 2) * (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N := by
            positivity
          nlinarith
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hAB : (A * B) ^ 2 ≤ (16 * (101 * 32 * Real.exp 1 / δ) ^ (2 * k) * Real.exp (c / 2) /
      (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    calc A * B ≤ (4 * (101 * 32 * Real.exp 1 / δ) ^ (2 * k)) *
        (4 * Real.exp (c / 2) / (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N) :=
          mul_le_mul hA hB hB0 (by positivity)
      _ = _ := by ring
  -- the ratio `K₀/(101² cos m) ≤ e^{-5/2}`
  have hK : Real.exp (1 / 2) * 168 / (101 ^ 2 * (Real.cos (Real.sqrt δ / 4) * unitMass)) ≤
      Real.exp (-(5 / 2)) := by
    have h1 := exp_half_le
    have h2 : Real.exp (5 / 2) ≤ 14 := by
      have e2 := exp_numeric_bounds.2.2.2.2.1
      have : Real.exp (5 / 2) = Real.exp 2 * Real.exp (1 / 2) := by
        rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith [Real.exp_pos 2, Real.exp_pos (1 / 2)]
    have h3 : Real.exp (-(5 / 2)) * Real.exp (5 / 2) = 1 := by rw [← Real.exp_add]; simp
    have h4 : (1 / 14 : ℝ) ≤ Real.exp (-(5 / 2)) := by
      have := Real.exp_pos (-(5 / 2)); nlinarith
    rw [div_le_iff₀ (by positivity)]
    have : (96 / 100 : ℝ) * (48 / 100) ≤ Real.cos (Real.sqrt δ / 4) * unitMass :=
      mul_le_mul hcos1 hm (by norm_num) hcos0.le
    nlinarith
  have hpow : (Real.exp (1 / 2) * 168) ^ (2 * N) / (101 : ℝ) ^ (4 * N) ≤
      Real.exp (-(5 * N)) * ((Real.cos (Real.sqrt δ / 4) * unitMass) ^ N) ^ 2 := by
    obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = Real.exp (1 / 2) * 168 := ⟨_, rfl⟩
    obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = Real.cos (Real.sqrt δ / 4) * unitMass := ⟨_, rfl⟩
    have hY0 : 0 < Y := by rw [hYdef]; positivity
    have hq : K ^ (2 * N) / (101 : ℝ) ^ (4 * N) = (K / (101 ^ 2 * Y)) ^ (2 * N) * (Y ^ N) ^ 2 := by
      rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, show 2 * (2 * N) = 4 * N by ring,
        show N * 2 = 2 * N by ring]
      field_simp
    rw [← hKdef, ← hYdef, hq]
    rw [← hKdef, ← hYdef] at hK
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hK0 : 0 ≤ K / (101 ^ 2 * Y) := by rw [hKdef]; positivity
    calc (K / (101 ^ 2 * Y)) ^ (2 * N)
        ≤ Real.exp (-(5 / 2)) ^ (2 * N) := pow_le_pow_left₀ hK0 hK _
      _ = Real.exp (-(5 * N)) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsplit : (1 + 100 : ℝ) ^ (4 * N - 4 * k - 7) * 101 ^ (4 * k + 7) = 101 ^ (4 * N) := by
    rw [show (1 + 100 : ℝ) = 101 by norm_num, ← pow_add]; congr 1; omega
  have h101 : (0 : ℝ) < (1 + 100) ^ (4 * N - 4 * k - 7) := by positivity
  rw [div_le_iff₀ h101]
  have hcm : 0 < (Real.cos (Real.sqrt δ / 4) * unitMass) ^ N := by positivity
  have hXe : (101 * 32 * Real.exp 1 / δ) ^ (4 * k) * 101 ^ (4 * k) ≤ (10 ^ 6 / δ) ^ (4 * k) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hδ.le
  have hK2 : (Real.exp (1 / 2) * 168) ^ (2 * N) ≤
      Real.exp (-(5 * N)) * ((Real.cos (Real.sqrt δ / 4) * unitMass) ^ N) ^ 2 * 101 ^ (4 * N) := by
    have h := hpow
    rw [div_le_iff₀ (by positivity)] at h
    exact h
  have hexp : Real.exp (c / 2) ^ 2 * Real.exp (-(5 * N)) = Real.exp (c - 5 * N) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = 101 * 32 * Real.exp 1 / δ := ⟨_, rfl⟩
  rw [← hXdef] at hAB hXe
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = Real.cos (Real.sqrt δ / 4) * unitMass := ⟨_, rfl⟩
  rw [← hYdef] at hAB hK2 hcm
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  clear_value A B
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = 4 * N - 4 * k - 7 := ⟨_, rfl⟩
  rw [← hE] at hsplit ⊢
  have hYN : Y ^ N ≠ 0 := hcm.ne'
  calc 4 * (A * B) ^ 2 * (Real.exp (1 / 2) * 168) ^ (2 * N)
      ≤ 4 * (16 * X ^ (2 * k) * Real.exp (c / 2) / Y ^ N) ^ 2 *
          (Real.exp (-(5 * N)) * (Y ^ N) ^ 2 * 101 ^ (4 * N)) := by
        gcongr
    _ = 1024 * X ^ (4 * k) * (Real.exp (c / 2) ^ 2 * Real.exp (-(5 * N))) * 101 ^ (4 * N) := by
        field_simp
        ring
    _ = 1024 * X ^ (4 * k) * Real.exp (c - 5 * N) * ((1 + 100) ^ E * 101 ^ (4 * k + 7)) := by
        rw [hexp, hsplit]
    _ = 1024 * 101 ^ 7 * (X ^ (4 * k) * 101 ^ (4 * k)) * Real.exp (c - 5 * N) * (1 + 100) ^ E := by
        rw [pow_add]
        generalize (101 : ℝ) ^ (4 * k) = u
        generalize (1 + 100 : ℝ) ^ E = v
        generalize Real.exp (c - 5 * N) = e
        generalize X ^ (4 * k) = x
        ring
    _ ≤ 1024 * 101 ^ 7 * (10 ^ 6 / δ) ^ (4 * k) * Real.exp (c - 5 * N) * (1 + 100) ^ E := by
        have hpos : (0 : ℝ) ≤ 1024 * 101 ^ 7 := by norm_num
        have hv : (0 : ℝ) ≤ (1 + 100) ^ E := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hXe hpos) (Real.exp_pos _).le) hv

theorem resolutionWindowConstant_nonneg {γ δ c : ℝ} {N k : ℕ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hc : 0 < c) : 0 ≤ resolutionWindowConstant γ δ 100 c N k := by
  unfold resolutionWindowConstant
  have hcos := exp_neg_le_cos_sqrt hδ.le hδ2
  have hcos0 : 0 ≤ Real.cos (Real.sqrt δ / 4) := le_trans (Real.exp_pos _).le hcos
  have hm := unitMass_pos
  have : 0 < Real.sinh (c * (δ / 4)) := Real.sinh_pos_iff.mpr (by positivity)
  positivity

theorem exp18_ge : (24 : ℝ) * 101 ^ 3 ≤ Real.exp 18 := by
  have he := Real.exp_one_gt_d9
  have h : (2.7 : ℝ) ^ 18 ≤ Real.exp 18 := by
    rw [show (18 : ℝ) = ((18 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith) 18
  norm_num at h ⊢; linarith

theorem exp43_ge : (1024 : ℝ) * 101 ^ 7 * 24 ≤ Real.exp 43 := by
  have he := Real.exp_one_gt_d9
  have h : (2.7 : ℝ) ^ 43 ≤ Real.exp 43 := by
    rw [show (43 : ℝ) = ((43 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith) 43
  norm_num at h ⊢; linarith

/-- The window term is `< 1` once its exponent is negative. -/
theorem resolution_window_term_lt {γ δ c A₀ L Λ G : ℝ} {N k : ℕ} (hγ : 103 ≤ |γ|) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hc : 2 ≤ c * δ) (hc0 : 0 < c) (hexpΛ : Real.exp Λ = 10 ^ 6 / δ)
    (hexpG : Real.exp G = A₀ * L) (hAL : 0 ≤ A₀ * L)
    (hexpo : 2 * Λ + 4 * k * Λ + 2 * (-(c * δ / 8) + 3 * N * δ / 16) + 18 + G < 0) :
    resolutionWindowConstant γ δ 100 c N k ^ 2 * (1 + 100) ^ 3 * (24 * A₀ * L) < 1 := by
  have hW := resolutionWindowConstant_le (γ := γ) (N := N) (k := k) hγ hδ hδ2 hc
  have hW0 := resolutionWindowConstant_nonneg (γ := γ) (N := N) (k := k) hδ hδ2 hc0
  have hsq := pow_le_pow_left₀ hW0 hW 2
  have h256 : 256 / δ ≤ Real.exp Λ := by
    rw [hexpΛ]; exact div_le_div_of_nonneg_right (by norm_num) hδ.le
  have h2e4 : 2 * 10 ^ 4 / δ ≤ Real.exp Λ := by
    rw [hexpΛ]; exact div_le_div_of_nonneg_right (by norm_num) hδ.le
  obtain ⟨X, hX⟩ : ∃ X, X = -(c * δ / 8) + 3 * N * δ / 16 := ⟨_, rfl⟩
  rw [← hX] at hsq hexpo
  have hbound : (256 / δ * (2 * 10 ^ 4 / δ) ^ (2 * k) * Real.exp X) ^ 2 ≤
      Real.exp (2 * Λ + 4 * k * Λ + 2 * X) := by
    calc (256 / δ * (2 * 10 ^ 4 / δ) ^ (2 * k) * Real.exp X) ^ 2
        ≤ (Real.exp Λ * Real.exp Λ ^ (2 * k) * Real.exp X) ^ 2 := by gcongr
      _ = Real.exp (2 * Λ + 4 * k * Λ + 2 * X) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul]
          congr 1; push_cast; ring
  have h18 := exp18_ge
  have hlhs : resolutionWindowConstant γ δ 100 c N k ^ 2 * (1 + 100) ^ 3 * (24 * A₀ * L) ≤
      Real.exp (2 * Λ + 4 * k * Λ + 2 * X) * Real.exp 18 * Real.exp G := by
    rw [hexpG]
    have hA : 0 ≤ A₀ * L := hAL
    calc resolutionWindowConstant γ δ 100 c N k ^ 2 * (1 + 100) ^ 3 * (24 * A₀ * L)
        = resolutionWindowConstant γ δ 100 c N k ^ 2 * (24 * 101 ^ 3) * (A₀ * L) := by ring
      _ ≤ Real.exp (2 * Λ + 4 * k * Λ + 2 * X) * Real.exp 18 * (A₀ * L) := by
          gcongr; exact hsq.trans hbound
  have hexp3 : Real.exp (2 * Λ + 4 * k * Λ + 2 * X) * Real.exp 18 * Real.exp G =
      Real.exp (2 * Λ + 4 * k * Λ + 2 * X + 18 + G) := by
    rw [← Real.exp_add, ← Real.exp_add]
  rw [hexp3] at hlhs
  refine lt_of_le_of_lt hlhs ?_
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr hexpo

/-- The far term is `< 1` once its exponent is negative. -/
theorem resolution_far_term_lt {γ δ c A₀ L Λ G : ℝ} {N k : ℕ} (hγ : 103 ≤ |γ|) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hc : 2 ≤ c * δ) (hNk : 2 * k + 2 ≤ N)
    (hexpΛ : Real.exp Λ = 10 ^ 6 / δ) (hexpG : Real.exp G = A₀ * L) (hAL : 0 ≤ A₀ * L)
    (hexpo : 43 + 4 * k * Λ + (c - 5 * N) + G < 0) :
    resolutionFarConstant γ δ 100 c N k / (1 + 100) ^ (4 * N - 4 * k - 7) * (24 * A₀ * L) < 1 := by
  have hF := resolutionFarConstant_div_le (γ := γ) (N := N) (k := k) hγ hδ hδ2 hc hNk
  have h1e6 : (10 ^ 6 / δ) ^ (4 * k) = Real.exp (4 * k * Λ) := by
    rw [← hexpΛ, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h1e6] at hF
  have h43 := exp43_ge
  have hlhs : resolutionFarConstant γ δ 100 c N k / (1 + 100) ^ (4 * N - 4 * k - 7) *
      (24 * A₀ * L) ≤ Real.exp 43 * Real.exp (4 * k * Λ) * Real.exp (c - 5 * N) * Real.exp G := by
    rw [hexpG]
    calc resolutionFarConstant γ δ 100 c N k / (1 + 100) ^ (4 * N - 4 * k - 7) * (24 * A₀ * L)
        ≤ 1024 * 101 ^ 7 * Real.exp (4 * k * Λ) * Real.exp (c - 5 * N) * (24 * A₀ * L) :=
          mul_le_mul_of_nonneg_right hF (by nlinarith [hAL])
      _ = (1024 * 101 ^ 7 * 24) * Real.exp (4 * k * Λ) * Real.exp (c - 5 * N) * (A₀ * L) := by
          ring
      _ ≤ Real.exp 43 * Real.exp (4 * k * Λ) * Real.exp (c - 5 * N) * (A₀ * L) := by gcongr
  have hexp4 : Real.exp 43 * Real.exp (4 * k * Λ) * Real.exp (c - 5 * N) * Real.exp G =
      Real.exp (43 + 4 * k * Λ + (c - 5 * N) + G) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  rw [hexp4] at hlhs
  refine lt_of_le_of_lt hlhs ?_
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr hexpo

/-- **The size condition.**  If `(12/δ)((4k + 2) log(10⁶/δ) + log(A₀ log(|γ| + 3)) + 18) ≤ a`, then
`c = 3a/4` and `N = ⌊a/4⌋` satisfy the hypotheses of `exists_hodge_violation_resolution` with
window half-width `100`. -/
theorem resolution_horizon_condition {A₀ δ a γ : ℝ} {k : ℕ} (hA₀ : 1 ≤ A₀) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hγ : 103 ≤ |γ|)
    (hsize : 12 / δ * ((4 * k + 2) * Real.log (10 ^ 6 / δ) +
      Real.log (A₀ * Real.log (|γ| + 3)) + 18) ≤ a) :
    0 < 3 * a / 4 ∧ ((⌊a / 4⌋₊ : ℕ) : ℝ) + 3 * a / 4 ≤ a ∧ 2 * k + 2 ≤ ⌊a / 4⌋₊ ∧
      (resolutionFarConstant γ δ 100 (3 * a / 4) ⌊a / 4⌋₊ k /
          (1 + 100) ^ (4 * ⌊a / 4⌋₊ - 4 * k - 7) +
        resolutionWindowConstant γ δ 100 (3 * a / 4) ⌊a / 4⌋₊ k ^ 2 * (1 + 100) ^ 3) *
        (24 * A₀ * Real.log (|γ| + 3)) < 2 := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = Real.log (10 ^ 6 / δ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (|γ| + 3) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = Real.log (A₀ * L) := ⟨_, rfl⟩
  rw [← hΛ, ← hL, ← hG] at hsize
  rw [← hL]
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hAL : 1 ≤ A₀ * L := by nlinarith
  have hG0 : 0 ≤ G := by rw [hG]; exact Real.log_nonneg hAL
  have hexpG : Real.exp G = A₀ * L := by rw [hG]; exact Real.exp_log (by linarith)
  have hexpΛ : Real.exp Λ = 10 ^ 6 / δ := by rw [hΛ]; exact Real.exp_log (by positivity)
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, ← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    rw [le_div_iff₀ hδ]
    nlinarith [Real.exp_one_lt_d9]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨B, hBdef⟩ : ∃ B, B = (4 * (k : ℝ) + 2) * Λ + G + 18 := ⟨_, rfl⟩
  rw [← hBdef] at hsize
  have hB : 18 ≤ B := by rw [hBdef]; nlinarith
  have hδ12 : 24 ≤ 12 / δ := by rw [le_div_iff₀ hδ]; linarith
  have ha : 24 * B ≤ a := le_trans (by nlinarith) hsize
  have haδ : 12 * B ≤ a * δ := by
    have h := hsize
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at h
    linarith
  obtain ⟨N, hNdef⟩ : ∃ N, N = ⌊a / 4⌋₊ := ⟨_, rfl⟩
  rw [← hNdef]
  have ha0 : 0 ≤ a := by linarith
  have hN1 : (N : ℝ) ≤ a / 4 := by rw [hNdef]; exact Nat.floor_le (by positivity)
  have hN2 : a / 4 - 1 < N := by
    have := Nat.lt_floor_add_one (a / 4)
    rw [← hNdef] at this
    linarith
  have hNk : 2 * k + 2 ≤ N := by
    have : ((2 * k + 2 : ℕ) : ℝ) ≤ N := by push_cast; nlinarith
    exact_mod_cast this
  refine ⟨by linarith, by linarith, hNk, ?_⟩
  have hcδ : 2 ≤ 3 * a / 4 * δ := by nlinarith
  have hT2 := resolution_window_term_lt (γ := γ) (N := N) (k := k) hγ hδ hδ2 hcδ
    (by linarith) hexpΛ hexpG (by linarith) (by
      have : (N : ℝ) * δ ≤ a / 4 * δ := mul_le_mul_of_nonneg_right hN1 hδ.le
      rw [hBdef] at haδ
      nlinarith)
  have hT1 := resolution_far_term_lt (γ := γ) (N := N) (k := k) hγ hδ hδ2 hcδ hNk hexpΛ hexpG
    (by linarith) (by rw [hBdef] at ha; nlinarith)
  linarith

/-! ### The resolution law -/

/-- **The localized resolution law.**  Let `Z` have local count `N(t, t+1] ≤ A₀ log(|t| + 3)` and
let `ρ₀` be a zero of depth `δ = |β₀ - ½| > 0` at height `|γ₀| ≥ 103`.  Let `n_δ` be the number of
zeros with `γ₀ - 100 < γ ≤ γ₀ + 100` and depth `≥ δ/8`.  If the level-`a` Hodge index holds, then
`δ a < 12((4 n_δ + 2) log(10⁶/δ) + log(A₀ log(|γ₀| + 3)) + 18)`.

So a deep zero that the Hodge index cannot see is hidden either by the density of the other zeros
(`δ a ≲ log log |γ₀|`, the on-line masking of a sparse configuration) or by a crowd of
`≳ δ a/log(1/δ)` zeros of comparable depth within ordinate distance `100`. -/
theorem resolution_law_of_hodgeIndex (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a : ℝ}
    (hodge : HodgeIndexAtLevel Z a) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ)
    (hre : |ρ₀.re - 1 / 2| = δ) (hγ : 103 ≤ |ρ₀.im|) :
    δ * a < 12 * ((4 * ((Z.finite_window (ρ₀.im - 100) (ρ₀.im + 100)).toFinset.filter
        (fun ρ => δ / 8 ≤ |ρ.re - 1 / 2|)).card + 2) * Real.log (10 ^ 6 / δ) +
      Real.log (A₀ * Real.log (|ρ₀.im| + 3)) + 18) := by
  classical
  by_contra hlt
  push Not at hlt
  set k := ((Z.finite_window (ρ₀.im - 100) (ρ₀.im + 100)).toFinset.filter
    (fun ρ => δ / 8 ≤ |ρ.re - 1 / 2|)).card with hkdef
  obtain ⟨σ, hσ, hσre, hσim⟩ : ∃ σ ∈ Z.carrier, σ.re = 1 / 2 + δ ∧ σ.im = ρ₀.im := by
    rcases le_or_gt (1 / 2) ρ₀.re with h | h
    · refine ⟨ρ₀, hρ₀, ?_, rfl⟩
      rw [abs_of_nonneg (by linarith)] at hre; linarith
    · refine ⟨Zeta23.reflect ρ₀, Z.reflect_mem ρ₀ hρ₀, ?_, reflect_im' ρ₀⟩
      rw [abs_of_neg (by linarith)] at hre
      rw [reflect_re']; linarith
  have hst := Z.strip σ hσ
  have hδ2 : δ ≤ 1 / 2 := by linarith [hst.2]
  have hsize : 12 / δ * ((4 * k + 2) * Real.log (10 ^ 6 / δ) +
      Real.log (A₀ * Real.log (|σ.im| + 3)) + 18) ≤ a := by
    rw [hσim, div_mul_eq_mul_div, div_le_iff₀ hδ]
    linarith
  obtain ⟨hc, hNa, hNk, hbig⟩ := resolution_horizon_condition (γ := σ.im) (k := k) hA₀ hδ hδ2
    (by rw [hσim]; exact hγ) hsize
  have hk : ((Z.finite_window (σ.im - 100) (σ.im + 100)).toFinset.filter
      (fun ρ => δ / 8 ≤ |ρ.re - 1 / 2|)).card ≤ k := by rw [hσim]
  obtain ⟨f, hf, hfs, hp, hm, hneg⟩ := exists_hodge_violation_resolution Z hA₀ hloc hσ hδ hσre
    (H := 100) (by norm_num) (by rw [hσim]; linarith) hc hNa hk hNk hbig
  exact absurd (hodge f hf hfs hp hm) (not_le.mpr hneg)

/-- **The resolution law for `ζ`.**  There is `A₀` such that, if the level-`a` Hodge index holds,
every zero `ρ` of `ζ` of depth `δ = |β - ½| > 0` with `|γ| ≥ 103` satisfies
`δ a < 12((4 n_δ + 2) log(10⁶/δ) + log(A₀ log(|γ| + 3)) + 18)`, where `n_δ` counts the zeros of
depth `≥ δ/8` with ordinate in `(γ - 100, γ + 100]`. -/
theorem zeta_resolution_law_of_hodgeIndex :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a : ℝ, HodgeIndexAtLevel zetaZeroConfig a →
      ∀ ρ ∈ zetaZeroConfig.carrier, ∀ δ : ℝ, 0 < δ → |ρ.re - 1 / 2| = δ → 103 ≤ |ρ.im| →
        δ * a < 12 * ((4 * ((zetaZeroConfig.finite_window (ρ.im - 100) (ρ.im + 100)).toFinset.filter
            (fun ρ' => δ / 8 ≤ |ρ'.re - 1 / 2|)).card + 2) * Real.log (10 ^ 6 / δ) +
          Real.log (A₀ * Real.log (|ρ.im| + 3)) + 18) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, hA₀, fun a hodge ρ hρ δ hδ hre hγ =>
    resolution_law_of_hodgeIndex zetaZeroConfig hA₀ hloc hodge hρ hδ hre hγ⟩

end RHTower
