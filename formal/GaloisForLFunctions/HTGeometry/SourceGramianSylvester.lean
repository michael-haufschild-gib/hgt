import GaloisForLFunctions.HTGeometry.DuhamelSourceResponse

/-!
# Source Gramian, Lyapunov and Sylvester responses

For a coercive self-adjoint generator `A` (`Re ⟨y, A y⟩ ≥ c ‖y‖²`, `c > 0`) on a
finite-dimensional complex Hilbert space and a vector `v`, the Gramian
`G = ∫₀^∞ |e^{-tA} v⟩⟨e^{-tA} v| dt` `(SR.6)` is the unique solution of the Lyapunov equation
`A G + G A = |v⟩⟨v|` `(SR.12)`.  Uniqueness is Sylvester injectivity: `A X + X A = 0` makes
`e^{-tA} X e^{-tA}` constant, and it tends to `0`.

For a cyclic source the Gramian is positive definite.  Perturbing `L` by a small self-adjoint
intervention `εK`, the Lyapunov identity `Λ(G_ε) = P - ε (K G_ε + G_ε K)` with `Λ X = L X + X L`
gives the derivative `Ġ = -Λ⁻¹(K G + G K)` `(SR.14)`; it equals the time integral of
`|Y_K⟩⟨x| + |x⟩⟨Y_K|` `(SR.13)`, reconstructs `K` through the positive Sylvester equation
`K G + G K = -(L Ġ + Ġ L)` `(SR.15)`, and determines the inverse-cost and log-determinant
responses `(SR.16)`–`(SR.17)`.  A unitary involution commuting with `L` and fixing `v` up to a
phase acts isometrically on all of these `(SR.18)`–`(SR.19)`.
-/

open Filter Topology Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### Exponentially dominated integrands -/

/-- `∫₀^∞ e^{-a t} dt = 1/a`. -/
theorem integral_Ioi_exp_neg_rate {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(a * t)) = 1 / a := by
  have h := integral_exp_mul_Ioi (a := -a) (by linarith) 0
  simp only [mul_zero, Real.exp_zero] at h
  rw [show (fun t : ℝ => Real.exp (-(a * t))) = fun t => Real.exp (-a * t) by
    funext t; ring_nf, h]
  field_simp

theorem integrableOn_Ioi_exp_neg_rate {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-(a * t))) (Ioi 0) :=
  (exp_neg_integrableOn_Ioi 0 ha).congr_fun (fun t _ => by ring_nf) measurableSet_Ioi

theorem integrableOn_Ioi_of_exp_bound {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) {δ C : ℝ} (hδ : 0 < δ)
    (hb : ∀ t, 0 < t → ‖f t‖ ≤ C * Real.exp (-(δ * t))) : IntegrableOn f (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_Ioi_exp_neg_rate hδ).const_mul C)
    hf.aestronglyMeasurable.restrict ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact hb t ht

/-- `t e^{-ct} ≤ (2/c) e^{-(c/2) t}`. -/
theorem mul_exp_neg_le_two_div_exp_half {c : ℝ} (hc : 0 < c) (t : ℝ) :
    t * Real.exp (-(c * t)) ≤ 2 / c * Real.exp (-(c / 2 * t)) := by
  have h1 := Real.add_one_le_exp (c / 2 * t)
  have h2 : t ≤ 2 / c * Real.exp (c / 2 * t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [Real.exp_pos (c / 2 * t)]
  calc t * Real.exp (-(c * t)) ≤ 2 / c * Real.exp (c / 2 * t) * Real.exp (-(c * t)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 2 / c * Real.exp (-(c / 2 * t)) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] operatorRatAlgebra

/-! ### Coercive generators -/

/-- The semigroup `e^{-tA}`. -/
abbrev expNeg (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H := NormedSpace.exp (t • -A)

theorem hasDerivAt_expNeg (A : H →L[ℂ] H) (t : ℝ) : HasDerivAt (expNeg A) (-A * expNeg A t) t :=
  hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) t

theorem commute_expNeg (A : H →L[ℂ] H) (t : ℝ) : Commute A (expNeg A t) :=
  (((Commute.refl A).neg_right).smul_right t).exp_right

theorem expNeg_zero (A : H →L[ℂ] H) : expNeg A 0 = 1 := by simp [expNeg]

theorem continuous_expNeg (A : H →L[ℂ] H) : Continuous (expNeg A) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_expNeg A t).continuousAt

theorem hasDerivAt_expNeg_apply (A : H →L[ℂ] H) (y : H) (t : ℝ) :
    HasDerivAt (fun t => expNeg A t y) (-A (expNeg A t y)) t := by
  have h := hasDerivAt_operator_apply (hasDerivAt_expNeg A t) (hasDerivAt_const t y)
  simpa [mul_apply_eq_comp] using h

theorem tendsto_expNeg_apply {A : H →L[ℂ] H} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) (y : H) :
    Tendsto (fun t => expNeg A t y) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hdecay : Tendsto (fun t : ℝ => Real.exp (-(c * t)) * ‖y‖) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)).mul_const
      ‖y‖
    simpa [Function.comp_def] using this
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hdecay
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact norm_exp_neg_le A hcoer ht y

/-- **Sylvester injectivity.**  For a coercive self-adjoint `A`, `A X + X A = 0` forces `X = 0`. -/
theorem eq_zero_of_sylvester {A : H →L[ℂ] H} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) {X : H →L[ℂ] H}
    (hX : A * X + X * A = 0) : X = 0 := by
  set φ : ℝ → H →L[ℂ] H := fun t => expNeg A t * X * expNeg A t
  have hφ : ∀ t, HasDerivAt φ 0 t := fun t => by
    have h := ((hasDerivAt_expNeg A t).mul (hasDerivAt_const t X)).mul (hasDerivAt_expNeg A t)
    refine h.congr_deriv ?_
    have hc1 := (commute_expNeg A t).eq
    have h1 : -A * expNeg A t * X = -(expNeg A t * A * X) := by rw [neg_mul, hc1, neg_mul]
    calc (-A * expNeg A t * X + expNeg A t * 0) * expNeg A t +
          expNeg A t * X * (-A * expNeg A t)
        = -(expNeg A t * (A * X + X * A) * expNeg A t) := by
          rw [h1]
          noncomm_ring
      _ = 0 := by rw [hX, mul_zero, zero_mul, neg_zero]
  have hconst := is_const_of_deriv_eq_zero (fun t => (hφ t).differentiableAt)
    (fun t => (hφ t).deriv)
  have hφX : ∀ t, φ t = X := fun t => by
    rw [hconst t 0]
    simp [φ, expNeg_zero]
  ext y
  have hlim : Tendsto (fun t => φ t y) atTop (𝓝 0) := by
    have h1 := tendsto_expNeg_apply hc hcoer y
    have hbound : ∀ t ≥ (0 : ℝ), ‖φ t y‖ ≤ ‖X‖ * ‖expNeg A t y‖ := fun t ht => by
      calc ‖φ t y‖ = ‖expNeg A t (X (expNeg A t y))‖ := by simp [φ, mul_apply_eq_comp]
        _ ≤ Real.exp (-(c * t)) * ‖X (expNeg A t y)‖ := norm_exp_neg_le A hcoer ht _
        _ ≤ 1 * (‖X‖ * ‖expNeg A t y‖) := by
            gcongr
            · exact Real.exp_le_one_iff.mpr (by nlinarith)
            · exact X.le_opNorm _
        _ = ‖X‖ * ‖expNeg A t y‖ := one_mul _
    have h2 : Tendsto (fun t => ‖X‖ * ‖expNeg A t y‖) atTop (𝓝 0) := by
      simpa using (tendsto_zero_iff_norm_tendsto_zero.mp h1).const_mul ‖X‖
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ h2
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact hbound t ht
  have := tendsto_nhds_unique (tendsto_const_nhds.congr fun t => (congrArg (· y) (hφX t)).symm)
    hlim
  simpa using this

/-! ### The Gramian -/

omit [CompleteSpace H] in
theorem continuous_rankOne_path {f g : ℝ → H} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => InnerProductSpace.rankOne ℂ (f t) (g t) := by
  simp_rw [InnerProductSpace.rankOne_def]
  fun_prop

/-- The Gramian `∫₀^∞ |e^{-tA} v⟩⟨e^{-tA} v| dt` `(SR.6)`. -/
def gramian (A : H →L[ℂ] H) (v : H) : H →L[ℂ] H :=
  ∫ t in Ioi (0 : ℝ), InnerProductSpace.rankOne ℂ (expNeg A t v) (expNeg A t v)

section Coercive

variable {A : H →L[ℂ] H} {c : ℝ}

theorem continuous_expNeg_apply (A : H →L[ℂ] H) (v : H) : Continuous fun t => expNeg A t v :=
  (continuous_expNeg A).clm_apply continuous_const

/-- Products of two orbit coordinates are integrable on the half-line. -/
theorem integrableOn_orbit_mul (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) (a u w b : H) :
    IntegrableOn (fun t => ⟪a, expNeg A t u⟫_ℂ * ⟪expNeg A t w, b⟫_ℂ) (Ioi 0) := by
  have hcont : Continuous fun t => ⟪a, expNeg A t u⟫_ℂ * ⟪expNeg A t w, b⟫_ℂ :=
    (continuous_const.inner (continuous_expNeg_apply A u)).mul
      ((continuous_expNeg_apply A w).inner continuous_const)
  refine Integrable.mono' ((integrableOn_Ioi_exp_neg_rate (a := 2 * c) (by positivity)).mul_const
    (‖a‖ * ‖u‖ * ‖w‖ * ‖b‖)) hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) ≤ t := le_of_lt ht
  have h1 := norm_exp_neg_le A hcoer ht' u
  have h2 := norm_exp_neg_le A hcoer ht' w
  rw [norm_mul]
  calc ‖⟪a, expNeg A t u⟫_ℂ‖ * ‖⟪expNeg A t w, b⟫_ℂ‖
      ≤ (‖a‖ * ‖expNeg A t u‖) * (‖expNeg A t w‖ * ‖b‖) :=
        mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _)
          (by positivity)
    _ ≤ (‖a‖ * (Real.exp (-(c * t)) * ‖u‖)) * ((Real.exp (-(c * t)) * ‖w‖) * ‖b‖) := by
        gcongr
    _ = Real.exp (-(2 * c * t)) * (‖a‖ * ‖u‖ * ‖w‖ * ‖b‖) := by
        rw [show -(2 * c * t) = -(c * t) + -(c * t) by ring, Real.exp_add]
        ring

theorem integrableOn_gramIntegrand (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) (v : H) :
    IntegrableOn (fun t => InnerProductSpace.rankOne ℂ (expNeg A t v) (expNeg A t v)) (Ioi 0) := by
  have hcont := continuous_rankOne_path (continuous_expNeg_apply A v)
    (continuous_expNeg_apply A v)
  refine Integrable.mono' ((integrableOn_Ioi_exp_neg_rate (a := 2 * c) (by positivity)).mul_const
    (‖v‖ ^ 2)) hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have h := norm_exp_neg_le A hcoer (le_of_lt ht) v
  rw [InnerProductSpace.norm_rankOne]
  calc ‖expNeg A t v‖ * ‖expNeg A t v‖ ≤ (Real.exp (-(c * t)) * ‖v‖) *
      (Real.exp (-(c * t)) * ‖v‖) := mul_le_mul h h (norm_nonneg _) (by positivity)
    _ = Real.exp (-(2 * c * t)) * ‖v‖ ^ 2 := by
        rw [show -(2 * c * t) = -(c * t) + -(c * t) by ring, Real.exp_add]
        ring

/-- **The weak form of the Gramian**: `⟨a, G b⟩ = ∫₀^∞ ⟨a, x(t)⟩ ⟨x(t), b⟩ dt`. -/
theorem inner_gramian (hc : 0 < c) (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ)
    (v a b : H) :
    ⟪a, gramian A v b⟫_ℂ = ∫ t in Ioi (0 : ℝ), ⟪a, expNeg A t v⟫_ℂ * ⟪expNeg A t v, b⟫_ℂ := by
  set Φ : (H →L[ℂ] H) →L[ℂ] ℂ := (innerSL ℂ a).comp (ContinuousLinearMap.apply ℂ H b)
  have h := Φ.integral_comp_comm (integrableOn_gramIntegrand hc hcoer v)
  rw [gramian, show ⟪a, (∫ t in Ioi (0 : ℝ), InnerProductSpace.rankOne ℂ (expNeg A t v)
      (expNeg A t v)) b⟫_ℂ = Φ (∫ t in Ioi (0 : ℝ), InnerProductSpace.rankOne ℂ (expNeg A t v)
      (expNeg A t v)) from rfl, ← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Φ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    innerSL_apply_apply,
    InnerProductSpace.rankOne_apply, inner_smul_right]
  ring

theorem hasDerivAt_orbitProduct (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (u w a b : H) (t : ℝ) :
    HasDerivAt (fun t => ⟪a, expNeg A t u⟫_ℂ * ⟪expNeg A t w, b⟫_ℂ)
      (-(⟪A a, expNeg A t u⟫_ℂ * ⟪expNeg A t w, b⟫_ℂ +
        ⟪a, expNeg A t u⟫_ℂ * ⟪expNeg A t w, A b⟫_ℂ)) t := by
  have hs : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := fun x y =>
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA x y
  have h1 := (hasDerivAt_const t a).inner ℂ (hasDerivAt_expNeg_apply A u t)
  have h2 := (hasDerivAt_expNeg_apply A w t).inner ℂ (hasDerivAt_const t b)
  refine (h1.mul h2).congr_deriv ?_
  simp only [inner_zero_left, inner_zero_right, zero_add, add_zero, inner_neg_right,
    inner_neg_left]
  rw [← hs a, hs (expNeg A t w) b]
  ring

/-- **`(SR.12)`: the Lyapunov law** `A G + G A = |v⟩⟨v|`. -/
theorem lyapunov_gramian (hA : IsSelfAdjoint A) (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) (v : H) :
    A * gramian A v + gramian A v * A = InnerProductSpace.rankOne ℂ v v := by
  have hs : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := fun x y =>
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA x y
  ext b
  refine ext_inner_left ℂ fun a => ?_
  have hint1 := integrableOn_orbit_mul hc hcoer (A a) v v b
  have hint2 := integrableOn_orbit_mul hc hcoer a v v (A b)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun t => ⟪a, expNeg A t v⟫_ℂ * ⟪expNeg A t v, b⟫_ℂ)
    ((((continuous_const.inner (continuous_expNeg_apply A v)).mul
      ((continuous_expNeg_apply A v).inner continuous_const)).continuousAt).continuousWithinAt)
    (fun t _ => hasDerivAt_orbitProduct A hA v v a b t) (hint1.add hint2).neg (m := 0) (by
      have h := tendsto_expNeg_apply hc hcoer v
      have hca : Continuous fun y : H => ⟪a, y⟫_ℂ := continuous_const.inner continuous_id
      have hcb : Continuous fun y : H => ⟪y, b⟫_ℂ := continuous_id.inner continuous_const
      have := (hca.tendsto 0 |>.comp h).mul (hcb.tendsto 0 |>.comp h)
      simpa [Function.comp_def] using this)
  rw [integral_neg, integral_add hint1 hint2] at hftc
  simp only [expNeg_zero, one_apply_eq_self, zero_sub] at hftc
  rw [add_apply, mul_apply_eq_comp, mul_apply_eq_comp, inner_add_right, ← hs a,
    inner_gramian hc hcoer, inner_gramian hc hcoer, InnerProductSpace.rankOne_apply,
    inner_smul_right]
  linear_combination -hftc

/-- The Gramian is self-adjoint. -/
theorem isSelfAdjoint_gramian (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) (v : H) :
    IsSelfAdjoint (gramian A v) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro a b
  rw [ContinuousLinearMap.coe_coe, ← inner_conj_symm,
    inner_gramian hc hcoer, inner_gramian hc hcoer, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [map_mul, inner_conj_symm]
  ring

/-- The Gramian quadratic form: `⟨z, G z⟩ = ∫₀^∞ |⟨z, x(t)⟩|² dt`. -/
theorem inner_gramian_self (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) (v z : H) :
    ⟪z, gramian A v z⟫_ℂ = ((∫ t in Ioi (0 : ℝ), ‖⟪z, expNeg A t v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_gramian hc hcoer, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [← inner_conj_symm (expNeg A t v) z, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Uniqueness of the Lyapunov solution.** -/
theorem eq_gramian_of_lyapunov (hA : IsSelfAdjoint A) (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) (v : H) {X : H →L[ℂ] H}
    (hX : A * X + X * A = InnerProductSpace.rankOne ℂ v v) : X = gramian A v := by
  have h := lyapunov_gramian hA hc hcoer v
  refine sub_eq_zero.mp (eq_zero_of_sylvester hc hcoer ?_)
  rw [mul_sub, sub_mul, show A * X - A * gramian A v + (X * A - gramian A v * A) =
    (A * X + X * A) - (A * gramian A v + gramian A v * A) by abel, hX, h, sub_self]

/-- The Gramian norm bound `‖G‖ ≤ ‖v‖² / (2c)`. -/
theorem norm_gramian_le (hc : 0 < c) (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ)
    (v : H) : ‖gramian A v‖ ≤ ‖v‖ ^ 2 / (2 * c) := by
  have hb := (integrableOn_Ioi_exp_neg_rate (a := 2 * c) (by positivity)).mul_const (‖v‖ ^ 2)
  have h := norm_integral_le_of_norm_le
    (f := fun t => InnerProductSpace.rankOne ℂ (expNeg A t v) (expNeg A t v)) hb (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have h := norm_exp_neg_le A hcoer (le_of_lt ht) v
    rw [InnerProductSpace.norm_rankOne]
    calc ‖expNeg A t v‖ * ‖expNeg A t v‖ ≤ (Real.exp (-(c * t)) * ‖v‖) *
        (Real.exp (-(c * t)) * ‖v‖) := mul_le_mul h h (norm_nonneg _) (by positivity)
      _ = Real.exp (-(2 * c * t)) * ‖v‖ ^ 2 := by
          rw [show -(2 * c * t) = -(c * t) + -(c * t) by ring, Real.exp_add]
          ring)
  rw [integral_mul_const, integral_Ioi_exp_neg_rate (by positivity)] at h
  calc ‖gramian A v‖ ≤ 1 / (2 * c) * ‖v‖ ^ 2 := h
    _ = ‖v‖ ^ 2 / (2 * c) := by ring

end Coercive


/-! ### The Lyapunov operator and its inverse -/

/-- The Lyapunov operator `X ↦ A X + X A`. -/
def lyapunovOp (A : H →L[ℂ] H) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ContinuousLinearMap.mul ℂ (H →L[ℂ] H) A + (ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip A

theorem lyapunovOp_apply (A X : H →L[ℂ] H) : lyapunovOp A X = A * X + X * A := rfl

section Coercive

variable {A : H →L[ℂ] H} {c : ℝ}

theorem lyapunovOp_injective (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) :
    Function.Injective (lyapunovOp A) := by
  intro X Y hXY
  refine sub_eq_zero.mp (eq_zero_of_sylvester hc hcoer ?_)
  have h := congrArg (· - lyapunovOp A Y) hXY
  simp only [sub_self, lyapunovOp_apply] at h
  calc A * (X - Y) + (X - Y) * A = A * X + X * A - (A * Y + Y * A) := by noncomm_ring
    _ = 0 := h

theorem lyapunovOp_bijective [FiniteDimensional ℂ H] (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) :
    Function.Bijective (lyapunovOp A) :=
  ⟨lyapunovOp_injective hc hcoer, LinearMap.injective_iff_surjective
    (f := (lyapunovOp A : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))).mp (lyapunovOp_injective hc hcoer)⟩

/-- **Unique solvability of the Sylvester equation** `A X + X A = B` for coercive `A`. -/
theorem existsUnique_sylvester [FiniteDimensional ℂ H] (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) (B : H →L[ℂ] H) :
    ∃! X : H →L[ℂ] H, A * X + X * A = B := by
  obtain ⟨X, hX⟩ := (lyapunovOp_bijective hc hcoer).2 B
  exact ⟨X, hX, fun Y hY => lyapunovOp_injective hc hcoer (hY.trans hX.symm)⟩

/-- A uniform inverse bound for the Lyapunov operator: `‖X‖ ≤ M ‖A X + X A‖`. -/
theorem exists_lyapunov_inverse_bound [FiniteDimensional ℂ H] (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) :
    ∃ M, 0 ≤ M ∧ ∀ X : H →L[ℂ] H, ‖X‖ ≤ M * ‖A * X + X * A‖ := by
  set e := (LinearEquiv.ofBijective (lyapunovOp A : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (lyapunovOp_bijective hc hcoer)).toContinuousLinearEquiv
  refine ⟨‖(e.symm : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))‖, norm_nonneg _, fun X => ?_⟩
  have h1 : X = e.symm (e X) := (e.symm_apply_apply X).symm
  have h2 : e X = A * X + X * A := rfl
  calc ‖X‖ = ‖e.symm (e X)‖ := congrArg norm h1
    _ ≤ ‖(e.symm : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))‖ * ‖e X‖ :=
        (e.symm : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)).le_opNorm _
    _ = _ := by rw [h2]

end Coercive

end GaloisForLFunctions.HTGeometry
