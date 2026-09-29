import GaloisForLFunctions.RHTower.ThetaTailScalingAsymptotics

/-!
# The Gaussian-base defect of zero division

The literal seed is built from the Gaussian base `ψ(x) = exp(x/2 − π e^{2x})`: with
`L = ∂ − (1/2 − 2π e^{2x})` one has `L ψ = 0` and `h = (∂² − 1/4) ψ`.  The outward Green operator
`T_α` commutes with constant-coefficient derivatives but not with `L`:

`[L, T_α] ψ(x) = −2πα e^{2x} ∫₀^∞ sin(αt)(e^{2t} − 1) ψ(x+t) dt`,

obtained by differentiating under the integral sign.  Since `ψ` has the theta tail, the Laplace
asymptotics give `e^{4x} [L, T_α] ψ / ψ → −α²/π²`, so for `α ≠ 0` the defect vanishes at no point of
a half-line `[X, ∞)`; also `T_α ψ / ψ → 0`.
-/
open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## The Gaussian base -/

/-- The Gaussian base `ψ(x) = exp(x/2 − π e^{2x})` of the literal seed. -/
def thetaGaussBase (x : ℝ) : ℝ := Real.exp (x / 2 - Real.pi * Real.exp (2 * x))

/-- The coefficient `1/2 − 2π e^{2x}` of the first-order operator `L = ∂ − (1/2 − 2π e^{2x})`. -/
def gaussBaseCoeff (x : ℝ) : ℝ := 1 / 2 - 2 * Real.pi * Real.exp (2 * x)

/-- The operator `L f = f' − (1/2 − 2π e^{2x}) f`. -/
def gaussBaseOperator (f : ℝ → ℂ) (x : ℝ) : ℂ := deriv f x - (gaussBaseCoeff x : ℂ) * f x

theorem thetaGaussBase_pos (x : ℝ) : 0 < thetaGaussBase x := Real.exp_pos _

theorem continuous_thetaGaussBase : Continuous thetaGaussBase := by
  unfold thetaGaussBase; fun_prop

theorem hasDerivAt_exp_two_mul (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (2 * y)) (2 * Real.exp (2 * x)) x := by
  have := ((hasDerivAt_id x).const_mul 2).exp
  exact this.congr_deriv (by simp only [id]; ring)

theorem hasDerivAt_thetaGaussBase (x : ℝ) :
    HasDerivAt thetaGaussBase (gaussBaseCoeff x * thetaGaussBase x) x := by
  have hin : HasDerivAt (fun y : ℝ => y / 2 - Real.pi * Real.exp (2 * y)) (gaussBaseCoeff x) x := by
    have h1 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := (hasDerivAt_id x).div_const 2
    exact (h1.sub ((hasDerivAt_exp_two_mul x).const_mul Real.pi)).congr_deriv
      (by rw [gaussBaseCoeff]; ring)
  exact hin.exp.congr_deriv (by rw [thetaGaussBase]; ring)

/-- **`Lψ = 0`.** -/
theorem gaussBaseOperator_thetaGaussBase (x : ℝ) :
    gaussBaseOperator (fun y => (thetaGaussBase y : ℂ)) x = 0 := by
  rw [gaussBaseOperator, ((hasDerivAt_thetaGaussBase x).ofReal_comp).deriv]
  push_cast
  ring

theorem deriv_thetaGaussBase : deriv thetaGaussBase = fun x => gaussBaseCoeff x * thetaGaussBase x :=
  funext fun x => (hasDerivAt_thetaGaussBase x).deriv

/-- **`h = (∂² − 1/4) ψ`.** -/
theorem thetaCuspLogSeed_eq_gaussBase (x : ℝ) :
    iteratedDeriv 2 thetaGaussBase x - thetaGaussBase x / 4 = thetaCuspLogSeed x := by
  have hc : HasDerivAt gaussBaseCoeff (-(4 * Real.pi * Real.exp (2 * x))) x :=
    (((hasDerivAt_exp_two_mul x).const_mul (2 * Real.pi)).const_sub (1 / 2)).congr_deriv (by ring)
  have h2 : HasDerivAt (fun y => gaussBaseCoeff y * thetaGaussBase y)
      (-(4 * Real.pi * Real.exp (2 * x)) * thetaGaussBase x +
        gaussBaseCoeff x * (gaussBaseCoeff x * thetaGaussBase x)) x :=
    hc.mul (hasDerivAt_thetaGaussBase x)
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_thetaGaussBase, h2.deriv, thetaCuspLogSeed_eq]
  simp only [gaussBaseCoeff, thetaGaussBase]
  rw [show x / 2 - Real.pi * Real.exp (2 * x) = 5 * x / 2 + (-(2 * x)) +
    (-(Real.pi * Real.exp (2 * x))) by ring, Real.exp_add, Real.exp_add]
  have h1 : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (2 * Real.pi * Real.exp (5 * x / 2) * Real.exp (-(Real.pi * Real.exp (2 * x))) *
    (2 * Real.pi * Real.exp (2 * x) - 3)) * h1

/-! ## Integrability and the theta tail of `ψ` -/

/-- `t ↦ exp(bt − a e^{2t})` is integrable on `(0, ∞)` for `a > 0`. -/
theorem integrableOn_exp_sub_mul_exp_two {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (b * t - a * Real.exp (2 * t))) (Ioi 0) := by
  refine (((integrable_exp_neg_mul_sq ha).const_mul (Real.exp (b ^ 2 / (4 * a)))).integrableOn).mono'
    ((by fun_prop : Continuous fun t : ℝ =>
      Real.exp (b * t - a * Real.exp (2 * t))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hq := Real.quadratic_le_exp_of_nonneg (x := 2 * t) (by linarith)
  have hsq : b * t - a * t ^ 2 ≤ b ^ 2 / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * a * t - b)]
  have h2 : a * (2 * t ^ 2) ≤ a * Real.exp (2 * t) := by
    refine mul_le_mul_of_nonneg_left ?_ ha.le
    nlinarith
  nlinarith

theorem thetaGaussBase_add (x t : ℝ) :
    thetaGaussBase (x + t) = Real.exp (t / 2 - Real.pi * Real.exp (2 * x) * (Real.exp (2 * t) - 1)) *
      thetaGaussBase x := by
  simp only [thetaGaussBase]
  rw [← Real.exp_add]
  congr 1
  rw [show 2 * (x + t) = 2 * x + 2 * t by ring, Real.exp_add]
  ring

/-- The Gaussian base has the theta tail. -/
theorem thetaTypeTail_gaussBase : ThetaTypeTail thetaGaussBase := by
  refine ⟨continuous_thetaGaussBase, ⟨1, 1 / 2, 0, by norm_num, le_rfl, fun x hx =>
    ⟨thetaGaussBase_pos x, fun t ht => ?_⟩⟩, fun τ hτ => ?_⟩
  · rw [thetaGaussBase_add, one_mul]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (thetaGaussBase_pos x).le
    have hq : 2 * t ≤ Real.exp (2 * t) - 1 := by linarith [Real.add_one_le_exp (2 * t)]
    have := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ Real.pi * Real.exp (2 * x))
    nlinarith
  · have hs0 : Tendsto (fun x : ℝ => τ * Real.exp (-(2 * x))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul τ
      simpa [Function.comp] using this
    have h1 : Tendsto (fun x : ℝ => τ * Real.exp (-(2 * x)) / 2 -
        Real.pi * (Real.exp (2 * x) * (Real.exp (2 * (τ * Real.exp (-(2 * x)))) - 1))) atTop
        (𝓝 (0 / 2 - Real.pi * (2 * τ))) :=
      (hs0.div_const 2).sub ((tendsto_exp_mul_exp_sub_one τ).const_mul Real.pi)
    have := (Real.continuous_exp.tendsto _).comp h1
    refine (this.congr fun x => ?_).trans_eq (by congr 2; ring)
    simp only [Function.comp]
    rw [thetaGaussBase_add, mul_div_cancel_right₀ _ (thetaGaussBase_pos x).ne']
    congr 1
    ring

/-! ## Differentiating the Green transform of `ψ` -/

/-- `ψ' = (1/2 − 2π e^{2x}) ψ` as a complex function. -/
def thetaGaussBaseDerivC (y : ℝ) : ℂ := ((gaussBaseCoeff y * thetaGaussBase y : ℝ) : ℂ)

theorem abs_gaussBaseCoeff_le (y : ℝ) :
    |gaussBaseCoeff y| ≤ 1 / 2 + 2 * Real.pi * Real.exp (2 * y) := by
  unfold gaussBaseCoeff
  rw [abs_le]
  constructor <;> nlinarith [Real.exp_pos (2 * y), Real.pi_pos]

/-- Local domination of `ψ` and `ψ'` on `x ∈ (x₀ − 1, x₀ + 1)`. -/
theorem gaussBase_local_bound (x₀ : ℝ) {x : ℝ} (hx : x ∈ Metric.ball x₀ 1) (t : ℝ) :
    thetaGaussBase (x + t) ≤ Real.exp ((x₀ + 1) / 2) *
      Real.exp (1 / 2 * t - Real.pi * Real.exp (2 * (x₀ - 1)) * Real.exp (2 * t)) := by
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
  simp only [thetaGaussBase]
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : Real.exp (2 * (x₀ - 1)) * Real.exp (2 * t) ≤ Real.exp (2 * (x + t)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have := mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
  nlinarith

theorem hasDerivAt_outwardSine_gaussBase (α : ℂ) (x₀ : ℝ) :
    IntegrableOn (fun t : ℝ => Complex.sin (α * t) * (thetaGaussBase (x₀ + t) : ℂ)) (Ioi 0) ∧
    IntegrableOn (fun t : ℝ => Complex.sin (α * t) * thetaGaussBaseDerivC (x₀ + t)) (Ioi 0) ∧
    HasDerivAt (outwardSine α fun y => (thetaGaussBase y : ℂ))
      (outwardSine α thetaGaussBaseDerivC x₀) x₀ := by
  set a := Real.pi * Real.exp (2 * (x₀ - 1))
  have ha : 0 < a := by positivity
  set c := |α.im|
  set E₀ := Real.exp ((x₀ + 1) / 2)
  set D₀ := 2 * Real.pi * Real.exp (2 * (x₀ + 1))
  have hD₀ : 0 < D₀ := by simp only [D₀]; positivity
  set bound : ℝ → ℝ := fun t => E₀ *
    (Real.exp ((c + 1 / 2) * t - a * Real.exp (2 * t)) +
      D₀ * Real.exp ((c + 5 / 2) * t - a * Real.exp (2 * t)))
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) :=
    ((integrableOn_exp_sub_mul_exp_two ha _).add
      ((integrableOn_exp_sub_mul_exp_two ha _).const_mul _)).const_mul _
  have hsin : ∀ t : ℝ, 0 ≤ t → ‖Complex.sin (α * t)‖ ≤ Real.exp (c * t) := fun t ht => by
    simpa [abs_of_nonneg ht] using norm_csin_mul_ofReal_le α t
  have hsplit : ∀ t : ℝ, Real.exp (c * t) * (E₀ * Real.exp (1 / 2 * t - a * Real.exp (2 * t))) =
      E₀ * Real.exp ((c + 1 / 2) * t - a * Real.exp (2 * t)) := fun t => by
    rw [show (c + 1 / 2) * t - a * Real.exp (2 * t) = c * t + (1 / 2 * t - a * Real.exp (2 * t)) by
      ring, Real.exp_add]; ring
  have hsplit2 : ∀ t : ℝ, Real.exp (c * t) * (D₀ * Real.exp (2 * t) *
      (E₀ * Real.exp (1 / 2 * t - a * Real.exp (2 * t)))) =
      E₀ * (D₀ * Real.exp ((c + 5 / 2) * t - a * Real.exp (2 * t))) := fun t => by
    rw [show (c + 5 / 2) * t - a * Real.exp (2 * t) =
      c * t + 2 * t + (1 / 2 * t - a * Real.exp (2 * t)) by ring, Real.exp_add, Real.exp_add]; ring
  have hF'b : ∀ t : ℝ, 0 < t → ∀ x ∈ Metric.ball x₀ 1,
      ‖Complex.sin (α * t) * thetaGaussBaseDerivC (x + t)‖ ≤ bound t := by
    intro t ht x hx
    have hx' := hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx'
    have hψ := gaussBase_local_bound x₀ hx t
    have hcoef : |gaussBaseCoeff (x + t)| ≤ 1 + D₀ * Real.exp (2 * t) := by
      refine (abs_gaussBaseCoeff_le _).trans ?_
      simp only [D₀]
      rw [mul_assoc (2 * Real.pi), ← Real.exp_add]
      have : Real.exp (2 * (x + t)) ≤ Real.exp (2 * (x₀ + 1) + 2 * t) :=
        Real.exp_le_exp.2 (by linarith)
      nlinarith [Real.pi_pos]
    rw [norm_mul, thetaGaussBaseDerivC, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (thetaGaussBase_pos _)]
    calc ‖Complex.sin (α * t)‖ * (|gaussBaseCoeff (x + t)| * thetaGaussBase (x + t))
        ≤ Real.exp (c * t) * ((1 + D₀ * Real.exp (2 * t)) *
          (E₀ * Real.exp (1 / 2 * t - a * Real.exp (2 * t)))) :=
          mul_le_mul (hsin t ht.le) (mul_le_mul hcoef hψ (thetaGaussBase_pos _).le
            (add_nonneg zero_le_one (mul_nonneg hD₀.le (Real.exp_pos _).le)))
            (mul_nonneg (abs_nonneg _) (thetaGaussBase_pos _).le) (Real.exp_pos _).le
      _ = bound t := by
          simp only [bound]
          rw [add_mul, one_mul, mul_add, hsplit, hsplit2]
          ring
  have hFb : ∀ t : ℝ, 0 < t → ‖Complex.sin (α * t) * (thetaGaussBase (x₀ + t) : ℂ)‖ ≤ bound t := by
    intro t ht
    have hψ := gaussBase_local_bound x₀ (Metric.mem_ball_self one_pos) t
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (thetaGaussBase_pos _).le]
    calc ‖Complex.sin (α * t)‖ * thetaGaussBase (x₀ + t) ≤ Real.exp (c * t) *
          (E₀ * Real.exp (1 / 2 * t - a * Real.exp (2 * t))) :=
          mul_le_mul (hsin t ht.le) hψ (thetaGaussBase_pos _).le (Real.exp_pos _).le
      _ = E₀ * Real.exp ((c + 1 / 2) * t - a * Real.exp (2 * t)) := hsplit t
      _ ≤ bound t := by
          simp only [bound]
          have : 0 ≤ D₀ * Real.exp ((c + 5 / 2) * t - a * Real.exp (2 * t)) :=
            mul_nonneg hD₀.le (Real.exp_pos _).le
          nlinarith [Real.exp_pos ((x₀ + 1) / 2)]
  have hmeasF : ∀ x : ℝ, AEStronglyMeasurable (fun t : ℝ => Complex.sin (α * t) *
      (thetaGaussBase (x + t) : ℂ)) (volume.restrict (Ioi 0)) := fun x =>
    ((by fun_prop : Continuous fun t : ℝ => Complex.sin (α * t)).mul (Complex.continuous_ofReal.comp
      (continuous_thetaGaussBase.comp (continuous_const.add continuous_id)))).aestronglyMeasurable
  have hFint : Integrable (fun t : ℝ => Complex.sin (α * t) * (thetaGaussBase (x₀ + t) : ℂ))
      (volume.restrict (Ioi 0)) :=
    hbound_int.mono' (hmeasF x₀) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hFb t ht)
  have hmeasF' : AEStronglyMeasurable (fun t : ℝ => Complex.sin (α * t) *
      thetaGaussBaseDerivC (x₀ + t)) (volume.restrict (Ioi 0)) :=
    ((by fun_prop : Continuous fun t : ℝ => Complex.sin (α * t)).mul (Complex.continuous_ofReal.comp
      ((by unfold gaussBaseCoeff; fun_prop : Continuous gaussBaseCoeff).mul
        continuous_thetaGaussBase |>.comp (continuous_const.add continuous_id)))).aestronglyMeasurable
  have hdiff : ∀ t : ℝ, ∀ x : ℝ, HasDerivAt (fun x => Complex.sin (α * t) *
      (thetaGaussBase (x + t) : ℂ)) (Complex.sin (α * t) * thetaGaussBaseDerivC (x + t)) x := by
    intro t x
    have h := ((hasDerivAt_thetaGaussBase (x + t)).comp x ((hasDerivAt_id x).add_const t)).ofReal_comp
    simp only [Function.comp, id, mul_one] at h
    exact (h.const_mul (Complex.sin (α * t))).congr_deriv (by simp [thetaGaussBaseDerivC])
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (Metric.ball_mem_nhds x₀ one_pos) (Eventually.of_forall hmeasF) hFint hmeasF'
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hF'b t ht)
    hbound_int (Eventually.of_forall fun t x _ => hdiff t x)
  exact ⟨hFint, key.1, key.2.const_mul α⟩

/-! ## The Gaussian-base defect -/

/-- The kernel `sin(αt)(e^{2t} − 1)` of the defect. -/
def gaussBaseDefectKernel (α : ℂ) (t : ℝ) : ℂ := Complex.sin (α * t) * ((Real.exp (2 * t) - 1 : ℝ) : ℂ)

/-- **The Gaussian-base commutator (3).**  `L ψ = 0` and
`[L, T_α] ψ(x) = −2πα e^{2x} ∫₀^∞ sin(αt)(e^{2t} − 1) ψ(x+t) dt`. -/
theorem gaussBase_commutator (α : ℂ) (x : ℝ) :
    gaussBaseOperator (outwardSine α fun y => (thetaGaussBase y : ℂ)) x -
      outwardSine α (gaussBaseOperator fun y => (thetaGaussBase y : ℂ)) x =
      -(2 * Real.pi * α * Real.exp (2 * x)) *
        ∫ t in Ioi (0 : ℝ), gaussBaseDefectKernel α t * (thetaGaussBase (x + t) : ℂ) := by
  obtain ⟨hI, hI', hd⟩ := hasDerivAt_outwardSine_gaussBase α x
  have h0 : outwardSine α (gaussBaseOperator fun y => (thetaGaussBase y : ℂ)) x = 0 := by
    have : (gaussBaseOperator fun y => (thetaGaussBase y : ℂ)) = fun _ => 0 :=
      funext gaussBaseOperator_thetaGaussBase
    simp [this, outwardSine]
  rw [h0, sub_zero, gaussBaseOperator, hd.deriv, outwardSine, outwardSine, ← mul_assoc,
    mul_comm _ α, mul_assoc, ← mul_sub, ← integral_const_mul, ← integral_sub hI' (hI.const_mul _),
    ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [gaussBaseDefectKernel, thetaGaussBaseDerivC, gaussBaseCoeff]
  rw [show 2 * (x + t) = 2 * x + 2 * t by ring, Real.exp_add]
  push_cast
  ring

theorem exp_two_mul_sub_one_le_mul_exp (t : ℝ) :
    Real.exp (2 * t) - 1 ≤ 2 * t * Real.exp (2 * t) := by
  have h := Real.add_one_le_exp (-(2 * t))
  have h1 : Real.exp (-(2 * t)) * Real.exp (2 * t) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (2 * t)]

/-- **The defect at the tail**: `e^{4x} [L, T_α] ψ(x) / ψ(x) → −α²/π²`. -/
theorem tendsto_gaussBase_commutator (α : ℂ) :
    Tendsto (fun x => ((Real.exp (4 * x) : ℝ) : ℂ) *
      (gaussBaseOperator (outwardSine α fun y => (thetaGaussBase y : ℂ)) x -
        outwardSine α (gaussBaseOperator fun y => (thetaGaussBase y : ℂ)) x) /
          (thetaGaussBase x : ℂ)) atTop (𝓝 (-(α ^ 2) / (Real.pi : ℂ) ^ 2)) := by
  have hKc : Continuous (gaussBaseDefectKernel α) := by
    unfold gaussBaseDefectKernel; fun_prop
  have hKb : ∀ t, 0 < t → ‖gaussBaseDefectKernel α t‖ ≤
      (2 * ‖α‖) * t ^ 2 * Real.exp ((|α.im| + 2) * t) := by
    intro t ht
    have hs := norm_csin_mul_ofReal_le_mul_exp α ht.le
    have he := exp_two_mul_sub_one_le_mul_exp t
    have he0 : 0 ≤ Real.exp (2 * t) - 1 := by linarith [Real.one_le_exp (by linarith : 0 ≤ 2 * t)]
    rw [gaussBaseDefectKernel, norm_mul, Complex.norm_real, Real.norm_of_nonneg he0]
    calc ‖Complex.sin (α * t)‖ * (Real.exp (2 * t) - 1) ≤
          (‖α‖ * t * Real.exp (|α.im| * t)) * (2 * t * Real.exp (2 * t)) :=
          mul_le_mul hs he he0 (by positivity)
      _ = _ := by rw [show (|α.im| + 2) * t = |α.im| * t + 2 * t by ring, Real.exp_add]; ring
  have hK0 : Tendsto (fun t => gaussBaseDefectKernel α t / (t : ℂ) ^ 2) (𝓝[>] 0) (𝓝 (2 * α)) := by
    have he : Tendsto (fun t : ℝ => (((Real.exp (2 * t) - 1 : ℝ) : ℂ) / (t : ℂ))) (𝓝[>] 0)
        (𝓝 2) := by
      have hd := (hasDerivAt_exp_two_mul 0).tendsto_slope_zero
      simp only [zero_add, mul_zero, Real.exp_zero, mul_one, smul_eq_mul] at hd
      have := (Complex.continuous_ofReal.tendsto 2).comp
        (hd.mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht))
      refine this.congr fun t => ?_
      simp only [Function.comp]
      push_cast
      rw [inv_mul_eq_div]
    have := (tendsto_csin_mul_div α).mul he
    rw [mul_comm] at this
    refine this.congr fun t => ?_
    simp only [gaussBaseDefectKernel]
    ring
  have hlim := thetaTypeTail_gaussBase.tendsto_integral_kernel hKc.stronglyMeasurable 2 hKb hK0
  have h2 := hlim.const_mul (-(2 * Real.pi * α) : ℂ)
  have hval : -(2 * (Real.pi : ℂ) * α) * (2 * α * ((Nat.factorial 2 : ℕ) : ℂ) /
      (2 * (Real.pi : ℂ)) ^ (2 + 1)) = -(α ^ 2) / (Real.pi : ℂ) ^ 2 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [Nat.factorial_two]
    push_cast
    field_simp
  rw [hval] at h2
  refine h2.congr fun x => ?_
  rw [gaussBase_commutator]
  have hψ : (thetaGaussBase x : ℂ) ≠ 0 := by exact_mod_cast (thetaGaussBase_pos x).ne'
  have hexp : ((Real.exp (2 * ((2 : ℕ) + 1) * x) : ℝ) : ℂ) =
      ((Real.exp (4 * x) : ℝ) : ℂ) * ((Real.exp (2 * x) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; push_cast; ring
  rw [hexp]
  push_cast
  ring

/-- **The defect is not identically zero**: for `α ≠ 0`, `[L, T_α] ψ` vanishes at no point of some
half-line `[X, ∞)`. -/
theorem gaussBase_commutator_eventually_ne_zero {α : ℂ} (hα : α ≠ 0) :
    ∀ᶠ x in atTop, gaussBaseOperator (outwardSine α fun y => (thetaGaussBase y : ℂ)) x -
      outwardSine α (gaussBaseOperator fun y => (thetaGaussBase y : ℂ)) x ≠ 0 := by
  have hne : -(α ^ 2) / (Real.pi : ℂ) ^ 2 ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact div_ne_zero (neg_ne_zero.2 (pow_ne_zero 2 hα)) (pow_ne_zero 2 hπ)
  filter_upwards [(tendsto_gaussBase_commutator α).eventually_ne hne] with x hx h0
  rw [h0, mul_zero, zero_div] at hx
  exact hx rfl

/-- The seed tail estimate for the base: `T_α ψ / ψ → 0` (indeed `e^{4x} T_α ψ/ψ → α²/(2π)²`). -/
theorem tendsto_outwardSine_gaussBase_div (α : ℂ) :
    Tendsto (fun x => ((Real.exp (4 * x) : ℝ) : ℂ) * outwardSine α (fun y => (thetaGaussBase y : ℂ)) x /
      (thetaGaussBase x : ℂ)) atTop (𝓝 (α ^ 2 / (2 * Real.pi) ^ 2)) ∧
    Tendsto (fun x => outwardSine α (fun y => (thetaGaussBase y : ℂ)) x / (thetaGaussBase x : ℂ))
      atTop (𝓝 0) := by
  have hbase : Tendsto (fun x => ((Real.exp (4 * ((0 : ℕ) : ℝ) * x) : ℝ) : ℂ) *
      (thetaGaussBase x : ℂ) / (thetaGaussBase x : ℂ)) atTop (𝓝 1) :=
    tendsto_const_nhds.congr fun x => by
      have : (thetaGaussBase x : ℂ) ≠ 0 := by exact_mod_cast (thetaGaussBase_pos x).ne'
      simp [this]
  have h1 := thetaTypeTail_gaussBase.tendsto_outwardSine
    (Complex.continuous_ofReal.comp continuous_thetaGaussBase).stronglyMeasurable hbase α
  have h1' : Tendsto (fun x => ((Real.exp (4 * ((1 : ℕ) : ℝ) * x) : ℝ) : ℂ) *
      outwardSine α (fun y => (thetaGaussBase y : ℂ)) x / (thetaGaussBase x : ℂ)) atTop
      (𝓝 (1 * α ^ 2 / (2 * Real.pi) ^ 2)) := by
    refine h1.congr fun x => ?_
    simp only [Nat.cast_zero, Nat.cast_one, zero_add, Function.comp_def]
  refine ⟨?_, ?_⟩
  · refine (h1'.congr fun x => ?_).trans_eq (by rw [one_mul])
    simp only [Nat.cast_one, mul_one]
  · have h2 := ThetaTypeTail.tendsto_of_lt_order (j := 1) (j' := 0) h1' (by norm_num)
    refine h2.congr fun x => ?_
    simp only [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]

end

end RHTower
