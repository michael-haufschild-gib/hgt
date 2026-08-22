/-
# Admissible activation functions (Section 5.2)

An activation `φ : ℝ → ℝ` is admissible for the Busemann layer when it is `C^{1,1}`, convex and
nondecreasing; the step-size condition is then `0 ≤ τ λ² M₂ ≤ 2` with `M₂` a global Lipschitz
constant for `φ'`.  This module verifies admissibility for the two activations used in the
source and records the resulting step-size bounds:

* **softplus** `φ(r) = log(1 + e^r)`, `φ'(r) = e^r/(1+e^r)`, `M₂ = 1/4`, so `τ ≤ 8/λ²`;
* **squared ReLU** `φ(r) = ReLU(r)²/2`, `φ'(r) = ReLU(r)`, `M₂ = 1`, so `τ ≤ 2/λ²`.

In each case `φ'` is proved to be the actual derivative of `φ` at every point — for the
squared ReLU this includes the kink at the origin, where the derivative exists and equals `0`.
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.BusemannLayer
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Real Filter Topology

/-! ## Softplus -/

/-- The softplus activation `φ(r) = log(1 + e^r)`. -/
noncomputable def softplus (r : ℝ) : ℝ := Real.log (1 + Real.exp r)

/-- The derivative of softplus, the logistic function. -/
noncomputable def softplusDeriv (r : ℝ) : ℝ := Real.exp r / (1 + Real.exp r)

theorem one_add_exp_pos (r : ℝ) : 0 < 1 + Real.exp r := by positivity

theorem hasDerivAt_softplus (r : ℝ) : HasDerivAt softplus (softplusDeriv r) r := by
  have h : HasDerivAt (fun x : ℝ => 1 + Real.exp x) (Real.exp r) r := by
    simpa using (Real.hasDerivAt_exp r).const_add 1
  exact h.log (ne_of_gt (one_add_exp_pos r))

theorem softplusDeriv_nonneg (r : ℝ) : 0 ≤ softplusDeriv r := by
  rw [softplusDeriv]; positivity

theorem softplusDeriv_eq (r : ℝ) : softplusDeriv r = 1 - 1 / (1 + Real.exp r) := by
  rw [softplusDeriv]
  field_simp
  ring

theorem softplusDeriv_monotone : Monotone softplusDeriv := by
  intro u v huv
  rw [softplusDeriv_eq, softplusDeriv_eq]
  have h1 : Real.exp u ≤ Real.exp v := Real.exp_le_exp.mpr huv
  have h2 : (0:ℝ) < 1 + Real.exp u := one_add_exp_pos u
  have h3 : (0:ℝ) < 1 + Real.exp v := one_add_exp_pos v
  have : 1 / (1 + Real.exp v) ≤ 1 / (1 + Real.exp u) := by
    apply one_div_le_one_div_of_le h2; linarith
  linarith

/-- The second derivative of softplus. -/
theorem hasDerivAt_softplusDeriv (r : ℝ) :
    HasDerivAt softplusDeriv (Real.exp r / (1 + Real.exp r) ^ 2) r := by
  have h1 : HasDerivAt Real.exp (Real.exp r) r := Real.hasDerivAt_exp r
  have h2 : HasDerivAt (fun x : ℝ => 1 + Real.exp x) (Real.exp r) r := by
    simpa using (Real.hasDerivAt_exp r).const_add 1
  have h := h1.div h2 (ne_of_gt (one_add_exp_pos r))
  have hval : (Real.exp r * (1 + Real.exp r) - Real.exp r * Real.exp r) / (1 + Real.exp r) ^ 2
      = Real.exp r / (1 + Real.exp r) ^ 2 := by
    congr 1; ring
  rw [hval] at h
  exact h

/-- The sharp bound `φ'' ≤ 1/4` for softplus. -/
theorem softplusDeriv_deriv_le (r : ℝ) : Real.exp r / (1 + Real.exp r) ^ 2 ≤ 1 / 4 := by
  have h : (0:ℝ) < (1 + Real.exp r) ^ 2 := by positivity
  rw [div_le_div_iff₀ h (by norm_num)]
  nlinarith [sq_nonneg (1 - Real.exp r)]

/-- `φ'` is globally `1/4`-Lipschitz for softplus. -/
theorem softplusDeriv_lipschitz (u v : ℝ) : |softplusDeriv u - softplusDeriv v| ≤ 1 / 4 * |u - v| := by
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt softplusDeriv (Real.exp x / (1 + Real.exp x) ^ 2) Set.univ x :=
    fun x _ => (hasDerivAt_softplusDeriv x).hasDerivWithinAt
  have hbound : ∀ x ∈ (Set.univ : Set ℝ), ‖Real.exp x / (1 + Real.exp x) ^ 2‖ ≤ 1 / 4 := by
    intro x _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact softplusDeriv_deriv_le x
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound convex_univ
    (Set.mem_univ v) (Set.mem_univ u)
  simpa [Real.norm_eq_abs] using this

/-! ## Squared ReLU -/

/-- The rectified linear unit. -/
noncomputable def relu (r : ℝ) : ℝ := max r 0

/-- The squared-ReLU activation `φ(r) = ReLU(r)²/2`. -/
noncomputable def squaredRelu (r : ℝ) : ℝ := relu r ^ 2 / 2

@[simp] theorem relu_nonneg (r : ℝ) : 0 ≤ relu r := le_max_right _ _

theorem relu_monotone : Monotone relu := fun _ _ h => max_le_max h le_rfl

theorem relu_lipschitz (u v : ℝ) : |relu u - relu v| ≤ 1 * |u - v| := by
  simpa [relu] using abs_max_sub_max_le_abs u v 0

theorem hasDerivAt_squaredRelu (r : ℝ) : HasDerivAt squaredRelu (relu r) r := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have heq : squaredRelu =ᶠ[𝓝 r] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hr] with x hx
      have hx' : x < 0 := hx
      simp [squaredRelu, relu, max_eq_right hx'.le]
    have h0 : HasDerivAt (fun _ : ℝ => (0:ℝ)) 0 r := hasDerivAt_const r 0
    have hz : relu r = 0 := by simp [relu, max_eq_right hr.le]
    rw [hz]
    exact h0.congr_of_eventuallyEq heq
  · subst hr
    have hrelu0 : relu (0:ℝ) = 0 := by simp [relu]
    have hzero : squaredRelu (0:ℝ) = 0 := by simp [squaredRelu, relu]
    rw [hasDerivAt_iff_isLittleO, hrelu0]
    have hsimp : (fun x' : ℝ => squaredRelu x' - squaredRelu 0 - (x' - 0) • (0:ℝ))
        = fun x' : ℝ => relu x' ^ 2 / 2 := by
      funext x'
      rw [hzero]
      simp [squaredRelu]
    rw [hsimp, Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by positivity : (0:ℝ) < 2 * c)] with x hx
    have hx' : |x| < 2 * c := by simpa [Real.dist_eq] using hx
    have hrx : relu x ≤ |x| := by
      rcases le_total x 0 with h | h
      · rw [relu, max_eq_right h]; exact abs_nonneg x
      · rw [relu, max_eq_left h, abs_of_nonneg h]
    have hnn : 0 ≤ relu x := relu_nonneg x
    have hsq : relu x ^ 2 ≤ |x| * |x| := by nlinarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ relu x ^ 2 / 2), sub_zero]
    nlinarith [hsq, abs_nonneg x, hx']
  · have heq : squaredRelu =ᶠ[𝓝 r] fun x => x ^ 2 / 2 := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      have hx' : (0:ℝ) < x := hx
      simp [squaredRelu, relu, max_eq_left hx'.le]
    have h0 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) r r := by
      simpa using (hasDerivAt_pow 2 r).div_const 2
    have hz : relu r = r := by simp [relu, max_eq_left hr.le]
    rw [hz]
    exact h0.congr_of_eventuallyEq heq

/-- **Remark 5.2.**  The squared ReLU is not of class `C²`: its derivative, the ReLU, is not
differentiable at the origin.  Hence the `C^{1,1}` hypothesis of Theorem 4.1 is the right one. -/
theorem not_differentiableAt_relu_zero : ¬ DifferentiableAt ℝ relu 0 := by
  intro hdiff
  have hc : HasDerivAt relu (deriv relu 0) 0 := hdiff.hasDerivAt
  have hslope := hasDerivAt_iff_tendsto_slope.mp hc
  have hpos : Tendsto (slope relu 0) (𝓝[>] (0:ℝ)) (𝓝 (deriv relu 0)) :=
    hslope.mono_left
      (nhdsWithin_mono _ fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_gt hx))
  have hneg : Tendsto (slope relu 0) (𝓝[<] (0:ℝ)) (𝓝 (deriv relu 0)) :=
    hslope.mono_left
      (nhdsWithin_mono _ fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_lt hx))
  have hone : Tendsto (slope relu 0) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0:ℝ) < x := hx
    rw [slope_def_field, relu, relu, max_eq_left hx'.le, max_self, sub_zero]
    exact (div_self (ne_of_gt hx')).symm
  have hzero : Tendsto (slope relu 0) (𝓝[<] (0:ℝ)) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : x < (0:ℝ) := hx
    rw [slope_def_field, relu, relu, max_eq_right hx'.le, max_self, sub_zero]
    simp
  have h1 : deriv relu 0 = 1 := tendsto_nhds_unique hpos hone
  have h0 : deriv relu 0 = 0 := tendsto_nhds_unique hneg hzero
  rw [h1] at h0
  exact one_ne_zero h0

/-- The derivative of the squared ReLU is the ReLU. -/
theorem deriv_squaredRelu : deriv squaredRelu = relu :=
  funext fun r => (hasDerivAt_squaredRelu r).deriv

/-! ## The resulting step-size bounds -/

variable {X : Type*} [MetricSpace X] [NPCSpace X]

/-- Softplus layers are 1-Lipschitz for `0 ≤ τ ≤ 8/λ²`, i.e. `τ λ² ≤ 8`. -/
theorem softplus_layer_nonexpansive (F : BusemannFlow X) (τ lam β : ℝ) (hτ : 0 ≤ τ)
    (hlam : 0 ≤ lam) (hstep : τ * lam ^ 2 ≤ 8) (x y : X) :
    dist (layer F (fun r => τ * lam * softplusDeriv (lam * r + β)) x)
         (layer F (fun r => τ * lam * softplusDeriv (lam * r + β)) y) ≤ dist x y := by
  refine activation_layer_nonexpansive F softplusDeriv τ lam β (1 / 4) hτ hlam
    softplusDeriv_nonneg softplusDeriv_monotone softplusDeriv_lipschitz ?_ x y
  linarith

/-- Squared-ReLU layers are 1-Lipschitz for `0 ≤ τ ≤ 2/λ²`, i.e. `τ λ² ≤ 2`. -/
theorem squaredRelu_layer_nonexpansive (F : BusemannFlow X) (τ lam β : ℝ) (hτ : 0 ≤ τ)
    (hlam : 0 ≤ lam) (hstep : τ * lam ^ 2 ≤ 2) (x y : X) :
    dist (layer F (fun r => τ * lam * relu (lam * r + β)) x)
         (layer F (fun r => τ * lam * relu (lam * r + β)) y) ≤ dist x y := by
  refine activation_layer_nonexpansive F relu τ lam β 1 hτ hlam
    (fun s => relu_nonneg s) relu_monotone relu_lipschitz ?_ x y
  linarith

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
