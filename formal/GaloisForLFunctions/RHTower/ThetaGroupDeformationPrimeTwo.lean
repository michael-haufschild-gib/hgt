import GaloisForLFunctions.RHTower.ThetaGroupOffLineStripZero
import GaloisForLFunctions.RHTower.ThetaCuspReflection
import GaloisForLFunctions.RHTower.ThetaCuspFourierLaplace

/-!
# The route-2 prime-2 relation is regularity at the zero-charge cusp

The undeformed basis form `θ₃` has exactly the theta source of `ξ`, so its transform is `XiC`.
The deformation `θ₃(1 + t₁h + t₂h²)` keeps the two-periodicity, the exact theta inversion law and an
even integer-spectrum source; `thetaGroupDeformation_offLine_strip_zero` gives real parameters for
which its transform `XiC + t₁Ξ₁ + t₂Ξ₂` vanishes at a point with `0 < im z < 1/2`.

The boundary self-similarity of route 2, `F(τ) + F(τ+1) = 2F(4τ)`
(`Q(r+1)+Q(r)=½Q(4r)` in potential form), forces exponential vanishing at the cusp `1`
(`norm_cusp_one_le_of_primeTwo`: the constant term cancels because `2 = 4^{1/2}`), and inside the
deformation family it holds exactly at `t₁ = t₂ = 0` (`thetaGroupDeformation_primeTwo_iff`).
-/

open Complex MeasureTheory Filter Topology
open scoped Real

namespace RHTower

noncomputable section

open Bottcher HurwitzZeta

theorem thetaGroupBasis_zero_axis (x : ℝ) :
    thetaGroupBasis 0 (modAxisPoint x) = ((evenKernel 0 (Real.exp (2 * x)) : ℝ) : ℂ) := by
  have h := evenKernel_def 0 (Real.exp (2 * x))
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, zero_pow two_ne_zero,
    Complex.exp_zero, one_mul] at h
  rw [show ((0 : ℝ) : UnitAddCircle) = 0 by simp] at h
  rw [h, thetaGroupBasis, pow_zero, mul_one, thetaThree, modAxisPoint]

theorem modTail_thetaGroupBasis_zero :
    modTail (thetaGroupBasis 0) 1 = fun x => ((thetaCuspTailDerivative 0 x : ℝ) : ℂ) := by
  funext x
  rw [modTail, thetaGroupBasis_zero_axis, thetaCuspTailDerivative_zero_eq_evenKernel]
  push_cast
  ring

theorem modTailDeriv_thetaGroupBasis_zero (x : ℝ) :
    modTailDeriv (thetaGroupBasis 0) 1 x = ((thetaCuspTailDerivative 1 x : ℝ) : ℂ) := by
  have h1 := hasDerivAt_modTail 1 (differentiableOn_thetaGroupBasis 0) x
  rw [modTail_thetaGroupBasis_zero] at h1
  have h2 := (hasDerivAt_thetaCuspTailDerivative 0 x).ofReal_comp
  exact h1.unique h2

theorem modTailDeriv2_thetaGroupBasis_zero (x : ℝ) :
    modTailDeriv2 (thetaGroupBasis 0) 1 x = ((thetaCuspTailDerivative 2 x : ℝ) : ℂ) := by
  have h1 := hasDerivAt_modTailDeriv 1 (differentiableOn_thetaGroupBasis 0) x
  have hfun : modTailDeriv (thetaGroupBasis 0) 1 =
      fun x => ((thetaCuspTailDerivative 1 x : ℝ) : ℂ) :=
    funext modTailDeriv_thetaGroupBasis_zero
  rw [hfun] at h1
  have h2 := (hasDerivAt_thetaCuspTailDerivative 1 x).ofReal_comp
  exact h1.unique h2

/-- The basis form `θ₃` has exactly the theta source of `ξ`. -/
theorem modSource_thetaGroupBasis_zero (x : ℝ) :
    modSource (thetaGroupBasis 0) x = ((thetaCuspFullSource x : ℝ) : ℂ) := by
  rw [modSource_eq _ 1, modTailDeriv2_thetaGroupBasis_zero, modTail_thetaGroupBasis_zero,
    thetaCuspFullSource_eq_tail_second_sub]
  push_cast
  ring

theorem thetaGroupXi_zero_eq_thetaCuspFourierLaplace (w : ℂ) :
    thetaGroupXi 0 w = thetaCuspFourierLaplace w := by
  unfold thetaGroupXi modXi thetaCuspFourierLaplace
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [modXiIntegrand, thetaCuspFourierLaplaceIntegrand, modSource_thetaGroupBasis_zero]

/-- **The undeformed member is `ξ`.** -/
theorem thetaGroupXi_zero_eq_XiC : thetaGroupXi 0 = XiC := by
  have hA : AnalyticOnNhd ℂ (fun w => thetaGroupXi 0 w - XiC w) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((differentiable_thetaGroupXi 0).sub XiC_differentiable)
  have h0 : thetaCuspFourierLaplaceStrip ∈ 𝓝 (0 : ℂ) :=
    isOpen_thetaCuspFourierLaplaceStrip.mem_nhds (by
      simp [thetaCuspFourierLaplaceStrip])
  have hev : (fun w => thetaGroupXi 0 w - XiC w) =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [h0] with w hw
    rw [thetaGroupXi_zero_eq_thetaCuspFourierLaplace, thetaCuspFourierLaplace_eq_XiC_on_strip hw]
    simp
  have hz := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ 0) hev
  funext w
  have := hz (Set.mem_univ w)
  simp only [Pi.zero_apply] at this
  exact sub_eq_zero.mp this


/-! ## The deformation family and its off-line zero -/

/-- The real two-parameter theta-group deformation `θ₃(1 + t₁h + t₂h²)` of the theta source. -/
def thetaGroupDeformation (t₁ t₂ : ℝ) (τ : ℂ) : ℂ :=
  thetaThree τ * (1 + (t₁ : ℂ) * thetaGroupHauptmodul τ + (t₂ : ℂ) * thetaGroupHauptmodul τ ^ 2)

theorem thetaGroupDeformation_eq_form (t₁ t₂ : ℝ) :
    thetaGroupDeformation t₁ t₂ =
      thetaGroupForm (1 + Polynomial.C (t₁ : ℂ) * Polynomial.X +
        Polynomial.C (t₂ : ℂ) * Polynomial.X ^ 2) := by
  funext τ
  simp [thetaGroupDeformation, thetaGroupForm]

theorem thetaGroupDeformation_add_two (t₁ t₂ : ℝ) (τ : ℂ) :
    thetaGroupDeformation t₁ t₂ (τ + 2) = thetaGroupDeformation t₁ t₂ τ := by
  rw [thetaGroupDeformation_eq_form, thetaGroupForm_add_two]

theorem thetaGroupDeformation_S (t₁ t₂ : ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaGroupDeformation t₁ t₂ (-1 / τ) =
      (-I * τ) ^ (1 / 2 : ℂ) * thetaGroupDeformation t₁ t₂ τ := by
  rw [thetaGroupDeformation_eq_form, thetaGroupForm_S _ hτ]

theorem thetaGroupDeformation_eq_comb (t₁ t₂ : ℝ) :
    thetaGroupDeformation t₁ t₂ = fun τ => (1 : ℂ) * thetaGroupBasis 0 τ +
      (1 : ℂ) * ((t₁ : ℂ) * thetaGroupBasis 1 τ + (t₂ : ℂ) * thetaGroupBasis 2 τ) := by
  funext τ
  simp only [thetaGroupDeformation, thetaGroupBasis]
  ring

theorem modXi_thetaGroupDeformation (t₁ t₂ : ℝ) (w : ℂ) :
    modXi (thetaGroupDeformation t₁ t₂) w =
      XiC w + (t₁ : ℂ) * thetaGroupXi 1 w + (t₂ : ℂ) * thetaGroupXi 2 w := by
  have h1 := differentiableOn_thetaGroupBasis 1
  have h2 := differentiableOn_thetaGroupBasis 2
  have h12 : DifferentiableOn ℂ
      (fun τ => (t₁ : ℂ) * thetaGroupBasis 1 τ + (t₂ : ℂ) * thetaGroupBasis 2 τ) modUpperSet :=
    (h1.const_mul _).add (h2.const_mul _)
  have hint12 : Integrable (modXiIntegrand
      (fun τ => (t₁ : ℂ) * thetaGroupBasis 1 τ + (t₂ : ℂ) * thetaGroupBasis 2 τ) w) := by
    have heq : modXiIntegrand
        (fun τ => (t₁ : ℂ) * thetaGroupBasis 1 τ + (t₂ : ℂ) * thetaGroupBasis 2 τ) w =
        fun x => (t₁ : ℂ) * modXiIntegrand (thetaGroupBasis 1) w x +
          (t₂ : ℂ) * modXiIntegrand (thetaGroupBasis 2) w x := by
      funext x
      unfold modXiIntegrand
      rw [modSource_linear_comb h1 h2]
      ring
    rw [heq]
    exact ((integrable_thetaGroupXiIntegrand 1 w).const_mul _).add
      ((integrable_thetaGroupXiIntegrand 2 w).const_mul _)
  rw [thetaGroupDeformation_eq_comb,
    modXi_two_comb 1 1 (differentiableOn_thetaGroupBasis 0) h12 w
      (integrable_thetaGroupXiIntegrand 0 w) hint12,
    modXi_two_comb _ _ h1 h2 w (integrable_thetaGroupXiIntegrand 1 w)
      (integrable_thetaGroupXiIntegrand 2 w)]
  rw [show modXi (thetaGroupBasis 0) w = thetaGroupXi 0 w from rfl, thetaGroupXi_zero_eq_XiC]
  simp only [thetaGroupXi]
  ring

/-- The source of every deformation is even, so its transform is even and conjugation-paired. -/
theorem modSource_thetaGroupDeformation_neg (t₁ t₂ : ℝ) (x : ℝ) :
    modSource (thetaGroupDeformation t₁ t₂) (-x) = modSource (thetaGroupDeformation t₁ t₂) x := by
  have hd : DifferentiableOn ℂ (thetaGroupDeformation t₁ t₂) modUpperSet := by
    rw [thetaGroupDeformation_eq_form]
    intro τ hτ
    exact (differentiableAt_thetaGroupForm _ hτ).differentiableWithinAt
  refine modSource_neg hd (fun y => ?_) x
  rw [thetaGroupDeformation_eq_form]
  exact thetaGroupForm_axis _ y

/-- **Countermodel.**  A real theta-group deformation `θ₃(1 + t₁h + t₂h²)` of the theta source of
`ξ` — two-periodic, with the exact theta inversion law, an even source, and the same analytic
domain — has a transform zero strictly inside the critical strip and off the critical line. -/
theorem thetaGroupDeformation_offLine_strip_zero :
    ∃ t₁ t₂ : ℝ, ∃ z₀ : ℂ, 0 < z₀.im ∧ z₀.im < 1 / 2 ∧
      modXi (thetaGroupDeformation t₁ t₂) z₀ = 0 := by
  obtain ⟨t₁, t₂, z₀, h1, h2, h0⟩ := thetaGroup_offLine_strip_zero
  refine ⟨t₁, t₂, z₀, h1, h2, ?_⟩
  rw [modXi_thetaGroupDeformation, ← thetaGroupXi_zero_eq_XiC]
  exact h0


/-! ## The prime-2 relation is regularity at the zero-charge cusp -/

/-- The prime-2 self-similarity `F(τ) + F(τ+1) = 2F(4τ)` of the route-2 boundary potential, in
theta normalization. -/
def PrimeTwoRelation (F : ℂ → ℂ) : Prop :=
  ∀ τ : ℂ, 0 < τ.im → F τ + F (τ + 1) = 2 * F (4 * τ)

theorem I_div_ofReal_im (y : ℝ) : (I / (y : ℂ)).im = 1 / y := by
  simp [Complex.div_im]

/-- **Cusp rigidity.**  The prime-2 relation and the weight-`½` inversion law force exponential
vanishing at the zero-charge cusp `1`: the constant term cancels because `2 = 4^{1/2}`. -/
theorem norm_cusp_one_le_of_primeTwo {F : ℂ → ℂ} {c : ℂ} {M : ℝ} (hR2 : PrimeTwoRelation F)
    (hS : ∀ y : ℝ, 0 < y → F (I / (y : ℂ)) = (Real.sqrt y : ℂ) * F (I * (y : ℂ)))
    (hdec : ∀ y : ℝ, 1 ≤ y → ‖F (I * (y : ℂ)) - c‖ ≤ M * Real.exp (-π * y))
    {y : ℝ} (hy : 4 ≤ y) :
    ‖F (1 + I / (y : ℂ))‖ ≤ 2 * M * Real.sqrt y * Real.exp (-π * y / 4) := by
  have hy0 : 0 < y := by linarith
  have hy4 : 0 < y / 4 := by linarith
  have hM : 0 ≤ M := by
    have h1 := hdec 1 le_rfl
    by_contra hneg
    have := not_le.mp hneg
    nlinarith [norm_nonneg (F (I * ((1 : ℝ) : ℂ)) - c), Real.exp_pos (-π * 1)]
  have hR := hR2 (I / (y : ℂ)) (by rw [I_div_ofReal_im y]; positivity)
  have h4 : 4 * (I / (y : ℂ)) = I / ((y / 4 : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [h4, hS (y / 4) hy4, hS y hy0, add_comm (I / (y : ℂ)) 1] at hR
  have hsq : Real.sqrt (y / 4) = Real.sqrt y / 2 := by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hkey : F (1 + I / (y : ℂ)) = (Real.sqrt y : ℂ) *
      ((F (I * ((y / 4 : ℝ) : ℂ)) - c) - (F (I * (y : ℂ)) - c)) := by
    rw [hsq] at hR
    push_cast at hR ⊢
    linear_combination hR
  rw [hkey, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := hdec (y / 4) (by linarith)
  have h2 := hdec y (by linarith)
  have hexp : Real.exp (-π * y) ≤ Real.exp (-π * (y / 4)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  calc Real.sqrt y * ‖(F (I * ((y / 4 : ℝ) : ℂ)) - c) - (F (I * (y : ℂ)) - c)‖
      ≤ Real.sqrt y * (M * Real.exp (-π * (y / 4)) + M * Real.exp (-π * y)) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2))
          (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt y * (M * Real.exp (-π * (y / 4)) + M * Real.exp (-π * (y / 4))) := by
        gcongr
    _ = 2 * M * Real.sqrt y * Real.exp (-π * y / 4) := by
        rw [show -π * (y / 4) = -π * y / 4 by ring]; ring

theorem thetaThree_primeTwo : PrimeTwoRelation thetaThree := by
  intro τ hτ
  rw [thetaThree_eq_jacobiTheta, thetaThree_eq_jacobiTheta, thetaThree_eq_jacobiTheta,
    add_comm τ 1, jacobiTheta_one_add hτ]
  ring

theorem sqrt_cpow_axis {y : ℝ} (hy : 0 < y) :
    (-I * (I * (y : ℂ))) ^ (1 / 2 : ℂ) = (Real.sqrt y : ℂ) := by
  rw [← mul_assoc, show -I * I = 1 by rw [neg_mul, I_mul_I]; ring, one_mul,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow hy.le, Real.sqrt_eq_rpow]

theorem neg_one_div_I_mul {y : ℝ} (hy : 0 < y) : -1 / (I * (y : ℂ)) = I / (y : ℂ) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  field_simp
  rw [I_sq]

theorem thetaGroupDeformation_axis_S (t₁ t₂ : ℝ) {y : ℝ} (hy : 0 < y) :
    thetaGroupDeformation t₁ t₂ (I / (y : ℂ)) =
      (Real.sqrt y : ℂ) * thetaGroupDeformation t₁ t₂ (I * (y : ℂ)) := by
  have h := thetaGroupDeformation_S t₁ t₂ (τ := I * (y : ℂ)) (by simpa using hy)
  rw [neg_one_div_I_mul hy, sqrt_cpow_axis hy] at h
  exact h

/-- Theta values at the zero-charge cusp, transported to the cusp `∞`. -/
theorem thetaThree_one_add_I_div {y : ℝ} (hy : 0 < y) :
    thetaThree (1 + I / (y : ℂ)) = (Real.sqrt y : ℂ) * thetaTwo (I * (y : ℂ)) := by
  have hy' : (I * (y : ℂ)) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hy.ne')
  rw [add_comm, thetaThree_add_one, ← neg_one_div_I_mul hy, thetaFour_S _ hy']
  have hIy : I / (I * (y : ℂ)) = ((1 / y : ℝ) : ℂ) := by
    have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast; field_simp
  rw [hIy, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_div' _ hy.le,
    Real.sqrt_one]
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  push_cast
  field_simp

theorem thetaGroupHauptmodul_one_add_I_div {y : ℝ} (hy : 0 < y) :
    thetaGroupHauptmodul (1 + I / (y : ℂ)) =
      -(thetaFour (I * (y : ℂ)) ^ 4 * thetaThree (I * (y : ℂ)) ^ 4 /
        thetaTwo (I * (y : ℂ)) ^ 8) := by
  have hy' : (I * (y : ℂ)) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hy.ne')
  have hτ : 0 < (I * (y : ℂ)).im := by simpa using hy
  unfold thetaGroupHauptmodul
  rw [add_comm, thetaTwo_add_one, thetaFour_add_one, thetaThree_add_one,
    ← neg_one_div_I_mul hy, thetaTwo_S _ hy', thetaThree_S _ hy', thetaFour_S _ hy']
  have hIy : I / (I * (y : ℂ)) = ((1 / y : ℝ) : ℂ) := by
    have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast; field_simp
  rw [hIy, show -I * (I * (y : ℂ)) = (y : ℂ) by rw [← mul_assoc, neg_mul, I_mul_I]; ring]
  have hexp : Complex.exp ((π : ℂ) * I / 4) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul, show ((4 : ℕ) : ℂ) * ((π : ℂ) * I / 4) = π * I by push_cast; ring]
    exact Complex.exp_pi_mul_I
  have h2 := thetaTwo_ne_zero_of_im_pos hτ
  have h3 := thetaThree_ne_zero_of_im_pos hτ
  have hA : ((1 / y : ℝ) : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push_cast; simp [hy.ne']
  have hB : (y : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; simp [hy.ne']
  have hAB : (((1 / y : ℝ) : ℂ) ^ (1 / 2 : ℂ)) * ((y : ℂ) ^ (1 / 2 : ℂ)) = 1 := by
    rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) hy.le]
    push_cast
    rw [div_mul_cancel₀ _ (by exact_mod_cast hy.ne'), Complex.one_cpow]
  rw [mul_pow, hexp]
  field_simp
  have hAB4 : (((1 / y : ℝ) : ℂ) ^ (1 / 2 : ℂ)) ^ 4 * ((y : ℂ) ^ (1 / 2 : ℂ)) ^ 4 = 1 := by
    rw [← mul_pow, hAB, one_pow]
  linear_combination (-(thetaFour (I * (y : ℂ)) ^ 4)) * hAB4


theorem tendsto_thetaTwo_axis : Tendsto (fun y : ℝ => thetaTwo (I * (y : ℂ))) atTop (𝓝 0) := by
  have hb : Tendsto (fun y : ℝ => thetaTwoCuspConstant * Real.exp (-π * y / 4)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < π / 4))
    have h2 := h.const_mul thetaTwoCuspConstant
    rw [mul_zero] at h2
    refine h2.congr fun y => ?_
    simp only [Function.comp_apply, id]; ring_nf
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have := norm_thetaTwo_le (τ := I * (y : ℂ)) (by simpa using hy)
  simpa using this

theorem tendsto_sub_one_axis {f : ℂ → ℂ}
    (hf : ∀ τ : ℂ, 1 ≤ τ.im → ‖f τ - 1‖ ≤ jacobiThetaTailConstant * Real.exp (-π * τ.im)) :
    Tendsto (fun y : ℝ => f (I * (y : ℂ))) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun y : ℝ => jacobiThetaTailConstant * Real.exp (-π * y)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop Real.pi_pos)
    have h2 := h.const_mul jacobiThetaTailConstant
    rw [mul_zero] at h2
    refine h2.congr fun y => ?_
    simp only [Function.comp_apply, id]; ring_nf
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have := hf (I * (y : ℂ)) (by simpa using hy)
  simpa using this

theorem thetaGroupDeformation_cuspDecay (t₁ t₂ : ℝ) :
    ∃ M : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
      ‖thetaGroupDeformation t₁ t₂ τ - 1‖ ≤ M * Real.exp (-π * τ.im) := by
  obtain ⟨M₀, h0⟩ := thetaGroupBasis_cuspDecay 0
  obtain ⟨M₁, h1⟩ := thetaGroupBasis_cuspDecay 1
  obtain ⟨M₂, h2⟩ := thetaGroupBasis_cuspDecay 2
  refine ⟨M₀ + |t₁| * M₁ + |t₂| * M₂, fun τ hτ => ?_⟩
  have e0 := h0 τ hτ
  have e1 := h1 τ hτ
  have e2 := h2 τ hτ
  simp only [thetaGroupBasisCusp, if_true, one_ne_zero, if_false, sub_zero,
    OfNat.ofNat_ne_zero] at e0 e1 e2
  have hsplit : thetaGroupDeformation t₁ t₂ τ - 1 = (thetaGroupBasis 0 τ - 1) +
      (t₁ : ℂ) * thetaGroupBasis 1 τ + (t₂ : ℂ) * thetaGroupBasis 2 τ := by
    simp only [thetaGroupDeformation, thetaGroupBasis]; ring
  rw [hsplit]
  calc ‖(thetaGroupBasis 0 τ - 1) + (t₁ : ℂ) * thetaGroupBasis 1 τ +
        (t₂ : ℂ) * thetaGroupBasis 2 τ‖
      ≤ ‖thetaGroupBasis 0 τ - 1‖ + |t₁| * ‖thetaGroupBasis 1 τ‖ +
          |t₂| * ‖thetaGroupBasis 2 τ‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ M₀ * Real.exp (-π * τ.im) + |t₁| * (M₁ * Real.exp (-π * τ.im)) +
          |t₂| * (M₂ * Real.exp (-π * τ.im)) := by gcongr
    _ = (M₀ + |t₁| * M₁ + |t₂| * M₂) * Real.exp (-π * τ.im) := by ring

/-- **The prime-2 relation singles out the theta source inside the deformation family.**
`θ₃(1 + t₁h + t₂h²)` satisfies `F(τ) + F(τ+1) = 2F(4τ)` exactly when `t₁ = t₂ = 0`: the
deformations carry charge at the zero-charge cusp `1`, which the relation forbids. -/
theorem thetaGroupDeformation_primeTwo_iff (t₁ t₂ : ℝ) :
    PrimeTwoRelation (thetaGroupDeformation t₁ t₂) ↔ t₁ = 0 ∧ t₂ = 0 := by
  constructor
  · intro hR2
    obtain ⟨M, hM⟩ := thetaGroupDeformation_cuspDecay t₁ t₂
    have hdec : ∀ y : ℝ, 1 ≤ y →
        ‖thetaGroupDeformation t₁ t₂ (I * (y : ℂ)) - 1‖ ≤ M * Real.exp (-π * y) := by
      intro y hy
      have := hM (I * (y : ℂ)) (by simpa using hy)
      simpa using this
    have hS : ∀ y : ℝ, 0 < y → thetaGroupDeformation t₁ t₂ (I / (y : ℂ)) =
        (Real.sqrt y : ℂ) * thetaGroupDeformation t₁ t₂ (I * (y : ℂ)) :=
      fun y hy => thetaGroupDeformation_axis_S t₁ t₂ hy
    -- the cusp-one expression
    set θ2 : ℝ → ℂ := fun y => thetaTwo (I * (y : ℂ)) with hθ2
    set θ3 : ℝ → ℂ := fun y => thetaThree (I * (y : ℂ)) with hθ3
    set θ4 : ℝ → ℂ := fun y => thetaFour (I * (y : ℂ)) with hθ4
    have hbound : ∀ᶠ y in atTop,
        ‖θ2 y ^ 16 - (t₁ : ℂ) * θ4 y ^ 4 * θ3 y ^ 4 * θ2 y ^ 8 + (t₂ : ℂ) * θ4 y ^ 8 * θ3 y ^ 8‖
          ≤ 2 * M * Real.exp (-π * y / 4) * ‖θ2 y‖ ^ 15 := by
      filter_upwards [eventually_ge_atTop (4 : ℝ)] with y hy
      have hy0 : 0 < y := by linarith
      have hτ : 0 < (I * (y : ℂ)).im := by simpa using hy0
      have hne : θ2 y ≠ 0 := thetaTwo_ne_zero_of_im_pos hτ
      have hc := norm_cusp_one_le_of_primeTwo (c := 1) hR2 hS hdec hy
      have hval : thetaGroupDeformation t₁ t₂ (1 + I / (y : ℂ)) =
          (Real.sqrt y : ℂ) * θ2 y * (1 + (t₁ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8)) +
            (t₂ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8)) ^ 2) := by
        simp only [thetaGroupDeformation, thetaThree_one_add_I_div hy0,
          thetaGroupHauptmodul_one_add_I_div hy0, hθ2, hθ3, hθ4]
      have hid : θ2 y ^ 16 - (t₁ : ℂ) * θ4 y ^ 4 * θ3 y ^ 4 * θ2 y ^ 8 +
          (t₂ : ℂ) * θ4 y ^ 8 * θ3 y ^ 8 =
          θ2 y ^ 15 * (θ2 y * (1 + (t₁ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8)) +
            (t₂ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8)) ^ 2)) := by
        field_simp
        ring
      rw [hval] at hc
      have hsq : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
      have hc' : ‖θ2 y * (1 + (t₁ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8)) +
            (t₂ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8)) ^ 2)‖ ≤
          2 * M * Real.exp (-π * y / 4) := by
        rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hsq] at hc
        have : Real.sqrt y * ‖θ2 y * (1 + (t₁ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8)) +
            (t₂ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8)) ^ 2)‖ ≤
            Real.sqrt y * (2 * M * Real.exp (-π * y / 4)) := by linarith
        exact le_of_mul_le_mul_left this hsq
      rw [hid, norm_mul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right hc' (by positivity)
    have hM0 : Tendsto (fun y : ℝ => 2 * M * Real.exp (-π * y / 4) * ‖θ2 y‖ ^ 15) atTop (𝓝 0) := by
      have h1 : Tendsto (fun y : ℝ => ‖θ2 y‖ ^ 15) atTop (𝓝 0) := by
        have := (tendsto_thetaTwo_axis.norm).pow 15
        simpa using this
      have h2 : Tendsto (fun y : ℝ => 2 * M * Real.exp (-π * y / 4)) atTop (𝓝 0) := by
        have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < π / 4))
        have h3 := h.const_mul (2 * M)
        rw [mul_zero] at h3
        refine h3.congr fun y => ?_
        simp only [Function.comp_apply, id]; ring_nf
      have := h2.mul h1
      rw [mul_zero] at this
      exact this
    have hlim0 := squeeze_zero_norm' hbound hM0
    have ht2lim : Tendsto (fun y : ℝ => θ2 y ^ 16 - (t₁ : ℂ) * θ4 y ^ 4 * θ3 y ^ 4 * θ2 y ^ 8 +
        (t₂ : ℂ) * θ4 y ^ 8 * θ3 y ^ 8) atTop (𝓝 (t₂ : ℂ)) := by
      have h2 := tendsto_thetaTwo_axis
      have h3 := tendsto_sub_one_axis (f := thetaThree) (fun τ hτ => norm_thetaThree_sub_one_le hτ)
      have h4 := tendsto_sub_one_axis (f := thetaFour) (fun τ hτ => norm_thetaFour_sub_one_le hτ)
      have := (((h2.pow 16).sub ((((tendsto_const_nhds (x := (t₁ : ℂ))).mul (h4.pow 4)).mul
        (h3.pow 4)).mul (h2.pow 8))).add (((tendsto_const_nhds (x := (t₂ : ℂ))).mul
        (h4.pow 8)).mul (h3.pow 8)))
      simpa using this
    have ht2 : (t₂ : ℂ) = 0 := tendsto_nhds_unique ht2lim hlim0
    have ht2' : t₂ = 0 := by exact_mod_cast ht2
    -- second stage with t₂ = 0
    have hbound1 : ∀ᶠ y in atTop,
        ‖θ2 y ^ 8 - (t₁ : ℂ) * θ4 y ^ 4 * θ3 y ^ 4‖ ≤ 2 * M * Real.exp (-π * y / 4) * ‖θ2 y‖ ^ 7 := by
      filter_upwards [eventually_ge_atTop (4 : ℝ)] with y hy
      have hy0 : 0 < y := by linarith
      have hτ : 0 < (I * (y : ℂ)).im := by simpa using hy0
      have hne : θ2 y ≠ 0 := thetaTwo_ne_zero_of_im_pos hτ
      have hc := norm_cusp_one_le_of_primeTwo (c := 1) hR2 hS hdec hy
      have hval : thetaGroupDeformation t₁ t₂ (1 + I / (y : ℂ)) =
          (Real.sqrt y : ℂ) * θ2 y * (1 + (t₁ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8))) := by
        simp only [thetaGroupDeformation, thetaThree_one_add_I_div hy0,
          thetaGroupHauptmodul_one_add_I_div hy0, hθ2, hθ3, hθ4, ht2', Complex.ofReal_zero,
          zero_mul, add_zero]
      have hid : θ2 y ^ 8 - (t₁ : ℂ) * θ4 y ^ 4 * θ3 y ^ 4 =
          θ2 y ^ 7 * (θ2 y * (1 + (t₁ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8)))) := by
        field_simp
        ring
      rw [hval] at hc
      have hsq : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
      have hc' : ‖θ2 y * (1 + (t₁ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8)))‖ ≤
          2 * M * Real.exp (-π * y / 4) := by
        rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hsq] at hc
        have : Real.sqrt y * ‖θ2 y * (1 + (t₁ : ℂ) * (-(θ4 y ^ 4 * θ3 y ^ 4 / θ2 y ^ 8)))‖ ≤
            Real.sqrt y * (2 * M * Real.exp (-π * y / 4)) := by linarith
        exact le_of_mul_le_mul_left this hsq
      rw [hid, norm_mul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right hc' (by positivity)
    have hM1 : Tendsto (fun y : ℝ => 2 * M * Real.exp (-π * y / 4) * ‖θ2 y‖ ^ 7) atTop (𝓝 0) := by
      have h1 : Tendsto (fun y : ℝ => ‖θ2 y‖ ^ 7) atTop (𝓝 0) := by
        have := (tendsto_thetaTwo_axis.norm).pow 7
        simpa using this
      have h2 : Tendsto (fun y : ℝ => 2 * M * Real.exp (-π * y / 4)) atTop (𝓝 0) := by
        have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < π / 4))
        have h3 := h.const_mul (2 * M)
        rw [mul_zero] at h3
        refine h3.congr fun y => ?_
        simp only [Function.comp_apply, id]; ring_nf
      have := h2.mul h1
      rw [mul_zero] at this
      exact this
    have hlim1 := squeeze_zero_norm' hbound1 hM1
    have ht1lim : Tendsto (fun y : ℝ => θ2 y ^ 8 - (t₁ : ℂ) * θ4 y ^ 4 * θ3 y ^ 4) atTop
        (𝓝 (-(t₁ : ℂ))) := by
      have h2 := tendsto_thetaTwo_axis
      have h3 := tendsto_sub_one_axis (f := thetaThree) (fun τ hτ => norm_thetaThree_sub_one_le hτ)
      have h4 := tendsto_sub_one_axis (f := thetaFour) (fun τ hτ => norm_thetaFour_sub_one_le hτ)
      have := (h2.pow 8).sub (((tendsto_const_nhds (x := (t₁ : ℂ))).mul (h4.pow 4)).mul (h3.pow 4))
      simpa using this
    have ht1 : -(t₁ : ℂ) = 0 := tendsto_nhds_unique ht1lim hlim1
    have ht1' : t₁ = 0 := by
      have : (t₁ : ℂ) = 0 := neg_eq_zero.mp ht1
      exact_mod_cast this
    exact ⟨ht1', ht2'⟩
  · rintro ⟨rfl, rfl⟩
    have hfun : thetaGroupDeformation 0 0 = thetaThree := by
      funext τ; simp [thetaGroupDeformation]
    rw [hfun]
    exact thetaThree_primeTwo

end

end RHTower
