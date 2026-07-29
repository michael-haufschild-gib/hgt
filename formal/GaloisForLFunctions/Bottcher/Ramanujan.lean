import GaloisForLFunctions.Bottcher.ThetaDiscriminant
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.Liouville

/-!
# Ramanujan's weight-two differential identity

The conflict-free Serre-derivative layer proves that
`D E₂ - E₂² / 12` transforms with weight four.  Adding `E₄ / 12` produces a
weight-four cusp form.  Mathlib's vanishing theorem below weight twelve forces that
defect to be zero, giving Ramanujan's `E₂` equation without an analytic premise.
-/

open UpperHalfPlane hiding I
open Real Complex Filter Topology Set
open ModularForm EisensteinSeries MatrixGroups SlashInvariantForm
open scoped MatrixGroups Manifold

namespace Bottcher

noncomputable section

local notation "D" => Derivative.normalizedDerivOfComplex
local notation "serre_D" => Derivative.serreDerivative
local notation "E₂" => EisensteinSeries.E2

private theorem tendsto_im_atImInfty_ramanujan :
    Tendsto (fun x : ℍ => x.im) atImInfty atTop := by
  exact tendsto_comap

private theorem mdifferentiable_D2_ramanujan (γ : SL(2, ℤ)) :
    MDiff (EisensteinSeries.D2 γ) := by
  have hconst : MDiff (fun _ : ℍ =>
      (2 * Real.pi * I * (γ 1 0 : ℂ))) := mdifferentiable_const
  have h := hconst.mul
    (UpperHalfPlane.mdifferentiable_inv_denom
      (γ : GL (Fin 2) ℝ))
  simpa only [EisensteinSeries.D2, div_eq_mul_inv, Pi.mul_apply] using! h

private theorem normalizedDerivOfComplex_D2_ramanujan
    (γ : SL(2, ℤ)) (z : ℍ) :
    D (EisensteinSeries.D2 γ) z =
      -(γ 1 0 : ℂ) ^ 2 / (denom γ z) ^ 2 := by
  have hz_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hderiv :
      deriv ((EisensteinSeries.D2 γ) ∘ ofComplex) z =
        deriv (fun w =>
          (2 * Real.pi * I * (γ 1 0 : ℂ)) / denom γ w) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw,
      EisensteinSeries.D2]
  simp only [Derivative.normalizedDerivOfComplex, hderiv,
    div_eq_mul_inv, ← zpow_neg_one]
  rw [((hasDerivAt_denom_zpow (γ : GL (Fin 2) ℝ) (-1) z).const_mul
    (2 * Real.pi * I * (γ 1 0 : ℂ))).deriv]
  simp only [Int.reduceNeg, Int.reduceSub, zpow_neg_one]
  field_simp
  have hentry :
      (((γ : GL (Fin 2) ℝ) 1 0 : ℝ) : ℂ) = (γ 1 0 : ℂ) := rfl
  rw [hentry]
  ring

private theorem diffContOnCl_comp_ofComplex_ramanujan
    {f : ℍ → ℂ} (hf : MDiff f) {c : ℂ} {R : ℝ}
    (hclosed : Metric.closedBall c R ⊆ {z : ℂ | 0 < z.im}) :
    DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball c R) :=
  ⟨fun z hz => (UpperHalfPlane.mdifferentiableAt_iff.mp
      (hf ⟨z, hclosed (Metric.ball_subset_closedBall hz)⟩)).differentiableWithinAt,
   fun z hz => (UpperHalfPlane.mdifferentiableAt_iff.mp
      (hf ⟨z, hclosed (Metric.closure_ball_subset_closedBall hz)⟩)).continuousAt
        |>.continuousWithinAt⟩

private theorem closedBall_center_subset_upperHalfPlane_ramanujan (z : ℍ) :
    Metric.closedBall (z : ℂ) (z.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have hdist : dist w z ≤ z.im / 2 := Metric.mem_closedBall.mp hw
  have habs : |w.im - z.im| ≤ z.im / 2 := calc
    |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
    _ ≤ ‖w - z‖ := abs_im_le_norm _
    _ = dist w z := (dist_eq_norm _ _).symm
    _ ≤ z.im / 2 := hdist
  have hlower : z.im / 2 ≤ w.im := by
    linarith [(abs_le.mp habs).1]
  exact lt_of_lt_of_le (by linarith [z.im_pos] : 0 < z.im / 2) hlower

private theorem norm_normalizedDerivOfComplex_le_of_sphere_bound_ramanujan
    {f : ℍ → ℂ} {z : ℍ} {r M : ℝ}
    (hr : 0 < r)
    (hDiff : DiffContOnCl ℂ (f ∘ ofComplex)
      (Metric.ball (z : ℂ) r))
    (hbdd : ∀ w ∈ Metric.sphere (z : ℂ) r,
      ‖(f ∘ ofComplex) w‖ ≤ M) :
    ‖D f z‖ ≤ M / (2 * Real.pi * r) := calc
  ‖D f z‖ =
      ‖(2 * Real.pi * I)⁻¹‖ * ‖deriv (f ∘ ofComplex) z‖ := by
        simp [Derivative.normalizedDerivOfComplex]
  _ = (2 * Real.pi)⁻¹ * ‖deriv (f ∘ ofComplex) z‖ := by
        simp [abs_of_pos Real.pi_pos]
  _ ≤ (2 * Real.pi)⁻¹ * (M / r) := by
        gcongr
        exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
          hr hDiff hbdd
  _ = M / (2 * Real.pi * r) := by ring

private theorem normalizedDerivOfComplex_tendsto_zero_ramanujan
    {f : ℍ → ℂ} (hf : MDiff f) (hbdd : IsBoundedAtImInfty f) :
    Tendsto (D f) atImInfty (nhds 0) := by
  obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.mp hbdd
  suffices h : ∀ᶠ z : ℍ in atImInfty,
      ‖D f z‖ ≤ M / (Real.pi * z.im) by
    apply squeeze_zero_norm' h
    have htend :=
      tendsto_im_atImInfty_ramanujan.inv_tendsto_atTop.const_mul
        (M / Real.pi)
    simp only [Pi.inv_apply, mul_zero] at htend
    exact htend.congr fun z => by field_simp
  have h_sphere_bdd : ∀ z : ℍ, 2 * max A 0 + 1 ≤ z.im →
      ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2),
        ‖(f ∘ ofComplex) w‖ ≤ M := by
    intro z hz_ge w hw
    have hw_im_pos : 0 < w.im :=
      closedBall_center_subset_upperHalfPlane_ramanujan z
        (Metric.sphere_subset_closedBall hw)
    have hdist : dist w z = z.im / 2 := Metric.mem_sphere.mp hw
    have habs : |w.im - z.im| ≤ z.im / 2 := by
      calc
        |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
        _ ≤ ‖w - z‖ := abs_im_le_norm _
        _ = dist w z := (dist_eq_norm _ _).symm
        _ = z.im / 2 := hdist
    have hw_im_ge_A : A ≤ w.im := by
      linarith [(abs_le.mp habs).1, le_max_left A 0]
    simpa [ofComplex_apply_of_im_pos hw_im_pos] using
      hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{z : ℍ | 2 * max A 0 + 1 ≤ z.im},
    (UpperHalfPlane.atImInfty_mem _).mpr
      ⟨_, fun _ h => h⟩, fun z hz => ?_⟩
  calc
    ‖D f z‖ ≤ M / (2 * Real.pi * (z.im / 2)) :=
      norm_normalizedDerivOfComplex_le_of_sphere_bound_ramanujan
        (by linarith [z.im_pos])
        (diffContOnCl_comp_ofComplex_ramanujan hf
          (closedBall_center_subset_upperHalfPlane_ramanujan z))
        (h_sphere_bdd z hz)
    _ = M / (Real.pi * z.im) := by ring

private theorem serreDerivative_E2_slash_invariant_ramanujan
    (γ : SL(2, ℤ)) :
    (serre_D 1 E₂) ∣[(4 : ℤ)] γ = serre_D 1 E₂ := by
  have hserre12 :
      serre_D 1 E₂ =
        serre_D 2 E₂ + (1 / 12 : ℂ) • (E₂ * E₂) := by
    ext z
    simp only [Derivative.serreDerivative, Pi.add_apply, Pi.smul_apply,
      Pi.mul_apply, smul_eq_mul]
    ring
  have hequiv := Derivative.serreDerivative_slash_equivariant
    (k := (2 : ℤ)) (F := E₂) E2_mdifferentiable (γ := γ)
  have hE₂slash := EisensteinSeries.E2_slash_action γ
  have hprod := ModularForm.mul_slash_SL2
    (2 : ℤ) (2 : ℤ) γ E₂ E₂
  ext z
  rw [hserre12]
  simp only [SlashAction.add_slash, Pi.add_apply,
    ModularForm.SL_smul_slash, Pi.smul_apply, smul_eq_mul]
  rw [show (serre_D 2 E₂ ∣[(4 : ℤ)] γ) z =
      serre_D 2 (E₂ ∣[(2 : ℤ)] γ) z by
        simpa using congrFun hequiv z,
    show ((E₂ * E₂) ∣[(4 : ℤ)] γ) z =
        (E₂ ∣[(2 : ℤ)] γ) z * (E₂ ∣[(2 : ℤ)] γ) z by
      simpa using congrFun hprod z]
  set α := (1 : ℂ) / (2 * riemannZeta 2) with hα_def
  have hE₂slash_fun :
      (E₂ ∣[(2 : ℤ)] γ) = E₂ - α • EisensteinSeries.D2 γ := by
    ext w
    simpa using congrFun hE₂slash w
  rw [hE₂slash_fun]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hD_lin :
      D (E₂ - α • EisensteinSeries.D2 γ) z =
        D E₂ z - α * D (EisensteinSeries.D2 γ) z := by
    have hαD₂ := (mdifferentiable_D2_ramanujan γ).const_smul α
    simp only [Derivative.normalizedDerivOfComplex_sub E₂ _
      E2_mdifferentiable hαD₂,
      Derivative.normalizedDerivOfComplex_smul α _
        (mdifferentiable_D2_ramanujan γ),
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Derivative.serreDerivative, Pi.sub_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [hD_lin, normalizedDerivOfComplex_D2_ramanujan γ z]
  have hα_val : α = 3 / (Real.pi : ℂ) ^ 2 := by
    simp only [hα_def, riemannZeta_two]
    field_simp
    ring
  have hpi_ne : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show EisensteinSeries.D2 γ z =
      (2 * Real.pi * I * (γ 1 0 : ℂ)) / denom γ z from rfl,
    hα_val]
  field_simp [UpperHalfPlane.denom_ne_zero γ z, hpi_ne]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem tendsto_exp_neg_mul_atTop_ramanujan
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => Real.exp (-c * y)) atTop (nhds 0) := by
  have h : Tendsto (fun y => -c * y) atTop atBot := by
    simpa using tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc)
  exact Real.tendsto_exp_atBot.comp h

private theorem tendsto_zero_of_exp_decay_ramanujan
    {f : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hO : f =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    Tendsto f atImInfty (nhds 0) :=
  hO.trans_tendsto
    ((tendsto_exp_neg_mul_atTop_ramanujan hc).comp
      tendsto_im_atImInfty_ramanujan)

private theorem E2_periodic_comp_ramanujan :
    Function.Periodic (E₂ ∘ UpperHalfPlane.ofComplex) (1 : ℂ) := by
  have hET : E₂ ∣[(2 : ℤ)] ModularGroup.T = E₂ := by
    rw [EisensteinSeries.E2_slash_action, EisensteinSeries.D2_T]
    simp
  intro z
  by_cases hz : 0 < z.im
  · have hzadd : 0 < (z + 1).im := by simpa
    rw [Function.comp_apply, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz,
      UpperHalfPlane.ofComplex_apply_of_im_pos hzadd]
    have h := congrFun hET ⟨z, hz⟩
    rw [ModularForm.SL_slash_apply, UpperHalfPlane.denom,
      UpperHalfPlane.modular_T_smul, ModularGroup.T] at h
    simp at h
    have heq :
        (⟨z + 1, hzadd⟩ : ℍ) = ((1 : ℝ) +ᵥ (⟨z, hz⟩ : ℍ)) := by
      ext
      rw [UpperHalfPlane.coe_vadd]
      push_cast
      ring
    exact (congrArg E₂ heq).trans h
  · exact UpperHalfPlane.comp_ofComplex_of_im_le_zero
      E₂ (z + 1) z (by simpa using le_of_not_gt hz) (le_of_not_gt hz)

private theorem eisensteinSeries_E2_sub_one_isBigO_exp :
    (fun z : ℍ => E₂ z - 1) =O[atImInfty]
      fun z => Real.exp (-(2 * Real.pi) * z.im) := by
  let c : ℕ → ℂ := fun m =>
    if m = 0 then 1 else -24 * ArithmeticFunction.sigma 1 m
  have hsum : ∀ τ : ℍ,
      HasSum (fun m => c m • Function.Periodic.qParam 1 τ ^ m) (E₂ τ) := by
    intro τ
    simpa [c, Function.Periodic.qParam] using
      EisensteinSeries.hasSum_qExpansion_E2 τ
  have hana : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 E₂) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos E2_periodic_comp_ramanujan
      E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  have hseries := UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction
    one_pos hana hsum
  have hcusp : UpperHalfPlane.cuspFunction 1 E₂ 0 = 1 := by
    have hzero := hseries.coeff_zero (fun _ => 0)
    simpa [c] using hzero.symm
  have hvalue : UpperHalfPlane.valueAtInfty E₂ = 1 := calc
    UpperHalfPlane.valueAtInfty E₂ =
        UpperHalfPlane.cuspFunction 1 E₂ 0 :=
      (UpperHalfPlane.cuspFunction_apply_zero
        one_pos hana E2_periodic_comp_ramanujan).symm
    _ = 1 := hcusp
  simpa [hvalue] using UpperHalfPlane.exp_decay_sub_atImInfty
    one_pos E2_periodic_comp_ramanujan E2_mdifferentiable
      EisensteinSeries.isBoundedAtImInfty_E2

theorem eisensteinSeries_E2_tendsto_one_atImInfty :
    Tendsto E₂ atImInfty (nhds 1) := by
  suffices h : Tendsto (fun z : ℍ => E₂ z - 1)
      atImInfty (nhds 0) by
    simpa using h.add_const 1
  exact tendsto_zero_of_exp_decay_ramanujan
    (by positivity : 0 < 2 * Real.pi)
    eisensteinSeries_E2_sub_one_isBigO_exp

theorem eisensteinSeries_E4_tendsto_one_atImInfty :
    Tendsto (ModularForm.E₄ : ℍ → ℂ) atImInfty (nhds 1) := by
  have h2 := tendsto_thetaTwo_atImInfty.comp tendsto_coe_atImInfty
  have h3 := tendsto_thetaThree_atImInfty.comp tendsto_coe_atImInfty
  have h4 := tendsto_thetaFour_atImInfty.comp tendsto_coe_atImInfty
  have h :
      Tendsto
        (fun z : ℍ =>
          (thetaTwo z ^ 8 + thetaThree z ^ 8 + thetaFour z ^ 8) / 2)
        atImInfty (nhds 1) := by
    convert (((h2.pow 8).add (h3.pow 8) |>.add (h4.pow 8)).div_const 2)
      using 1 <;> norm_num
  simpa only [← eisensteinSeries_E4_eq_theta_nullwerte] using h

/-- Weight-four defect whose vanishing is Ramanujan's `E₂` equation. -/
def ramanujanE2DefectH : ℍ → ℂ :=
  fun z => serre_D 1 E₂ z + (1 / 12 : ℂ) * ModularForm.E₄ z

theorem ramanujanE2DefectH_mdiff :
    MDiff ramanujanE2DefectH := by
  have hserre : MDiff (serre_D 1 E₂) :=
    Derivative.serreDerivative_mdifferentiable 1 E2_mdifferentiable
  have hE : MDiff (fun z : ℍ =>
      (1 / 12 : ℂ) * ModularForm.E₄ z) :=
    mdifferentiable_const.mul ModularForm.E₄.holo'
  exact hserre.add hE

theorem ramanujanE2DefectH_slash_SL2Z (γ : SL(2, ℤ)) :
    ramanujanE2DefectH ∣[(4 : ℤ)] γ = ramanujanE2DefectH := by
  change
    ((serre_D 1 E₂) + (1 / 12 : ℂ) • (ModularForm.E₄ : ℍ → ℂ))
        ∣[(4 : ℤ)] γ =
      (serre_D 1 E₂) + (1 / 12 : ℂ) • (ModularForm.E₄ : ℍ → ℂ)
  rw [SlashAction.add_slash,
    serreDerivative_E2_slash_invariant_ramanujan]
  rw [ModularForm.SL_smul_slash]
  have hE :
      (ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ =
        (ModularForm.E₄ : ℍ → ℂ) := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantForm.slash_action_eqn
      ModularForm.E₄ (γ : GL (Fin 2) ℝ)
        (show (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨γ, rfl⟩)
  rw [hE]

theorem ramanujanE2DefectH_zeroAtImInfty :
    IsZeroAtImInfty ramanujanE2DefectH := by
  have hD : Tendsto (D E₂) atImInfty (nhds 0) :=
    normalizedDerivOfComplex_tendsto_zero_ramanujan
      E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  have hE2 := eisensteinSeries_E2_tendsto_one_atImInfty
  have hscale :
      Tendsto (fun z : ℍ => (1 / 12 : ℂ) * E₂ z * E₂ z)
        atImInfty (nhds (1 / 12 : ℂ)) := by
    convert (tendsto_const_nhds.mul hE2 |>.mul hE2) using 1
    all_goals norm_num
  have hserre :
      Tendsto (serre_D 1 E₂) atImInfty (nhds (-(1 / 12 : ℂ))) := by
    have heq :
        serre_D 1 E₂ =
          fun z => D E₂ z - (1 / 12 : ℂ) * E₂ z * E₂ z := by
      funext z
      simp [Derivative.serreDerivative]
    rw [heq]
    convert hD.sub hscale using 1
    all_goals norm_num
  have hE4 := eisensteinSeries_E4_tendsto_one_atImInfty
  have hE4scale :
      Tendsto (fun z : ℍ => (1 / 12 : ℂ) * ModularForm.E₄ z)
        atImInfty (nhds (1 / 12 : ℂ)) := by
    convert tendsto_const_nhds.mul hE4 using 1
    all_goals norm_num
  rw [IsZeroAtImInfty, Filter.ZeroAtFilter]
  change
    Tendsto
      (fun z : ℍ =>
        serre_D 1 E₂ z + (1 / 12 : ℂ) * ModularForm.E₄ z)
      atImInfty (nhds 0)
  convert hserre.add hE4scale using 1
  all_goals norm_num

/-- Ramanujan's weight-four defect packaged as a level-one cusp form. -/
def ramanujanE2DefectCusp : CuspForm 𝒮ℒ 4 where
  toFun := ramanujanE2DefectH
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact ramanujanE2DefectH_slash_SL2Z γ
  holo' := ramanujanE2DefectH_mdiff
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [ramanujanE2DefectH_slash_SL2Z γ]
    exact ramanujanE2DefectH_zeroAtImInfty

/-- `E₂' = pi*i/6 * (E₂² - E₄)` on the upper half-plane, with no premise. -/
theorem deriv_eisensteinSeries_E2_comp_ofComplex (z : ℍ) :
    deriv (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) z =
      (Real.pi : ℂ) * I / 6 *
        (EisensteinSeries.E2 z ^ 2 - ModularForm.E₄ z) := by
  have hzero : ramanujanE2DefectCusp = 0 :=
    rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))
        ramanujanE2DefectCusp
  have h := DFunLike.congr_fun hzero z
  rw [CuspForm.zero_apply] at h
  have hnorm :
      D E₂ z = (1 / 12 : ℂ) *
        (E₂ z ^ 2 - ModularForm.E₄ z) := by
    change
      D E₂ z - (1 : ℂ) * 12⁻¹ * E₂ z * E₂ z +
          (1 / 12 : ℂ) * ModularForm.E₄ z = 0 at h
    linear_combination h
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  change
    (2 * (Real.pi : ℂ) * I)⁻¹ *
        deriv (E₂ ∘ UpperHalfPlane.ofComplex) z =
      (1 / 12 : ℂ) * (E₂ z ^ 2 - ModularForm.E₄ z) at hnorm
  change
    deriv (E₂ ∘ UpperHalfPlane.ofComplex) z =
      (Real.pi : ℂ) * I / 6 *
        (E₂ z ^ 2 - ModularForm.E₄ z)
  calc
    deriv (E₂ ∘ UpperHalfPlane.ofComplex) z =
        (2 * (Real.pi : ℂ) * I) *
          ((2 * (Real.pi : ℂ) * I)⁻¹ *
            deriv (E₂ ∘ UpperHalfPlane.ofComplex) z) := by
      field_simp [hpi, Complex.I_ne_zero]
    _ = (2 * (Real.pi : ℂ) * I) *
          ((1 / 12 : ℂ) * (E₂ z ^ 2 - ModularForm.E₄ z)) := by
      rw [hnorm]
    _ = (Real.pi : ℂ) * I / 6 *
          (E₂ z ^ 2 - ModularForm.E₄ z) := by ring

end

end Bottcher
