import GaloisForLFunctions.Bottcher.ThetaDiscriminant
import SpherePacking.ModularForms.SerreDerivativeSlash

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
    ((tendsto_exp_neg_mul_atTop_ramanujan hc).comp tendsto_im_atImInfty)

private theorem eisensteinSeries_E2_sub_one_isBigO_exp :
    (fun z : ℍ => E₂ z - 1) =O[atImInfty]
      fun z => Real.exp (-(2 * Real.pi) * z.im) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨192, Filter.eventually_atImInfty.mpr ⟨1, fun z hz => ?_⟩⟩
  have hsub :
      E₂ z - 1 =
        -24 * ∑' (n : ℕ+),
          (n : ℂ) * Complex.exp
              (2 * Real.pi * Complex.I * (n : ℂ) * (z : ℂ)) /
            (1 - Complex.exp
              (2 * Real.pi * Complex.I * (n : ℂ) * (z : ℂ))) := by
    rw [E₂_eq z]
    ring
  rw [hsub, norm_mul, show ‖(-24 : ℂ)‖ = 24 by simp,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  set q : ℂ := Complex.exp (2 * Real.pi * Complex.I * (z : ℂ))
  simp_rw [show ∀ n : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (z : ℂ)) =
        q ^ n by
    intro n
    rw [← Complex.exp_nat_mul]
    congr 1
    ring]
  have hq_bound : ‖q‖ ≤ Real.exp (-2 * Real.pi) :=
    norm_exp_two_pi_I_le_exp_neg_two_pi z hz
  have hexp_lt_half : Real.exp (-2 * Real.pi) < 1 / 2 := by
    have htwo : 1 < 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    calc
      Real.exp (-2 * Real.pi) < Real.exp (-1) :=
        Real.exp_strictMono (by linarith)
      _ < 1 / 2 := by
        rw [Real.exp_neg, one_div,
          inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)]
        have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
        linarith
  have hq_lt_half : ‖q‖ < 1 / 2 :=
    lt_of_le_of_lt hq_bound hexp_lt_half
  have hone_sub_q_gt_half : 1 / 2 < 1 - ‖q‖ := by
    linarith
  have htsum_bound :=
    norm_tsum_logDeriv_expo_le (norm_exp_two_pi_I_lt_one z)
  have hsum_le_8q : ‖q‖ / (1 - ‖q‖) ^ 3 ≤ 8 * ‖q‖ := by
    have h1 : (1 / 8 : ℝ) ≤ (1 - ‖q‖) ^ 3 := by
      nlinarith [sq_nonneg (1 - ‖q‖)]
    calc
      ‖q‖ / (1 - ‖q‖) ^ 3 ≤ ‖q‖ / (1 / 8) := by
        apply div_le_div_of_nonneg_left (norm_nonneg _)
          (by positivity) h1
      _ = 8 * ‖q‖ := by ring
  have hq_eq_exp : ‖q‖ = Real.exp (-2 * Real.pi * z.im) := by
    have hre :
        (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ)).re =
          -2 * Real.pi * z.im := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (z : ℂ) =
          Complex.I * (2 * Real.pi * (z : ℂ)) by ring]
      simp [mul_comm]
    rw [Complex.norm_exp, hre]
  calc
    24 * ‖∑' n : ℕ+,
        (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
        ≤ 24 * (‖q‖ / (1 - ‖q‖) ^ 3) := by gcongr
    _ ≤ 24 * (8 * ‖q‖) := by gcongr
    _ = 192 * ‖q‖ := by ring
    _ = 192 * Real.exp (-(2 * Real.pi) * z.im) := by
      rw [hq_eq_exp]
      ring_nf

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
    serre_D_differentiable E₂_holo'
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
  rw [SlashAction.add_slash, serre_DE₂_slash_invariant]
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
    D_tendsto_zero_of_isBoundedAtImInfty E₂_holo'
      E₂_isBoundedAtImInfty
  have hE2 := eisensteinSeries_E2_tendsto_one_atImInfty
  have hscale :
      Tendsto (fun z : ℍ => (1 / 12 : ℂ) * E₂ z * E₂ z)
        atImInfty (nhds (1 / 12 : ℂ)) := by
    convert (tendsto_const_nhds.mul hE2 |>.mul hE2) using 1 <;>
      norm_num
  have hserre :
      Tendsto (serre_D 1 E₂) atImInfty (nhds (-(1 / 12 : ℂ))) := by
    have heq :
        serre_D 1 E₂ =
          fun z => D E₂ z - (1 / 12 : ℂ) * E₂ z * E₂ z := by
      funext z
      simp [serre_D]
    rw [heq]
    convert hD.sub hscale using 1 <;> norm_num
  have hE4 := eisensteinSeries_E4_tendsto_one_atImInfty
  have hE4scale :
      Tendsto (fun z : ℍ => (1 / 12 : ℂ) * ModularForm.E₄ z)
        atImInfty (nhds (1 / 12 : ℂ)) := by
    convert tendsto_const_nhds.mul hE4 using 1 <;> norm_num
  rw [IsZeroAtImInfty, Filter.ZeroAtFilter]
  change
    Tendsto
      (fun z : ℍ =>
        serre_D 1 E₂ z + (1 / 12 : ℂ) * ModularForm.E₄ z)
      atImInfty (nhds 0)
  convert hserre.add hE4scale using 1 <;> norm_num

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
