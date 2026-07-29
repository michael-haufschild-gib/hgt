import GaloisForLFunctions.Bottcher.ThetaWronskian
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

/-!
# Jacobi theta product and the modular discriminant

The corpus already proves the Jacobi quartic identity and theta Wronskian unconditionally.
Those two identities determine differences of theta logarithmic derivatives, but not their common
mode. This module supplies that missing mode from source data by proving

`(thetaTwo * thetaThree * thetaFour)^8 = 256 * discriminant`.

The eighth power removes both theta-product multipliers. It is a weight-twelve level-one cusp
form, hence a scalar multiple of the modular discriminant. Their normalized cusp limits determine
the scalar as `256`.
-/

open Complex Filter Topology
open Matrix ModularGroup CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold

namespace Bottcher

noncomputable section

/-- Eighth power of the theta-nullwert product, viewed on the upper half-plane. -/
def thetaProductPow8H : ℍ → ℂ :=
  fun z => (thetaTwo z * thetaThree z * thetaFour z) ^ 8

theorem thetaProductPow8H_mdiff : MDiff thetaProductPow8H := by
  rw [mdifferentiable_iff]
  intro z hz
  have hz' : 0 < z.im := by simpa using hz
  have hdiff :
      DifferentiableAt ℂ
        (fun w : ℂ => (thetaTwo w * thetaThree w * thetaFour w) ^ 8) z :=
    (((differentiableAt_thetaTwo hz').mul (differentiableAt_thetaThree hz')).mul
      (differentiableAt_thetaFour hz')).pow 8
  refine hdiff.differentiableWithinAt.congr (fun w hw => ?_) ?_
  · show (thetaTwo ((ofComplex w : ℍ) : ℂ) *
        thetaThree ((ofComplex w : ℍ) : ℂ) *
        thetaFour ((ofComplex w : ℍ) : ℂ)) ^ 8 =
      (thetaTwo w * thetaThree w * thetaFour w) ^ 8
    rw [ofComplex_apply_of_im_pos (by simpa using hw)]
  · show (thetaTwo ((ofComplex z : ℍ) : ℂ) *
        thetaThree ((ofComplex z : ℍ) : ℂ) *
        thetaFour ((ofComplex z : ℍ) : ℂ)) ^ 8 =
      (thetaTwo z * thetaThree z * thetaFour z) ^ 8
    rw [ofComplex_apply_of_im_pos hz']

theorem thetaProductPow8H_slash_S :
    thetaProductPow8H ∣[(12 : ℤ)] ModularGroup.S = thetaProductPow8H := by
  funext z
  rw [ModularForm.SL_slash_apply, thetaProductPow8H, thetaProductPow8H]
  have hact : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, neg_div, one_div, inv_neg]
  rw [hact, show denom ModularGroup.S z = (z : ℂ) from denom_S z, _root_.zpow_neg]
  have h4 := thetaProductPow4_S (τ := (z : ℂ)) z.ne_zero
  rw [show
      (thetaTwo (-1 / (z : ℂ)) * thetaThree (-1 / (z : ℂ)) *
          thetaFour (-1 / (z : ℂ))) ^ 8 =
        ((thetaTwo (-1 / (z : ℂ)) * thetaThree (-1 / (z : ℂ)) *
          thetaFour (-1 / (z : ℂ))) ^ 4) ^ 2 by ring,
    h4]
  rw [show (((z : ℂ) ^ (12 : ℤ)) : ℂ) = (z : ℂ) ^ 12 by norm_cast]
  field_simp
  field_simp [z.ne_zero]

theorem thetaProductPow8H_slash_T :
    thetaProductPow8H ∣[(12 : ℤ)] ModularGroup.T = thetaProductPow8H := by
  funext z
  rw [ModularForm.SL_slash_apply, thetaProductPow8H, thetaProductPow8H]
  have hact : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    rw [← zpow_one ModularGroup.T, ModularGroup.coe_T_zpow_smul_eq]
    push_cast
    ring
  have hden : denom ModularGroup.T z = 1 := by simp [ModularGroup.T, denom_apply]
  rw [hact, hden, _root_.one_zpow, mul_one]
  rw [show
      (thetaTwo ((z : ℂ) + 1) * thetaThree ((z : ℂ) + 1) *
          thetaFour ((z : ℂ) + 1)) ^ 8 =
        ((thetaTwo ((z : ℂ) + 1) * thetaThree ((z : ℂ) + 1) *
          thetaFour ((z : ℂ) + 1)) ^ 4) ^ 2 by ring,
    thetaProductPow4_add_one]
  ring

theorem thetaProductPow8H_slash_SL2Z (γ : SL(2, ℤ)) :
    thetaProductPow8H ∣[(12 : ℤ)] γ = thetaProductPow8H := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [thetaProductPow8H_slash_S, thetaProductPow8H_slash_T]
  | one => exact SlashAction.slash_one 12 thetaProductPow8H
  | mul x y _ _ ihx ihy => rw [SlashAction.slash_mul, ihx, ihy]
  | inv x _ ih =>
    have h : thetaProductPow8H ∣[(12 : ℤ)] x⁻¹ =
        (thetaProductPow8H ∣[(12 : ℤ)] x) ∣[(12 : ℤ)] x⁻¹ := by rw [ih]
    rw [h, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem thetaProductPow8H_zeroAtImInfty : IsZeroAtImInfty thetaProductPow8H := by
  have h2 := tendsto_thetaTwo_atImInfty.comp tendsto_coe_atImInfty
  have h3 := tendsto_thetaThree_atImInfty.comp tendsto_coe_atImInfty
  have h4 := tendsto_thetaFour_atImInfty.comp tendsto_coe_atImInfty
  change Tendsto
    (fun z : ℍ => (thetaTwo z * thetaThree z * thetaFour z) ^ 8)
    atImInfty (nhds 0)
  simpa [Function.comp_apply] using ((h2.mul h3).mul h4).pow 8

/-- The eighth theta-product power as a weight-twelve level-one cusp form. -/
def thetaProductPow8Cusp : CuspForm 𝒮ℒ 12 where
  toFun := thetaProductPow8H
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact thetaProductPow8H_slash_SL2Z γ
  holo' := thetaProductPow8H_mdiff
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [thetaProductPow8H_slash_SL2Z γ]
    exact thetaProductPow8H_zeroAtImInfty

/-- **Theta-product/discriminant identity.**
`Delta = (thetaTwo * thetaThree * thetaFour)^8 / 256` on the upper half-plane. -/
theorem thetaProductPow8_discriminant_identity (τ : ℍ) :
    ModularForm.discriminant τ =
      (thetaTwo τ * thetaThree τ * thetaFour τ) ^ 8 / 256 := by
  obtain ⟨c, hc⟩ :=
    CuspForm.exists_smul_discriminant_of_weight_eq_twelve thetaProductPow8Cusp
  have hc_pw : ∀ z : ℍ, c * ModularForm.discriminant z = thetaProductPow8H z := by
    intro z
    have h := DFunLike.congr_fun hc z
    rw [show (c • CuspForm.discriminant : CuspForm _ _) z =
      c * ModularForm.discriminant z from rfl] at h
    exact h
  have hD_asymp :
      Tendsto (fun z : ℍ =>
        ModularForm.discriminant z / Complex.exp (2 * (Real.pi : ℂ) * I * z))
        atImInfty (nhds 1) := by
    have h_eq : ∀ z : ℍ,
        ModularForm.discriminant z / Complex.exp (2 * (Real.pi : ℂ) * I * z) =
          ∏' n : ℕ, (1 - ModularForm.eta_q n z) ^ 24 := by
      intro z
      rw [ModularForm.discriminant_eq_q_prod]
      rw [show Function.Periodic.qParam 1 (z : ℂ) =
          Complex.exp (2 * (Real.pi : ℂ) * I * z) by
        simp [Function.Periodic.qParam]]
      exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
    simpa only [h_eq] using
      ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow
  have hdiag :
      Tendsto (fun z : ℍ => jacobiTheta₂ ((z : ℂ) / 2) z)
        atImInfty (nhds 2) :=
    tendsto_jacobiTheta₂_diag_atImInfty.comp tendsto_coe_atImInfty
  have h3 := tendsto_thetaThree_atImInfty.comp tendsto_coe_atImInfty
  have h4 := tendsto_thetaFour_atImInfty.comp tendsto_coe_atImInfty
  have hP_asymp :
      Tendsto (fun z : ℍ =>
        thetaProductPow8H z / Complex.exp (2 * (Real.pi : ℂ) * I * z))
        atImInfty (nhds 256) := by
    have h_rewrite : ∀ z : ℍ,
        thetaProductPow8H z / Complex.exp (2 * (Real.pi : ℂ) * I * z) =
          jacobiTheta₂ ((z : ℂ) / 2) z ^ 8 *
            thetaThree z ^ 8 * thetaFour z ^ 8 := by
      intro z
      rw [thetaProductPow8H, thetaTwo]
      have hexp :
          Complex.exp ((Real.pi : ℂ) * I * z / 4) ^ 8 =
            Complex.exp (2 * (Real.pi : ℂ) * I * z) := by
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      simp only [mul_pow]
      rw [hexp]
      field_simp
    rw [show (256 : ℂ) = 2 ^ 8 * 1 ^ 8 * 1 ^ 8 by norm_num]
    exact (((hdiag.pow 8).mul (h3.pow 8)).mul (h4.pow 8)).congr
      (fun z => (h_rewrite z).symm)
  have hc_eq : c = 256 := by
    have hc_lim :
        Tendsto (fun z : ℍ =>
          c * (ModularForm.discriminant z /
            Complex.exp (2 * (Real.pi : ℂ) * I * z)))
          atImInfty (nhds c) := by
      simpa using hD_asymp.const_mul c
    have heq : ∀ z : ℍ,
        c * (ModularForm.discriminant z /
            Complex.exp (2 * (Real.pi : ℂ) * I * z)) =
          thetaProductPow8H z /
            Complex.exp (2 * (Real.pi : ℂ) * I * z) := by
      intro z
      rw [← mul_div_assoc, hc_pw]
    exact tendsto_nhds_unique (hc_lim.congr heq) hP_asymp
  have h := hc_pw τ
  rw [hc_eq, thetaProductPow8H] at h
  rw [eq_div_iff (by norm_num : (256 : ℂ) ≠ 0), mul_comm]
  exact h

/-- The theta-nullwert product supplies the common logarithmic-derivative mode:
`thetaTwo'/thetaTwo + thetaThree'/thetaThree + thetaFour'/thetaFour = pi*i*E2/4`.

Together with the unconditional theta Wronskian and differentiated Jacobi quartic identity, this
determines all three theta logarithmic derivatives without a carried analytic premise. -/
theorem thetaProduct_logDeriv_eq_E2 {τ : ℂ} (hτ : 0 < τ.im) :
    deriv thetaTwo τ / thetaTwo τ +
        deriv thetaThree τ / thetaThree τ +
        deriv thetaFour τ / thetaFour τ =
      (Real.pi : ℂ) * I / 4 * EisensteinSeries.E2 ⟨τ, hτ⟩ := by
  let P : ℂ → ℂ := fun z => thetaTwo z * thetaThree z * thetaFour z
  have h2 : DifferentiableAt ℂ thetaTwo τ := differentiableAt_thetaTwo hτ
  have h3 : DifferentiableAt ℂ thetaThree τ := differentiableAt_thetaThree hτ
  have h4 : DifferentiableAt ℂ thetaFour τ := differentiableAt_thetaFour hτ
  have hP : DifferentiableAt ℂ P τ := (h2.mul h3).mul h4
  have h2ne : thetaTwo τ ≠ 0 := thetaTwo_ne_zero_of_im_pos hτ
  have h3ne : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  have h4ne : thetaFour τ ≠ 0 := thetaFour_ne_zero_of_im_pos hτ
  have heta : DifferentiableAt ℂ ModularForm.eta τ :=
    ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hτ
  have hlocal :
      (fun z : ℂ => ModularForm.eta z ^ 24) =ᶠ[nhds τ]
        (fun z : ℂ => P z ^ 8 / 256) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hτ] with z hz
    simpa [ModularForm.discriminant, P] using
      thetaProductPow8_discriminant_identity ⟨z, hz⟩
  have hlog :
      logDeriv (fun z : ℂ => ModularForm.eta z ^ 24) τ =
        logDeriv (fun z : ℂ => P z ^ 8 / 256) τ := by
    have hval : ModularForm.eta τ ^ 24 = P τ ^ 8 / 256 :=
      hlocal.self_of_nhds
    rw [logDeriv_apply, logDeriv_apply, hlocal.deriv_eq, hval]
  rw [logDeriv_fun_pow heta 24] at hlog
  have hright :
      logDeriv (fun z : ℂ => P z ^ 8 / 256) τ =
        8 * logDeriv P τ := by
    rw [show (fun z : ℂ => P z ^ 8 / 256) =
        fun z : ℂ => P z ^ 8 * (256 : ℂ)⁻¹ by
      funext z
      rw [div_eq_mul_inv]]
    rw [logDeriv_mul_const _ _ (by norm_num : (256 : ℂ)⁻¹ ≠ 0),
      logDeriv_fun_pow hP 8]
    norm_num
  rw [hright, ModularForm.logDeriv_eta_eq_E2 ⟨τ, hτ⟩] at hlog
  have hPlog :
      logDeriv P τ =
        logDeriv thetaTwo τ + logDeriv thetaThree τ + logDeriv thetaFour τ := by
    have h23ne : thetaTwo τ * thetaThree τ ≠ 0 :=
      _root_.mul_ne_zero h2ne h3ne
    change logDeriv (fun z => (thetaTwo z * thetaThree z) * thetaFour z) τ =
      logDeriv thetaTwo τ + logDeriv thetaThree τ + logDeriv thetaFour τ
    calc
      logDeriv (fun z => (thetaTwo z * thetaThree z) * thetaFour z) τ =
          logDeriv (fun z => thetaTwo z * thetaThree z) τ +
            logDeriv thetaFour τ :=
        logDeriv_mul (f := fun z => thetaTwo z * thetaThree z)
          (g := thetaFour) τ h23ne h4ne (h2.mul h3) h4
      _ = logDeriv thetaTwo τ + logDeriv thetaThree τ +
            logDeriv thetaFour τ := by
        rw [logDeriv_mul (f := thetaTwo) (g := thetaThree)
          τ h2ne h3ne h2 h3]
  rw [hPlog] at hlog
  simp only [logDeriv_apply] at hlog
  calc
    deriv thetaTwo τ / thetaTwo τ +
          deriv thetaThree τ / thetaThree τ +
          deriv thetaFour τ / thetaFour τ =
        (8 : ℂ)⁻¹ * (8 *
          (deriv thetaTwo τ / thetaTwo τ +
            deriv thetaThree τ / thetaThree τ +
            deriv thetaFour τ / thetaFour τ)) := by ring
    _ = (8 : ℂ)⁻¹ * (24 *
          ((Real.pi : ℂ) * I / 12 * EisensteinSeries.E2 ⟨τ, hτ⟩)) := by
      congr 1
      simpa using hlog.symm
    _ = (Real.pi : ℂ) * I / 4 * EisensteinSeries.E2 ⟨τ, hτ⟩ := by ring

/-- The individual `thetaThree` logarithmic derivative, with no carried theta-derivative premise:
`thetaThree'/thetaThree = pi*i/12 * (E2 + thetaTwo^4 - thetaFour^4)`.

The product/discriminant identity fixes the common logarithmic-derivative mode. The unconditional
theta Wronskian fixes the `thetaTwo`--`thetaThree` difference, and differentiated Jacobi quartic
fixes the remaining `thetaFour` mode. -/
theorem thetaThree_logDeriv_eq_E2 {τ : ℂ} (hτ : 0 < τ.im) :
    deriv thetaThree τ / thetaThree τ =
      (Real.pi : ℂ) * I / 12 *
        (EisensteinSeries.E2 ⟨τ, hτ⟩ + thetaTwo τ ^ 4 - thetaFour τ ^ 4) := by
  have h2ne : thetaTwo τ ≠ 0 := thetaTwo_ne_zero_of_im_pos hτ
  have h3ne : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  have h4ne : thetaFour τ ≠ 0 := thetaFour_ne_zero_of_im_pos hτ
  have hcommon := thetaProduct_logDeriv_eq_E2 hτ
  have hW := thetaWronskian23 hτ
  have hJ := deriv_pow4_jacobi hτ
  have hQ := pow4_jacobi hτ
  have hWlog :
      deriv thetaTwo τ / thetaTwo τ - deriv thetaThree τ / thetaThree τ =
        (Real.pi : ℂ) * I / 4 * thetaFour τ ^ 4 := by
    field_simp [h2ne, h3ne]
    linear_combination 4 * hW
  have hJlog :
      thetaThree τ ^ 4 * (deriv thetaThree τ / thetaThree τ) =
        thetaTwo τ ^ 4 * (deriv thetaTwo τ / thetaTwo τ) +
          thetaFour τ ^ 4 * (deriv thetaFour τ / thetaFour τ) := by
    field_simp [h2ne, h3ne, h4ne]
    linear_combination (1 / 4 : ℂ) * hJ
  have hfour :
      deriv thetaFour τ / thetaFour τ =
        deriv thetaThree τ / thetaThree τ -
          (Real.pi : ℂ) * I / 4 * thetaTwo τ ^ 4 := by
    have hc :
        thetaFour τ ^ 4 *
          (deriv thetaFour τ / thetaFour τ -
            (deriv thetaThree τ / thetaThree τ -
              (Real.pi : ℂ) * I / 4 * thetaTwo τ ^ 4)) = 0 := by
      linear_combination
        -hJlog +
        (deriv thetaThree τ / thetaThree τ) * hQ -
        thetaTwo τ ^ 4 * hWlog
    have hz :
        deriv thetaFour τ / thetaFour τ -
          (deriv thetaThree τ / thetaThree τ -
            (Real.pi : ℂ) * I / 4 * thetaTwo τ ^ 4) = 0 :=
      (mul_eq_zero.mp hc).resolve_left (pow_ne_zero 4 h4ne)
    linear_combination hz
  linear_combination
    (1 / 3 : ℂ) * hcommon -
    (1 / 3 : ℂ) * hWlog -
    (1 / 3 : ℂ) * hfour

/-! ### The weight-four theta/Eisenstein identity

The same source-data route also supplies the exact algebraic term needed in Ramanujan's
`E₂` equation.  We prove it inside the present corpus, rather than importing a theta-derivative
package whose unrelated modular-form dimension instance is conditional. -/

/-- Difference between the theta-nullwert weight-four combination and the normalized
weight-four Eisenstein series. -/
def thetaEisensteinFourDefectH : ℍ → ℂ :=
  fun z =>
    (thetaTwo z ^ 8 + thetaThree z ^ 8 + thetaFour z ^ 8) / 2 -
      ModularForm.E₄ z

theorem thetaEisensteinFourDefectH_mdiff :
    MDiff thetaEisensteinFourDefectH := by
  have htheta : MDiff (fun z : ℍ =>
      ((thetaTwo z ^ 8 + thetaThree z ^ 8 + thetaFour z ^ 8) / 2 : ℂ)) := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    intro z hz
    have hz' : 0 < z.im := by simpa using hz
    have hdiff :
        DifferentiableAt ℂ
          (fun w : ℂ =>
            (thetaTwo w ^ 8 + thetaThree w ^ 8 + thetaFour w ^ 8) / 2) z :=
      (((differentiableAt_thetaTwo hz').pow 8).add
        ((differentiableAt_thetaThree hz').pow 8) |>.add
          ((differentiableAt_thetaFour hz').pow 8)).div_const 2
    exact hdiff.differentiableWithinAt.congr
      (fun w hw => by
        show (thetaTwo ((ofComplex w : ℍ) : ℂ) ^ 8 +
              thetaThree ((ofComplex w : ℍ) : ℂ) ^ 8 +
              thetaFour ((ofComplex w : ℍ) : ℂ) ^ 8) / 2 =
            (thetaTwo w ^ 8 + thetaThree w ^ 8 + thetaFour w ^ 8) / 2
        rw [ofComplex_apply_of_im_pos (by simpa using hw)])
      (by
        show (thetaTwo ((ofComplex z : ℍ) : ℂ) ^ 8 +
              thetaThree ((ofComplex z : ℍ) : ℂ) ^ 8 +
              thetaFour ((ofComplex z : ℍ) : ℂ) ^ 8) / 2 =
            (thetaTwo z ^ 8 + thetaThree z ^ 8 + thetaFour z ^ 8) / 2
        rw [ofComplex_apply_of_im_pos hz'])
  have hE : MDiff (ModularForm.E₄ : ℍ → ℂ) := ModularForm.E₄.holo'
  exact htheta.sub hE

theorem thetaEisensteinFourDefectH_slash_S :
    thetaEisensteinFourDefectH ∣[(4 : ℤ)] ModularGroup.S =
      thetaEisensteinFourDefectH := by
  funext z
  rw [ModularForm.SL_slash_apply, thetaEisensteinFourDefectH,
    thetaEisensteinFourDefectH]
  have hact : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
      neg_div, one_div, inv_neg]
  have hE := SlashInvariantForm.slash_action_eqn''
    ModularForm.E₄
      (show (ModularGroup.S : GL (Fin 2) ℝ) ∈ 𝒮ℒ from
        ⟨ModularGroup.S, rfl⟩) z
  rw [hact, show denom ModularGroup.S z = (z : ℂ) from denom_S z,
    _root_.zpow_neg]
  have h2 := thetaTwo_pow4_S (τ := (z : ℂ)) z.ne_zero
  have h3 := thetaThree_pow4_S (τ := (z : ℂ)) z.ne_zero
  have h4 := thetaFour_pow4_S (τ := (z : ℂ)) z.ne_zero
  rw [show thetaTwo (-1 / (z : ℂ)) ^ 8 =
      (thetaTwo (-1 / (z : ℂ)) ^ 4) ^ 2 by ring,
    show thetaThree (-1 / (z : ℂ)) ^ 8 =
      (thetaThree (-1 / (z : ℂ)) ^ 4) ^ 2 by ring,
    show thetaFour (-1 / (z : ℂ)) ^ 8 =
      (thetaFour (-1 / (z : ℂ)) ^ 4) ^ 2 by ring,
    h2, h3, h4]
  rw [show (((z : ℂ) ^ (4 : ℤ)) : ℂ) = (z : ℂ) ^ 4 by norm_cast]
  rw [show ModularForm.E₄ (ModularGroup.S • z) =
      (z : ℂ) ^ 4 * ModularForm.E₄ z by
        field_simp [z.ne_zero] at hE
        simpa [mul_comm] using hE]
  field_simp [z.ne_zero]
  ring

theorem thetaEisensteinFourDefectH_slash_T :
    thetaEisensteinFourDefectH ∣[(4 : ℤ)] ModularGroup.T =
      thetaEisensteinFourDefectH := by
  funext z
  rw [ModularForm.SL_slash_apply, thetaEisensteinFourDefectH,
    thetaEisensteinFourDefectH]
  have hact : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    rw [← zpow_one ModularGroup.T, ModularGroup.coe_T_zpow_smul_eq]
    push_cast
    ring
  have hden : denom ModularGroup.T z = 1 := by
    simp [ModularGroup.T, denom_apply]
  have hTz : (ModularGroup.T : SL(2, ℤ)) • z =
      (1 : ℝ) +ᵥ z := by
    apply UpperHalfPlane.ext
    simpa [add_comm] using hact
  have hE : ModularForm.E₄ ((ModularGroup.T : SL(2, ℤ)) • z) =
      ModularForm.E₄ z := by
    rw [hTz]
    exact SlashInvariantForm.vAdd_apply_of_mem_strictPeriods
      ModularForm.E₄ z one_mem_strictPeriods_SL
  rw [hact, hden, _root_.one_zpow, mul_one, hE,
    show thetaTwo ((z : ℂ) + 1) ^ 8 =
      (thetaTwo ((z : ℂ) + 1) ^ 4) ^ 2 by ring,
    show thetaThree ((z : ℂ) + 1) ^ 8 =
      (thetaThree ((z : ℂ) + 1) ^ 4) ^ 2 by ring,
    show thetaFour ((z : ℂ) + 1) ^ 8 =
      (thetaFour ((z : ℂ) + 1) ^ 4) ^ 2 by ring,
    thetaTwo_pow4_add_one, thetaThree_pow4_add_one,
    thetaFour_pow4_add_one]
  ring

theorem thetaEisensteinFourDefectH_slash_SL2Z (γ : SL(2, ℤ)) :
    thetaEisensteinFourDefectH ∣[(4 : ℤ)] γ =
      thetaEisensteinFourDefectH := by
  have hmem :
      γ ∈ Subgroup.closure
        ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      exacts [thetaEisensteinFourDefectH_slash_S,
        thetaEisensteinFourDefectH_slash_T]
  | one => exact SlashAction.slash_one 4 thetaEisensteinFourDefectH
  | mul x y _ _ ihx ihy => rw [SlashAction.slash_mul, ihx, ihy]
  | inv x _ ih =>
      have h : thetaEisensteinFourDefectH ∣[(4 : ℤ)] x⁻¹ =
          (thetaEisensteinFourDefectH ∣[(4 : ℤ)] x) ∣[(4 : ℤ)] x⁻¹ := by
        rw [ih]
      rw [h, ← SlashAction.slash_mul, mul_inv_cancel,
        SlashAction.slash_one]

private theorem tendsto_zero_of_exp_decay_thetaEisenstein
    {f : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hO : f =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    Tendsto f atImInfty (nhds 0) := by
  have hlin : Tendsto (fun y : ℝ => -c * y) atTop atBot := by
    simpa using tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc)
  have him : Tendsto (fun z : ℍ => z.im) atImInfty atTop := by
    exact tendsto_comap
  exact hO.trans_tendsto
    (Real.tendsto_exp_atBot.comp hlin |>.comp him)

theorem thetaEisensteinFourDefectH_zeroAtImInfty :
    IsZeroAtImInfty thetaEisensteinFourDefectH := by
  have h2 := tendsto_thetaTwo_atImInfty.comp tendsto_coe_atImInfty
  have h3 := tendsto_thetaThree_atImInfty.comp tendsto_coe_atImInfty
  have h4 := tendsto_thetaFour_atImInfty.comp tendsto_coe_atImInfty
  have hE0 :
      Tendsto (ModularForm.E₄ : ℍ → ℂ) atImInfty
        (nhds ((qExpansion 1 ModularForm.E₄).coeff 0)) := by
    obtain ⟨c, hc, hO⟩ :=
      ModularFormClass.exp_decay_sub_atImInfty' ModularForm.E₄
    have hΓ : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods :=
      one_mem_strictPeriods_SL
    rw [qExpansion_coeff_zero (by norm_num : (0 : ℝ) < 1)
      (ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄
        (by norm_num) hΓ)
      (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ hΓ)]
    simpa using
      (tendsto_zero_of_exp_decay_thetaEisenstein hc hO).add_const
        (valueAtInfty (ModularForm.E₄ : ℍ → ℂ))
  have hE : Tendsto (ModularForm.E₄ : ℍ → ℂ) atImInfty (nhds 1) := by
    simpa [EisensteinSeries.E_qExpansion_coeff_zero
      (by norm_num : 3 ≤ 4) ⟨2, rfl⟩] using hE0
  change Tendsto
    (fun z : ℍ =>
      (thetaTwo z ^ 8 + thetaThree z ^ 8 + thetaFour z ^ 8) / 2 -
        ModularForm.E₄ z)
    atImInfty (nhds 0)
  simpa [Function.comp_apply] using
    (((h2.pow 8).add (h3.pow 8) |>.add (h4.pow 8)).div_const 2).sub hE

/-- The weight-four theta/Eisenstein defect as a level-one cusp form. -/
def thetaEisensteinFourDefectCusp : CuspForm 𝒮ℒ 4 where
  toFun := thetaEisensteinFourDefectH
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact thetaEisensteinFourDefectH_slash_SL2Z γ
  holo' := thetaEisensteinFourDefectH_mdiff
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [thetaEisensteinFourDefectH_slash_SL2Z γ]
    exact thetaEisensteinFourDefectH_zeroAtImInfty

/-- Jacobi's exact weight-four identity, derived entirely from source theta transformations:
`E4 = (thetaTwo^8 + thetaThree^8 + thetaFour^8) / 2`. -/
theorem eisensteinSeries_E4_eq_theta_nullwerte (τ : ℍ) :
    ModularForm.E₄ τ =
      (thetaTwo τ ^ 8 + thetaThree τ ^ 8 + thetaFour τ ^ 8) / 2 := by
  have h0 : thetaEisensteinFourDefectCusp = 0 :=
    rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))
        thetaEisensteinFourDefectCusp
  have h := DFunLike.congr_fun h0 τ
  rw [CuspForm.zero_apply] at h
  exact sub_eq_zero.mp h |>.symm

/-- The quasimodular fixed-point value `E2(i) = 3 / pi`, obtained directly from the `S`
transformation law. -/
theorem eisensteinSeries_E2_at_I :
    EisensteinSeries.E2 ⟨I, by simp⟩ = (3 : ℂ) / Real.pi := by
  let z : ℍ := ⟨I, by simp⟩
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.S) z
  rw [ModularForm.SL_slash_apply] at h
  simp [EisensteinSeries.D2, riemannZeta_two, UpperHalfPlane.denom,
    ModularGroup.S] at h
  change EisensteinSeries.E2 (ModularGroup.S • z) * (((z : ℂ) ^ 2)⁻¹) =
    EisensteinSeries.E2 z - 6 / (Real.pi : ℂ) ^ 2 * (2 : ℂ)⁻¹ *
      (2 * (Real.pi : ℂ) * I / (z : ℂ)) at h
  have hfix : ModularGroup.S • z = z := by
    rw [UpperHalfPlane.modular_S_smul]
    ext
    simp [z]
  rw [hfix] at h
  change EisensteinSeries.E2 z = (3 : ℂ) / Real.pi
  simp only [z] at h
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  field_simp [Complex.I_ne_zero] at h ⊢
  linear_combination
    (1 / 2 : ℂ) * h +
    (1 / 2 : ℂ) * (EisensteinSeries.E2 z * (Real.pi : ℂ) - 6) * hI

/-- At the self-dual point, Jacobi's two off-center nullwerte have equal fourth powers. -/
theorem thetaTwo_pow_four_eq_thetaFour_pow_four_at_I :
    thetaTwo I ^ 4 = thetaFour I ^ 4 := by
  have hlambda := modularLambda_at_I'
  have hQ := pow4_jacobi (by simp : (0 : ℝ) < I.im)
  have h3ne := thetaThree_ne_zero_of_im_pos (by simp : (0 : ℝ) < I.im)
  rw [modularLambda, div_pow] at hlambda
  field_simp [h3ne] at hlambda
  linear_combination hQ + hlambda

/-- The theta mass has the exact self-dual logarithmic derivative `thetaThree'(i)/thetaThree(i)
= i/4`. This is the first analytic seam jet needed by the RHTower theta source. -/
theorem thetaThree_logDeriv_at_I :
    deriv thetaThree I / thetaThree I = I / 4 := by
  have h := thetaThree_logDeriv_eq_E2 (τ := I) (by simp)
  rw [eisensteinSeries_E2_at_I, thetaTwo_pow_four_eq_thetaFour_pow_four_at_I] at h
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h3ne := thetaThree_ne_zero_of_im_pos (by simp : (0 : ℝ) < I.im)
  field_simp [hπ, h3ne] at h ⊢
  linear_combination (1 / 3 : ℂ) * h

/-- Mathlib's real even Hurwitz kernel is exactly the Jacobi `thetaThree` nullwert on the
imaginary axis. This identifies the RHTower theta source data with the Bottcher modular
differential system. -/
theorem ofReal_evenKernel_zero_eq_thetaThree (t : ℝ) :
    ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) =
      thetaThree (I * (t : ℂ)) := by
  simpa [thetaThree] using HurwitzZeta.evenKernel_def 0 t

/-- Completed real theta profile whose Hedenmalm source is obtained by applying
`(d^2/dx^2 - 1/4)/2`. -/
def completedThetaProfile (x : ℝ) : ℝ :=
  Real.exp (x / 2) * HurwitzZeta.evenKernel 0 (Real.exp (2 * x))

/-- The completed real profile is the restriction
`exp(x/2) * thetaThree(i * exp(2x))` of the holomorphic theta nullwert. -/
theorem ofReal_completedThetaProfile_eq_thetaThree (x : ℝ) :
    ((completedThetaProfile x : ℝ) : ℂ) =
      ((Real.exp (x / 2) : ℝ) : ℂ) *
        thetaThree (I * (Real.exp (2 * x) : ℂ)) := by
  rw [completedThetaProfile, Complex.ofReal_mul,
    ofReal_evenKernel_zero_eq_thetaThree]

end

end Bottcher
