import GaloisForLFunctions.Bottcher.Ramanujan

/-!
# Ramanujan's full differential system and the Chazy equation

The existing weight-two identity is completed here by the weight-four and weight-six
Ramanujan equations.  Each missing equation is the vanishing of a level-one cusp form of weight
below twelve.  Eliminating `E₄` and `E₆` then gives the exact Chazy equation for `E₂` under the
normalized derivation `D = (2πi)⁻¹ d/dτ`.
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

theorem eisensteinSeries_E6_tendsto_one_atImInfty :
    Tendsto (ModularForm.E₆ : ℍ → ℂ) atImInfty (nhds 1) := by
  have hper : Function.Periodic
      ((ModularForm.E₆ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) (1 : ℂ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL
  have hhol : MDiff (ModularForm.E₆ : ℍ → ℂ) :=
    ModularFormClass.holo ModularForm.E₆
  have hbdd : IsBoundedAtImInfty (ModularForm.E₆ : ℍ → ℂ) :=
    ModularFormClass.bdd_at_infty ModularForm.E₆
  have hana : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 (ModularForm.E₆ : ℍ → ℂ)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hper hhol hbdd
  have hvalue : UpperHalfPlane.valueAtInfty (ModularForm.E₆ : ℍ → ℂ) = 1 := by
    rw [← UpperHalfPlane.qExpansion_coeff_zero one_pos hana hper]
    exact EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 6) (by norm_num)
  have hzero : UpperHalfPlane.cuspFunction 1 (ModularForm.E₆ : ℍ → ℂ) 0 = 1 := by
    rw [UpperHalfPlane.cuspFunction_apply_zero one_pos hana hper, hvalue]
  have ht := hana.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)
  rw [hzero] at ht
  exact ht.congr fun τ => by
    simpa only [Function.comp_apply] using
      UpperHalfPlane.eq_cuspFunction τ one_ne_zero hper

/-- Weight-six defect whose vanishing is Ramanujan's `E₄` equation. -/
def ramanujanE4DefectH : ℍ → ℂ := fun z =>
  serre_D 4 (ModularForm.E₄ : ℍ → ℂ) z + (1 / 3 : ℂ) * ModularForm.E₆ z

theorem ramanujanE4DefectH_mdiff : MDiff ramanujanE4DefectH := by
  exact (Derivative.serreDerivative_mdifferentiable 4 ModularForm.E₄.holo').add
    (mdifferentiable_const.mul ModularForm.E₆.holo')

theorem ramanujanE4DefectH_slash_SL2Z (γ : SL(2, ℤ)) :
    ramanujanE4DefectH ∣[(6 : ℤ)] γ = ramanujanE4DefectH := by
  have hserre := Derivative.serreDerivative_slash_equivariant
    (k := (4 : ℤ)) (F := (ModularForm.E₄ : ℍ → ℂ)) ModularForm.E₄.holo' (γ := γ)
  have hE4 : (ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ = ModularForm.E₄ := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantForm.slash_action_eqn ModularForm.E₄ (γ : GL (Fin 2) ℝ)
      ⟨γ, rfl⟩
  have hE6 : (ModularForm.E₆ : ℍ → ℂ) ∣[(6 : ℤ)] γ = ModularForm.E₆ := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantForm.slash_action_eqn ModularForm.E₆ (γ : GL (Fin 2) ℝ)
      ⟨γ, rfl⟩
  change ((serre_D 4 (ModularForm.E₄ : ℍ → ℂ)) +
      (1 / 3 : ℂ) • (ModularForm.E₆ : ℍ → ℂ)) ∣[(6 : ℤ)] γ =
    serre_D 4 (ModularForm.E₄ : ℍ → ℂ) +
      (1 / 3 : ℂ) • (ModularForm.E₆ : ℍ → ℂ)
  rw [SlashAction.add_slash, ModularForm.SL_smul_slash]
  rw [show (serre_D 4 (ModularForm.E₄ : ℍ → ℂ) ∣[(6 : ℤ)] γ) =
      serre_D 4 ((ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ) by simpa using hserre]
  rw [hE4, hE6]

theorem ramanujanE4DefectH_zeroAtImInfty : IsZeroAtImInfty ramanujanE4DefectH := by
  have hD : Tendsto (D (ModularForm.E₄ : ℍ → ℂ)) atImInfty (nhds 0) :=
    normalizedDerivOfComplex_tendsto_zero_ramanujan ModularForm.E₄.holo'
      (ModularFormClass.bdd_at_infty ModularForm.E₄)
  have hE2 := eisensteinSeries_E2_tendsto_one_atImInfty
  have hE4 := eisensteinSeries_E4_tendsto_one_atImInfty
  have hE6 := eisensteinSeries_E6_tendsto_one_atImInfty
  rw [IsZeroAtImInfty, Filter.ZeroAtFilter]
  change Tendsto (fun z : ℍ =>
    (D (ModularForm.E₄ : ℍ → ℂ) z - (4 / 12 : ℂ) * E₂ z * ModularForm.E₄ z) +
      (1 / 3 : ℂ) * ModularForm.E₆ z) atImInfty (nhds 0)
  convert (hD.sub ((tendsto_const_nhds.mul hE2).mul hE4)).add
    (tendsto_const_nhds.mul hE6) using 1 <;> norm_num

/-- Ramanujan's weight-six defect packaged as a level-one cusp form. -/
def ramanujanE4DefectCusp : CuspForm 𝒮ℒ 6 where
  toFun := ramanujanE4DefectH
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact ramanujanE4DefectH_slash_SL2Z γ
  holo' := ramanujanE4DefectH_mdiff
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [ramanujanE4DefectH_slash_SL2Z γ]
    exact ramanujanE4DefectH_zeroAtImInfty

theorem ramanujanE4DefectH_eq_zero : ramanujanE4DefectH = 0 := by
  have hz : ramanujanE4DefectCusp = 0 :=
    rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) ramanujanE4DefectCusp
  funext z
  exact DFunLike.congr_fun hz z

/-- Weight-eight defect whose vanishing is Ramanujan's `E₆` equation. -/
def ramanujanE6DefectH : ℍ → ℂ := fun z =>
  serre_D 6 (ModularForm.E₆ : ℍ → ℂ) z + (1 / 2 : ℂ) * ModularForm.E₄ z ^ 2

theorem ramanujanE6DefectH_mdiff : MDiff ramanujanE6DefectH := by
  exact (Derivative.serreDerivative_mdifferentiable 6 ModularForm.E₆.holo').add
    (mdifferentiable_const.mul (ModularForm.E₄.holo'.pow 2))

theorem ramanujanE6DefectH_slash_SL2Z (γ : SL(2, ℤ)) :
    ramanujanE6DefectH ∣[(8 : ℤ)] γ = ramanujanE6DefectH := by
  have hdef : ramanujanE6DefectH =
      serre_D 6 (ModularForm.E₆ : ℍ → ℂ) +
        (1 / 2 : ℂ) • ((ModularForm.E₄ : ℍ → ℂ) * ModularForm.E₄) := by
    funext z
    simp only [ramanujanE6DefectH, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [pow_two]
  have hserre := Derivative.serreDerivative_slash_equivariant
    (k := (6 : ℤ)) (F := (ModularForm.E₆ : ℍ → ℂ)) ModularForm.E₆.holo' (γ := γ)
  have hE6 : (ModularForm.E₆ : ℍ → ℂ) ∣[(6 : ℤ)] γ = ModularForm.E₆ := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantForm.slash_action_eqn ModularForm.E₆ (γ : GL (Fin 2) ℝ)
      ⟨γ, rfl⟩
  have hprod := ModularForm.mul_slash_SL2
    (4 : ℤ) (4 : ℤ) γ (ModularForm.E₄ : ℍ → ℂ) ModularForm.E₄
  have hE4 : (ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ = ModularForm.E₄ := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantForm.slash_action_eqn ModularForm.E₄ (γ : GL (Fin 2) ℝ)
      ⟨γ, rfl⟩
  rw [hdef, SlashAction.add_slash, ModularForm.SL_smul_slash]
  rw [show (serre_D 6 (ModularForm.E₆ : ℍ → ℂ) ∣[(8 : ℤ)] γ) =
      serre_D 6 ((ModularForm.E₆ : ℍ → ℂ) ∣[(6 : ℤ)] γ) by simpa using hserre]
  rw [show (((ModularForm.E₄ : ℍ → ℂ) * ModularForm.E₄) ∣[(8 : ℤ)] γ) =
      ((ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ) *
        ((ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ) by simpa using hprod]
  rw [hE6, hE4]

theorem ramanujanE6DefectH_zeroAtImInfty : IsZeroAtImInfty ramanujanE6DefectH := by
  have hD : Tendsto (D (ModularForm.E₆ : ℍ → ℂ)) atImInfty (nhds 0) :=
    normalizedDerivOfComplex_tendsto_zero_ramanujan ModularForm.E₆.holo'
      (ModularFormClass.bdd_at_infty ModularForm.E₆)
  have hE2 := eisensteinSeries_E2_tendsto_one_atImInfty
  have hE4 := eisensteinSeries_E4_tendsto_one_atImInfty
  have hE6 := eisensteinSeries_E6_tendsto_one_atImInfty
  rw [IsZeroAtImInfty, Filter.ZeroAtFilter]
  change Tendsto (fun z : ℍ =>
    (D (ModularForm.E₆ : ℍ → ℂ) z - (6 / 12 : ℂ) * E₂ z * ModularForm.E₆ z) +
      (1 / 2 : ℂ) * ModularForm.E₄ z ^ 2) atImInfty (nhds 0)
  convert (hD.sub ((tendsto_const_nhds.mul hE2).mul hE6)).add
    (tendsto_const_nhds.mul (hE4.pow 2)) using 1 <;> norm_num

/-- Ramanujan's weight-eight defect packaged as a level-one cusp form. -/
def ramanujanE6DefectCusp : CuspForm 𝒮ℒ 8 where
  toFun := ramanujanE6DefectH
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact ramanujanE6DefectH_slash_SL2Z γ
  holo' := ramanujanE6DefectH_mdiff
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [ramanujanE6DefectH_slash_SL2Z γ]
    exact ramanujanE6DefectH_zeroAtImInfty

theorem ramanujanE6DefectH_eq_zero : ramanujanE6DefectH = 0 := by
  have hz : ramanujanE6DefectCusp = 0 :=
    rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) ramanujanE6DefectCusp
  funext z
  exact DFunLike.congr_fun hz z

/-- First Ramanujan equation in normalized-derivative form. -/
theorem normalizedDeriv_eisensteinSeries_E2 (z : ℍ) :
    D E₂ z = (1 / 12 : ℂ) * (E₂ z ^ 2 - ModularForm.E₄ z) := by
  have hzero : ramanujanE2DefectCusp = 0 :=
    rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) ramanujanE2DefectCusp
  have h := DFunLike.congr_fun hzero z
  rw [CuspForm.zero_apply] at h
  change D E₂ z - (1 : ℂ) * 12⁻¹ * E₂ z * E₂ z +
      (1 / 12 : ℂ) * ModularForm.E₄ z = 0 at h
  linear_combination h

/-- Second Ramanujan equation in normalized-derivative form. -/
theorem normalizedDeriv_eisensteinSeries_E4 (z : ℍ) :
    D (ModularForm.E₄ : ℍ → ℂ) z =
      (1 / 3 : ℂ) * (E₂ z * ModularForm.E₄ z - ModularForm.E₆ z) := by
  have h := congrFun ramanujanE4DefectH_eq_zero z
  change D (ModularForm.E₄ : ℍ → ℂ) z -
      (4 / 12 : ℂ) * E₂ z * ModularForm.E₄ z +
      (1 / 3 : ℂ) * ModularForm.E₆ z = 0 at h
  linear_combination h

/-- Third Ramanujan equation in normalized-derivative form. -/
theorem normalizedDeriv_eisensteinSeries_E6 (z : ℍ) :
    D (ModularForm.E₆ : ℍ → ℂ) z =
      (1 / 2 : ℂ) * (E₂ z * ModularForm.E₆ z - ModularForm.E₄ z ^ 2) := by
  have h := congrFun ramanujanE6DefectH_eq_zero z
  change D (ModularForm.E₆ : ℍ → ℂ) z -
      (6 / 12 : ℂ) * E₂ z * ModularForm.E₆ z +
      (1 / 2 : ℂ) * ModularForm.E₄ z ^ 2 = 0 at h
  linear_combination h

theorem normalizedDeriv_two_eisensteinSeries_E2 (z : ℍ) :
    D (D E₂) z = (1 / 12 : ℂ) *
      (2 * E₂ z * D E₂ z - D (ModularForm.E₄ : ℍ → ℂ) z) := by
  have hfun : D E₂ = (1 / 12 : ℂ) •
      ((E₂ : ℍ → ℂ) ^ 2 - (ModularForm.E₄ : ℍ → ℂ)) := by
    funext w
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul]
    exact normalizedDeriv_eisensteinSeries_E2 w
  rw [hfun,
    Derivative.normalizedDerivOfComplex_smul (1 / 12 : ℂ)
      ((E₂ : ℍ → ℂ) ^ 2 - (ModularForm.E₄ : ℍ → ℂ))
      ((E2_mdifferentiable.pow 2).sub ModularForm.E₄.holo'),
    Derivative.normalizedDerivOfComplex_sub ((E₂ : ℍ → ℂ) ^ 2)
      (ModularForm.E₄ : ℍ → ℂ)
      (E2_mdifferentiable.pow 2) ModularForm.E₄.holo',
    Derivative.normalizedDerivOfComplex_pow (E₂ : ℍ → ℂ) 2 E2_mdifferentiable,
    hfun]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  norm_num

theorem normalizedDeriv_two_eisensteinSeries_E4 (z : ℍ) :
    D (D (ModularForm.E₄ : ℍ → ℂ)) z = (1 / 3 : ℂ) *
      (D E₂ z * ModularForm.E₄ z + E₂ z * D (ModularForm.E₄ : ℍ → ℂ) z -
        D (ModularForm.E₆ : ℍ → ℂ) z) := by
  have hfun : D (ModularForm.E₄ : ℍ → ℂ) = (1 / 3 : ℂ) •
      ((E₂ : ℍ → ℂ) * (ModularForm.E₄ : ℍ → ℂ) -
        (ModularForm.E₆ : ℍ → ℂ)) := by
    funext w
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
    exact normalizedDeriv_eisensteinSeries_E4 w
  rw [hfun,
    Derivative.normalizedDerivOfComplex_smul (1 / 3 : ℂ)
      ((E₂ : ℍ → ℂ) * (ModularForm.E₄ : ℍ → ℂ) - (ModularForm.E₆ : ℍ → ℂ))
      ((E2_mdifferentiable.mul ModularForm.E₄.holo').sub ModularForm.E₆.holo'),
    Derivative.normalizedDerivOfComplex_sub
      ((E₂ : ℍ → ℂ) * (ModularForm.E₄ : ℍ → ℂ))
      (ModularForm.E₆ : ℍ → ℂ)
      (E2_mdifferentiable.mul ModularForm.E₄.holo') ModularForm.E₆.holo',
    Derivative.normalizedDerivOfComplex_mul (E₂ : ℍ → ℂ)
      (ModularForm.E₄ : ℍ → ℂ) E2_mdifferentiable ModularForm.E₄.holo', hfun]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]

theorem normalizedDeriv_three_eisensteinSeries_E2 (z : ℍ) :
    D (D (D E₂)) z = (1 / 12 : ℂ) *
      (2 * D E₂ z ^ 2 + 2 * E₂ z * D (D E₂) z -
        D (D (ModularForm.E₄ : ℍ → ℂ)) z) := by
  have hfun : D (D E₂) = (1 / 12 : ℂ) •
      ((2 : ℂ) • ((E₂ : ℍ → ℂ) * D E₂) -
        D (ModularForm.E₄ : ℍ → ℂ)) := by
    funext w
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
    convert normalizedDeriv_two_eisensteinSeries_E2 w using 1 <;> ring
  have hDE2 : MDiff (D E₂) :=
    Derivative.normalizedDerivOfComplex_mdifferentiable E2_mdifferentiable
  have hDE4 : MDiff (D (ModularForm.E₄ : ℍ → ℂ)) :=
    Derivative.normalizedDerivOfComplex_mdifferentiable ModularForm.E₄.holo'
  rw [hfun,
    Derivative.normalizedDerivOfComplex_smul (1 / 12 : ℂ)
      ((2 : ℂ) • ((E₂ : ℍ → ℂ) * D E₂) - D (ModularForm.E₄ : ℍ → ℂ))
      (((E2_mdifferentiable.mul hDE2).const_smul 2).sub hDE4),
    Derivative.normalizedDerivOfComplex_sub
      ((2 : ℂ) • ((E₂ : ℍ → ℂ) * D E₂)) (D (ModularForm.E₄ : ℍ → ℂ))
      ((E2_mdifferentiable.mul hDE2).const_smul 2) hDE4,
    Derivative.normalizedDerivOfComplex_smul 2
      ((E₂ : ℍ → ℂ) * D E₂) (E2_mdifferentiable.mul hDE2),
    Derivative.normalizedDerivOfComplex_mul (E₂ : ℍ → ℂ) (D E₂)
      E2_mdifferentiable hDE2, hfun]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- Chazy's equation for `E₂`, under `D = (2πi)⁻¹ d/dτ`. -/
theorem chazy_eisensteinSeries_E2 (z : ℍ) :
    2 * D (D (D E₂)) z - 2 * E₂ z * D (D E₂) z + 3 * D E₂ z ^ 2 = 0 := by
  rw [normalizedDeriv_three_eisensteinSeries_E2,
    normalizedDeriv_two_eisensteinSeries_E2,
    normalizedDeriv_two_eisensteinSeries_E4,
    normalizedDeriv_eisensteinSeries_E2,
    normalizedDeriv_eisensteinSeries_E4,
    normalizedDeriv_eisensteinSeries_E6]
  ring

end

end Bottcher
