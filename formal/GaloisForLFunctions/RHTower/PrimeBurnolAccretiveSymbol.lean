import GaloisForLFunctions.RHTower.PrimeBurnolSymbolClassification
import GaloisForLFunctions.HTGeometry.CayleyDenseResolvent

/-! # Actual prime resolvents of arbitrary accretive holomorphic symbols -/

open Complex Set Filter Topology
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

structure BurnolAccretiveSymbol where
  toFun : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ toFun PrimeBlindCarlson.rightHalf
  nonneg : ∀ z ∈ PrimeBlindCarlson.rightHalf, 0 ≤ (toFun z).re

instance : CoeFun BurnolAccretiveSymbol (fun _ => ℂ → ℂ) := ⟨BurnolAccretiveSymbol.toFun⟩

namespace BurnolAccretiveSymbol
variable (ψ : BurnolAccretiveSymbol)

theorem one_add_ne_zero {z : ℂ} (hz : 0 < z.re) : 1+ψ z ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
  linarith [ψ.nonneg z hz]

def resolventFn (z : ℂ) : ℂ := (1+ψ z)⁻¹

theorem analytic_resolventFn :
    AnalyticOnNhd ℂ ψ.resolventFn PrimeBlindCarlson.rightHalf := by
  intro z hz
  exact (analyticAt_const.add (ψ.analytic z hz)).inv (ψ.one_add_ne_zero hz)

theorem resolventFn_ne_zero {z : ℂ} (hz : 0 < z.re) : ψ.resolventFn z ≠ 0 :=
  inv_ne_zero (ψ.one_add_ne_zero hz)

theorem norm_resolventFn_le {z : ℂ} (hz : 0 < z.re) : ‖ψ.resolventFn z‖ ≤ 1 := by
  have hd : (1 : ℝ) ≤ ‖1+ψ z‖ := by
    have h := (le_abs_self (1+ψ z).re).trans (Complex.abs_re_le_norm (1+ψ z))
    simp only [Complex.add_re, Complex.one_re] at h
    linarith [ψ.nonneg z hz]
  simpa only [resolventFn, norm_inv, one_div, inv_one] using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd)

private theorem exists_resolvent :
    ∃! R : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2,
      ‖R‖ ≤ 1 ∧ ∀ (z : ℂ) (hz : 0 < z.re),
        R (burnolComplexFeature z hz) = ψ.resolventFn z • burnolComplexFeature z hz :=
  existsUnique_burnol_operator_of_holomorphic ψ.analytic_resolventFn zero_le_one
    (fun _ hz => ψ.norm_resolventFn_le hz)

def resolvent : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 := ψ.exists_resolvent.choose

theorem norm_resolvent_le : ‖ψ.resolvent‖ ≤ 1 := ψ.exists_resolvent.choose_spec.1.1

theorem resolvent_feature (z : ℂ) (hz : 0 < z.re) :
    ψ.resolvent (burnolComplexFeature z hz) = ψ.resolventFn z • burnolComplexFeature z hz :=
  ψ.exists_resolvent.choose_spec.1.2 z hz

theorem resolvent_prime (p : Nat.Primes) :
    ψ.resolvent (primeLogCriticalLaplaceFeatureL2 p) =
      ψ.resolventFn (Real.log (p : ℝ)) • primeLogCriticalLaplaceFeatureL2 p :=
  (primeBurnol_eigenvalue_iff ψ.resolvent p _).mpr (ψ.resolvent_feature _ _)

theorem norm_cayleyFn_le {z : ℂ} (hz : 0 < z.re) :
    ‖1-2*ψ.resolventFn z‖ ≤ 1 := by
  have he : 1-2*ψ.resolventFn z = (ψ z-1)/(1+ψ z) := by
    rw [resolventFn]
    field_simp [ψ.one_add_ne_zero hz]
    ring
  rw [he, norm_div]
  apply (div_le_one (norm_pos_iff.mpr (ψ.one_add_ne_zero hz))).mpr
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    sub_zero, Complex.add_re, Complex.add_im, zero_add]
  nlinarith [ψ.nonneg z hz]

theorem norm_cayley_le :
    ‖(1 : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) - (2 : ℂ) • ψ.resolvent‖ ≤ 1 := by
  have hhol : AnalyticOnNhd ℂ (fun z => 1-2*ψ.resolventFn z) PrimeBlindCarlson.rightHalf := by
    intro z hz
    exact analyticAt_const.sub (analyticAt_const.mul (ψ.analytic_resolventFn z hz))
  obtain ⟨U, ⟨hU, he⟩, _⟩ := existsUnique_burnol_operator_of_holomorphic hhol zero_le_one
    (fun _ hz => ψ.norm_cayleyFn_le hz)
  have hUeq : U = 1-(2 : ℂ) • ψ.resolvent := by
    apply primeBurnol_operator_ext
    intro p
    have hp := (primeBurnol_eigenvalue_iff U p _).mpr (he _
      (Real.log_pos (by exact_mod_cast p.property.one_lt)))
    rw [hp]
    change (1-2*ψ.resolventFn (Real.log (p : ℝ))) • primeLogCriticalLaplaceFeatureL2 p =
      primeLogCriticalLaplaceFeatureL2 p-(2 : ℂ) • ψ.resolvent (primeLogCriticalLaplaceFeatureL2 p)
    rw [ψ.resolvent_prime, smul_smul, sub_smul, one_smul]
  rwa [hUeq] at hU

theorem resolvent_denseRange : DenseRange ψ.resolvent := by
  have hs : Submodule.span ℂ (Set.range primeLogCriticalLaplaceFeatureL2) ≤
      ψ.resolvent.toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    refine ⟨(1+ψ (Real.log (p : ℝ))) • primeLogCriticalLaplaceFeatureL2 p, ?_⟩
    change ψ.resolvent ((1+ψ (Real.log (p : ℝ))) • primeLogCriticalLaplaceFeatureL2 p) = _
    rw [map_smul, ψ.resolvent_prime, smul_smul, resolventFn,
      mul_inv_cancel₀ (ψ.one_add_ne_zero (Real.log_pos (by exact_mod_cast p.property.one_lt))), one_smul]
  exact dense_primeLogCriticalLaplaceFeature_span.mono hs

theorem resolvent_injective : Function.Injective ψ.resolvent :=
  injective_of_denseRange_cayley_contraction ψ.resolvent ψ.resolvent_denseRange ψ.norm_cayley_le

end BurnolAccretiveSymbol
end RHTower
