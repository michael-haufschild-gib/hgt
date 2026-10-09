import GaloisForLFunctions.HTGeometry.L2TranslationExponentialIndependence
import GaloisForLFunctions.RHTower.RiemannKernelSpectralLocalization
import GaloisForLFunctions.RHTower.WeilLogShiftDomainBoundary

/-!
# Faithful finite translation synthesis for the actual autocorrelation

The actual autocorrelation belongs to L² and has a nonzero class. Its
literal translates therefore admit no nontrivial finite cancellation.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform BigOperators
open Zeta23

noncomputable section

namespace RHTower

open WeilExcess

/-- The existing L¹ and uniform bounds give actual square integrability. -/
theorem memLp_riemannAutocorr_complex :
    MemLp (fun y : ℝ => ((riemannAutocorr y : ℝ) : ℂ)) 2 volume := by
  have hc := Complex.continuous_ofReal.comp riemannAutocorr_continuous
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  apply (integrable_riemannAutocorr_complex.norm.const_mul (riemannAutocorr 0)).mono'
    (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards with y
  have hn : ‖((riemannAutocorr y : ℝ) : ℂ)‖ = riemannAutocorr y := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (riemannAutocorr_nonneg y)]
  change ‖‖((riemannAutocorr y : ℝ) : ℂ)‖ ^ 2‖ ≤
    riemannAutocorr 0 * ‖((riemannAutocorr y : ℝ) : ℂ)‖
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hn, pow_two]
  exact mul_le_mul_of_nonneg_right (riemannAutocorr_le_zero y) (riemannAutocorr_nonneg y)

/-- The actual complex L² class of the real autocorrelation. -/
def riemannAutocorrL2 : Lp ℂ 2 (volume : Measure ℝ) :=
  memLp_riemannAutocorr_complex.toLp _

theorem riemannAutocorrL2_ae : (riemannAutocorrL2 : ℝ → ℂ) =ᵐ[volume]
    fun y => ((riemannAutocorr y : ℝ) : ℂ) :=
  memLp_riemannAutocorr_complex.coeFn_toLp

/-- Positivity at the origin and continuity exclude the zero L² class. -/
theorem riemannAutocorrL2_ne_zero : riemannAutocorrL2 ≠ 0 := by
  intro hzero
  have hae : (fun y : ℝ => ((riemannAutocorr y : ℝ) : ℂ)) =ᵐ[volume] 0 :=
    riemannAutocorrL2_ae.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hzero)
  have he := ((Complex.continuous_ofReal.comp riemannAutocorr_continuous).ae_eq_iff_eq
    (μ := (volume : Measure ℝ)) continuous_const).mp hae
  have h0 : ((riemannAutocorr 0 : ℝ) : ℂ) = 0 := congrFun he 0
  exact (riemannAutocorr_pos 0).ne' (Complex.ofReal_eq_zero.mp h0)

/-- Translation of the actual L² class has the literal translated kernel
as a representative; no Schwartz premise is used. -/
theorem additiveTranslation_riemannAutocorrL2_ae (a : ℝ) :
    (MellinL2.additiveTranslationUnitary a riemannAutocorrL2 : ℝ → ℂ) =ᵐ[volume]
      fun y => ((riemannAutocorr (y + a) : ℝ) : ℂ) := by
  exact (Lp.coeFn_compMeasurePreserving riemannAutocorrL2
    (MellinL2.realTranslation_measurePreserving a)).trans
      (riemannAutocorrL2_ae.comp_tendsto
        (MellinL2.realTranslation_measurePreserving a).quasiMeasurePreserving.tendsto_ae)

/-- The entire real-indexed family of actual translated L² classes is independent. -/
theorem linearIndependent_riemannAutocorrL2_translates :
    LinearIndependent ℂ (fun a : ℝ => MellinL2.additiveTranslationUnitary a riemannAutocorrL2) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  apply (linearIndependent_equiv e).mp
  exact GaloisForLFunctions.HTGeometry.linearIndependent_L2_translates
    (fun i => (e i : ℝ)) (Subtype.val_injective.comp e.injective) riemannAutocorrL2_ne_zero

/-- Exact faithfulness of finite synthesis against the literal autocorrelation
translates. The analytic premises have all been discharged for this kernel. -/
theorem riemannAutocorr_translate_sum_eq_zero_iff (d : ℝ →₀ ℂ) :
    (∀ y : ℝ, d.sum (fun a c => c * ((riemannAutocorr (y + a) : ℝ) : ℂ)) = 0) ↔ d = 0 := by
  classical
  constructor
  · intro h
    apply (linearIndependent_iff.mp linearIndependent_riemannAutocorrL2_translates) d
    rw [Finsupp.linearCombination_apply]
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    have hterm (a : ℝ) :
        ((d a • MellinL2.additiveTranslationUnitary a riemannAutocorrL2 : Lp ℂ 2 volume) : ℝ → ℂ)
          =ᵐ[volume] fun y => d a * ((riemannAutocorr (y + a) : ℝ) : ℂ) := by
      filter_upwards [Lp.coeFn_smul (d a) (MellinL2.additiveTranslationUnitary a riemannAutocorrL2),
        additiveTranslation_riemannAutocorrL2_ae a] with y hs ht
      simpa only [Pi.smul_apply, smul_eq_mul, ht] using hs
    filter_upwards [Lp.coeFn_finsetSum d.support
      (fun a => d a • MellinL2.additiveTranslationUnitary a riemannAutocorrL2),
      ae_all_iff.mpr (fun a : d.support => hterm (a : ℝ))] with y hs ht
    change (∑ a ∈ d.support, d a • MellinL2.additiveTranslationUnitary a riemannAutocorrL2) y = 0
    calc
      _ = ∑ a ∈ d.support, (d a • MellinL2.additiveTranslationUnitary a riemannAutocorrL2 :
          Lp ℂ 2 volume) y := by simpa only [Finset.sum_apply] using hs
      _ = d.sum (fun a c => c * ((riemannAutocorr (y + a) : ℝ) : ℂ)) :=
        Finset.sum_congr rfl (fun a ha => ht ⟨a, ha⟩)
      _ = 0 := h y
  · rintro rfl
    simp

end RHTower
