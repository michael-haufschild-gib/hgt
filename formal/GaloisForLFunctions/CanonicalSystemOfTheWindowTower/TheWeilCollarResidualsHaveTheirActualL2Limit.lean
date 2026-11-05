import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheExteriorWeilResponseHasItsScaledBoundaryLimit
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFormDetectsIntervalLength
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilKernelIncrementSolvesTheFullCollarEquation
import GaloisForLFunctions.HTGeometry.HardyPaleyWienerTransport

/-!
# Actual L² rescaling of a logarithmic collar response

Unitary dilation and a literal unit-interval cut turn a local boundary
profile into an actual L² vector. Its normalized mean-square limit is
therefore strong L² convergence, and determines the limiting source mass.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

/-- The normalized actual source seen on a closing collar, rescaled to the unit interval. -/
def logarithmicCollarRescaling (h : ℝ) (f : SoninL2) : SoninL2 :=
  if hh : 0 < h then
    (((Real.sqrt h*Real.sqrt (Real.log (1/h)) : ℝ) : ℂ)⁻¹) •
      indicatorCutoff (Ioc (0 : ℝ) 1) measurableSet_Ioc (dilation h hh f)
  else 0

private theorem collarCut_dilation {h : ℝ} (hh : 0 < h) (f : SoninL2) :
    indicatorCutoff (Ioc (0 : ℝ) 1) measurableSet_Ioc (dilation h hh f) =
      dilation h hh (indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc f) := by
  apply Lp.ext
  have hc := (indicatorCutoff_ae (Ioc (0 : ℝ) h) measurableSet_Ioc f).comp_tendsto
    (realMul_quasiMeasurePreserving h hh.ne').tendsto_ae
  filter_upwards [indicatorCutoff_ae (Ioc (0 : ℝ) 1) measurableSet_Ioc (dilation h hh f),
    dilation_ae h hh f,
    dilation_ae h hh (indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc f), hc]
      with s hu hd he hc
  change indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc f (h*s) =
    (Ioc (0 : ℝ) h).indicator (fun x => f x) (h*s) at hc
  rw [hu, he, hc]
  have hm : h*s ∈ Ioc (0 : ℝ) h ↔ s ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · intro hs
      refine ⟨(mul_pos_iff_of_pos_left hh).mp hs.1, ?_⟩
      have hi := mul_le_mul_of_nonneg_left hs.2 (inv_nonneg.mpr hh.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul] using hi
    · intro hs
      exact ⟨mul_pos hh hs.1, mul_le_of_le_one_right hh.le hs.2⟩
  by_cases hs : s ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hs, indicator_of_mem (hm.mpr hs), hd]
  · rw [indicator_of_notMem hs, indicator_of_notMem (fun hp => hs (hm.mp hp)), mul_zero]

/-- The rescaled mass is exactly the original collar mass divided by its logarithmic scale. -/
theorem norm_logarithmicCollarRescaling_sq {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (f : SoninL2) :
    ‖logarithmicCollarRescaling h f‖^2 =
      ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc f‖^2 / (h*Real.log (1/h)) := by
  have hlog : 0 < Real.log (1/h) := Real.log_pos ((one_lt_div hh).mpr hh1)
  rw [logarithmicCollarRescaling, dif_pos hh, collarCut_dilation hh,
    norm_smul, (dilation h hh).norm_map, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
    mul_pow, inv_pow, mul_pow, Real.sq_sqrt hh.le, Real.sq_sqrt hlog.le]
  exact (div_eq_inv_mul _ _).symm

/-- The rescaled L² vector has the literal normalized profile on the unit interval. -/
theorem logarithmicCollarRescaling_coeFn {h : ℝ} (hh : 0 < h) (f : SoninL2) :
    (logarithmicCollarRescaling h f : ℝ → ℂ) =ᵐ[volume]
      (Ioc (0 : ℝ) 1).indicator (fun s => f (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ)) := by
  rw [logarithmicCollarRescaling, dif_pos hh]
  filter_upwards [Lp.coeFn_smul (((Real.sqrt h*Real.sqrt (Real.log (1/h)) : ℝ) : ℂ)⁻¹)
    (indicatorCutoff (Ioc (0 : ℝ) 1) measurableSet_Ioc (dilation h hh f)),
    indicatorCutoff_ae (Ioc (0 : ℝ) 1) measurableSet_Ioc (dilation h hh f),
    dilation_ae h hh f] with s hm hc hd
  rw [hm, Pi.smul_apply, smul_eq_mul, hc]
  by_cases hs : s ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hs, indicator_of_mem hs, hd, Complex.ofReal_mul, mul_inv_rev]
    have hn : (Real.sqrt h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hh).ne'
    calc
      _ = ((Real.sqrt h : ℂ)⁻¹*(Real.sqrt h : ℂ)) *
          (f (h*s)*(Real.sqrt (Real.log (1/h)) : ℂ)⁻¹) := by ring
      _ = _ := by
        rw [inv_mul_cancel₀ hn, one_mul]
        exact (div_eq_mul_inv _ _).symm
  · rw [indicator_of_notMem hs, indicator_of_notMem hs, mul_zero]

private theorem logarithmicCollarRescaling_profile_ae {δ h : ℝ} (hh : 0 < h) (hδ : h ≤ δ)
    (f : SoninL2) (F : ℝ → ℂ) (hF : (f : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) δ)] F) :
    (logarithmicCollarRescaling h f : ℝ → ℂ) =ᵐ[volume]
      (Ioc (0 : ℝ) 1).indicator (fun s => F (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ)) := by
  have he := (realMul_quasiMeasurePreserving h hh.ne').tendsto_ae.eventually
    ((ae_restrict_iff' measurableSet_Ioc).mp hF)
  filter_upwards [logarithmicCollarRescaling_coeFn hh f, he] with s hs he
  rw [hs]
  by_cases hu : s ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hu, indicator_of_mem hu]
    apply congrArg (fun z : ℂ => z/(Real.sqrt (Real.log (1/h)) : ℂ))
    apply he
    exact ⟨mul_pos hh hu.1, (mul_le_of_le_one_right hh.le hu.2).trans hδ⟩
  · rw [indicator_of_notMem hu, indicator_of_notMem hu]

/-- The actual squared L² distance is exactly the literal mean-square collar error. -/
theorem norm_logarithmicCollarRescaling_sub_const_sq {δ h : ℝ} (hh : 0 < h) (hδ : h ≤ δ)
    (f : SoninL2) (F : ℝ → ℂ) (hF : (f : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) δ)] F)
    (τ : ℂ) :
    ‖logarithmicCollarRescaling h f - τ • logarithmicIntervalSource 0 1‖^2 =
      ∫ s in Ioc (0 : ℝ) 1, ‖F (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ)-τ‖^2 := by
  rw [norm_sq_lp_eq_integral_norm_sq]
  calc
    _ = ∫ s : ℝ, (Ioc (0 : ℝ) 1).indicator
        (fun t => ‖F (h*t)/(Real.sqrt (Real.log (1/h)) : ℂ)-τ‖^2) s := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (logarithmicCollarRescaling h f)
        (τ • logarithmicIntervalSource 0 1),
        logarithmicCollarRescaling_profile_ae hh hδ f F hF,
        Lp.coeFn_smul τ (logarithmicIntervalSource 0 1), logarithmicIntervalSource_coeFn 0 1]
          with s hs he hm hc
      rw [hs, Pi.sub_apply, he, hm, Pi.smul_apply, smul_eq_mul, hc]
      by_cases hu : s ∈ Ioc (0 : ℝ) 1
      · rw [indicator_of_mem hu, indicator_of_mem hu, indicator_of_mem hu, mul_one]
      · rw [indicator_of_notMem hu, indicator_of_notMem hu, indicator_of_notMem hu,
          mul_zero, sub_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    _ = _ := integral_indicator measurableSet_Ioc

/-- Every actual L² source with a local normalized logarithmic profile converges strongly after rescaling. -/
theorem tendsto_logarithmicCollarRescaling {δ : ℝ} (hδ : 0 < δ)
    (f : SoninL2) (F : ℝ → ℂ) (hF : Measurable F)
    (hlocal : (f : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) δ)] F) {τ : ℂ}
    (hτ : Tendsto (fun d : ℝ => F d/(Real.sqrt (Real.log (1/d)) : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds τ)) :
    Tendsto (fun h : ℝ => logarithmicCollarRescaling h f)
      (𝓝[>] (0 : ℝ)) (nhds (τ • logarithmicIntervalSource 0 1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmean := logarithmic_boundary_limit_in_mean_square hF hτ
  have hsquare : Tendsto (fun h : ℝ =>
      ‖logarithmicCollarRescaling h f-τ • logarithmicIntervalSource 0 1‖^2)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
    apply hmean.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with h hh hhd
    exact (norm_logarithmicCollarRescaling_sub_const_sq hh hhd.le f F hlocal τ).symm
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_norm] using h

/-- The rescaled source mass tends to the squared modulus of its actual boundary coefficient. -/
theorem tendsto_norm_logarithmicCollarRescaling_sq {δ : ℝ} (hδ : 0 < δ)
    (f : SoninL2) (F : ℝ → ℂ) (hF : Measurable F)
    (hlocal : (f : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) δ)] F) {τ : ℂ}
    (hτ : Tendsto (fun d : ℝ => F d/(Real.sqrt (Real.log (1/d)) : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds τ)) :
    Tendsto (fun h : ℝ => ‖logarithmicCollarRescaling h f‖^2)
      (𝓝[>] (0 : ℝ)) (nhds (‖τ‖^2)) := by
  have h := (tendsto_logarithmicCollarRescaling hδ f F hF hlocal hτ).norm.pow 2
  simpa only [norm_smul, mul_pow, norm_logarithmicIntervalSource_sq zero_le_one,
    sub_zero, mul_one] using h

/-- The actual shrinking-collar mass has the exact coefficient read by the normalized profile. -/
theorem tendsto_collar_mass_div_logarithmic_scale {δ : ℝ} (hδ : 0 < δ)
    (f : SoninL2) (F : ℝ → ℂ) (hF : Measurable F)
    (hlocal : (f : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) δ)] F) {τ : ℂ}
    (hτ : Tendsto (fun d : ℝ => F d/(Real.sqrt (Real.log (1/d)) : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds τ)) :
    Tendsto (fun h : ℝ =>
      ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc f‖^2/(h*Real.log (1/h)))
      (𝓝[>] (0 : ℝ)) (nhds (‖τ‖^2)) := by
  apply (tendsto_norm_logarithmicCollarRescaling_sq hδ f F hF hlocal hτ).congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds]
      with h hh hh1
  exact norm_logarithmicCollarRescaling_sq hh hh1 f

namespace WeilHilbertBeforeContact

private theorem rightResidual_extension_profile_ae {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    (suzukiPositiveZeroExtension (evalVectorRightCollarResidual hab z) : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (b.1.1-a.1.1))] evalVectorRightCollarProfile a b.1 hab z := by
  filter_upwards [evalVectorRightCollarResidual_ae hab z,
    ae_restrict_of_ae (suzukiPositiveZeroExtension_ae (evalVectorRightCollarResidual hab z)),
    ae_restrict_mem measurableSet_Ioc] with d hp he hd
  have hdpos : d ∈ Ioi (0 : ℝ) := hd.1
  rw [he, suzukiPositiveZeroExtensionFun, indicator_of_mem hdpos, hp]

private theorem leftResidual_extension_profile_ae {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual hab z) : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (b.1.1-a.1.1))] evalVectorLeftCollarProfile a b.1 hab z := by
  filter_upwards [evalVectorLeftCollarResidual_ae hab z,
    ae_restrict_of_ae (suzukiPositiveZeroExtension_ae (evalVectorLeftCollarResidual hab z)),
    ae_restrict_mem measurableSet_Ioc] with d hp he hd
  have hdpos : d ∈ Ioi (0 : ℝ) := hd.1
  rw [he, suzukiPositiveZeroExtensionFun, indicator_of_mem hdpos, hp]

/-- The full actual right residual converges strongly to its constant endpoint trace after rescaling. -/
theorem evalVectorRightCollarResidual_scaled_limit {a b : PrecontactAperture}
    (hab : a.1.1 < b.1.1) (z : ℂ) :
    Tendsto (fun h : ℝ => logarithmicCollarRescaling h
      (suzukiPositiveZeroExtension (evalVectorRightCollarResidual hab.le z)))
      (𝓝[>] (0 : ℝ)) (nhds ((∫ y : ℝ, (logarithmicCausalKernel y : ℂ)*
        (evalVectorRightEndpointForcing a z : RealLineL2) y) • logarithmicIntervalSource 0 1)) :=
  tendsto_logarithmicCollarRescaling (sub_pos.mpr hab) _ _
    (measurable_evalVectorRightCollarProfile a b.1 hab.le z)
    (rightResidual_extension_profile_ae hab.le z)
    (evalVectorRightCollarProfile_normalized_limit a b.1 hab.le z)

/-- The reflected left actual residual has the matching strong L² boundary limit. -/
theorem evalVectorLeftCollarResidual_scaled_limit {a b : PrecontactAperture}
    (hab : a.1.1 < b.1.1) (z : ℂ) :
    Tendsto (fun h : ℝ => logarithmicCollarRescaling h
      (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual hab.le z)))
      (𝓝[>] (0 : ℝ)) (nhds ((∫ y : ℝ, (logarithmicCausalKernel y : ℂ)*
        (evalVectorLeftEndpointForcing a z : RealLineL2) y) • logarithmicIntervalSource 0 1)) :=
  tendsto_logarithmicCollarRescaling (sub_pos.mpr hab) _ _
    (measurable_evalVectorLeftCollarProfile a b.1 hab.le z)
    (leftResidual_extension_profile_ae hab.le z)
    (evalVectorLeftCollarProfile_normalized_limit a b.1 hab.le z)

/-- The right collar mass has exact leading size `h log(1/h)` times the squared right trace. -/
theorem evalVectorRightCollarResidual_mass_limit {a b : PrecontactAperture}
    (hab : a.1.1 < b.1.1) (z : ℂ) :
    Tendsto (fun h : ℝ => ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc
      (suzukiPositiveZeroExtension (evalVectorRightCollarResidual hab.le z))‖^2 /
        (h*Real.log (1/h))) (𝓝[>] (0 : ℝ))
      (nhds (‖∫ y : ℝ, (logarithmicCausalKernel y : ℂ)*
        (evalVectorRightEndpointForcing a z : RealLineL2) y‖^2)) :=
  tendsto_collar_mass_div_logarithmic_scale (sub_pos.mpr hab) _ _
    (measurable_evalVectorRightCollarProfile a b.1 hab.le z)
    (rightResidual_extension_profile_ae hab.le z)
    (evalVectorRightCollarProfile_normalized_limit a b.1 hab.le z)

/-- The left collar mass has the same exact law with the actual left trace. -/
theorem evalVectorLeftCollarResidual_mass_limit {a b : PrecontactAperture}
    (hab : a.1.1 < b.1.1) (z : ℂ) :
    Tendsto (fun h : ℝ => ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc
      (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual hab.le z))‖^2 /
        (h*Real.log (1/h))) (𝓝[>] (0 : ℝ))
      (nhds (‖∫ y : ℝ, (logarithmicCausalKernel y : ℂ)*
        (evalVectorLeftEndpointForcing a z : RealLineL2) y‖^2)) :=
  tendsto_collar_mass_div_logarithmic_scale (sub_pos.mpr hab) _ _
    (measurable_evalVectorLeftCollarProfile a b.1 hab.le z)
    (leftResidual_extension_profile_ae hab.le z)
    (evalVectorLeftCollarProfile_normalized_limit a b.1 hab.le z)

#print axioms evalVectorRightCollarResidual_scaled_limit
#print axioms evalVectorLeftCollarResidual_scaled_limit
#print axioms evalVectorRightCollarResidual_mass_limit
#print axioms evalVectorLeftCollarResidual_mass_limit
end WeilHilbertBeforeContact

#print axioms tendsto_logarithmicCollarRescaling
#print axioms tendsto_norm_logarithmicCollarRescaling_sq
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
