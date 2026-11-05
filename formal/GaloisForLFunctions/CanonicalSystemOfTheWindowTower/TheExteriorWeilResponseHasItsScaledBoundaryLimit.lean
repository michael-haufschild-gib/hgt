import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilTracesDetermineTheirExteriorGammaResponse

/-!
# Mean-square boundary scaling of the exterior Weil response

A square-root logarithmic boundary asymptotic remains valid after dilation
in the unit-interval L² norm. The logarithmic ratio is bounded by
`1 + log(1/s)`, an integrable majorant on the unit interval.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

private theorem tendsto_positive_scale_zero {s : ℝ} (hs : 0 < s) :
    Tendsto (fun h : ℝ => h*s) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have ht : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (nhds 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  rw [nhdsWithin]
  refine tendsto_inf.mpr ⟨by simpa only [zero_mul, nhdsWithin] using ht.mul_const s, ?_⟩
  apply tendsto_principal.mpr
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact mul_pos hh hs

private theorem log_reciprocal_product {h s : ℝ} (hh : 0 < h) (hs : 0 < s) :
    Real.log (1/(h*s)) = Real.log (1/h) + Real.log (1/s) := by
  simp only [one_div, Real.log_inv, Real.log_mul hh.ne' hs.ne', neg_add]

private theorem tendsto_logarithmic_scale_ratio {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Tendsto (fun h : ℝ => Real.sqrt (Real.log (1/(h*s))) /
      Real.sqrt (Real.log (1/h))) (𝓝[>] (0 : ℝ)) (nhds 1) := by
  have hlog : Tendsto (fun h : ℝ => Real.log (1/h)) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hratio : Tendsto (fun h : ℝ => 1+Real.log (1/s)/Real.log (1/h))
      (𝓝[>] (0 : ℝ)) (nhds 1) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero, Function.comp_def] using
      ((tendsto_inv_atTop_zero.comp hlog).const_mul (Real.log (1/s))).const_add 1
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  simp only [Real.sqrt_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with h hh hh1
  change (0 : ℝ) < h at hh
  have hhs : h*s < 1 := (mul_le_of_le_one_right hh.le hs1).trans_lt hh1
  have hL : 0 < Real.log (1/h) := Real.log_pos (by rw [lt_div_iff₀ hh]; linarith only [hh1])
  have hLs : 0 ≤ Real.log (1/(h*s)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (mul_pos hh hs)]; linarith only [hhs])
  dsimp only [Function.comp_apply]
  rw [show 1+Real.log (1/s)/Real.log (1/h) =
    Real.log (1/(h*s))/Real.log (1/h) by
      rw [log_reciprocal_product hh hs]; field_simp [hL.ne']]
  exact Real.sqrt_div hLs _

/-- A normalized logarithmic boundary limit also holds after dilation in mean square. -/
theorem logarithmic_boundary_limit_in_mean_square {F : ℝ → ℂ} (hF : Measurable F) {τ : ℂ}
    (hτ : Tendsto (fun d : ℝ => F d / (Real.sqrt (Real.log (1/d)) : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds τ)) :
    Tendsto (fun h : ℝ => ∫ s in Ioc (0 : ℝ) 1,
      ‖F (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ)-τ‖^2)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  let C : ℝ := ‖τ‖+1
  obtain ⟨δ, hδ, hlocal⟩ := Metric.tendsto_nhdsWithin_nhds.mp hτ 1 zero_lt_one
  have hb {d : ℝ} (hd : 0 < d) (hdδ : d < δ) :
      ‖F d/(Real.sqrt (Real.log (1/d)) : ℂ)‖ ≤ C := by
    have he := hlocal hd (by rw [Real.dist_eq, sub_zero, abs_of_pos hd]; exact hdδ)
    rw [dist_eq_norm] at he
    calc
      _ ≤ ‖F d/(Real.sqrt (Real.log (1/d)) : ℂ)-τ‖+‖τ‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (F d/(Real.sqrt (Real.log (1/d)) : ℂ)-τ) τ
      _ ≤ C := by dsimp only [C]; linarith only [he]
  let G : ℝ → ℝ → ℝ := fun h s => ‖F (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ)-τ‖^2
  let B : ℝ → ℝ := fun s => 2*(C^2*(1+Real.log (1/s))+‖τ‖^2)
  have hBm : IntegrableOn B (Ioc (0 : ℝ) 1) := by
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hl : IntegrableOn (fun s : ℝ => Real.log (1/s)) (Ioc (0 : ℝ) 1) := by
      have hi : IntegrableOn Real.log (Ioc (0 : ℝ) 1) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
          (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      apply hi.neg.congr
      exact Eventually.of_forall fun s => by
        simp only [Pi.neg_apply, one_div, Real.log_inv]
    change Integrable B (volume.restrict (Ioc (0 : ℝ) 1))
    simpa only [B, Pi.add_apply, mul_one] using
      (((hc.add hl).const_mul (C^2)).add (hc.const_mul (‖τ‖^2))).const_mul 2
  have hGm : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (G h)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply Eventually.of_forall
    intro h
    exact (((hF.comp (measurable_const.mul measurable_id)).div_const _).sub_const τ).norm.pow_const
      2 |>.aestronglyMeasurable
  have hdom : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      ‖G h s‖ ≤ B s := by
    have hlog : Tendsto (fun h : ℝ => Real.log (1/h)) (𝓝[>] (0 : ℝ)) atTop := by
      simpa only [one_div, Real.log_inv, Function.comp_def] using
        tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds,
      hlog.eventually (eventually_ge_atTop (1 : ℝ))] with h hh hhδ hL
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hh0 : 0 < h := hh
    have hs0 : 0 < s := hs.1
    have hhs0 : 0 < h*s := mul_pos hh0 hs0
    have hhsδ : h*s < δ := (mul_le_of_le_one_right hh0.le hs.2).trans_lt hhδ
    have hq := hb hhs0 hhsδ
    have hl : 0 ≤ Real.log (1/s) := Real.log_nonneg (by
      rw [le_div_iff₀ hs0]
      simpa only [one_mul] using hs.2)
    have hLs : 0 < Real.log (1/(h*s)) := by
      rw [log_reciprocal_product hh0 hs0]
      linarith only [hL, hl]
    have hnorm : ‖F (h*s)‖ ≤ C*Real.sqrt (Real.log (1/(h*s))) := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hq
      exact (div_le_iff₀ (Real.sqrt_pos.mpr hLs)).mp hq
    have hsq : ‖F (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ)‖^2 ≤
        C^2*(1+Real.log (1/s)) := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
        Real.sq_sqrt (zero_le_one.trans hL)]
      apply (div_le_iff₀ (zero_lt_one.trans_le hL)).mpr
      have hn := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      rw [mul_pow, Real.sq_sqrt hLs.le, log_reciprocal_product hh0 hs0] at hn
      have hextra : 0 ≤ C^2*Real.log (1/s)*(Real.log (1/h)-1) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hl) (sub_nonneg.mpr hL)
      nlinarith only [hn, hextra]
    have htri := norm_sub_le (F (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ)) τ
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
    dsimp only [G, B]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith only [hsquare, hsq,
      sq_nonneg (‖F (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ)‖-‖τ‖)]
  have hpoint : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      Tendsto (fun h : ℝ => G h s) (𝓝[>] (0 : ℝ)) (nhds 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hp := (hτ.comp (tendsto_positive_scale_zero hs.1)).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_logarithmic_scale_ratio hs.1 hs.2))
    simp only [Complex.ofReal_one, mul_one] at hp
    have hp' : Tendsto (fun h : ℝ => F (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ))
        (𝓝[>] (0 : ℝ)) (nhds τ) := by
      apply hp.congr'
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with h hh hh1
      have hhs : h*s < 1 := (mul_le_of_le_one_right (show (0 : ℝ) ≤ h from le_of_lt hh) hs.2).trans_lt hh1
      have hl : 0 < Real.log (1/(h*s)) :=
        Real.log_pos (by rw [lt_div_iff₀ (mul_pos hh hs.1)]; linarith only [hhs])
      dsimp only [Function.comp_apply]
      rw [Complex.ofReal_div]
      have hn : (Real.sqrt (Real.log (1/(h*s))) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne'
      calc
        _ = F (h*s) * (((Real.sqrt (Real.log (1/(h*s))) : ℂ)⁻¹) *
            (Real.sqrt (Real.log (1/(h*s))) : ℂ)) *
            (Real.sqrt (Real.log (1/h)) : ℂ)⁻¹ := by
          simp only [div_eq_mul_inv]
          ring
        _ = _ := by
          rw [inv_mul_cancel₀ hn, mul_one]
          exact (div_eq_mul_inv _ _).symm
    have he := (hp'.sub_const τ).norm.pow 2
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using he
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence B hGm hdom hBm hpoint
  simpa only [integral_zero] using h

namespace WeilHilbertBeforeContact

/-- The actual right exterior response converges in mean square to its constant normalized trace. -/
theorem evalVectorRightExteriorResponse_scaled_mean_square (a : PrecontactAperture) (z : ℂ) :
    Tendsto (fun h : ℝ => ∫ s in Ioc (0 : ℝ) 1,
      ‖evalVectorRightExteriorResponse a z (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ) +
        (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
          (evalVectorRightEndpointForcing a z : RealLineL2) y)‖^2)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  simpa only [sub_neg_eq_add] using logarithmic_boundary_limit_in_mean_square
    (measurable_evalVectorRightExteriorResponse a z)
    (evalVectorRightExteriorResponse_normalized_limit a z)

/-- The same scaled L² limit holds for the actual left exterior response. -/
theorem evalVectorLeftExteriorResponse_scaled_mean_square (a : PrecontactAperture) (z : ℂ) :
    Tendsto (fun h : ℝ => ∫ s in Ioc (0 : ℝ) 1,
      ‖evalVectorLeftExteriorResponse a z (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ) +
        (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
          (evalVectorLeftEndpointForcing a z : RealLineL2) y)‖^2)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  simpa only [sub_neg_eq_add] using logarithmic_boundary_limit_in_mean_square
    (measurable_evalVectorLeftExteriorResponse a z)
    (evalVectorLeftExteriorResponse_normalized_limit a z)

#print axioms evalVectorRightExteriorResponse_scaled_mean_square
#print axioms evalVectorLeftExteriorResponse_scaled_mean_square
end WeilHilbertBeforeContact
#print axioms logarithmic_boundary_limit_in_mean_square
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
