import GaloisForLFunctions.RHTower.L2MellinUnitary
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Frequency-gap Abel pairing for the moving-band argument

The actual L2 frequency-phase unitary has vanishing normalized Abel pairing
against a test separated from the chosen ordinate. The proof first establishes
integrability of the full two-variable phase integrand and its exact scalar
resolvent formula, then applies the literal L2 inner-product representation.
No arithmetic energy bound or analytic continuation is assumed or concluded.
-/

open MeasureTheory Set Complex Filter Topology
noncomputable section
namespace RHTower

private theorem pmba_integrable_product {f : ℝ → ℂ} (hf : Integrable f)
    {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) :
    Integrable (fun p : ℝ × ℝ => f p.2 *
      Complex.exp (-((δ : ℂ)+((γ-p.2 : ℝ) : ℂ)*I)*(p.1 : ℂ)))
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hdom := (integrableOn_exp_mul_Ioi (by linarith : -δ < 0) 0).mul_prod hf.norm
  apply hdom.mono'
  · exact hf.aestronglyMeasurable.comp_snd.mul
      (show Continuous (fun p : ℝ × ℝ =>
        Complex.exp (-((δ : ℂ)+((γ-p.2 : ℝ) : ℂ)*I)*(p.1 : ℂ))) by fun_prop).aestronglyMeasurable
  · exact .of_forall fun p => by
      simp [Complex.norm_exp, Complex.mul_re, mul_comm]

theorem pm_frequencyLaplace_eq_resolvent {f : ℝ → ℂ} (hf : Integrable f)
    {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) :
    (∫ u in Ioi (0 : ℝ), ∫ τ : ℝ, f τ *
      Complex.exp (-((δ : ℂ)+((γ-τ : ℝ) : ℂ)*I)*(u : ℂ))) =
      ∫ τ : ℝ, f τ / ((δ : ℂ)+((γ-τ : ℝ) : ℂ)*I) := by
  rw [integral_integral_swap (pmba_integrable_product hf hδ γ)]
  apply integral_congr_ae
  exact .of_forall fun τ => by
    dsimp only
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hδ)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_eq_mul_inv,
      inv_neg, neg_mul, one_mul, neg_neg]

private theorem pmba_gap_bound {f : ℝ → ℂ} {γ d : ℝ} (hd : 0 < d)
    (hgap : ∀ᵐ τ : ℝ, f τ ≠ 0 → d ≤ |γ-τ|) (δ : ℝ) :
    ∀ᵐ τ : ℝ, ‖f τ / ((δ : ℂ)+((γ-τ : ℝ) : ℂ)*I)‖ ≤ ‖f τ‖/d := by
  filter_upwards [hgap] with τ hτ
  by_cases hfτ : f τ = 0
  · simp [hfτ]
  have hn : d ≤ ‖(δ : ℂ)+((γ-τ : ℝ) : ℂ)*I‖ := by
    exact (hτ hfτ).trans (by simpa using
      (Complex.abs_im_le_norm ((δ : ℂ)+((γ-τ : ℝ) : ℂ)*I)))
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hd hn

theorem pm_frequencyGap_abel_zero {f : ℝ → ℂ} (hf : Integrable f)
    {γ d : ℝ} (hd : 0 < d)
    (hgap : ∀ᵐ τ : ℝ, f τ ≠ 0 → d ≤ |γ-τ|) :
    Tendsto (fun δ : ℝ => (δ : ℂ) *
      ∫ u in Ioi (0 : ℝ), ∫ τ : ℝ, f τ *
        Complex.exp (-((δ : ℂ)+((γ-τ : ℝ) : ℂ)*I)*(u : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun δ : ℝ => δ * ((∫ τ : ℝ, ‖f τ‖)/d))
      (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.mul_const ((∫ τ : ℝ, ‖f τ‖)/d)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ
  rw [pm_frequencyLaplace_eq_resolvent hf hδ0 γ, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
  apply mul_le_mul_of_nonneg_left _ hδ0.le
  have hh := norm_integral_le_of_norm_le (hf.norm.div_const d) (pmba_gap_bound hd hgap δ)
  simpa only [integral_div] using hh

private theorem pmba_phase_pair (h F : Lp ℂ 2 (volume : Measure ℝ)) (δ γ u : ℝ) :
    Complex.exp (-((δ : ℂ)+(γ : ℂ)*I)*(u : ℂ)) *
      inner ℂ h (MellinL2.fourierPhaseMulUnitary (u/(2*Real.pi)) F) =
      ∫ τ : ℝ, ((starRingEnd ℂ) (h τ) * F τ) *
        Complex.exp (-((δ : ℂ)+((γ-τ : ℝ) : ℂ)*I)*(u : ℂ)) := by
  rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [MellinL2.fourierPhaseMulAux_ae (u/(2*Real.pi)) F] with τ hτ
  change (MellinL2.fourierPhaseMulUnitary (u/(2*Real.pi)) F : ℝ → ℂ) τ = _ at hτ
  rw [hτ, RCLike.inner_apply]
  have hp : 2*Real.pi*((u/(2*Real.pi))*τ) = u*τ := by
    field_simp [Real.pi_ne_zero]
  have he : Complex.exp (-((δ : ℂ)+(γ : ℂ)*I)*(u : ℂ)) *
      MellinL2.fourierPhase (u/(2*Real.pi)) τ =
        Complex.exp (-((δ : ℂ)+((γ-τ : ℝ) : ℂ)*I)*(u : ℂ)) := by
    rw [MellinL2.fourierPhase, Real.fourierChar_apply, hp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = ((starRingEnd ℂ) (h τ) * F τ) *
        (Complex.exp (-((δ : ℂ)+(γ : ℂ)*I)*(u : ℂ)) *
          MellinL2.fourierPhase (u/(2*Real.pi)) τ) := by ring
    _ = _ := by rw [he]

theorem integrableOn_pm_frequencyPhasePair (h F : Lp ℂ 2 (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) :
    IntegrableOn (fun u : ℝ => Complex.exp (-((δ : ℂ)+(γ : ℂ)*I)*(u : ℂ)) *
      inner ℂ h (MellinL2.fourierPhaseMulUnitary (u/(2*Real.pi)) F)) (Ioi 0) := by
  have hf : Integrable (fun τ : ℝ => (starRingEnd ℂ) (h τ) * F τ) := by
    simpa only [RCLike.inner_apply, mul_comm] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) h F)
  have hi := (pmba_integrable_product hf hδ γ).integral_prod_left
  exact hi.congr (.of_forall fun u => (pmba_phase_pair h F _ _ u).symm)

/-- The actual phase unitary has zero normalized Abel pairing against any separated L2 test. -/
theorem pm_frequencyGap_phaseUnitary_abel_zero
    (h F : Lp ℂ 2 (volume : Measure ℝ)) {γ d : ℝ} (hd : 0 < d)
    (hgap : ∀ᵐ τ : ℝ, h τ ≠ 0 → d ≤ |γ-τ|) :
    Tendsto (fun δ : ℝ => (δ : ℂ) * ∫ u in Ioi (0 : ℝ),
      Complex.exp (-((δ : ℂ)+(γ : ℂ)*I)*(u : ℂ)) *
        inner ℂ h (MellinL2.fourierPhaseMulUnitary (u/(2*Real.pi)) F))
      (𝓝[>] 0) (𝓝 0) := by
  have hf : Integrable (fun τ : ℝ => (starRingEnd ℂ) (h τ) * F τ) := by
    simpa only [RCLike.inner_apply, mul_comm] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) h F)
  have hgf : ∀ᵐ τ : ℝ, (starRingEnd ℂ) (h τ) * F τ ≠ 0 → d ≤ |γ-τ| := by
    filter_upwards [hgap] with τ hτ
    intro hn
    apply hτ
    intro hz
    exact hn (by simp [hz])
  have ht := pm_frequencyGap_abel_zero hf hd hgf
  simpa only [pmba_phase_pair] using ht

end RHTower
