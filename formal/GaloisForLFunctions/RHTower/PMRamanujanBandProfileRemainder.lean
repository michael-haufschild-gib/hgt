import GaloisForLFunctions.RHTower.PMRamanujanBandTestedScale
import GaloisForLFunctions.RHTower.PMRamanujanBandAbel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Zero Abel mass of the actual norm-null band-profile remainder

Positive rescaling and dominated convergence prove the bounded-null Abel law.
The actual phase remainder is measurable, norm-null, and bounded under the
proposed normalized-profile convergence. The exact exponential substitution
and the audited fixed-profile gap law then give zero Abel mass for the literal
tested scale integral. No convergence or small-damping energy bound is asserted.
-/

open MeasureTheory Set Complex Filter Topology
noncomputable section
namespace RHTower

theorem pm_bounded_null_abel_zero {f : ℝ → ℂ} (hm : Measurable f)
    {B : ℝ} (hb : ∀ u ∈ Ioi (0 : ℝ), ‖f u‖ ≤ B)
    (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun δ : ℝ => (δ : ℂ) *
      ∫ u in Ioi (0 : ℝ), ((Real.exp (-δ*u) : ℝ) : ℂ)*f u)
      (𝓝[>] 0) (𝓝 0) := by
  let G : ℝ → ℝ → ℂ := fun δ v => ((Real.exp (-v) : ℝ) : ℂ)*f (v/δ)
  have hGm : ∀ δ : ℝ, AEStronglyMeasurable (G δ) (volume.restrict (Ioi 0)) := by
    intro δ
    exact ((show Measurable (fun v : ℝ => ((Real.exp (-v) : ℝ) : ℂ)) by fun_prop).mul
      (hm.comp (measurable_id.div_const δ))).aestronglyMeasurable
  have hGb : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ v ∂volume.restrict (Ioi (0 : ℝ)),
      ‖G δ v‖ ≤ Real.exp (-v)*B := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hδ0 : (0 : ℝ) < δ := hδ
    have hv0 : (0 : ℝ) < v := hv
    have hvd : (0 : ℝ) < v/δ := div_pos hv0 hδ0
    simp only [G,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hb (v/δ) hvd) (Real.exp_pos _).le
  have hBi : IntegrableOn (fun v : ℝ => Real.exp (-v)*B) (Ioi 0) := by
    simpa only [IntegrableOn,neg_one_mul] using
      (integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).mul_const B
  have hGl : ∀ᵐ v ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun δ : ℝ => G δ v) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have ht : Tendsto (fun δ : ℝ => v/δ) (𝓝[>] 0) atTop := by
      simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hv
    simpa only [G,Function.comp_def,mul_zero] using (hf.comp ht).const_mul ((Real.exp (-v) : ℝ) : ℂ)
  have hlim : Tendsto (fun δ : ℝ => ∫ v in Ioi (0 : ℝ), G δ v) (𝓝[>] 0) (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
      (fun v : ℝ => Real.exp (-v)*B) (.of_forall hGm) hGb hBi hGl
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ
  have hs := integral_comp_mul_left_Ioi
    (fun u : ℝ => ((Real.exp (-δ*u) : ℝ) : ℂ)*f u) 0 (inv_pos.mpr hδ0)
  simp only [mul_zero, inv_inv, Complex.real_smul] at hs
  rw [← hs]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only [G]
  have he : -δ*(δ⁻¹*v) = -v := by field_simp [hδ0.ne']
  rw [he]
  congr 2
  rw [div_eq_mul_inv,mul_comm]

def pmRamanujanBandPhaseRemainder (ε γ : ℝ)
    (h F : Lp ℂ 2 (volume : Measure ℝ)) (u : ℝ) : ℂ :=
  Complex.exp (-((γ : ℂ)*I)*(u : ℂ)) *
    (pmRamanujanBandTestedScale ε h (Real.exp u) -
      inner ℂ h (MellinL2.fourierPhaseMulUnitary (u/(2*Real.pi)) F))

private theorem pmbpr_phase_norm (γ u : ℝ) :
    ‖Complex.exp (-((γ : ℂ)*I)*(u : ℂ))‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re]

private theorem pmbpr_pair_eq (ε : ℝ) (h F : Lp ℂ 2 (volume : Measure ℝ)) (u : ℝ) :
    pmRamanujanBandTestedScale ε h (Real.exp u) -
      inner ℂ h (MellinL2.fourierPhaseMulUnitary (u/(2*Real.pi)) F) =
      inner ℂ h (MellinL2.fourierPhaseMulUnitary (u/(2*Real.pi))
        (pmRamanujanNormalizedBandMellinVector ε (Real.exp u)-F)) := by
  simp only [pmRamanujanBandTestedScale,pmRamanujanMovingBandMellinVector,
    Real.log_exp,map_sub,inner_sub_right]

theorem measurable_pmRamanujanBandPhaseRemainder (ε γ : ℝ)
    (h F : Lp ℂ 2 (volume : Measure ℝ)) :
    Measurable (pmRamanujanBandPhaseRemainder ε γ h F) := by
  have hp : Continuous (fun u : ℝ => inner ℂ h
      (MellinL2.fourierPhaseMulUnitary (u/(2*Real.pi)) F)) :=
    (continuous_pm_inner_phaseUnitary h F).comp (continuous_id.div_const _)
  have he : Continuous (fun u : ℝ => Complex.exp (-((γ : ℂ)*I)*(u : ℂ))) := by fun_prop
  exact he.measurable.mul
    (((measurable_pmRamanujanBandTestedScale ε h).comp Real.continuous_exp.measurable).sub hp.measurable)

theorem tendsto_pmRamanujanBandPhaseRemainder {ε : ℝ}
    {F : Lp ℂ 2 (volume : Measure ℝ)}
    (hc : Tendsto (pmRamanujanNormalizedBandMellinVector ε) atTop (𝓝 F))
    (h : Lp ℂ 2 (volume : Measure ℝ)) (γ : ℝ) :
    Tendsto (pmRamanujanBandPhaseRemainder ε γ h F) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun u : ℝ => ‖h‖*
      ‖pmRamanujanNormalizedBandMellinVector ε (Real.exp u)-F‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self,norm_zero,mul_zero] using
      (((hc.comp Real.tendsto_exp_atTop).sub_const F).norm.const_mul ‖h‖)
  apply squeeze_zero_norm' _ hnorm
  exact .of_forall fun u => by
    rw [pmRamanujanBandPhaseRemainder,norm_mul,pmbpr_phase_norm,one_mul,pmbpr_pair_eq]
    exact (norm_inner_le_norm _ _).trans_eq
      (congrArg (fun t : ℝ => ‖h‖*t) ((MellinL2.fourierPhaseMulUnitary _).norm_map _))

private theorem pmbpr_bound_of_tendsto {ε : ℝ} (hε : 0 ≤ ε)
    {F : Lp ℂ 2 (volume : Measure ℝ)}
    (hc : Tendsto (pmRamanujanNormalizedBandMellinVector ε) atTop (𝓝 F))
    (h : Lp ℂ 2 (volume : Measure ℝ)) (γ : ℝ) :
    ∃ B : ℝ, ∀ u ∈ Ioi (0 : ℝ), ‖pmRamanujanBandPhaseRemainder ε γ h F u‖ ≤ B := by
  obtain ⟨C,_hC,hC⟩ := exists_bound_pmRamanujanMovingBandMellinVector_of_tendsto hε hc
  refine ⟨‖h‖*(C+‖F‖), ?_⟩
  intro u hu
  rw [pmRamanujanBandPhaseRemainder,norm_mul,pmbpr_phase_norm,one_mul]
  calc
    _ ≤ ‖pmRamanujanBandTestedScale ε h (Real.exp u)‖ +
        ‖inner ℂ h (MellinL2.fourierPhaseMulUnitary (u/(2*Real.pi)) F)‖ := norm_sub_le _ _
    _ ≤ ‖h‖*C+‖h‖*‖F‖ := by
      apply add_le_add
      · exact (norm_inner_le_norm h _).trans (mul_le_mul_of_nonneg_left
          (hC (Real.exp u) (Real.one_le_exp hu.le)) (norm_nonneg _))
      · simpa only [(MellinL2.fourierPhaseMulUnitary _).norm_map] using
          norm_inner_le_norm h (MellinL2.fourierPhaseMulUnitary (u/(2*Real.pi)) F)
    _ = _ := by ring

theorem pmRamanujanBandPhaseRemainder_abel_zero {ε : ℝ} (hε : 0 ≤ ε)
    {F : Lp ℂ 2 (volume : Measure ℝ)}
    (hc : Tendsto (pmRamanujanNormalizedBandMellinVector ε) atTop (𝓝 F))
    (h : Lp ℂ 2 (volume : Measure ℝ)) (γ : ℝ) :
    Tendsto (fun δ : ℝ => (δ : ℂ) *
      ∫ u in Ioi (0 : ℝ), ((Real.exp (-δ*u) : ℝ) : ℂ)*
        pmRamanujanBandPhaseRemainder ε γ h F u) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨B,hb⟩ := pmbpr_bound_of_tendsto hε hc h γ
  exact pm_bounded_null_abel_zero (measurable_pmRamanujanBandPhaseRemainder ε γ h F)
    hb (tendsto_pmRamanujanBandPhaseRemainder hc h γ)

theorem pmRamanujanBandTestedScale_eq_laplace (ε : ℝ)
    (h : Lp ℂ 2 (volume : Measure ℝ)) {ρ : ℂ} (hρ : ρ.re = 1/2) (δ : ℝ) :
    (∫ X in Ici (1 : ℝ), (X : ℂ)^(-(ρ+(δ : ℂ))-(1/2 : ℂ)) *
      pmRamanujanBandTestedScale ε h X) =
      ∫ u in Ioi (0 : ℝ), Complex.exp (-((δ : ℂ)+(ρ.im : ℂ)*I)*(u : ℂ)) *
        pmRamanujanBandTestedScale ε h (Real.exp u) := by
  have himage : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
    simpa only [Real.exp_zero] using Real.image_exp_Ioi 0
  rw [integral_Ici_eq_integral_Ioi, ← himage,
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  apply integral_congr_ae
  exact .of_forall fun u => by
    simp only [abs_of_pos (Real.exp_pos u),Complex.real_smul]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le,Real.log_exp,Complex.ofReal_exp,
      ← mul_assoc,← Complex.exp_add]
    congr 2
    have he : ρ = (1/2 : ℂ)+(ρ.im : ℂ)*I := by
      apply Complex.ext <;> simp [hρ]
    rw [he]
    simp; ring

private theorem pmbpr_integrable_laplace {f : ℝ → ℂ} (hm : Measurable f)
    {B : ℝ} (hb : ∀ u ∈ Ioi (0 : ℝ), ‖f u‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun u : ℝ => ((Real.exp (-δ*u) : ℝ) : ℂ)*f u) (Ioi 0) := by
  have hd := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hδ) 0).mul_const B
  apply hd.mono'
  · exact ((show Measurable (fun u : ℝ => ((Real.exp (-δ*u) : ℝ) : ℂ)) by fun_prop).mul hm).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hb u hu) (Real.exp_pos _).le

theorem pmRamanujanBandTestedScale_abel_zero {ε : ℝ} (hε : 0 ≤ ε)
    {F : Lp ℂ 2 (volume : Measure ℝ)}
    (hc : Tendsto (pmRamanujanNormalizedBandMellinVector ε) atTop (𝓝 F))
    (h : Lp ℂ 2 (volume : Measure ℝ)) {ρ : ℂ} (hρ : ρ.re = 1/2)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ᵐ τ : ℝ, h τ ≠ 0 → d ≤ |ρ.im-τ|) :
    Tendsto (fun δ : ℝ => (δ : ℂ) *
      ∫ X in Ici (1 : ℝ), (X : ℂ)^(-(ρ+(δ : ℂ))-(1/2 : ℂ)) *
        pmRamanujanBandTestedScale ε h X) (𝓝[>] 0) (𝓝 0) := by
  have hl := (pm_frequencyGap_phaseUnitary_abel_zero h F hd hgap).add
    (pmRamanujanBandPhaseRemainder_abel_zero hε hc h ρ.im)
  rw [add_zero] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  obtain ⟨B,hb⟩ := pmbpr_bound_of_tendsto hε hc h ρ.im
  have hi := pmbpr_integrable_laplace
    (measurable_pmRamanujanBandPhaseRemainder ε ρ.im h F) hb hδ
  have hf := integrableOn_pm_frequencyPhasePair h F hδ ρ.im
  rw [← mul_add, ← integral_add hf hi,pmRamanujanBandTestedScale_eq_laplace ε h hρ δ]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  have he : ((Real.exp (-δ*u) : ℝ) : ℂ)*Complex.exp (-((ρ.im : ℂ)*I)*(u : ℂ)) =
      Complex.exp (-((δ : ℂ)+(ρ.im : ℂ)*I)*(u : ℂ)) := by
    rw [Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  dsimp only [Pi.add_apply,pmRamanujanBandPhaseRemainder]
  rw [← mul_assoc,he]
  ring

end RHTower
