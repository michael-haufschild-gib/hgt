import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilRieszVectorsLocalizeToTheLogarithmicHalfLine

/-!
# Normalized endpoint traces of the actual Weil Riesz vectors

Overlapping Lipschitz localizations have continuous Green representatives.
Their weighted gluing gives one continuous representative of the complete
Weil Riesz vector and exact renewal readouts at both aperture endpoints.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

private theorem endpointCutoff_sum_pos (a : SuzukiPositiveAperture) (x : ℝ) :
    0 < logarithmicEndpointCutoff a.1 (x + a.1) + logarithmicEndpointCutoff a.1 (a.1 - x) := by
  by_cases hx : x ≤ 0
  · have hc := logarithmicEndpointCutoff_eq_one a.2 (show x + a.1 ≤ a.1 by linarith only [hx])
    rw [hc]
    exact add_pos_of_pos_of_nonneg zero_lt_one (logarithmicEndpointCutoff_nonneg _ _)
  · have hc := logarithmicEndpointCutoff_eq_one a.2 (show a.1 - x ≤ a.1 by linarith only [hx])
    rw [hc]
    exact add_pos_of_nonneg_of_pos (logarithmicEndpointCutoff_nonneg _ _) zero_lt_one

private def endpointGluing (a : SuzukiPositiveAperture) (L R : ℝ → ℂ) (x : ℝ) : ℂ :=
  (L (x + a.1) + R (a.1 - x)) /
    ((logarithmicEndpointCutoff a.1 (x + a.1) + logarithmicEndpointCutoff a.1 (a.1 - x) : ℝ) : ℂ)

private theorem continuous_endpointGluing (a : SuzukiPositiveAperture) {L R : ℝ → ℂ}
    (hL : Continuous L) (hR : Continuous R) : Continuous (endpointGluing a L R) := by
  apply Continuous.div ((hL.comp (by fun_prop)).add (hR.comp (by fun_prop)))
    (Complex.continuous_ofReal.comp (((continuous_logarithmicEndpointCutoff a.1).comp
      (by fun_prop)).add ((continuous_logarithmicEndpointCutoff a.1).comp (by fun_prop))))
  intro x
  change ((logarithmicEndpointCutoff a.1 (x+a.1) +
    logarithmicEndpointCutoff a.1 (a.1-x) : ℝ) : ℂ) ≠ 0
  exact_mod_cast (ne_of_gt (endpointCutoff_sum_pos a x))

private theorem endpointGluing_ae (a : SuzukiPositiveAperture) {L R u : ℝ → ℂ}
    (hL : (fun x => L (x + a.1)) =ᵐ[volume]
      fun x => (logarithmicEndpointCutoff a.1 (x + a.1) : ℂ) * u x)
    (hR : (fun x => R (a.1 - x)) =ᵐ[volume]
      fun x => (logarithmicEndpointCutoff a.1 (a.1 - x) : ℂ) * u x) :
    endpointGluing a L R =ᵐ[volume] u := by
  filter_upwards [hL, hR] with x hx hy
  unfold endpointGluing
  rw [hx, hy, Complex.ofReal_add, ← add_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast ne_of_gt (endpointCutoff_sum_pos a x))

private theorem endpointGluing_left (a : SuzukiPositiveAperture) {L R u : ℝ → ℂ}
    (hLc : Continuous L) (hRc : Continuous R)
    (hL : (fun x => L (x + a.1)) =ᵐ[volume]
      fun x => (logarithmicEndpointCutoff a.1 (x + a.1) : ℂ) * u x)
    (hR : (fun x => R (a.1 - x)) =ᵐ[volume]
      fun x => (logarithmicEndpointCutoff a.1 (a.1 - x) : ℂ) * u x) (x : ℝ) :
    L (x + a.1) = (logarithmicEndpointCutoff a.1 (x + a.1) : ℂ) * endpointGluing a L R x := by
  have he : (fun x => L (x + a.1)) =ᵐ[volume] fun x =>
      (logarithmicEndpointCutoff a.1 (x + a.1) : ℂ) * endpointGluing a L R x := by
    filter_upwards [hL, endpointGluing_ae a hL hR] with x hx hu
    rw [hx, hu]
  have hcont : Continuous (fun x => (logarithmicEndpointCutoff a.1 (x + a.1) : ℂ) *
      endpointGluing a L R x) :=
    (Complex.continuous_ofReal.comp ((continuous_logarithmicEndpointCutoff a.1).comp
      (by fun_prop))).mul (continuous_endpointGluing a hLc hRc)
  exact congrFun ((Continuous.ae_eq_iff_eq volume (hLc.comp (by fun_prop)) hcont).mp he) x

private theorem endpointGluing_right (a : SuzukiPositiveAperture) {L R u : ℝ → ℂ}
    (hLc : Continuous L) (hRc : Continuous R)
    (hL : (fun x => L (x + a.1)) =ᵐ[volume]
      fun x => (logarithmicEndpointCutoff a.1 (x + a.1) : ℂ) * u x)
    (hR : (fun x => R (a.1 - x)) =ᵐ[volume]
      fun x => (logarithmicEndpointCutoff a.1 (a.1 - x) : ℂ) * u x) (x : ℝ) :
    R (a.1 - x) = (logarithmicEndpointCutoff a.1 (a.1 - x) : ℂ) * endpointGluing a L R x := by
  have he : (fun x => R (a.1 - x)) =ᵐ[volume] fun x =>
      (logarithmicEndpointCutoff a.1 (a.1 - x) : ℂ) * endpointGluing a L R x := by
    filter_upwards [hR, endpointGluing_ae a hL hR] with x hx hu
    rw [hx, hu]
  have hcont : Continuous (fun x => (logarithmicEndpointCutoff a.1 (a.1 - x) : ℂ) *
      endpointGluing a L R x) :=
    (Complex.continuous_ofReal.comp ((continuous_logarithmicEndpointCutoff a.1).comp
      (by fun_prop))).mul (continuous_endpointGluing a hLc hRc)
  exact congrFun ((Continuous.ae_eq_iff_eq volume (hRc.comp (by fun_prop)) hcont).mp he) x

namespace WeilHilbertBeforeContact

/-- The complete localized forcing at the left endpoint of the actual evaluation Riesz source. -/
def evalVectorLeftEndpointForcing (a : PrecontactAperture) (z : ℂ) : LogarithmicHalfLineL2 :=
  logarithmicApertureLeftForcing a.1
    (ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z))) (logarithmicForcing a z)

/-- The complete localized forcing at the reflected right endpoint. -/
def evalVectorRightEndpointForcing (a : PrecontactAperture) (z : ℂ) : LogarithmicHalfLineL2 :=
  logarithmicApertureLeftForcing a.1
    (logarithmicApertureReflection a.1 (ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z))))
    (logarithmicApertureReflection a.1 (logarithmicForcing a z))

private theorem leftGreen_continuous (a : PrecontactAperture) (z : ℂ) :
    Continuous (logarithmicGreenRepresentative (evalVectorLeftEndpointForcing a z)) := by
  obtain ⟨C, hC, hb⟩ := evalVector_leftLocalized_forcing_bounded a z
  exact continuous_logarithmicGreenRepresentative _ hC hb

private theorem rightGreen_continuous (a : PrecontactAperture) (z : ℂ) :
    Continuous (logarithmicGreenRepresentative (evalVectorRightEndpointForcing a z)) := by
  obtain ⟨C, hC, hb⟩ := evalVector_rightLocalized_forcing_bounded a z
  exact continuous_logarithmicGreenRepresentative _ hC hb

private theorem leftGreen_ae (a : PrecontactAperture) (z : ℂ) :
    (fun x => logarithmicGreenRepresentative (evalVectorLeftEndpointForcing a z) (x + a.1.1)) =ᵐ[volume]
      fun x => (logarithmicEndpointCutoff a.1.1 (x + a.1.1) : ℂ) *
        ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)) x := by
  let u := ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z))
  have hphys : (u : RealLineL2) = ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)) :=
    ccmArchimedeanFormToAperture_coe a.1 _
  have hG := logarithmicHalfLineGreenOperator_eq_representative (evalVectorLeftEndpointForcing a z)
  change ((logarithmicHalfLineGreenOperator (logarithmicApertureLeftForcing a.1 u
    (logarithmicForcing a z)) : RealLineL2) : ℝ → ℂ) =ᵐ[volume] _ at hG
  rw [← evalVector_leftLocalized_eq_green a z] at hG
  have he := hG.symm.trans (logarithmicApertureLeftLocalized_coeFn a.1 u)
  have ht := he.comp_tendsto
    (MellinL2.realTranslation_measurePreserving a.1.1).quasiMeasurePreserving.tendsto_ae
  filter_upwards [ht] with x hx
  change logarithmicGreenRepresentative (evalVectorLeftEndpointForcing a z) (x+a.1.1) =
    (logarithmicEndpointCutoff a.1.1 (x+a.1.1) : ℂ) * (u : RealLineL2) (x+a.1.1-a.1.1) at hx
  rw [hphys] at hx
  simpa only [add_sub_cancel_right] using hx

private theorem rightGreen_ae (a : PrecontactAperture) (z : ℂ) :
    (fun x => logarithmicGreenRepresentative (evalVectorRightEndpointForcing a z) (a.1.1 - x)) =ᵐ[volume]
      fun x => (logarithmicEndpointCutoff a.1.1 (a.1.1 - x) : ℂ) *
        ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)) x := by
  let u := ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z))
  have hphys : (u : RealLineL2) = ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)) :=
    ccmArchimedeanFormToAperture_coe a.1 _
  let ru := logarithmicApertureReflection a.1 u
  let rg := logarithmicApertureReflection a.1 (logarithmicForcing a z)
  have hG := logarithmicHalfLineGreenOperator_eq_representative (evalVectorRightEndpointForcing a z)
  change ((logarithmicHalfLineGreenOperator (logarithmicApertureLeftForcing a.1 ru rg) :
    RealLineL2) : ℝ → ℂ) =ᵐ[volume] _ at hG
  rw [← evalVector_rightLocalized_eq_green a z] at hG
  have he := hG.symm.trans (logarithmicApertureLeftLocalized_coeFn a.1 ru)
  have hm : MeasurePreserving (fun x : ℝ => a.1.1 - x) volume volume :=
    (measurePreserving_add_left volume a.1.1).comp (Measure.measurePreserving_neg volume)
  have ht := he.comp_tendsto hm.quasiMeasurePreserving.tendsto_ae
  have hr := (l2Reflection_ae (u : RealLineL2)).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [ht, hr] with x hx hrx
  dsimp only [Function.comp_apply] at hx hrx
  rw [hx, show a.1.1 - x - a.1.1 = -x by ring]
  change _ * l2Reflection (u : RealLineL2) (-x) = _
  rw [hrx, neg_neg, hphys]

/-- The canonical continuous physical representative obtained from the two actual endpoint resolvents. -/
def evalVectorContinuousRepresentative (a : PrecontactAperture) (z : ℂ) : ℝ → ℂ :=
  endpointGluing a.1 (logarithmicGreenRepresentative (evalVectorLeftEndpointForcing a z))
    (logarithmicGreenRepresentative (evalVectorRightEndpointForcing a z))

theorem continuous_evalVectorContinuousRepresentative (a : PrecontactAperture) (z : ℂ) :
    Continuous (evalVectorContinuousRepresentative a z) :=
  continuous_endpointGluing a.1 (leftGreen_continuous a z) (rightGreen_continuous a z)

/-- The continuous representative is the actual complete Weil Riesz vector almost everywhere. -/
theorem evalVectorContinuousRepresentative_ae (a : PrecontactAperture) (z : ℂ) :
    evalVectorContinuousRepresentative a z =ᵐ[volume]
      (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)) : ℝ → ℂ) :=
  endpointGluing_ae a.1 (leftGreen_ae a z) (rightGreen_ae a z)

/-- The actual physical Riesz source has a unique continuous representative. -/
theorem evalVectorContinuousRepresentative_unique (a : PrecontactAperture) (z : ℂ)
    {f : ℝ → ℂ} (hf : Continuous f)
    (hae : f =ᵐ[volume] (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)) : ℝ → ℂ)) :
    f = evalVectorContinuousRepresentative a z := by
  apply (Continuous.ae_eq_iff_eq volume hf (continuous_evalVectorContinuousRepresentative a z)).mp
  exact hae.trans (evalVectorContinuousRepresentative_ae a z).symm

/-- Both exact endpoint coefficients are absolutely convergent renewal integrals. -/
theorem evalVectorEndpointReadouts_integrable (a : PrecontactAperture) (z : ℂ) :
    Integrable (fun y : ℝ => (logarithmicCausalKernel y : ℂ) *
      (evalVectorLeftEndpointForcing a z : RealLineL2) y) ∧
    Integrable (fun y : ℝ => (logarithmicCausalKernel y : ℂ) *
      (evalVectorRightEndpointForcing a z : RealLineL2) y) := by
  constructor
  · obtain ⟨C, hC, hb⟩ := evalVector_leftLocalized_forcing_bounded a z
    apply integrable_logarithmicGreen_boundary_readout _ (δ := 1) (by norm_num)
    filter_upwards [hb] with y hy
    exact fun _ => hy
  · obtain ⟨C, hC, hb⟩ := evalVector_rightLocalized_forcing_bounded a z
    apply integrable_logarithmicGreen_boundary_readout _ (δ := 1) (by norm_num)
    filter_upwards [hb] with y hy
    exact fun _ => hy

private theorem continuousRepresentative_left (a : PrecontactAperture) (z : ℂ)
    {t : ℝ} (ht : t ≤ a.1.1) :
    evalVectorContinuousRepresentative a z (t - a.1.1) =
      logarithmicGreenRepresentative (evalVectorLeftEndpointForcing a z) t := by
  have he := endpointGluing_left a.1 (leftGreen_continuous a z) (rightGreen_continuous a z)
    (leftGreen_ae a z) (rightGreen_ae a z) (t - a.1.1)
  rw [sub_add_cancel, logarithmicEndpointCutoff_eq_one a.1.2 ht,
    Complex.ofReal_one, one_mul] at he
  exact he.symm

private theorem continuousRepresentative_right (a : PrecontactAperture) (z : ℂ)
    {t : ℝ} (ht : t ≤ a.1.1) :
    evalVectorContinuousRepresentative a z (a.1.1 - t) =
      logarithmicGreenRepresentative (evalVectorRightEndpointForcing a z) t := by
  have he := endpointGluing_right a.1 (leftGreen_continuous a z) (rightGreen_continuous a z)
    (leftGreen_ae a z) (rightGreen_ae a z) (a.1.1 - t)
  rw [sub_sub_cancel, logarithmicEndpointCutoff_eq_one a.1.2 ht,
    Complex.ofReal_one, one_mul] at he
  exact he.symm

/-- The continuous actual source vanishes outside the open aperture, including both endpoints. -/
theorem evalVectorContinuousRepresentative_eq_zero (a : PrecontactAperture) (z : ℂ) {x : ℝ}
    (hx : x ≤ -a.1.1 ∨ a.1.1 ≤ x) : evalVectorContinuousRepresentative a z x = 0 := by
  rcases hx with hx | hx
  · have ht : x + a.1.1 ≤ 0 := by linarith only [hx]
    have he := continuousRepresentative_left a z (ht.trans a.1.2.le)
    rw [add_sub_cancel_right, logarithmicGreenRepresentative_of_nonpos _ ht] at he
    exact he
  · have ht : a.1.1 - x ≤ 0 := sub_nonpos.mpr hx
    have he := continuousRepresentative_right a z (ht.trans a.1.2.le)
    rw [sub_sub_cancel, logarithmicGreenRepresentative_of_nonpos _ ht] at he
    exact he

/-- The unique continuous actual source has compact support in the closed aperture. -/
theorem hasCompactSupport_evalVectorContinuousRepresentative (a : PrecontactAperture) (z : ℂ) :
    HasCompactSupport (evalVectorContinuousRepresentative a z) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -a.1.1) (b := a.1.1))
  intro x hx
  apply evalVectorContinuousRepresentative_eq_zero a z
  have hs : ¬(-a.1.1 ≤ x ∧ x ≤ a.1.1) := hx
  rcases not_and_or.mp hs with hl | hr
  · exact Or.inl (lt_of_not_ge hl).le
  · exact Or.inr (lt_of_not_ge hr).le

/-- Exact left trace of the actual Weil Riesz vector, with an absolutely convergent renewal readout. -/
theorem evalVectorContinuousRepresentative_left_normalized_limit (a : PrecontactAperture) (z : ℂ) :
    Tendsto (fun t : ℝ => evalVectorContinuousRepresentative a z (t - a.1.1) *
      (Real.sqrt (Real.log (1 / t)) : ℂ)) (𝓝[>] (0 : ℝ))
      (nhds (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
        (evalVectorLeftEndpointForcing a z : RealLineL2) y)) := by
  apply (evalVector_leftLocalized_normalized_limit a z).congr'
  filter_upwards [show ∀ᶠ t in 𝓝[>] (0 : ℝ), t < a.1.1 from
    (eventually_lt_nhds a.1.2).filter_mono nhdsWithin_le_nhds] with t ht
  rw [continuousRepresentative_left a z ht.le]
  rfl

/-- Exact right trace of the same continuous actual Weil representative. -/
theorem evalVectorContinuousRepresentative_right_normalized_limit (a : PrecontactAperture) (z : ℂ) :
    Tendsto (fun t : ℝ => evalVectorContinuousRepresentative a z (a.1.1 - t) *
      (Real.sqrt (Real.log (1 / t)) : ℂ)) (𝓝[>] (0 : ℝ))
      (nhds (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
        (evalVectorRightEndpointForcing a z : RealLineL2) y)) := by
  apply (evalVector_rightLocalized_normalized_limit a z).congr'
  filter_upwards [show ∀ᶠ t in 𝓝[>] (0 : ℝ), t < a.1.1 from
    (eventually_lt_nhds a.1.2).filter_mono nhdsWithin_le_nhds] with t ht
  rw [continuousRepresentative_right a z ht.le]
  rfl

end WeilHilbertBeforeContact
#print axioms WeilHilbertBeforeContact.evalVectorContinuousRepresentative_left_normalized_limit
#print axioms WeilHilbertBeforeContact.evalVectorContinuousRepresentative_right_normalized_limit
#print axioms WeilHilbertBeforeContact.evalVectorContinuousRepresentative_ae
#print axioms WeilHilbertBeforeContact.evalVectorContinuousRepresentative_unique
#print axioms WeilHilbertBeforeContact.evalVectorEndpointReadouts_integrable
#print axioms WeilHilbertBeforeContact.evalVectorContinuousRepresentative_eq_zero
#print axioms WeilHilbertBeforeContact.hasCompactSupport_evalVectorContinuousRepresentative
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
