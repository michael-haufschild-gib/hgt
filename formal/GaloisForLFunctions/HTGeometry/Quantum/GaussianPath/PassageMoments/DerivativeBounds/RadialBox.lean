import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.DerivativeBounds.RadialSections
import GaloisForLFunctions.HTGeometry.DiagonalPatchConstruction
import GaloisForLFunctions.HTGeometry.GaussianRadialLaw

/-! # Removing a coupling box from homogeneous first-passage tails -/
open MeasureTheory ProbabilityTheory Set Metric Real
namespace GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
noncomputable section

abbrev PolarSample (m : ℕ) := sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0:ℝ)

/-- Cartesian couplings reconstructed from direction and radius. -/
def polarCoordinates (m : ℕ) (p : PolarSample m) : Fin m → ℝ := p.2.val • p.1.val.ofLp

theorem measurable_polarCoordinates (m : ℕ) : Measurable (polarCoordinates m) :=
  (measurable_subtype_coe.comp measurable_snd).smul
    ((MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm.measurable.comp (measurable_subtype_coe.comp measurable_fst))

theorem gaussian_polar_event (m : ℕ) (hm : 0 < m) (E : Set (Fin m → ℝ)) (hE : MeasurableSet E) :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1).real E =
      ((gaussianAngularMeasure m).prod (gaussianRadiusMeasure m)).real (polarCoordinates m ⁻¹' E) := by
  classical
  let f := E.indicator (1 : (Fin m → ℝ) → ℝ)
  let μ := Measure.pi fun _ : Fin m => gaussianReal 0 1
  have h := integral_stdGaussian_independent_polar hm (fun x => f x.ofLp)
  have he : (∫ x, f x ∂μ) = ∫ z : EuclideanSpace ℝ (Fin m), f z.ofLp ∂stdGaussian _ := by
    rw [←map_pi_eq_stdGaussian,←MeasurableEquiv.coe_toLp,integral_map_equiv]
    rfl
  rw [←integral_indicator_one hE,←integral_indicator_one (hE.preimage (measurable_polarCoordinates m))]
  apply (he.trans h).trans
  apply integral_congr_ae
  filter_upwards with p
  change E.indicator (1 : (Fin m → ℝ) → ℝ) (polarCoordinates m p) =
    (polarCoordinates m ⁻¹' E).indicator (1 : PolarSample m → ℝ) p
  by_cases hx : polarCoordinates m p ∈ E
  · rw [indicator_of_mem hx,indicator_of_mem (show p ∈ polarCoordinates m ⁻¹' E from hx)]
    rfl
  · rw [indicator_of_notMem hx,indicator_of_notMem (show p ∉ polarCoordinates m ⁻¹' E from hx)]

/-- On each direction, survival is an initial radial interval. A box
containing the ball of radius twice the root mean square retains at
least three quarters of the survival probability. -/
theorem gaussian_box_retains_tail (m : ℕ) (hm : 0 < m) (J : (Fin m → ℝ) → ℝ) (hJ : Measurable J)
    (hh : ∀ a > (0:ℝ), ∀ x, a*J (a • x)=J x) {G T : ℝ} (hG : 0≤G) (hT : 2*sqrt (m:ℝ)≤T) :
    let μ := Measure.pi fun _ : Fin m => gaussianReal 0 1
    (3/4:ℝ)*μ.real {x | G<J x} ≤ μ.real {x | (∀ i, |x i|≤T) ∧ G<J x} := by
  intro μ
  let α := gaussianAngularMeasure m
  let ν := gaussianRadiusMeasure m
  letI : IsProbabilityMeasure α := ⟨gaussianAngularMeasure_univ hm⟩
  letI : IsProbabilityMeasure ν := ⟨gaussianRadiusMeasure_univ hm⟩
  let E := {x | G<J x}
  let K := {x : Fin m → ℝ | (∀ i, |x i|≤T) ∧ x∈E}
  let F := polarCoordinates m ⁻¹' E
  let B := {r : Ioi (0:ℝ) | r.val≤2*sqrt (m:ℝ)}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hJ
  have hbox : MeasurableSet {x : Fin m → ℝ | ∀ i, |x i|≤T} := by
    rw [show {x : Fin m → ℝ | ∀ i, |x i|≤T}=⋂ i, {x | |x i|≤T} by ext x; simp only [mem_setOf_eq,mem_iInter]]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i).abs measurable_const
  have hK : MeasurableSet K := hbox.inter hE
  have hF : MeasurableSet F := hE.preimage (measurable_polarCoordinates m)
  have hB : MeasurableSet B := measurableSet_le measurable_subtype_coe measurable_const
  have hdown (y : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : IsLowerSet (Prod.mk y ⁻¹' F) := by
    intro s r hrs hs
    change G<J (s.val • y.val.ofLp) at hs
    change G<J (r.val • y.val.ofLp)
    have h := mul_lt_mul_of_pos_left hs s.property
    rw [hh _ s.property] at h
    apply (mul_lt_mul_iff_right₀ r.property).mp
    rw [hh _ r.property]
    exact (mul_le_mul_of_nonneg_right (show r.val ≤ s.val from hrs) hG).trans_lt h
  have hl : IsLowerSet B := by
    intro s r hrs hs
    exact (show r.val ≤ s.val from hrs).trans hs
  have hle := radial_section_product α ν F hF hdown B hB hl
  have hsub : F ∩ Prod.snd ⁻¹' B ⊆ polarCoordinates m ⁻¹' K := by
    rintro ⟨y,r⟩ ⟨hw,hr⟩
    refine ⟨fun i => ?_,hw⟩
    change |r.val*y.val.ofLp i|≤T
    have hy : |y.val.ofLp i| ≤ 1 := (abs_coord_le_norm y.val i).trans_eq (norm_eq_of_mem_sphere y)
    rw [abs_mul,abs_of_pos r.property]
    exact (mul_le_of_le_one_right r.property.le hy).trans (le_trans hr hT)
  have hh' := ENNReal.toReal_mono (measure_ne_top _ _) (hle.trans (measure_mono hsub))
  rw [ENNReal.toReal_mul] at hh'
  have hraw : μ.real E=(α.prod ν).real F := gaussian_polar_event m hm E hE
  have hcut : μ.real K=(α.prod ν).real (polarCoordinates m ⁻¹' K) := gaussian_polar_event m hm K hK
  change (3/4:ℝ)*μ.real E ≤ μ.real K
  rw [hraw,hcut,mul_comm (3/4:ℝ)]
  exact (mul_le_mul_of_nonneg_left (gaussian_radius_mass m hm) measureReal_nonneg).trans hh'

#print axioms gaussian_box_retains_tail
end
end GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
