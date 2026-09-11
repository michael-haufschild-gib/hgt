import GaloisForLFunctions.HTGeometry.KukolOrbitProductTopology
import GaloisForLFunctions.HTGeometry.KukolTubeSaturationCoordinates

/-!
# Product geometry and analytic coordinates of the saturated tube

The exact single-point saturation criterion for Kukol's complex unipotent
action (arXiv:2609.10214, Section 5) becomes a homeomorphism with two upper
half-planes times the transverse complex space. The associated forward and
inverse rational coordinate maps are proved complex analytic on the entire
nonzero-minus locus in the original ambient vector space.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
open Topology
variable {κ : Type*} [Fintype κ]

/-- The global invariant quotient coordinate is continuous in the raw coordinate topology. -/
@[fun_prop] theorem continuous_kukolRegularQuotientCoordinate :
    Continuous (kukolRegularQuotientCoordinate (κ := κ)) := by
  exact continuous_kukolRegularQuadratic.div
    (Units.continuous_val.comp continuous_kukolRegularMinus) (fun x => x.minus.ne_zero)

/-- The exact saturation criterion describes an open domain in the genuine complex coordinate topology. -/
theorem isOpen_kukolRegularTubeSaturation :
    IsOpen (kukolRegularTubeSaturation (κ := κ)) := by
  have he : kukolRegularTubeSaturation (κ := κ) =
      {x | 0 < (x.minus : ℂ).im} ∩ {x | 0 < (kukolRegularQuotientCoordinate x).im} := by
    ext x
    exact kukolRegularTubeSaturation_iff x
  rw [he]
  exact (isOpen_lt continuous_const
    (Complex.continuous_im.comp (Units.continuous_val.comp continuous_kukolRegularMinus))).inter
    (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_kukolRegularQuotientCoordinate))

/-- The upper-half-plane product parameterization is continuous in ordinary raw coordinates. -/
@[fun_prop] theorem continuous_kukolTubeParameters :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane × (κ → ℂ) =>
      kukolTubeParameters p.1 p.2.1 p.2.2) := by
  have hm : Continuous (fun m : UpperHalfPlane => Units.mk0 (m : ℂ) m.ne_zero) := by
    apply Units.isEmbedding_val₀.continuous_iff.mpr
    exact UpperHalfPlane.continuous_coe
  apply continuous_induced_rng.mpr
  change Continuous (fun p : UpperHalfPlane × UpperHalfPlane × (κ → ℂ) =>
    (Units.mk0 (p.1 : ℂ) p.1.ne_zero,(p.2.1 : ℂ)+(∑ k,p.2.2 k^2)/(p.1 : ℂ),p.2.2))
  refine (hm.comp continuous_fst).prodMk ((Continuous.add ?_ ?_).prodMk continuous_snd.snd)
  · fun_prop
  · exact (by fun_prop : Continuous (fun p : UpperHalfPlane × UpperHalfPlane × (κ → ℂ) =>
        ∑ k,p.2.2 k^2)).div (UpperHalfPlane.continuous_coe.comp continuous_fst)
      (fun p => p.1.ne_zero)

/-- The whole saturated tube is homeomorphic to two upper half-planes times the transverse complex space. -/
def kukolTubeProductHomeomorph :
    (UpperHalfPlane × UpperHalfPlane × (κ → ℂ)) ≃ₜ
      {x : KukolRegularPoint κ | x ∈ kukolRegularTubeSaturation} where
  toEquiv := kukolTubeParameterEquiv
  continuous_toFun := continuous_kukolTubeParameters.subtype_mk _
  continuous_invFun := by
    have hm : Continuous (fun x : {x : KukolRegularPoint κ | x ∈ kukolRegularTubeSaturation} =>
        (x.val.minus : ℂ)) :=
      Units.continuous_val.comp (continuous_kukolRegularMinus.comp continuous_subtype_val)
    have hq := continuous_kukolRegularQuotientCoordinate.comp
      (continuous_subtype_val (p := fun x : KukolRegularPoint κ => x ∈ kukolRegularTubeSaturation))
    exact (hm.upperHalfPlaneMk _).prodMk
      ((hq.upperHalfPlaneMk _).prodMk (continuous_kukolRegularTransverse.comp continuous_subtype_val))

/-- Ordinary ambient complex coordinates before restricting to the nonzero-minus locus. -/
abbrev KukolComplexAmbient (κ : Type*) := ℂ × ℂ × (κ → ℂ)

/-- The invariant coordinate change written in the original ambient complex vector space. -/
def kukolAmbientNormalize (x : KukolComplexAmbient κ) : KukolComplexAmbient κ :=
  (x.1,x.2.1-(∑ k,x.2.2 k^2)/x.1,x.2.2)

/-- The explicit inverse change, also written in ordinary ambient coordinates. -/
def kukolAmbientDenormalize (x : KukolComplexAmbient κ) : KukolComplexAmbient κ :=
  (x.1,x.2.1+(∑ k,x.2.2 k^2)/x.1,x.2.2)

/-- The two rational coordinate formulae are mutually inverse. -/
def kukolAmbientCoordinateEquiv : KukolComplexAmbient κ ≃ KukolComplexAmbient κ where
  toFun := kukolAmbientNormalize
  invFun := kukolAmbientDenormalize
  left_inv x := by
    rcases x with ⟨m,p,z⟩
    simp [kukolAmbientNormalize,kukolAmbientDenormalize]
  right_inv x := by
    rcases x with ⟨m,p,z⟩
    simp [kukolAmbientNormalize,kukolAmbientDenormalize]

/-- The forward coordinate formula is complex analytic throughout the genuine nonzero-minus locus. -/
theorem analyticOnNhd_kukolAmbientNormalize :
    AnalyticOnNhd ℂ (kukolAmbientNormalize (κ := κ)) {x | x.1≠0} := by
  intro x hx
  have hm : AnalyticAt ℂ (fun y : KukolComplexAmbient κ => y.1) x := analyticAt_fst
  have hp : AnalyticAt ℂ (fun y : KukolComplexAmbient κ => y.2.1) x := analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun y : KukolComplexAmbient κ => y.2.2) x := analyticAt_snd.comp analyticAt_snd
  have hs : AnalyticAt ℂ (fun y : KukolComplexAmbient κ => ∑ k,y.2.2 k^2) x := by
    apply Finset.analyticAt_fun_sum
    intro k _
    exact (((ContinuousLinearMap.proj k : (κ → ℂ) →L[ℂ] ℂ).analyticAt _).comp hz).pow 2
  exact hm.prod ((hp.sub (hs.div hm hx)).prod hz)

/-- The inverse coordinate formula is complex analytic on the same nonzero-minus locus. -/
theorem analyticOnNhd_kukolAmbientDenormalize :
    AnalyticOnNhd ℂ (kukolAmbientDenormalize (κ := κ)) {x | x.1≠0} := by
  intro x hx
  have hm : AnalyticAt ℂ (fun y : KukolComplexAmbient κ => y.1) x := analyticAt_fst
  have hp : AnalyticAt ℂ (fun y : KukolComplexAmbient κ => y.2.1) x := analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun y : KukolComplexAmbient κ => y.2.2) x := analyticAt_snd.comp analyticAt_snd
  have hs : AnalyticAt ℂ (fun y : KukolComplexAmbient κ => ∑ k,y.2.2 k^2) x := by
    apply Finset.analyticAt_fun_sum
    intro k _
    exact (((ContinuousLinearMap.proj k : (κ → ℂ) →L[ℂ] ℂ).analyticAt _).comp hz).pow 2
  exact hm.prod ((hp.add (hs.div hm hx)).prod hz)

/-- The ambient analytic coordinate is exactly the previously classified Lorentz quotient coordinate. -/
theorem kukolAmbientNormalize_regular (x : KukolRegularPoint κ) :
    kukolAmbientNormalize ((x.minus : ℂ),x.plus,x.transverse) =
      ((x.minus : ℂ),kukolRegularQuotientCoordinate x,x.transverse) := by
  rw [kukolRegularQuotientCoordinate_eq,← Finset.sum_div]
  rfl

end GaloisForLFunctions.HTGeometry
