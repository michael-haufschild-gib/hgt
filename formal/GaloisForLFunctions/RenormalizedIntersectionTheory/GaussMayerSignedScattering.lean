import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringVector
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerNegativeUnitResolventPole

/-! Signed constant-input inverse channels distinguish scattering poles
from operator singularities invisible to the input. The negative channel
has an entire successor-response representative; the positive channel
retains precisely the zeta multiplicities in the critical strip. -/

open Complex Set Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringVector
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerSignedScattering

/-- Actual negative-unit constant-input vector. -/
def negativeResponse (w : ℂ) : DiscSpace := Ring.inverse (1+source w) (constant 1)

/-- The actual transfer source with either unit spectral sign. -/
def signedResponse (ε w : ℂ) : DiscSpace := Ring.inverse (1-ε • source w) (constant 1)

/-- The successor response solves the negative equation at every source parameter in the half-plane. -/
theorem successor_equation {w : ℂ} (hw : 0 < w.re) :
    (1+source w) (MayerCancellation.response w)=constant 1 := by
  change MayerCancellation.response w+source w (MayerCancellation.response w)=constant 1
  rw [source]
  simp only [_root_.add_apply,_root_.smul_apply,MayerCancellation.projection_response,
    smul_zero,zero_add]
  rw [MayerCancellation.remainder_response hw]
  abel

/-- The negative-channel model is nonzero, despite its zero boundary evaluation. -/
theorem successor_ne_zero {w : ℂ} (hw : 0 < w.re) : MayerCancellation.response w ≠ 0 := by
  intro he
  have h := successor_equation hw
  rw [he,map_zero] at h
  have he0 := congrArg (fun f : DiscSpace => f.1 zeroPoint) h
  exact zero_ne_one he0

private theorem analyticOn_negativeCleared :
    AnalyticOnNhd ℂ (MayerPole.clearedDeterminant (-1)) {w : ℂ | 0 < w.re} :=
  (MayerPole.differentiableOn_clearedDeterminant (-1)).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

private theorem negativeCleared_three_ne_zero : MayerPole.clearedDeterminant (-1) 3 ≠ 0 := by
  rw [MayerPole.clearedDeterminant_eq (by norm_num) (by norm_num) (-1)]
  apply mul_ne_zero (by norm_num)
  rw [sourceDeterminant_eq (by norm_num)]
  exact MayerUnitOrbitDeterminant.determinant_ne_zero_on_closed_unit (by norm_num) (by simp)

private theorem negativeCleared_order_ne_top {w : ℂ} (hw : 0 < w.re) :
    analyticOrderAt (MayerPole.clearedDeterminant (-1)) w ≠ ⊤ := by
  apply analyticOn_negativeCleared.analyticOrderAt_ne_top_of_isPreconnected
    MayerCofactorContinuation.rightHalfPlane_preconnected (x := 3) (by norm_num) hw
  rw [(analyticOn_negativeCleared 3 (by norm_num)).analyticOrderAt_eq_zero.mpr
    negativeCleared_three_ne_zero]
  exact ENat.zero_ne_top

private theorem punctured_avoid_one (w : ℂ) : ∀ᶠ v in 𝓝[≠] w, v ≠ 1 := by
  by_cases h : w=1
  · subst w
    exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds h)

private theorem eventually_negative_unit {w : ℂ} (hw : 0 < w.re) :
    ∀ᶠ v in 𝓝[≠] w, IsUnit (1+source v) := by
  have hn : ∀ᶠ v in 𝓝[≠] w, MayerPole.clearedDeterminant (-1) v ≠ 0 := by
    rcases (analyticOn_negativeCleared w hw).eventually_eq_zero_or_eventually_ne_zero with he | he
    · exact False.elim (negativeCleared_order_ne_top hw (analyticOrderAt_eq_top.mpr he))
    · exact he
  have hh : ∀ᶠ v in 𝓝[≠] w, 0 < v.re :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)
  filter_upwards [hn,hh,punctured_avoid_one w] with v hv h0 h1
  have hD : sourceDeterminant v (-1) ≠ 0 := by
    intro he
    rw [MayerPole.clearedDeterminant_eq h0 h1 (-1),he,mul_zero] at hv
    exact hv rfl
  by_contra hu
  apply hD
  rw [sourceDeterminant_eq h0]
  apply (MayerFredholm.determinant_eq_zero_iff_not_isUnit h0 (-1)).mpr
  simpa only [neg_one_smul,sub_neg_eq_add,← source_eq h0] using hu

/-- The full negative constant-input inverse has an entire successor-response germ. -/
theorem negativeResponse_germ {w : ℂ} (hw : 0 < w.re) :
    negativeResponse =ᶠ[𝓝[≠] w] MayerCancellation.response := by
  have hh : ∀ᶠ v in 𝓝[≠] w, 0 < v.re :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)
  filter_upwards [eventually_negative_unit hw,hh] with v hu hv
  have h := congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T (MayerCancellation.response v))
    (Ring.inverse_mul_cancel (1+source v) hu)
  change Ring.inverse (1+source v) ((1+source v) (MayerCancellation.response v))=
    MayerCancellation.response v at h
  rw [successor_equation hv] at h
  exact h

/-- Meromorphy concerns the actual inverse, including its assigned values at nonunits. -/
theorem meromorphicAt_negativeResponse {w : ℂ} (hw : 0 < w.re) :
    MeromorphicAt negativeResponse w :=
  (MayerResolvent.differentiable_response.analyticAt w).meromorphicAt.congr
    (negativeResponse_germ hw).symm

/-- Every negative constant-input germ is regular and nonzero. -/
theorem negativeResponse_order {w : ℂ} (hw : 0 < w.re) :
    meromorphicOrderAt negativeResponse w=0 := by
  have ha := MayerResolvent.differentiable_response.analyticAt w
  rw [meromorphicOrderAt_congr (negativeResponse_germ hw),ha.meromorphicOrderAt_eq,
    ha.analyticOrderAt_eq_zero.mpr (successor_ne_zero hw)]
  rfl

/-- The actual negative inverse converges to its explicit removable representative. -/
theorem negativeResponse_limit {w : ℂ} (hw : 0 < w.re) :
    Tendsto negativeResponse (𝓝[≠] w) (𝓝 (MayerCancellation.response w)) :=
  ((MayerResolvent.differentiable_response.analyticAt w).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr' (negativeResponse_germ hw).symm

/-- The genuine rank-one pole of the full negative operator inverse does not excite the constant input. -/
theorem negativeOperatorResidue_constant_zero : MayerResolvent.inversePoleResidue (constant 1)=0 := by
  have h := ((ContinuousLinearMap.apply ℂ DiscSpace (constant 1)).continuous.tendsto
    MayerResolvent.inversePoleResidue).comp MayerResolvent.sourceInverse_residue
  change Tendsto (fun w : ℂ => (w-1) • negativeResponse w) (𝓝[≠] (1 : ℂ))
    (𝓝 (MayerResolvent.inversePoleResidue (constant 1))) at h
  have hz : Tendsto (fun w : ℂ => w-1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have hc : Continuous (fun w : ℂ => w-1) := continuous_id.sub continuous_const
    simpa only [sub_self] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun w : ℂ => (w-1) • negativeResponse w) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa only [zero_smul] using hz.smul (negativeResponse_limit (by norm_num))
  exact tendsto_nhds_unique h hzero

private theorem signedResponse_one : signedResponse 1=vectorResponse := by
  funext w
  simp only [signedResponse,one_smul,vectorResponse]

private theorem signedResponse_neg_one : signedResponse (-1)=negativeResponse := by
  funext w
  simp only [signedResponse,neg_one_smul,sub_neg_eq_add,negativeResponse]

/-- Exact multiplicity in both signed constant-input channels. -/
theorem signedResponse_order {ε w : ℂ} (hε : ε=1 ∨ ε= -1)
    (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt (signedResponse ε) w=
      if ε=1 then -((analyticOrderNatAt riemannZeta w : ℤ) : WithTop ℤ) else 0 := by
  rcases hε with rfl | rfl
  · rw [signedResponse_one,vectorResponse_strip_order h0 h1,if_pos rfl]
  · rw [signedResponse_neg_one,negativeResponse_order h0,if_neg (by norm_num)]

/-- Signed source-channel poles occur precisely in the positive channel at zeta zeros. -/
theorem signedResponse_pole_iff {ε w : ℂ} (hε : ε=1 ∨ ε= -1)
    (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt (signedResponse ε) w < 0 ↔ ε=1 ∧ riemannZeta w=0 := by
  rcases hε with rfl | rfl
  · rw [signedResponse_one,vectorResponse_pole_iff h0 h1]
    simp
  · rw [signedResponse_neg_one,negativeResponse_order h0]
    norm_num

#print axioms successor_equation
#print axioms successor_ne_zero
#print axioms negativeResponse_germ
#print axioms meromorphicAt_negativeResponse
#print axioms negativeResponse_order
#print axioms negativeResponse_limit
#print axioms negativeOperatorResidue_constant_zero
#print axioms signedResponse_order
#print axioms signedResponse_pole_iff
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerSignedScattering
