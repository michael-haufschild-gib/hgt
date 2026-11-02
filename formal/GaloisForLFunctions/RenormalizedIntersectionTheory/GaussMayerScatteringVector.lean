import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringState
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerBoundaryResolvent

/-! The full constant-input inverse has one nowhere-vanishing holomorphic
numerator. Its vector-valued divisor is exactly the inverse of the zeta
factor and the constant-state pole; common Fredholm zeros add no hidden
poles to this source channel. -/

open Complex Set Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringMellin MayerScatteringState
open MayerScatteringMultiplicity
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringVector

/-- The actual full constant-input response, with ring inversion zero at nonunits. -/
def vectorResponse (w : ℂ) : DiscSpace := Ring.inverse (1-source w) (constant 1)

/-- The two scalar factors in the complete source-channel divisor. -/
def scatteringDenominator (w : ℂ) : ℂ := riemannZeta w*(w-2)

private theorem punctured_avoid (w c : ℂ) : ∀ᶠ v in 𝓝[≠] w, v ≠ c := by
  by_cases h : w=c
  · subst w
    exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds h)

/-- The filled state at the constant-state pole has its nonzero elementary value. -/
theorem clearedState_two : clearedState 2=(2 : ℂ) • MayerCoprimeSource.endpoint 1 := by
  have hG : Complex.Gamma 2=1 := by simp
  rw [clearedState,hG,inv_one,sub_self,zero_smul,add_zero,one_smul]

/-- The filled state's boundary value at the source pole is one. -/
theorem clearedState_one_zero : (clearedState 1).1 zeroPoint=1 := by
  rw [clearedState_eq (by norm_num : (1 : ℂ) ≠ 2)]
  change (1-2 : ℂ)*(state 1).1 zeroPoint=1
  rw [state_zero (by norm_num) (by norm_num)]
  norm_num [riemannZeta_zero]

/-- The filled numerator never vanishes anywhere in the source half-plane. -/
theorem clearedState_ne_zero {w : ℂ} (hw : 0 < w.re) : clearedState w ≠ 0 := by
  by_cases hw1 : w=1
  · subst w
    intro he
    have h := clearedState_one_zero
    rw [he] at h
    exact zero_ne_one h
  by_cases hw2 : w=2
  · subst w
    intro he
    have h := congrArg (fun f : DiscSpace => f.1 zeroPoint) he
    rw [clearedState_two] at h
    change (2 : ℂ)*(MayerCoprimeSource.endpoint 1).1 zeroPoint=0 at h
    rw [MayerCoprimeSource.endpoint_apply] at h
    norm_num [zeroPoint] at h
  intro he
  rw [clearedState_eq hw2] at he
  have hH : state w=0 := (smul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hw2)
  by_cases hz : riemannZeta w=0
  · have h1 : w.re < 1 := lt_of_not_ge fun hle => riemannZeta_ne_zero_of_one_le_re hle hz
    have h := (observable_remainder_eigenfunction hw h1 hz).2
    rw [hH] at h
    exact h rfl
  · have h := state_equation hw hw1 hw2
    rw [hH,map_zero,sub_self] at h
    have he0 := congrArg (fun f : DiscSpace => f.1 zeroPoint) h
    change (0 : ℂ)=riemannZeta w*1 at he0
    exact hz (by simpa only [mul_one] using he0.symm)

private theorem analyticOn_clearedDeterminant :
    AnalyticOnNhd ℂ (MayerPole.clearedDeterminant 1) {w : ℂ | 0 < w.re} :=
  (MayerPole.differentiableOn_clearedDeterminant 1).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

private theorem clearedDeterminant_order_ne_top {w : ℂ} (hw : 0 < w.re) :
    analyticOrderAt (MayerPole.clearedDeterminant 1) w ≠ ⊤ := by
  have hn : MayerPole.clearedDeterminant 1 1 ≠ 0 := by
    rw [MayerPole.clearedDeterminant_one]
    exact MayerPositivePole.polePart_one_one_ne_zero
  apply analyticOn_clearedDeterminant.analyticOrderAt_ne_top_of_isPreconnected
    MayerCofactorContinuation.rightHalfPlane_preconnected (x := 1) (by norm_num) hw
  rw [(analyticOn_clearedDeterminant 1 (by norm_num)).analyticOrderAt_eq_zero.mpr hn]
  exact ENat.zero_ne_top

private theorem eventually_clearedDeterminant_ne_zero {w : ℂ} (hw : 0 < w.re) :
    ∀ᶠ v in 𝓝[≠] w, MayerPole.clearedDeterminant 1 v ≠ 0 := by
  rcases (analyticOn_clearedDeterminant w hw).eventually_eq_zero_or_eventually_ne_zero with he | he
  · exact False.elim (clearedDeterminant_order_ne_top hw (analyticOrderAt_eq_top.mpr he))
  · exact he

/-- The entire vector inverse channel has the filled scattering state as its exact numerator. -/
theorem vectorResponse_germ {w : ℂ} (hw : 0 < w.re) :
    vectorResponse =ᶠ[𝓝[≠] w] fun v => (scatteringDenominator v)⁻¹ • clearedState v := by
  have hh : ∀ᶠ v in 𝓝[≠] w, 0 < v.re :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)
  filter_upwards [hh,punctured_avoid w 1,punctured_avoid w 2,
    eventually_clearedDeterminant_ne_zero hw] with v hv hv1 hv2 hC
  have hD : sourceDeterminant v 1 ≠ 0 := by
    intro he
    rw [MayerPole.clearedDeterminant_eq hv hv1 1,he,mul_zero] at hC
    exact hC rfl
  have hu : IsUnit (1-source v) := by
    by_contra hn
    apply hD
    rw [sourceDeterminant_eq hv]
    apply (MayerFredholm.determinant_eq_zero_iff_not_isUnit hv 1).mpr
    simpa only [one_smul,← source_eq hv] using hn
  have hp : riemannZeta v • vectorResponse v=state v := by
    have h := congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T (state v))
      (Ring.inverse_mul_cancel (1-source v) hu)
    change Ring.inverse (1-source v) ((1-source v) (state v))=state v at h
    have he : (1-source v) (state v)=riemannZeta v • constant 1 := state_equation hv hv1 hv2
    rw [he,map_smul] at h
    exact h
  have hz : riemannZeta v ≠ 0 := by
    intro he
    have hH : state v=0 := by simpa only [he,zero_smul] using hp.symm
    exact clearedState_ne_zero hv (by rw [clearedState_eq hv2,hH,smul_zero])
  rw [clearedState_eq hv2,scatteringDenominator,smul_smul,← hp,smul_smul]
  have he : (((riemannZeta v*(v-2))⁻¹)*(v-2))*riemannZeta v=1 := by
    field_simp [hz,sub_ne_zero.mpr hv2]
  rw [he,one_smul]

private theorem meromorphicAt_scatteringDenominator (w : ℂ) :
    MeromorphicAt scatteringDenominator w :=
  (GaloisForLFunctions.HTGeometry.meromorphicOn_riemannZeta w (mem_univ w)).mul
    (analyticAt_id.sub analyticAt_const).meromorphicAt

/-- Meromorphy holds in the full disc Banach space, including both scalar source points. -/
theorem meromorphicAt_vectorResponse {w : ℂ} (hw : 0 < w.re) :
    MeromorphicAt vectorResponse w :=
  ((meromorphicAt_scatteringDenominator w).inv.smul (analyticAt_clearedState hw).meromorphicAt).congr
    (vectorResponse_germ hw).symm

/-- Exact Banach-valued divisor of the actual constant-input inverse. -/
theorem vectorResponse_order {w : ℂ} (hw : 0 < w.re) :
    meromorphicOrderAt vectorResponse w= -meromorphicOrderAt scatteringDenominator w := by
  have hC := analyticAt_clearedState hw
  rw [meromorphicOrderAt_congr (vectorResponse_germ hw)]
  change meromorphicOrderAt (scatteringDenominator⁻¹ • clearedState) w=_
  rw [meromorphicOrderAt_smul (meromorphicAt_scatteringDenominator w).inv hC.meromorphicAt,
    meromorphicOrderAt_inv,hC.meromorphicOrderAt_eq,
    hC.analyticOrderAt_eq_zero.mpr (clearedState_ne_zero hw)]
  simp

private theorem linear_order_zero {w : ℂ} (hw2 : w ≠ 2) :
    meromorphicOrderAt (fun v : ℂ => v-2) w=0 := by
  have ha : AnalyticAt ℂ (fun v : ℂ => v-2) w := analyticAt_id.sub analyticAt_const
  rw [ha.meromorphicOrderAt_eq,ha.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hw2)]
  rfl

private theorem denominator_order_of_ne_two {w : ℂ} (hw2 : w ≠ 2) :
    meromorphicOrderAt scatteringDenominator w=meromorphicOrderAt riemannZeta w := by
  have ha : AnalyticAt ℂ (fun v : ℂ => v-2) w := analyticAt_id.sub analyticAt_const
  change meromorphicOrderAt (riemannZeta*(fun v : ℂ => v-2)) w=_
  rw [meromorphicOrderAt_mul
    (GaloisForLFunctions.HTGeometry.meromorphicOn_riemannZeta w (mem_univ w))
    ha.meromorphicAt,linear_order_zero hw2,add_zero]

private theorem zeta_order_finite {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderAt riemannZeta w ≠ ⊤ := by
  intro ht
  have h := determinant_order h0 h1
  rw [ht,add_top] at h
  exact determinant_order_ne_top h0 h1 h

/-- No unobserved vector factor changes the scattering pole multiplicity. -/
theorem vectorResponse_strip_order {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt vectorResponse w= -((analyticOrderNatAt riemannZeta w : ℤ) : WithTop ℤ) := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at h1
  have hZ := GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1
  have hf := ENat.coe_toNat (zeta_order_finite h0 h1)
  rw [vectorResponse_order h0,denominator_order_of_ne_two hw2,hZ.meromorphicOrderAt_eq,← hf]
  simp [analyticOrderNatAt]

/-- The actual full source vector has a pole exactly at strip zeta zeros. -/
theorem vectorResponse_pole_iff {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt vectorResponse w < 0 ↔ riemannZeta w=0 := by
  rw [vectorResponse_strip_order h0 h1,← MayerBoundaryResolvent.positiveBoundary_order h0 h1]
  exact MayerBoundaryResolvent.positiveBoundary_pole_iff h0 h1

/-- An analytic particular response wherever zeta is nonzero, independent of determinant zeros. -/
def regularResponse (w : ℂ) : DiscSpace := (riemannZeta w)⁻¹ • state w

theorem analyticAt_regularResponse {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hw2 : w ≠ 2)
    (hz : riemannZeta w ≠ 0) : AnalyticAt ℂ regularResponse w :=
  ((GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1).inv hz).smul (analyticAt_state hw hw2)

/-- This particular solution is valid even when the full source operator is not invertible. -/
theorem regularResponse_equation {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hw2 : w ≠ 2)
    (hz : riemannZeta w ≠ 0) : regularResponse w-source w (regularResponse w)=constant 1 := by
  rw [regularResponse,map_smul,← smul_sub,state_equation hw hw1 hw2,smul_smul,
    inv_mul_cancel₀ hz,one_smul]

/-- The particular solution represents the actual inverse on every punctured germ. -/
theorem vectorResponse_germ_regular {w : ℂ} (hw : 0 < w.re) :
    vectorResponse =ᶠ[𝓝[≠] w] regularResponse := by
  filter_upwards [vectorResponse_germ hw,punctured_avoid w 2] with v hv hv2
  rw [hv,regularResponse,clearedState_eq hv2,scatteringDenominator,mul_inv_rev,smul_smul]
  have he : ((v-2)⁻¹*(riemannZeta v)⁻¹)*(v-2)=(riemannZeta v)⁻¹ := by
    field_simp [sub_ne_zero.mpr hv2]
  rw [he]

/-- Clearing the zeta factor recovers the explicit observable vector as a genuine Banach-space limit. -/
theorem zeta_cleared_limit {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    Tendsto (fun v => riemannZeta v • vectorResponse v) (𝓝[≠] w) (𝓝 (state w)) := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at h1
  have hZ := GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1
  have hz : ∀ᶠ v in 𝓝[≠] w, riemannZeta v ≠ 0 := by
    rcases hZ.eventually_eq_zero_or_eventually_ne_zero with he | he
    · exact False.elim (zeta_order_finite h0 h1 (analyticOrderAt_eq_top.mpr he))
    · exact he
  have he : (fun v => riemannZeta v • vectorResponse v) =ᶠ[𝓝[≠] w] state := by
    filter_upwards [vectorResponse_germ_regular h0,hz] with v hv hzv
    rw [hv,regularResponse,smul_smul,mul_inv_cancel₀ hzv,one_smul]
  exact ((analyticAt_state h0 hw2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm

/-- A determinant zero away from zeta zeros contributes no vector pole to the constant-input channel. -/
theorem vectorResponse_order_zero {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hw2 : w ≠ 2)
    (hz : riemannZeta w ≠ 0) : meromorphicOrderAt vectorResponse w=0 := by
  have hZ := GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1
  rw [vectorResponse_order hw,denominator_order_of_ne_two hw2,hZ.meromorphicOrderAt_eq,
    hZ.analyticOrderAt_eq_zero.mpr hz]
  rfl

/-- The apparent source pole becomes a simple zero of the entire constant-input vector germ. -/
theorem vectorResponse_order_one : meromorphicOrderAt vectorResponse (1 : ℂ)=1 := by
  rw [vectorResponse_order (by norm_num),denominator_order_of_ne_two (by norm_num),GaloisForLFunctions.meromorphicOrderAt_riemannZeta_one]
  norm_num

/-- The constant-state pole at two is simple in the actual vector response. -/
theorem vectorResponse_order_two : meromorphicOrderAt vectorResponse (2 : ℂ)= -1 := by
  have hZ := GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta (s := 2) (by norm_num)
  have hz : riemannZeta (2 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hid : AnalyticAt ℂ (fun v : ℂ => v) 2 := analyticAt_id
  have hl : analyticOrderAt (fun v : ℂ => v-2) 2=1 :=
    hid.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (by simp)
  have ha : AnalyticAt ℂ (fun v : ℂ => v-2) 2 := analyticAt_id.sub analyticAt_const
  rw [vectorResponse_order (by norm_num)]
  change -meromorphicOrderAt (riemannZeta*(fun v : ℂ => v-2)) (2 : ℂ)= -1
  rw [meromorphicOrderAt_mul hZ.meromorphicAt ha.meromorphicAt,
    hZ.meromorphicOrderAt_eq,hZ.analyticOrderAt_eq_zero.mpr hz,ha.meromorphicOrderAt_eq,hl]
  norm_num

#print axioms clearedState_two
#print axioms clearedState_one_zero
#print axioms clearedState_ne_zero
#print axioms vectorResponse_germ
#print axioms meromorphicAt_vectorResponse
#print axioms vectorResponse_order
#print axioms vectorResponse_strip_order
#print axioms vectorResponse_pole_iff
#print axioms analyticAt_regularResponse
#print axioms regularResponse_equation
#print axioms vectorResponse_germ_regular
#print axioms zeta_cleared_limit
#print axioms vectorResponse_order_zero
#print axioms vectorResponse_order_one
#print axioms vectorResponse_order_two
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringVector
