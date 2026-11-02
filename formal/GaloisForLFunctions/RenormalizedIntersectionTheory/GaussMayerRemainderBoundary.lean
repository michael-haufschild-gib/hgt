import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerBoundaryResolvent

/-! Removing the constant zeta mode changes the actual boundary inverse by
an explicit rank-one feedback factor. Its zeros contribute an additional
divisor to the observable remainder poles. -/

open Complex Set Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerBoundaryResolvent MayerScatteringMultiplicity
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerRemainderBoundary

/-- Actual constant-input, evaluation-output inverse entry of the remainder. -/
def boundary (w : ℂ) : ℂ :=
  (Ring.inverse (1-remainder w) (constant 1)).1 zeroPoint

/-- The scalar factor introduced by subtracting the zeta constant mode. -/
def feedbackFactor (w : ℂ) : ℂ := 1+2*riemannZeta (w-1)

private def sourceResponse (w : ℂ) : DiscSpace :=
  Ring.inverse (1-source w) (constant 1)

private def responseRankOne (w : ℂ) : DiscSpace →L[ℂ] DiscSpace :=
  (evaluation zeroPoint).smulRight (sourceResponse w)

private theorem responseRankOne_twice (w : ℂ) (f : DiscSpace) :
    responseRankOne w (responseRankOne w f)=positiveBoundary w • responseRankOne w f := by
  change responseRankOne w (f.1 zeroPoint • sourceResponse w)=_
  rw [map_smul]
  change f.1 zeroPoint • (positiveBoundary w • sourceResponse w)=
    positiveBoundary w • (f.1 zeroPoint • sourceResponse w)
  exact smul_comm _ _ _

private def feedbackUnit (w : ℂ) (h : 1+riemannZeta w*positiveBoundary w ≠ 0) :
    (DiscSpace →L[ℂ] DiscSpace)ˣ where
  val := 1+riemannZeta w • responseRankOne w
  inv := 1-(riemannZeta w/(1+riemannZeta w*positiveBoundary w)) • responseRankOne w
  val_inv := by
    apply ContinuousLinearMap.ext
    intro f
    let c := riemannZeta w/(1+riemannZeta w*positiveBoundary w)
    change (f-c • responseRankOne w f)+riemannZeta w •
      responseRankOne w (f-c • responseRankOne w f)=f
    rw [map_sub,map_smul,responseRankOne_twice]
    have hc : riemannZeta w-c-riemannZeta w*c*positiveBoundary w=0 := by
      dsimp [c]
      field_simp [h]
      ring
    calc
      _ = f+(riemannZeta w-c-riemannZeta w*c*positiveBoundary w) •
        responseRankOne w f := by module
      _ = f := by rw [hc,zero_smul,add_zero]
  inv_val := by
    apply ContinuousLinearMap.ext
    intro f
    let c := riemannZeta w/(1+riemannZeta w*positiveBoundary w)
    change (f+riemannZeta w • responseRankOne w f)-c •
      responseRankOne w (f+riemannZeta w • responseRankOne w f)=f
    rw [map_add,map_smul,responseRankOne_twice]
    have hc : riemannZeta w-c-c*riemannZeta w*positiveBoundary w=0 := by
      dsimp [c]
      field_simp [h]
      ring
    calc
      _ = f+(riemannZeta w-c-c*riemannZeta w*positiveBoundary w) •
        responseRankOne w f := by module
      _ = f := by rw [hc,zero_smul,add_zero]

private theorem sourceResponse_equation {w : ℂ} (hu : IsUnit (1-source w)) :
    (1-source w) (sourceResponse w)=constant 1 :=
  congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T (constant 1))
    (Ring.mul_inverse_cancel (1-source w) hu)

/-- Actual operator factorization by the rank-one response of the full source. -/
private theorem remainder_factorization {w : ℂ} (hu : IsUnit (1-source w)) :
    (1-source w)*(1+riemannZeta w • responseRankOne w)=1-remainder w := by
  apply ContinuousLinearMap.ext
  intro f
  change (1-source w) (f+riemannZeta w • (f.1 zeroPoint • sourceResponse w))=_
  rw [map_add,map_smul,map_smul,sourceResponse_equation hu]
  change f-source w f+riemannZeta w • (f.1 zeroPoint • constant 1)=f-remainder w f
  rw [source]
  change f-(riemannZeta w • constant (f.1 zeroPoint)+remainder w f)+
    riemannZeta w • (f.1 zeroPoint • constant 1)=f-remainder w f
  have hc : f.1 zeroPoint • constant (1 : ℂ)=constant (f.1 zeroPoint) := by
    apply Subtype.ext
    ext z
    exact mul_one _
  rw [hc]
  abel

/-- The scalar rank-one feedback law for the actual remainder inverse. -/
theorem boundary_eq_feedback {w : ℂ} (hu : IsUnit (1-source w))
    (h : 1+riemannZeta w*positiveBoundary w ≠ 0) :
    boundary w=positiveBoundary w/(1+riemannZeta w*positiveBoundary w) := by
  obtain ⟨u,huv⟩ := hu
  have he : 1-remainder w=
      ((u*feedbackUnit w h : (DiscSpace →L[ℂ] DiscSpace)ˣ) : DiscSpace →L[ℂ] DiscSpace) := by
    rw [← remainder_factorization (show IsUnit (1-source w) from ⟨u,huv⟩),← huv]
    rfl
  have hi : Ring.inverse (1-remainder w)=
      (1-(riemannZeta w/(1+riemannZeta w*positiveBoundary w)) • responseRankOne w)*
        Ring.inverse (1-source w) := by
    rw [he,← huv,Ring.inverse_unit,Ring.inverse_unit]
    rfl
  rw [boundary,hi]
  change positiveBoundary w-(riemannZeta w/(1+riemannZeta w*positiveBoundary w))*
    (positiveBoundary w*positiveBoundary w)=_
  have hc : 1-(riemannZeta w*positiveBoundary w)/(1+riemannZeta w*positiveBoundary w)=
      1/(1+riemannZeta w*positiveBoundary w) := by
    rw [eq_div_iff h,sub_mul,one_mul,div_mul_cancel₀ _ h]
    ring
  calc
    _ = positiveBoundary w*
        (1-(riemannZeta w*positiveBoundary w)/(1+riemannZeta w*positiveBoundary w)) := by ring
    _ = _ := by rw [hc]; ring

private def clearedFeedback (w : ℂ) : ℂ :=
  w-2+2*_root_.RHTower.zetaResidueUnit (w-1)

private theorem analyticAt_clearedFeedback (w : ℂ) : AnalyticAt ℂ clearedFeedback w :=
  (analyticAt_id.sub analyticAt_const).add (analyticAt_const.mul
    ((_root_.RHTower.analyticAt_zetaResidueUnit (w-1)).comp
      (f := fun v : ℂ => v-1) (analyticAt_id.sub analyticAt_const)))

private theorem clearedFeedback_two : clearedFeedback 2=2 := by
  norm_num [clearedFeedback,_root_.RHTower.zetaResidueUnit_one]

private theorem clearedFeedback_eq {w : ℂ} (hw : w ≠ 2) :
    clearedFeedback w=(w-2)*feedbackFactor w := by
  have hw1 : w-1 ≠ 1 := by intro he; apply hw; linear_combination he
  rw [clearedFeedback,_root_.RHTower.zetaResidueUnit,Function.update_of_ne hw1,feedbackFactor]
  ring

/-- The extra feedback factor has no identically zero germ away from its source pole. -/
theorem feedback_order_ne_top {w : ℂ} (hw : w ≠ 2) :
    analyticOrderAt feedbackFactor w ≠ ⊤ := by
  have hJ : AnalyticOnNhd ℂ clearedFeedback univ := fun v _ => analyticAt_clearedFeedback v
  have hfinite := hJ.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 2) (mem_univ 2) (mem_univ w)
    (by rw [(hJ 2 (mem_univ 2)).analyticOrderAt_eq_zero.mpr
          (by rw [clearedFeedback_two]; norm_num)]; exact ENat.zero_ne_top)
  intro ht
  apply hfinite
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [analyticOrderAt_eq_top.mp ht,isOpen_ne.mem_nhds hw] with v hv hv2
  rw [clearedFeedback_eq hv2,hv,mul_zero]

private theorem analyticAt_feedbackFactor {w : ℂ} (hw : w ≠ 2) :
    AnalyticAt ℂ feedbackFactor w := by
  have hw1 : w-1 ≠ 1 := by intro he; apply hw; linear_combination he
  exact analyticAt_const.add (analyticAt_const.mul
    ((GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1).comp
      (f := fun v : ℂ => v-1) (analyticAt_id.sub analyticAt_const)))

private theorem eventually_feedback_ne_zero {w : ℂ} (hw : w ≠ 2) :
    ∀ᶠ v in 𝓝[≠] w, feedbackFactor v ≠ 0 := by
  rcases (analyticAt_feedbackFactor hw).eventually_eq_zero_or_eventually_ne_zero with he | he
  · exact False.elim (feedback_order_ne_top hw (analyticOrderAt_eq_top.mpr he))
  · exact he

private theorem eventually_source_isUnit {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    ∀ᶠ v in 𝓝[≠] w, IsUnit (1-source v) := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have ho : IsOpen {v : ℂ | 0 < v.re ∧ v ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have hA := (differentiableOn_sourceDeterminant 1).analyticAt (ho.mem_nhds ⟨h0,hw1⟩)
  have hn : ∀ᶠ v in 𝓝[≠] w, sourceDeterminant v 1 ≠ 0 := by
    rcases hA.eventually_eq_zero_or_eventually_ne_zero with he | he
    · exact False.elim (determinant_order_ne_top h0 h1 (analyticOrderAt_eq_top.mpr he))
    · exact he
  have hh : ∀ᶠ v in 𝓝[≠] w, 0 < v.re := nhdsWithin_le_nhds
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h0)
  filter_upwards [hn,hh] with v hv hv0
  by_contra hunit
  apply hv
  rw [sourceDeterminant_eq hv0,MayerFredholm.determinant_eq_zero_iff_not_isUnit hv0,
    one_smul,← source_eq hv0]
  exact hunit

/-- Exact meromorphic germ of the observable remainder inverse. -/
theorem boundary_germ {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    boundary =ᶠ[𝓝[≠] w]
      fun v => 2*riemannZeta (v-1)/(riemannZeta v*feedbackFactor v) := by
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at h1
  have ho : IsOpen {v : ℂ | 0 < v.re ∧ v.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hs : ∀ᶠ v in 𝓝[≠] w, 0 < v.re ∧ v.re < 1 :=
    nhdsWithin_le_nhds (ho.mem_nhds ⟨h0,h1⟩)
  filter_upwards [positiveBoundary_germ h0 h1,eventually_source_isUnit h0 h1,
    eventually_feedback_ne_zero hw2,hs] with v hb hu hF hv
  have hz : riemannZeta v ≠ 0 := by
    intro hz
    have hd := sourceDeterminant_zero_of_zeta_zero hv.1 hv.2 hz
    rw [sourceDeterminant_eq hv.1,MayerFredholm.determinant_eq_zero_iff_not_isUnit hv.1,
      one_smul,← source_eq hv.1] at hd
    exact hd hu
  have hfactor : 1+riemannZeta v*positiveBoundary v=feedbackFactor v := by
    rw [hb,feedbackFactor]
    field_simp [hz]
  have hden : 1+riemannZeta v*positiveBoundary v ≠ 0 := by rwa [hfactor]
  rw [boundary_eq_feedback hu hden,hfactor,hb,div_div]

/-- The actual source-to-remainder response relation also holds as a meromorphic germ. -/
theorem boundary_feedback_germ {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    boundary =ᶠ[𝓝[≠] w] fun v => positiveBoundary v/feedbackFactor v := by
  filter_upwards [boundary_germ h0 h1,positiveBoundary_germ h0 h1] with v hr hb
  rw [hr,hb,div_div]

/-- The actual scalar remainder inverse is meromorphic throughout the open strip. -/
theorem meromorphicAt_boundary {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    MeromorphicAt boundary w := by
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at h1
  exact ((meromorphicAt_positiveBoundary h0 h1).div
    (analyticAt_feedbackFactor hw2).meromorphicAt).congr (boundary_feedback_germ h0 h1).symm

/-- Subtracting the constant zeta mode adds the feedback divisor to the exact pole order. -/
theorem boundary_order {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt boundary w=
      -(((analyticOrderNatAt riemannZeta w+analyticOrderNatAt feedbackFactor w : ℕ) : ℤ) :
        WithTop ℤ) := by
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at h1
  have hF := analyticAt_feedbackFactor hw2
  have hfin := ENat.coe_toNat (feedback_order_ne_top hw2)
  rw [meromorphicOrderAt_congr (boundary_feedback_germ h0 h1)]
  change meromorphicOrderAt (positiveBoundary/feedbackFactor) w=_
  rw [meromorphicOrderAt_div (meromorphicAt_positiveBoundary h0 h1) hF.meromorphicAt,
    positiveBoundary_order h0 h1,hF.meromorphicOrderAt_eq,← hfin]
  simp only [ENat.map_coe]
  norm_cast
  simp only [analyticOrderNatAt]
  omega

/-- Exact classification of the two possible observable remainder pole causes. -/
theorem boundary_pole_iff {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt boundary w < 0 ↔
      riemannZeta w=0 ∨ riemannZeta (w-1)=-(1/2 : ℂ) := by
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at h1
  have hF := analyticAt_feedbackFactor hw2
  have hfin : (analyticOrderNatAt feedbackFactor w : ℕ∞)=analyticOrderAt feedbackFactor w :=
    ENat.coe_toNat (feedback_order_ne_top hw2)
  have hz : riemannZeta w=0 ↔ analyticOrderNatAt riemannZeta w ≠ 0 := by
    rw [← positiveBoundary_pole_iff h0 h1,positiveBoundary_order h0 h1]
    norm_cast
    omega
  have hf : feedbackFactor w=0 ↔ analyticOrderNatAt feedbackFactor w ≠ 0 := by
    rw [← hF.analyticOrderAt_ne_zero,← hfin]
    simp
  have hlevel : feedbackFactor w=0 ↔ riemannZeta (w-1)=-(1/2 : ℂ) := by
    unfold feedbackFactor
    constructor
    · intro h
      linear_combination (1/2 : ℂ)*h
    · intro h
      linear_combination 2*h
  rw [boundary_order h0 h1,hz,← hlevel,hf]
  norm_cast
  omega

/-- Restoring the feedback factor recovers the independently normalized source channel. -/
theorem normalized_boundary_germ {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    (fun v => feedbackFactor v*boundary v) =ᶠ[𝓝[≠] w] positiveBoundary := by
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at h1
  filter_upwards [boundary_feedback_germ h0 h1,eventually_feedback_ne_zero hw2] with v hv hF
  rw [hv]
  field_simp [hF]

/-- The corrected actual remainder response has exactly the zeta pole multiplicities. -/
theorem normalized_boundary_order {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt (fun v => feedbackFactor v*boundary v) w=
      -((analyticOrderNatAt riemannZeta w : ℤ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_congr (normalized_boundary_germ h0 h1),positiveBoundary_order h0 h1]

/-- Faithful zeta-zero detection by the canonically corrected actual remainder inverse. -/
theorem normalized_boundary_pole_iff {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt (fun v => feedbackFactor v*boundary v) w < 0 ↔ riemannZeta w=0 := by
  rw [meromorphicOrderAt_congr (normalized_boundary_germ h0 h1)]
  exact positiveBoundary_pole_iff h0 h1

#print axioms remainder_factorization
#print axioms boundary_eq_feedback
#print axioms feedback_order_ne_top
#print axioms boundary_germ
#print axioms meromorphicAt_boundary
#print axioms boundary_order
#print axioms boundary_pole_iff
#print axioms normalized_boundary_germ
#print axioms normalized_boundary_order
#print axioms normalized_boundary_pole_iff
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerRemainderBoundary
