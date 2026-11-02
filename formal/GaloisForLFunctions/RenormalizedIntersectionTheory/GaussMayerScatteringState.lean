import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringChamber
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerLatticeSource
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCofactorContinuation
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringMultiplicity

/-! The continued kernel represents the actual positive-lattice response.
Agreement on the real diameter determines the full disc-algebra state. -/

open Complex Set Filter Metric Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringMellin
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringState

private theorem disc_ext_real (f g : DiscSpace)
    (he : ∀ (z : Disc) (x : ℝ), z.1=(x : ℂ) → f.1 z=g.1 z) : f=g := by
  have hacc : (0 : ℂ) ∈ closure ({z | plane f z=plane g z} \ {0}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let t : ℝ := min ε 1/2
    have ht : 0 < t := div_pos (lt_min hε zero_lt_one) (by norm_num)
    have ht1 : t < 1 := by
      have hm := min_le_right ε (1 : ℝ)
      dsimp [t]
      linarith only [hm]
    have htε : t < ε := by
      have hm := min_le_left ε (1 : ℝ)
      dsimp [t]
      linarith only [hm,hε]
    have hto : (t : ℂ) ∈ outer := by
      rw [outer,mem_closedBall,dist_eq_norm,
        show (t : ℂ)-1=((t-1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real,Real.norm_eq_abs,abs_of_neg (sub_neg.mpr ht1)]
      linarith only [ht]
    refine ⟨(t : ℂ),⟨?_,?_⟩,?_⟩
    · change plane f (t : ℂ)=plane g (t : ℂ)
      simpa only [plane_eq f ⟨(t : ℂ),hto⟩,plane_eq g ⟨(t : ℂ),hto⟩] using
        he ⟨(t : ℂ),hto⟩ t rfl
    · exact fun hn => (Complex.ofReal_ne_zero.mpr ht.ne') (Set.mem_singleton_iff.mp hn)
    · simpa only [dist_zero_right,dist_zero_left,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos ht] using htε
  have hf := (differentiableOn_plane f).analyticOnNhd isOpen_ball
  have hg := (differentiableOn_plane g).analyticOnNhd isOpen_ball
  have hi : Set.EqOn (plane f) (plane g) MayerCutoff.inner :=
    hf.eqOn_of_preconnected_of_mem_closure hg (convex_ball (1 : ℂ) (3/2 : ℝ)).isPreconnected
      (by norm_num [MayerCutoff.inner,mem_ball,dist_eq_norm]) hacc
  have hc (v : DiscSpace) : ContinuousOn (plane v) outer := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun z : Disc => plane v z.1)
    simpa only [plane_eq] using v.1.continuous
  have hcl : outer ⊆ closure MayerCutoff.inner := by
    rw [MayerCutoff.inner,closure_ball (1 : ℂ) (by norm_num : (3/2 : ℝ) ≠ 0)]
  have ho := hi.of_subset_closure (hc f) (hc g) ball_subset_closedBall hcl
  apply Subtype.ext
  ext z
  simpa only [plane_eq] using ho z.property

/-- The continued Mellin state equals the actual lattice response in its absolute chamber. -/
theorem state_eq_response {w : ℂ} (hw : 2 < w.re) :
    state w=MayerLatticeSource.response w := by
  apply disc_ext_real
  intro z x hz
  rw [MayerScatteringChamber.state_apply_real_expanded hw z x hz]
  change _=riemannZeta w*(1+(MayerCoprimeSource.endpoint w).1 z)+
    2*(MayerLatticeSource.coneSum w).1 z
  rw [MayerLatticeSource.coneSum_apply_real hw z x hz,MayerCoprimeSource.endpoint_apply,hz]
  push_cast
  rfl

/-- The absolute-chamber forcing equation holds for the continued state itself. -/
theorem state_equation_absolute {w : ℂ} (hw : 2 < w.re) :
    state w-source w (state w)=riemannZeta w • constant 1 := by
  rw [state_eq_response hw,source_eq (show 0 < w.re by linarith only [hw])]
  exact MayerLatticeSource.response_equation hw

/-- The same actual state has the shifted-zeta boundary value in the absolute chamber. -/
theorem state_zero_absolute {w : ℂ} (hw : 2 < w.re) :
    (state w).1 zeroPoint=2*riemannZeta (w-1) := by
  rw [state_eq_response hw,MayerLatticeSource.response_zero hw]

/-- Removing the explicit Mellin pole gives a state holomorphic on the full right half-plane. -/
def clearedState (w : ℂ) : DiscSpace :=
  (Complex.Gamma w)⁻¹ • ((2 : ℂ) • MayerCoprimeSource.endpoint 1+
    (w-2) • (mellin headInput w+mellin tailInput w))

theorem analyticAt_clearedState {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ clearedState w := by
  have hG : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.neg_re,Complex.natCast_re] at hr
    linarith only [hr,hw,Nat.cast_nonneg (α := ℝ) n]
  have hGa : AnalyticAt ℂ Complex.Gamma w :=
    (Meromorphic.Gamma w).analyticAt (Complex.continuousAt_Gamma _ hG)
  have hhalf : {v : ℂ | 0 < v.re} ∈ 𝓝 w :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
  have hH : AnalyticAt ℂ (mellin headInput) w :=
    (show DifferentiableOn ℂ (mellin headInput) {v : ℂ | 0 < v.re} from
      fun v hv => (differentiableAt_headMellin hv).differentiableWithinAt).analyticAt hhalf
  have hT : AnalyticAt ℂ (mellin tailInput) w :=
    (show DifferentiableOn ℂ (mellin tailInput) {v : ℂ | 0 < v.re} from
      fun v hv => (differentiableAt_tailMellin hv).differentiableWithinAt).analyticAt hhalf
  exact (hGa.inv (Complex.Gamma_ne_zero hG)).smul
    (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).smul (hH.add hT)))

theorem clearedState_eq {w : ℂ} (hw2 : w ≠ 2) : clearedState w=(w-2) • state w := by
  rw [clearedState,state,smul_comm (w-2) (Complex.Gamma w)⁻¹]
  congr 1
  have he : (w-2)*(2/(w-2))=2 := by field_simp [sub_ne_zero.mpr hw2]
  simp only [smul_add,smul_smul,he,add_assoc]

private theorem residue_eq {w : ℂ} (hw : w ≠ 1) :
    _root_.RHTower.zetaResidueUnit w=(w-1)*riemannZeta w := by
  rw [_root_.RHTower.zetaResidueUnit,Function.update_of_ne hw]

/-- The actual operator equation after clearing its two scalar poles. -/
def clearedForcing (w : ℂ) : DiscSpace :=
  (w-1) • (clearedState w-remainder w (clearedState w))-
    _root_.RHTower.zetaResidueUnit w • constantProjection (clearedState w)-
      ((w-2)*_root_.RHTower.zetaResidueUnit w) • constant 1

private theorem analyticOn_clearedForcing :
    AnalyticOnNhd ℂ clearedForcing {w : ℂ | 0 < w.re} := by
  have hd : DifferentiableOn ℂ clearedForcing {w : ℂ | 0 < w.re} := by
    intro w hw
    have hc := (analyticAt_clearedState hw).differentiableAt
    have hr := differentiableOn_remainder.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)
    have hz := (_root_.RHTower.analyticAt_zetaResidueUnit w).differentiableAt
    exact ((((differentiableAt_id.sub (differentiableAt_const (1 : ℂ))).smul
      (hc.sub (hr.clm_apply hc))).sub
        (hz.smul ((differentiableAt_const constantProjection).clm_apply hc))).sub
          (((differentiableAt_id.sub (differentiableAt_const (2 : ℂ))).mul hz).smul
            (differentiableAt_const (constant 1)))).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

private theorem clearedForcing_absolute {w : ℂ} (hw : 2 < w.re) : clearedForcing w=0 := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at hw
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at hw
  have he : state w-(riemannZeta w • constantProjection (state w)+remainder w (state w))=
      riemannZeta w • constant 1 := by
    simpa only [source,_root_.add_apply,_root_.smul_apply] using state_equation_absolute hw
  have hs : state w-remainder w (state w)=
      riemannZeta w • constant 1+riemannZeta w • constantProjection (state w) := by
    rw [← he]
    abel
  rw [clearedForcing,clearedState_eq hw2,residue_eq hw1]
  simp only [map_smul,← smul_sub]
  rw [hs]
  module

/-- The pole-cleared forcing equation holds throughout the source half-plane. -/
theorem clearedForcing_zero {w : ℂ} (hw : 0 < w.re) : clearedForcing w=0 := by
  have he : clearedForcing =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have ho : IsOpen {v : ℂ | 2 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (3 : ℂ) ∈ {v : ℂ | 2 < v.re} by norm_num)] with v hv
    exact clearedForcing_absolute hv
  exact analyticOn_clearedForcing.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    MayerCofactorContinuation.rightHalfPlane_preconnected (by norm_num) he hw

private def clearedBoundary (w : ℂ) : ℂ :=
  evaluation zeroPoint (clearedState w)-2*_root_.RHTower.zetaResidueUnit (w-1)

private theorem analyticOn_clearedBoundary :
    AnalyticOnNhd ℂ clearedBoundary {w : ℂ | 0 < w.re} := by
  have hd : DifferentiableOn ℂ clearedBoundary {w : ℂ | 0 < w.re} := by
    intro w hw
    have hz := (_root_.RHTower.analyticAt_zetaResidueUnit (w-1)).comp
      (f := fun v : ℂ => v-1) (analyticAt_id.sub analyticAt_const)
    exact (((differentiableAt_const (evaluation zeroPoint)).clm_apply
      (analyticAt_clearedState hw).differentiableAt).sub
        ((differentiableAt_const (2 : ℂ)).mul hz.differentiableAt)).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

private theorem clearedBoundary_absolute {w : ℂ} (hw : 2 < w.re) : clearedBoundary w=0 := by
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at hw
  have hs : w-1 ≠ 1 := by
    intro he
    apply hw2
    linear_combination he
  rw [clearedBoundary,clearedState_eq hw2,map_smul,evaluation_apply,
    state_zero_absolute hw,residue_eq hs,smul_eq_mul]
  ring

private theorem clearedBoundary_zero {w : ℂ} (hw : 0 < w.re) : clearedBoundary w=0 := by
  have he : clearedBoundary =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have ho : IsOpen {v : ℂ | 2 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (3 : ℂ) ∈ {v : ℂ | 2 < v.re} by norm_num)] with v hv
    exact clearedBoundary_absolute hv
  exact analyticOn_clearedBoundary.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    MayerCofactorContinuation.rightHalfPlane_preconnected (by norm_num) he hw

/-- The continued state retains the exact shifted-zeta boundary value. -/
theorem state_zero {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2) :
    (state w).1 zeroPoint=2*riemannZeta (w-1) := by
  have hs : w-1 ≠ 1 := by
    intro he
    apply hw2
    linear_combination he
  have he := clearedBoundary_zero hw
  rw [clearedBoundary,clearedState_eq hw2,map_smul,evaluation_apply,
    residue_eq hs,smul_eq_mul] at he
  apply mul_left_cancel₀ (sub_ne_zero.mpr hw2)
  linear_combination he

/-- The continued state solves the actual constant forcing equation away from scalar poles. -/
theorem state_equation {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hw2 : w ≠ 2) :
    state w-source w (state w)=riemannZeta w • constant 1 := by
  have he : ((w-1)*(w-2)) •
      (state w-source w (state w)-riemannZeta w • constant 1)=0 := by
    convert clearedForcing_zero hw using 1
    rw [clearedForcing,clearedState_eq hw2,residue_eq hw1,source]
    simp only [_root_.add_apply,_root_.smul_apply,map_smul]
    module
  exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_left
    (mul_ne_zero (sub_ne_zero.mpr hw1) (sub_ne_zero.mpr hw2)))

/-- Every strip zeta zero has this explicit actual remainder eigenfunction, observable at zero. -/
theorem observable_remainder_eigenfunction {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1)
    (hz : riemannZeta w=0) :
    remainder w (state w)=state w ∧ (state w).1 zeroPoint ≠ 0 := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at h1
  have he := state_equation h0 hw1 hw2
  rw [source,hz,zero_smul,zero_add,zero_smul] at he
  refine ⟨(sub_eq_zero.mp he).symm,?_⟩
  rw [state_zero h0 hw2]
  exact mul_ne_zero (by norm_num) (MayerScatteringMultiplicity.shifted_zeta_ne_zero h0 h1)

#print axioms state_eq_response
#print axioms state_equation_absolute
#print axioms state_zero_absolute
#print axioms analyticAt_clearedState
#print axioms clearedForcing_zero
#print axioms state_zero
#print axioms state_equation
#print axioms observable_remainder_eigenfunction
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringState
