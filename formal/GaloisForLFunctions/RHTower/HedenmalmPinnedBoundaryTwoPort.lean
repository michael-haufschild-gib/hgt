import GaloisForLFunctions.RHTower.HedenmalmQuantileBoundaryFlux

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

private theorem pinnedBoundary_inner_pinnedOne_eq_mean (f : H) :
    inner ℂ pinnedOne f = pinnedMean f := by
  rw [inner_lp_eq, pinnedMean]
  apply integral_congr_ae
  filter_upwards [pinnedOne_coeFn] with t ht
  rw [ht]
  simp

private theorem pinnedBoundary_inner_pinnedCoordinate_eq_firstMoment (f : H) :
    inner ℂ pinnedCoordinate f = pinnedFirstMoment f := by
  rw [inner_lp_eq, pinnedFirstMoment]
  apply integral_congr_ae
  filter_upwards [pinnedCoordinate_coeFn] with t ht
  rw [ht]
  simp

theorem pinnedBoundaryCLM_eq_rankOne :
    pinnedBoundaryCLM =
      InnerProductSpace.rankOne ℂ pinnedOne pinnedOne -
        InnerProductSpace.rankOne ℂ pinnedOne pinnedCoordinate -
          InnerProductSpace.rankOne ℂ pinnedCoordinate pinnedOne := by
  apply ContinuousLinearMap.ext
  intro f
  rw [pinnedBoundaryCLM_eq_affine_combination]
  simp only [sub_apply, InnerProductSpace.rankOne_apply]
  rw [pinnedBoundary_inner_pinnedOne_eq_mean, pinnedBoundary_inner_pinnedCoordinate_eq_firstMoment]
  module

/-- Exact incoming boundary vector for the rank-two Green form. -/
def pinnedBoundaryInVector : H := pinnedOne - pinnedCenter

/-- Exact outgoing boundary vector for the rank-two Green form. -/
def pinnedBoundaryOutVector : H := pinnedOne + pinnedCenter

theorem pinnedBoundaryCLM_eq_portVectors :
    pinnedBoundaryCLM =
      (1 / 2 : ℂ) • InnerProductSpace.rankOne ℂ pinnedBoundaryInVector pinnedBoundaryInVector -
        (1 / 2 : ℂ) • InnerProductSpace.rankOne ℂ pinnedBoundaryOutVector pinnedBoundaryOutVector := by
  rw [pinnedBoundaryCLM_eq_rankOne]
  apply ContinuousLinearMap.ext
  intro f
  simp only [sub_apply, smul_apply, InnerProductSpace.rankOne_apply,
    pinnedBoundaryInVector, pinnedBoundaryOutVector, pinnedCenter, inner_sub_left,
    inner_add_left, inner_smul_left, map_div₀, map_one,
    map_ofNat]
  module

private def pinnedBoundaryPortScale : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- Incoming scalar boundary port. -/
def pinnedBoundaryInPort : H →L[ℂ] ℂ :=
  pinnedBoundaryPortScale • innerSL ℂ pinnedBoundaryInVector

/-- Outgoing scalar boundary port. -/
def pinnedBoundaryOutPort : H →L[ℂ] ℂ :=
  pinnedBoundaryPortScale • innerSL ℂ pinnedBoundaryOutVector

private theorem pinned_boundary_port_scale_sq :
    (starRingEnd ℂ) pinnedBoundaryPortScale * pinnedBoundaryPortScale = (1 / 2 : ℂ) := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast h.ne'
  rw [pinnedBoundaryPortScale, map_inv₀, Complex.conj_ofReal]
  field_simp
  rw [pow_two, hsq]

private theorem pinned_port_adjoint_comp (v : H) :
    (pinnedBoundaryPortScale • innerSL ℂ v).adjoint.comp
        (pinnedBoundaryPortScale • innerSL ℂ v) =
      (1 / 2 : ℂ) • InnerProductSpace.rankOne ℂ v v := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    smul_apply, map_mul, inner_smul_left,
    InnerProductSpace.rankOne_apply, innerSL_apply_apply, RCLike.inner_apply',
    map_div₀, map_one, map_ofNat, smul_eq_mul]
  calc
    _ = ((starRingEnd ℂ) pinnedBoundaryPortScale * pinnedBoundaryPortScale) *
        ((starRingEnd ℂ) (inner ℂ v f) * inner ℂ v g) := by ring
    _ = _ := by rw [pinned_boundary_port_scale_sq]

theorem pinnedBoundaryCLM_eq_port_difference :
    pinnedBoundaryCLM = pinnedBoundaryInPort.adjoint.comp pinnedBoundaryInPort -
      pinnedBoundaryOutPort.adjoint.comp pinnedBoundaryOutPort := by
  rw [pinnedBoundaryCLM_eq_portVectors, pinnedBoundaryInPort, pinnedBoundaryOutPort,
    pinned_port_adjoint_comp, pinned_port_adjoint_comp]

end
end RHTower
