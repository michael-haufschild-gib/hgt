import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticReducedDrift
import GaloisForLFunctions.RHTower.ThetaCuspRatioNonlinearBoundaryParameter
import Mathlib.Topology.Order.IntermediateValue
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem nonlinearCone_boundary_projection {h r t : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 4/5) (hr0 : 0 < r) (hr1 : r ≤ 361/25)
    (hv : 0 < 9-r*h^2) (ht : 0 < t) (hht : h*t < 1)
    (hbar : r*ThetaCriticalBarrier.b h < t-h^2*t^2) :
    ∃ s : ℝ, 0 < s ∧ s < (6/5)*(361/25) ∧
      kineticBoundaryV h s=9-r*h^2 ∧
      0 < (1-h*t)/3 ∧ (1-h*t)/3 < kineticBoundaryZ h s ∧
      kineticBoundaryZ h s < 1/3 := by
  have hb : 0 < ThetaCriticalBarrier.b h := by
    unfold ThetaCriticalBarrier.b
    linarith only [hh1]
  have hrb := mul_pos hr0 hb
  have hf : Continuous (fun y : ℝ => y-h^2*y^2) := by fun_prop
  obtain ⟨t0,ht0,he⟩ := intermediate_value_Icc (f := fun y : ℝ => y-h^2*y^2)
    ht.le hf.continuousOn ⟨by simpa using hrb.le,hbar.le⟩
  have ht00 : 0 < t0 := by
    by_contra hn
    have hz : t0=0 := le_antisymm (not_lt.mp hn) ht0.1
    rw [hz] at he
    rw [←he] at hrb
    norm_num at hrb
  have ht0t : t0 < t := by
    by_contra hn
    have hz : t0=t := le_antisymm ht0.2 (not_lt.mp hn)
    rw [hz] at he
    linarith only [he,hbar]
  have hht0 : h*t0 < 1 := (mul_lt_mul_of_pos_left ht0t hh0).trans hht
  obtain ⟨s,hs0,hs1,hts,hrs⟩ := nonlinearBoundary_parameter_coverage
    hh0 hh1 hr0 hr1 hv ht00 hht0 he
  have hV : kineticBoundaryV h s=9-r*h^2 := by
    have hrR : r=s*(1-h^2*(1/12-7*h/72)*s) := by
      simpa only [ThetaCriticalBarrier.b] using hrs
    unfold kineticBoundaryV
    rw [←hrR]
  have hZ : kineticBoundaryZ h s=(1-h*t0)/3 := by
    rw [hts]
    unfold kineticBoundaryZ ThetaCriticalBarrier.b
    ring
  refine ⟨s,hs0,hs1,hV,by linarith,?_,?_⟩
  · rw [hZ]
    linarith only [mul_lt_mul_of_pos_left ht0t hh0]
  · rw [hZ]
    linarith only [mul_pos hh0 ht00]

theorem reducedKineticValue_source_identity (h v z : ℝ) (hh : h ≠ 0) :
    v*reducedKineticValue h v z=
      h^24*(eval (basePoint (v:ℂ) (h:ℂ)⁻¹ (z:ℂ)) ThetaRatioSquare.slope).re := by
  rw [←completeKineticValue_reduced]
  have he := congrArg Complex.re (clearSlope_eval (h:ℂ) (v:ℂ) (z:ℂ)
    (by exact_mod_cast hh))
  simpa only [completeKineticValue,←Complex.ofReal_pow,Complex.re_ofReal_mul] using he

end
end HTGeometry.ThetaRatioKineticContraction
