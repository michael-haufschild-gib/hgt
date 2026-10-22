import Mathlib.Data.Complex.Basic
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticBarrierBranch
/-!
# Polynomial parametrization of the exact nonlinear ratio boundary

Writing `t=b(h)*s` solves `t-h^2*t^2=r*b(h)` by
`r=s*(1-h^2*b(h)*s)`. The existing small-branch theorem bounds the
parameter for every admissible boundary state. No source-slope sign is assumed.
-/
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open ThetaCriticalBarrier

def nonlinearBoundarySeed (h : ℂ) : ℂ := 1/12-7*h/72
def nonlinearBoundaryR (h s : ℂ) : ℂ := s*(1-h^2*nonlinearBoundarySeed h*s)
def nonlinearBoundaryT (h s : ℂ) : ℂ := nonlinearBoundarySeed h*s
def nonlinearBoundaryV (h s : ℂ) : ℂ := 9-nonlinearBoundaryR h s*h^2
def nonlinearBoundaryZ (h s : ℂ) : ℂ := (1-h*nonlinearBoundaryT h s)/3

theorem nonlinearBoundary_error (h s : ℂ) :
    nonlinearBoundaryT h s-h^2*(nonlinearBoundaryT h s)^2=
      nonlinearBoundaryR h s*nonlinearBoundarySeed h := by
  unfold nonlinearBoundaryT nonlinearBoundaryR
  ring

theorem nonlinearBoundary_recoverR {h r t : ℂ}
    (hb : nonlinearBoundarySeed h≠0)
    (he : t-h^2*t^2=r*nonlinearBoundarySeed h) :
    nonlinearBoundaryR h (t/nonlinearBoundarySeed h)=r := by
  calc
    _ = (t-h^2*t^2)/nonlinearBoundarySeed h := by
      unfold nonlinearBoundaryR
      field_simp [hb]
    _ = r := (div_eq_iff hb).mpr he

theorem nonlinearBoundary_recoverT {h t : ℂ} (hb : nonlinearBoundarySeed h≠0) :
    nonlinearBoundaryT h (t/nonlinearBoundarySeed h)=t := by
  unfold nonlinearBoundaryT
  field_simp [hb]

theorem nonlinearBoundary_parameter_coverage {h r t : ℝ}
    (hh0 : 0<h) (hh1 : h≤4/5) (hr0 : 0<r) (hr1 : r≤361/25)
    (hv : 0<9-r*h^2) (ht : 0<t) (hht : h*t<1)
    (he : t-h^2*t^2=r*b h) :
    ∃ s : ℝ, 0<s ∧ s<(6/5)*(361/25) ∧
      t=b h*s ∧ r=s*(1-h^2*b h*s) := by
  have hb : 0<b h := by unfold b; linarith only [hh1]
  have heq : quadraticError h (9-r*h^2) (t/r)=
      (t-h^2*t^2-r*b h)/r := by
    unfold quadraticError
    field_simp [hr0.ne']
    all_goals ring
  have hscale : (9-(9-r*h^2))*(t/r)=h^2*t := by
    field_simp [hr0.ne']
    all_goals ring
  have hkin : 9-(9-r*h^2)≤(361/25)*h^2 := by
    have hk := mul_le_mul_of_nonneg_right hr1 (sq_nonneg h)
    nlinarith only [hk]
  have hsmall := failure_small_branch hh0.le hh1 hv
    (by nlinarith [mul_nonneg hr0.le (sq_nonneg h)])
    (div_nonneg ht.le hr0.le)
    (by rw [heq,he]; simp)
    (by rw [hscale]; nlinarith only [mul_lt_mul_of_pos_left hht hh0]) hkin
  rw [hscale] at hsmall
  have hs : 0<t/b h := div_pos ht hb
  have hr : r=(t/b h)*(1-h^2*t) := by
    calc
      r=(t-h^2*t^2)/b h := ((div_eq_iff hb.ne').mpr he).symm
      _ = _ := by field_simp [hb.ne']
  have hu := mul_lt_mul_of_pos_left (show (5:ℝ)/6<1-h^2*t by linarith) hs
  have hbound : t/b h<(6/5)*(361/25) := by nlinarith only [hu,hr,hr1]
  refine ⟨t/b h,hs,hbound,?_,?_⟩
  · field_simp [hb.ne']
  · rw [hr]
    field_simp [hb.ne']

end
end HTGeometry.ThetaRatioInfinity
