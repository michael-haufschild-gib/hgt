import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticBarrierForcingTail

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Filter Topology

def quadraticNormalizedError (x : ℝ) : ℝ := quadraticSourceError x/t x
def quadraticNormalizedRate (x : ℝ) : ℝ :=
  HTGeometry.ThetaCriticalBarrier.qQuadraticRate ((k x)⁻¹) (u x^2) (boundaryRatio x)
def quadraticNormalizedSpeed (x : ℝ) : ℝ :=
  (k x/u x)*(quadraticNormalizedRate x*quadraticNormalizedError x+quadraticSourceForce x)

theorem dQuadraticNormalizedError {x : ℝ} (hx : 0<x) :
    HasDerivAt quadraticNormalizedError (quadraticNormalizedSpeed x) x := by
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  have ht := (t_pos hx.le).ne'
  have hd := (dQuadraticSourceError hx).div (dt hx.le) ht
  have hf := HTGeometry.ThetaCriticalBarrier.normalized_quadratic_field
    ((k x)⁻¹) (u x^2) (boundaryRatio x)
  rw [←quadraticSourceError_eq] at hf
  have he : HTGeometry.ThetaCriticalBarrier.quadraticField ((k x)⁻¹) (u x^2) (boundaryRatio x)=
      6*(quadraticNormalizedRate x*quadraticSourceError x+t x*quadraticSourceForce x)-
        12*u x^2*quadraticSourceError x := by
    dsimp [quadraticNormalizedRate,quadraticSourceForce,t]
    linarith only [hf]
  convert hd using 1 <;> first | rfl | skip
  unfold quadraticNormalizedSpeed quadraticSourceSpeed quadraticNormalizedError
  rw [he]
  field_simp [hu,ht]
  ring

theorem quadraticNormalizedRate_tendsto :
    Tendsto quadraticNormalizedRate atTop (𝓝 (54:ℝ)) := by
  let f : ℝ×ℝ×ℝ → ℝ := fun p => HTGeometry.ThetaCriticalBarrier.qQuadraticRate p.1 p.2.1 p.2.2
  have hc : Continuous f := by
    dsimp [f,HTGeometry.ThetaCriticalBarrier.qQuadraticRate,HTGeometry.ThetaCriticalBarrier.A,
      HTGeometry.ThetaCriticalBarrier.b]
    fun_prop
  have hp := inverse_k_tendsto_zero.prodMk_nhds
    (drift_square_tendsto.prodMk_nhds boundaryRatio_tendsto)
  have hl := (hc.tendsto (0,9,(1/12:ℝ))).comp hp
  convert hl using 1 <;> first | rfl | skip
  norm_num [f,HTGeometry.ThetaCriticalBarrier.qQuadraticRate,HTGeometry.ThetaCriticalBarrier.A,
    HTGeometry.ThetaCriticalBarrier.b]

theorem quadraticNormalizedError_lower {x : ℝ} (hx : 1≤x) :
    -(3/(2*u 1^2))^2≤quadraticNormalizedError x := by
  have hx0 : 0<x := by linarith
  have ht := t_pos hx0.le
  have hc := criticalError_pos hx0
  have he : quadraticNormalizedError x=criticalError x/t x-(boundaryRatio x)^2 := by
    unfold quadraticNormalizedError quadraticSourceError
    field_simp [ht.ne']
  have hb := boundaryRatio_bound hx
  have hq := boundaryRatio_nonneg hx0
  have hb0 : 0≤3/(2*u 1^2) := by positivity
  have hs : (boundaryRatio x)^2≤(3/(2*u 1^2))^2 := by nlinarith only [hq,hb,hb0]
  have hp : 0≤criticalError x/t x := (div_pos hc ht).le
  rw [he]
  linarith only [hs,hp]

end
end RHTower.ThetaCuspModularRatio
