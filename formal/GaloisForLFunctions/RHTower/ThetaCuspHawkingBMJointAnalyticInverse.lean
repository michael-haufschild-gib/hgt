import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointResponse
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Holomorphy of the original energy-form inverse with independent Laplace frequency. -/
namespace RHTower.D4BMJointWave
open scoped ComplexConjugate
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Invertibility of the original pencil is derived from its proved rotated coercivity. -/
theorem waveFormOperator_isUnit (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (w : ℂ) (hw : 0 < w.re) : IsUnit (waveFormOperator J w) := by
  obtain ⟨S,hS,hT,_⟩ := rotatedWaveOperator_inverse J hJ w hw
  let T : V →L[ℂ] V := S.comp (conj w • ContinuousLinearMap.id ℂ V)
  have h0 : conj w ≠ 0 := by simpa using (show w ≠ 0 from fun h => by simp [h] at hw)
  refine ⟨⟨waveFormOperator J w,T,?_,?_⟩,rfl⟩
  · apply ContinuousLinearMap.ext
    intro v
    change waveFormOperator J w (T v) = v
    apply smul_right_injective V h0
    exact hS (conj w • v)
  · apply ContinuousLinearMap.ext
    intro v
    exact hT v

/-- Total operator-valued expression for the inverse; its physical values lie in Re(w)>0. -/
def waveEnergyInverse (J : V →L[ℂ] H) (w : ℂ) : V →L[ℂ] V :=
  Ring.inverse (waveFormOperator J w)

theorem waveEnergyInverse_right (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (w : ℂ) (hw : 0 < w.re) (v : V) :
    waveFormOperator J w (waveEnergyInverse J w v) = v := by
  exact congrArg (fun A : V →L[ℂ] V => A v)
    (Ring.mul_inverse_cancel _ (waveFormOperator_isUnit J hJ w hw))

theorem waveEnergyInverse_left (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (w : ℂ) (hw : 0 < w.re) (v : V) :
    waveEnergyInverse J w (waveFormOperator J w v) = v := by
  exact congrArg (fun A : V →L[ℂ] V => A v)
    (Ring.inverse_mul_cancel _ (waveFormOperator_isUnit J hJ w hw))

theorem waveEnergyInverse_solution (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (w : ℂ) (hw : 0 < w.re) (F : H) :
    WaveFormSolution J w F (waveEnergyInverse J w (J.adjoint F)) := by
  intro v
  rw [← waveFormOperator_inner,waveEnergyInverse_right J hJ w hw,J.adjoint_inner_right]

/-- The inverse is holomorphic as a bounded operator on the actual energy space. -/
theorem waveEnergyInverse_differentiableAt (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (w : ℂ) (hw : 0 < w.re) : DifferentiableAt ℂ (waveEnergyInverse J) w := by
  apply (differentiableAt_inverse (waveFormOperator_isUnit J hJ w hw)).comp
  unfold waveFormOperator
  fun_prop

/-- The holomorphic formula is exactly the original selected response. -/
theorem waveEnergyInverse_jointResponse (w : ℂ) (hw : 0 < w.re) (F : SpatialSpace) :
    waveEnergyInverse jointEmbedding w (jointEmbedding.adjoint F) =
      jointWaveResponse w hw F :=
  waveFormSolution_unique jointEmbedding jointEmbedding_norm_le w hw F
    (waveEnergyInverse_solution jointEmbedding jointEmbedding_norm_le w hw F)
    (jointWaveResponse_spec w hw F)

/-- Actual spatial resolvent, defined independently of any frequency proof term. -/
def waveSpatialResolvent (J : V →L[ℂ] H) (w : ℂ) : H →L[ℂ] H :=
  J.comp ((waveEnergyInverse J w).comp J.adjoint)

theorem waveSpatialResolvent_bound (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (w : ℂ) (hw : 0 < w.re) (F : H) :
    ‖waveSpatialResolvent J w F‖ ≤ ‖F‖ / (w.re * ‖w‖) :=
  waveFormSolution_mass_bound J hJ w hw F (waveEnergyInverse_solution J hJ w hw F)

theorem waveSpatialResolvent_apply_differentiableAt (J : V →L[ℂ] H)
    (hJ : ∀ v, ‖J v‖ ≤ ‖v‖) (F : H) (w : ℂ) (hw : 0 < w.re) :
    DifferentiableAt ℂ (fun z => waveSpatialResolvent J z F) w :=
  J.differentiableAt.comp w
    ((waveEnergyInverse_differentiableAt J hJ w hw).clm_apply (differentiableAt_const _))

end
end RHTower.D4BMJointWave
