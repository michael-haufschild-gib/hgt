import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointDomain
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointCoordinate
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointWaveInverse

/-! A constructed full joint spatial wave response for every L² source and independent right-half-plane frequency. -/
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointWave
noncomputable section

/-- The complete joint variational equation on the proved differential domain. -/
def JointWaveSolution (w : ℂ) (F : SpatialSpace) (u : jointDomain) : Prop :=
  WaveFormSolution jointEmbedding w F u

/-- No angular mode or angular eigenvalue is supplied to this forced joint inverse. -/
theorem exists_bounded_jointWaveSolution (w : ℂ) (hw : 0 < w.re) (F : SpatialSpace) :
    ∃ u : jointDomain, JointWaveSolution w F u ∧
      ‖u‖ ≤ (waveCoercivity w)⁻¹ * ‖w‖ * ‖F‖ :=
  exists_bounded_waveFormSolution jointEmbedding jointEmbedding_norm_le w hw F

/-- The selected full energy response to the actual supplied spatial L² forcing. -/
def jointWaveResponse (w : ℂ) (hw : 0 < w.re) (F : SpatialSpace) : jointDomain :=
  (exists_bounded_jointWaveSolution w hw F).choose

theorem jointWaveResponse_spec (w : ℂ) (hw : 0 < w.re) (F : SpatialSpace) :
    JointWaveSolution w F (jointWaveResponse w hw F) :=
  (exists_bounded_jointWaveSolution w hw F).choose_spec.1

theorem jointWaveResponse_bound (w : ℂ) (hw : 0 < w.re) (F : SpatialSpace) :
    ‖jointWaveResponse w hw F‖ ≤ (waveCoercivity w)⁻¹ * ‖w‖ * ‖F‖ :=
  (exists_bounded_jointWaveSolution w hw F).choose_spec.2

/-- The physical scalar response obeys the decaying L² resolvent estimate. -/
theorem jointWaveResponse_scalar_bound (w : ℂ) (hw : 0 < w.re) (F : SpatialSpace) :
    ‖jointEmbedding (jointWaveResponse w hw F)‖ ≤ ‖F‖ / (w.re * ‖w‖) :=
  waveFormSolution_mass_bound jointEmbedding jointEmbedding_norm_le w hw F
    (jointWaveResponse_spec w hw F)

/-- All three actual derivative components occur in the forced equation, with their original signs. -/
theorem jointWaveSolution_gradient (w : ℂ) (F : SpatialSpace) (u : jointDomain) :
    JointWaveSolution w F u ↔ ∀ v : jointDomain,
      (∑ i : Fin 3, inner ℂ ((v : JointEnergySpace) i.succ) ((u : JointEnergySpace) i.succ)) +
        w^(2 : ℕ)*inner ℂ (jointEmbedding v) (jointEmbedding u) = inner ℂ (jointEmbedding v) F := by
  unfold JointWaveSolution WaveFormSolution
  apply forall_congr'
  intro v
  rw [joint_inner_decomposition]
  have he (a b : ℂ) : a+b+(w^(2 : ℕ)-1)*a = b+w^(2 : ℕ)*a := by ring
  rw [he]

theorem jointWaveSolution_unique (w : ℂ) (hw : 0 < w.re) (F : SpatialSpace)
    {u v : jointDomain} (hu : JointWaveSolution w F u) (hv : JointWaveSolution w F v) : u = v :=
  waveFormSolution_unique jointEmbedding jointEmbedding_norm_le w hw F hu hv

/-- The constructed response belongs to the actual unbounded operator domain and solves its
shifted equation. This is a graph-domain statement, not only a formal weak identity. -/
theorem jointWaveResponse_operator (w : ℂ) (hw : 0 < w.re) (F : SpatialSpace) :
    ∃ hmem : jointEmbedding (jointWaveResponse w hw F) ∈ jointEnergyOperator.domain,
      jointEnergyOperator ⟨jointEmbedding (jointWaveResponse w hw F),hmem⟩ +
        (w^(2 : ℕ)-1) • jointEmbedding (jointWaveResponse w hw F) = F := by
  let u := jointWaveResponse w hw F
  let y := F + (1-w^(2 : ℕ)) • jointEmbedding u
  have hJ : jointEmbedding.adjoint y = u := by
    apply ext_inner_left ℂ
    intro v
    rw [jointEmbedding.adjoint_inner_right]
    change inner ℂ (jointEmbedding v) (F+(1-w^(2 : ℕ)) • jointEmbedding u) = inner ℂ v u
    rw [inner_add_right,inner_smul_right]
    have he := jointWaveResponse_spec w hw F v
    change inner ℂ v u + (w^(2 : ℕ)-1)*inner ℂ (jointEmbedding v) (jointEmbedding u) =
      inner ℂ (jointEmbedding v) F at he
    linear_combination -he
  have hc : formEmbeddingCovariance jointEmbedding y = jointEmbedding u :=
    congrArg jointEmbedding hJ
  have happ := friedrichsFormOperator_apply_covariance jointEmbedding
    jointEmbedding_injective jointEmbedding_dense y
  have hm : jointEmbedding u ∈ jointEnergyOperator.domain := hc ▸ happ.1
  refine ⟨hm,?_⟩
  have he : jointEnergyOperator ⟨jointEmbedding u,hm⟩ = y := by
    have hx : (⟨jointEmbedding u,hm⟩ : jointEnergyOperator.domain) =
        ⟨formEmbeddingCovariance jointEmbedding y,happ.1⟩ := Subtype.ext hc.symm
    exact (congrArg jointEnergyOperator hx).trans happ.2
  change jointEnergyOperator ⟨jointEmbedding u,hm⟩ + (w^(2 : ℕ)-1) • jointEmbedding u = F
  rw [he]
  dsimp only [y]
  rw [add_assoc,← add_smul]
  have hz : (1-w^(2 : ℕ))+(w^(2 : ℕ)-1) = 0 := by ring
  rw [hz,zero_smul,add_zero]

end
end RHTower.D4BMJointWave
