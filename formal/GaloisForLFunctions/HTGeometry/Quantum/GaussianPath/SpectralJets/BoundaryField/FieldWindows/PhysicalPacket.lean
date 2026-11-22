import GaloisForLFunctions.HTGeometry.LagrangeSpectralProjector
import GaloisForLFunctions.HTGeometry.ObserverInvisibleRayPreservation
import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.FixedDate
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortArcHaar

/-! # Physical evolution in continuously ordered spectral directions -/
open Matrix Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
noncomputable section
variable {I : Type} [Fintype I] [DecidableEq I]

private def phaseWeight (r : I) (x : UnitAddTorus {j // j≠r}) (j : I) : ℂ :=
  fourier 1 (relativeUnitPhasePacket r x j)

private theorem weight_norm (r : I) (x : UnitAddTorus {j // j≠r}) (j : I) : ‖phaseWeight r x j‖=1 :=
  Circle.norm_coe _

private theorem weight_at_clock (E : I→ℝ) (r j : I) (t : ℝ) :
    anchorPhase E r t*phaseWeight r (finiteClockPhasePoint (projectiveFrequency (fun i => -E i) r) t) j =
      anchorPhase E j t := by
  rcases eq_or_ne j r with rfl | hj
  · simp [phaseWeight,relativeUnitPhasePacket]
  · simp only [phaseWeight,relativeUnitPhasePacket,dif_pos hj,finiteClockPhasePoint,projectiveFrequency,
      fourier_coe_apply,anchorPhase,←Complex.exp_add]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero] <;> ring

/-- The projective phase packet represented with phase one on the anchor eigenspace. -/
def physicalPacket (H : Matrix I I ℂ) (E : I→ℝ) (r : I) (x : UnitAddTorus {j // j≠r}) : Matrix I I ℂ :=
  ∑ j, phaseWeight r x j • lagrangeSpectralProjector E j H

private theorem packet_on_eigenline {H : Matrix I I ℂ} {E : I→ℝ} {e : I→I→ℂ}
    (he : IsOrthoEigenBasis H e E) (hi : Function.Injective E) (r : I)
    (x : UnitAddTorus {j // j≠r}) (j : I) :
    physicalPacket H E r x *ᵥ e j=phaseWeight r x j • e j := by
  classical
  rw [physicalPacket,Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec,lagrangeSpectralProjector_mulVec_eigen he hi]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hn
    simp [Ne.symm hn]
  · simp

/-- An arbitrary labeling of a simple eigensystem reconstructs the
actual matrix at every time, up to the anchor phase. -/
theorem evolution_eq_physicalPacket {H : Matrix I I ℂ} {E : I→ℝ} {e : I→I→ℂ}
    (he : IsOrthoEigenBasis H e E) (hi : Function.Injective E) (r : I) (t : ℝ) :
    unitaryEvolution H t=anchorPhase E r t • physicalPacket H E r
      (finiteClockPhasePoint (projectiveFrequency (fun i => -E i) r) t) := by
  let x := finiteClockPhasePoint (projectiveFrequency (fun i => -E i) r) t
  have hline (j : I) : unitaryEvolution H t *ᵥ e j=(anchorPhase E r t • physicalPacket H E r x) *ᵥ e j := by
    rw [QuantumAlg.unitaryEvolution_mulVec_of_eigenvector (he.eigen j),Matrix.smul_mulVec,packet_on_eigenline he hi,smul_smul]
    rw [show anchorPhase E r t*phaseWeight r x j=anchorPhase E j t from weight_at_clock ..]
    rfl
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  conv_lhs => rw [←he.complete v]
  conv_rhs => rw [←he.complete v]
  simp only [Matrix.mulVec_sum,Matrix.mulVec_smul,hline]

theorem continuous_physicalPacket (H : Matrix I I ℂ) (E : I→ℝ) (r : I) : Continuous (physicalPacket H E r) := by
  apply continuous_finsetSum
  intro j _
  apply Continuous.smul _ continuous_const
  apply (fourier 1).continuous.comp
  by_cases hj : j≠r
  · simpa only [relativeUnitPhasePacket,dif_pos hj] using (continuous_apply (⟨j,hj⟩ : {i : I // i≠r}))
  · simp only [relativeUnitPhasePacket,dif_neg hj]
    exact continuous_const

/-- Freezing the eigenspaces gives an error bound independent of every phase. -/
theorem norm_physicalPacket_sub (H K : Matrix I I ℂ) (E F : I→ℝ) (r : I) (x : UnitAddTorus {j // j≠r}) :
    ‖physicalPacket H E r x-physicalPacket K F r x‖ ≤
      ∑ j, ‖lagrangeSpectralProjector E j H-lagrangeSpectralProjector F j K‖ := by
  rw [physicalPacket,physicalPacket,←Finset.sum_sub_distrib]
  simp_rw [←smul_sub]
  refine (norm_sum_le _ _).trans_eq ?_
  simp only [norm_smul,weight_norm,one_mul]

/-- On the simple locus the error from freezing the eigenspaces vanishes
uniformly over the projective phase torus. -/
theorem packet_freezing {K : ℝ→Matrix I I ℂ} {E : ℝ→I→ℝ} (hK : Continuous K)
    (hE : Continuous E) {b : ℝ} (hb : Function.Injective (E b)) (r : I) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z in 𝓝 b, ∀ x, ‖physicalPacket (K z) (E z) r x-physicalPacket (K b) (E b) r x‖ < δ := by
  let P (z : ℝ) (j : I) := lagrangeSpectralProjector (E z) j (K z)
  have hc : ContinuousAt (fun z => ∑ j, ‖P z j-P b j‖) b :=
    continuousAt_finsetSum _ fun j _ => ((continuousAt_lagrangeSpectralProjector hE hK j hb).sub continuousAt_const).norm
  have hzero : (∑ j, ‖P b j-P b j‖)=0 := by simp
  filter_upwards [hc.tendsto.eventually_lt_const (hzero.trans_lt hδ)] with z hz
  exact fun x => (norm_physicalPacket_sub ..).trans_lt hz

#print axioms packet_freezing
#print axioms evolution_eq_physicalPacket
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
