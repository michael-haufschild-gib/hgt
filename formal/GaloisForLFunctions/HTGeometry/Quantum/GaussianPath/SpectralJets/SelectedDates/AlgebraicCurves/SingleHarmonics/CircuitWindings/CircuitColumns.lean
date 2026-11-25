import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.PhaseExtraction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.EigenlineCenter
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.ChordArc
import GaloisForLFunctions.HTGeometry.ReplicaHilbertCoareaIncidenceLaw
import GaloisForLFunctions.HTGeometry.ObserverInvisibleRayPreservation
import GaloisForLFunctions.HTGeometry.SelfAdjointPropagator

/-! # Operator approximation forces one corrected arc on all spectral lines -/

open Matrix Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open SharpOccupation
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Correct the evolution angle on each eigenspace by the argument of
the fixed circuit's diagonal entry. Its remaining phase must be close to
the same scalar on every line, with the original operator tolerance. -/
theorem circuit_column_chord {H W : Matrix I I ℂ} {E : I→ℝ} {v : I→I→ℂ}
    (he : IsOrthoEigenBasis H v E) (hs : Function.Injective E) (hW : W∈unitary (Matrix I I ℂ))
    (t : ℝ) {c : ℂ} (hc : ‖c‖=1) {ε : ℝ} (hε : ε<sqrt 2)
    (hfit : ‖unitaryEvolution H t-c • W‖≤ε) (j : I) :
    ‖Complex.exp (((-t*E j-(circuitEntry E H W j).arg:ℝ):ℂ)*Complex.I)-
      Complex.exp ((c.arg:ℂ)*Complex.I)‖≤ε := by
  let A := c⁻¹ • unitaryEvolution H t
  let θ := -t*E j
  let z := Complex.exp (((θ-c.arg:ℝ):ℂ)*Complex.I)
  have hc₀ : c≠0 := fun hz => by simp [hz] at hc
  have hnorm : ‖A-W‖≤ε := calc
    ‖A-W‖ = ‖c⁻¹ • (unitaryEvolution H t-c • W)‖ := by
      rw [smul_sub,smul_smul,inv_mul_cancel₀ hc₀,one_smul]
    _ = ‖unitaryEvolution H t-c • W‖ := by rw [norm_smul,norm_inv,hc,inv_one,one_mul]
    _ ≤ ε := hfit
  have hpolar : Complex.exp ((c.arg:ℂ)*Complex.I)=c := by simpa only [hc,Complex.ofReal_one,one_mul] using Complex.norm_mul_exp_arg_mul_I c
  have hz : ‖z‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hphase : z=c⁻¹*Complex.exp (-(Complex.I*((t:ℂ)*(E j:ℂ)))) := by
    dsimp only [z,θ]
    rw [Complex.ofReal_sub,sub_mul,Complex.exp_sub,hpolar,div_eq_mul_inv,mul_comm _ c⁻¹]
    congr 2
    push_cast
    ring
  have heig : A *ᵥ v j=z • v j := by
    rw [show A=c⁻¹ • unitaryEvolution H t from rfl,Matrix.smul_mulVec,
      QuantumAlg.unitaryEvolution_mulVec_of_eigenvector (he.eigen j),smul_smul,hphase]
  let u := WithLp.toLp 2 (v j)
  let w := WithLp.toLp 2 (W *ᵥ v j)
  have hu : ‖u‖=1 := by
    rw [norm_eq_sqrt_re_inner (𝕜:=ℂ)]
    change sqrt ((inner ℂ (WithLp.toLp 2 (v j)) (WithLp.toLp 2 (v j))).re)=1
    rw [inner_toLp_eq_finiteComplexInner,he.orth]
    simp
  have hw : ‖w‖=1 := by
    let Φ := Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ)
    rw [show w=(Φ W) u from (Matrix.toEuclideanCLM_toLp W (v j)).symm]
    exact (norm_apply_of_mem_unitary (Unitary.map_mem Φ hW) u).trans hu
  have hd := (A-W).l2_opNorm_mulVec u
  change ‖WithLp.toLp 2 ((A-W) *ᵥ v j)‖≤‖A-W‖*‖u‖ at hd
  rw [Matrix.sub_mulVec,heig,WithLp.toLp_sub,WithLp.toLp_smul,hu,mul_one] at hd
  have hdist : ‖z • u-w‖≤ε := hd.trans hnorm
  have h := (sharp_line_chord u w hu hw z hz (hdist.trans_lt hε)).trans hdist
  change ‖z-unitPhase (inner ℂ (WithLp.toLp 2 (v j)) (WithLp.toLp 2 (W *ᵥ v j)))‖≤ε at h
  rw [inner_toLp_eq_finiteComplexInner,←circuitEntry_eq he hs] at h
  rw [chord_exchange]
  exact h

/-- An approximation by any scalar multiple of W gives one enclosing arc
after correcting the phases. The line corrections do not use the scalar. -/
theorem circuit_corrected_arc [Nonempty I] {H W : Matrix I I ℂ} {E : I→ℝ} {v : I→I→ℂ}
    (he : IsOrthoEigenBasis H v E) (hs : Function.Injective E) (hW : W∈unitary (Matrix I I ℂ))
    (t : ℝ) {c : ℂ} (hc : ‖c‖=1) {ε : ℝ} (hε : ε∈Ioo (0:ℝ) (sqrt 2))
    (hfit : ‖unitaryEvolution H t-c • W‖≤ε) :
    (fun j => (((-t*E j-(circuitEntry E H W j).arg)/(2*π):ℝ):UnitAddCircle))∈enclosingUnitArc (physicalArc ε) :=
  enclosing_of_common_chord _ c.arg hε (circuit_column_chord he hs hW t hc hε.2 hfit)

#print axioms circuit_corrected_arc
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
