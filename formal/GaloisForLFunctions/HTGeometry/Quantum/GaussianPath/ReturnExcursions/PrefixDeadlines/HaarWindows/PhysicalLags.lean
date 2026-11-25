import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HalfArc
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseFluctuations.MaximumMean
import GaloisForLFunctions.HTGeometry.ProjectiveSpectralRandomizedCircuitHardIntervalLaw

/-! # Difference of two affordable dates on the same translated phase orbit -/

open Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
open SharpOccupation
noncomputable section

private theorem inverse_fit {N j : ℕ} (V : unitaryGroup (Fin N → Bool) ℂ) {d : ℝ}
    (h : HasProjectiveCircuitApproximation N d j V.val) :
    HasProjectiveCircuitApproximation N d j (V⁻¹).val := by
  obtain ⟨z,hz,C,hC,he⟩ := h
  refine ⟨star z,by rwa [norm_star],C.adjoint,hC,?_⟩
  rw [TwoQubitCircuit.adjoint_eval]
  change ‖star V.val - star z • star C.eval.val‖ ≤ d
  rwa [←star_smul,←star_sub,norm_star]

/-- The unknown initial phase cancels when comparing times on the same
translate. Inverting the second fitted circuit preserves cost and error. -/
theorem shifted_capture_difference {N d : ℕ} (i : (Fin N → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Register N)) (j : ℕ) {e : ℝ} (he : e ∈ Ioo (0:ℝ) 2) :
    let V := hermitianEigenbasisUnitary H.2.isHermitian
    let E := H.2.isHermitian.eigenvalues ∘ i.symm
    let φ := RHTower.projectivePhysicalPhaseFlowHom E
    let A := projectiveContinuousCircuitCaptureTarget i V j (zeroGateArcTolerance (physicalArc e/2))
    ∀ y t u, φ t + y ∈ A → φ u + y ∈ A → t-u ∈ visitSet H (j+j) e := by
  intro V E φ A y t u ht hu
  let R := projectiveSpectralUnitary i V
  let x := physicalArc e
  let θ := Real.pi*(x/2)/2
  obtain ⟨hx,htol⟩ := FiniteRecords.physicalArc_full he
  have hθ : 0 ≤ θ := div_nonneg (mul_nonneg Real.pi_pos.le (half_pos hx.1).le) zero_le_two
  have htwice : 2*θ = Real.pi*x/2 := by dsimp only [θ]; ring
  have hmax : 2*θ ≤ Real.pi/2 := by
    rw [htwice]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right Real.pi_pos.le hx.2.le) zero_le_two
  have hquot : R (φ t + y) * (R (φ u + y))⁻¹ = R (φ (t-u)) := by
    apply (mul_inv_eq_iff_eq_mul).mpr
    apply Subtype.ext
    change projectiveSpectralMatrix i V _ = projectiveSpectralMatrix i V _ * projectiveSpectralMatrix i V _
    rw [PhaseFluctuations.phase_mul,map_sub]
    congr 1
    abel
  have h := AngularError.affordable_product_angle (R (φ t+y)).property ((R (φ u+y))⁻¹).property hθ hmax
    ((mem_projectiveContinuousCircuitCaptureTarget_iff i V j _ _).mp ht)
    (inverse_fit (R (φ u+y)) ((mem_projectiveContinuousCircuitCaptureTarget_iff i V j _ _).mp hu))
  change HasProjectiveCircuitApproximation N (2*Real.sin (2*θ)) (j+j)
    (R (φ t+y)*(R (φ u+y))⁻¹).val at h
  rw [hquot,htwice] at h
  apply (physical_circuit_approximation_iff_spectral_capture i H (j+j) e (t-u)).mpr
  apply (mem_projectiveContinuousCircuitCaptureTarget_iff i V (j+j) e _).mpr
  rwa [←htol]

#print axioms shifted_capture_difference
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
