import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.OrbitMaximumAtError

/-! # The maximum physical circuit cost on a Gaussian phase orbit -/
open Set MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- The orbit maximum at projective operator error one tenth. -/
abbrev IsRecurrentOrbitCircuitMaximum (H : selfAdjoint (Reg n)) (m : ℕ) : Prop :=
  IsRecurrentOrbitCircuitMaximumAt H (1/10) m

private theorem circuit_approx_phase (n s : ℕ) (ε : ℝ) {X : Reg n} (z : ℂ) (hz : ‖z‖ = 1) :
    HasProjectiveCircuitApproximation n ε s (z • X) ↔ HasProjectiveCircuitApproximation n ε s X := by
  have move (Y : Reg n) (a : ℂ) (ha : ‖a‖ = 1)
      (h : HasProjectiveCircuitApproximation n ε s Y) :
      HasProjectiveCircuitApproximation n ε s (a • Y) := by
    obtain ⟨c,hc,C,hC,he⟩ := h
    refine ⟨a*c,by rw [norm_mul,ha,hc,one_mul],C,hC,?_⟩
    rwa [← smul_smul,← smul_sub,norm_smul,ha,one_mul]
  refine ⟨fun h => ?_,move X z hz⟩
  have h0 : z ≠ 0 := by intro hz0; simp [hz0] at hz
  simpa only [smul_smul,inv_mul_cancel₀ h0,one_smul] using
    move (z • X) z⁻¹ (by rw [norm_inv,hz,inv_one]) h

/-- Physical circuit affordability is precisely capture of the relative
spectral phases, also when the spectrum has rational relations. -/
theorem physical_circuit_approximation_iff_spectral_capture {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n)) (s : ℕ) (ε t : ℝ) :
    HasProjectiveCircuitApproximation n ε s (unitaryEvolution (H : Reg n) t) ↔
      RHTower.projectivePhysicalPhaseFlow (fun i => H.2.isHermitian.eigenvalues (e.symm i)) t ∈
        projectiveContinuousCircuitCaptureTarget e (hermitianEigenbasisUnitary H.2.isHermitian) s ε := by
  rw [unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix e H.2.isHermitian]
  exact (circuit_approx_phase n s ε _ (by simp [Complex.norm_exp])).trans
    (mem_projectiveContinuousCircuitCaptureTarget_iff e _ s ε _).symm

/-- At every error, the budgets covering a full-rank physical orbit are
exactly the budgets covering every independently assigned energy phase.
Thus the orbit maximum depends on the eigenbasis and the gate model. -/
theorem uniform_circuit_budget_iff_all_spectral_phases {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i)))
    (s : ℕ) (ε : ℝ) :
    (∀ t : ℝ, HasProjectiveCircuitApproximation n ε s (unitaryEvolution (H : Reg n) t)) ↔
      ∀ θ : Fin d → UnitAddCircle, HasProjectiveCircuitApproximation n ε s
        (projectiveSpectralMatrix e (hermitianEigenbasisUnitary H.2.isHermitian) θ) := by
  let E := fun i => H.2.isHermitian.eigenvalues (e.symm i)
  let Φ := RHTower.projectivePhysicalPhaseFlowHom E
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let A := projectiveContinuousCircuitCaptureTarget e V s ε
  have ht (t : ℝ) : HasProjectiveCircuitApproximation n ε s (unitaryEvolution (H : Reg n) t) ↔ Φ t ∈ A :=
    physical_circuit_approximation_iff_spectral_capture e H s ε t
  constructor
  · intro h θ
    have hs : range Φ ⊆ A := by rintro y ⟨t,rfl⟩; exact (ht t).mp (h t)
    have hc := isClosed_projectiveContinuousCircuitCaptureTarget e V s ε
    exact (mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε θ).mp
      (closure_minimal hs hc (RHTower.denseRange_projectivePhysicalPhaseFlowHom E hmax θ))
  · intro h t
    exact (ht t).mpr ((mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε _).mpr (h _))

#print axioms uniform_circuit_budget_iff_all_spectral_phases

/-- A full Gaussian nearest-neighbour draw attains its own maximum minimum
gate count on recurrent intervals. This maximum exceeds the exponential
budget, and the same draw remains distinguishable from Haar at all times. -/
theorem gaussianPath_attained_circuit_maximum_and_permanent_locality :
    ∀ᶠ L : ℕ in Filter.atTop,
    ∀ᵐ p ∂(centredProductGaussian (Fin
      (StaticLocalLaboratoryComplexityGrowthLaw.nearestNeighborPathLocalParameterCount L)) 1),
      let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
      (∃ m > excursionGateBudget (L*2), IsRecurrentOrbitCircuitMaximum H m) ∧
        RHTower.NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  filter_upwards [Filter.eventually_ge_atTop 1,gaussianPath_translatedCircuitExcursions_and_permanentLocality]
    with L hL hgauss
  filter_upwards [hgauss] with p hp
  let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
  obtain ⟨m,hm⟩ := twoLocal_exists_recurrent_maximum_at (by omega) H
    (RHTower.pairQubitProjectivePauliSeed_hasPauliWeightAtMost_two L p) (1/10) (by norm_num)
  refine ⟨⟨m,?_,hm⟩,hp.2⟩
  obtain ⟨G,_,hb⟩ := hp.1
  obtain ⟨u,_,hu⟩ := hb 0
  have hw : 0 ≤ translatedExcursionWidth (L*2) ‖(H : Reg (L*2))‖ := by
    unfold translatedExcursionWidth; positivity
  obtain ⟨c,hc,C,hC,he⟩ := hm.1 u
  by_contra! h
  exact (not_lt_of_ge he) (hu u ⟨le_rfl,le_add_of_nonneg_right hw⟩ c hc C (hC.trans h))

#print axioms gaussianPath_attained_circuit_maximum_and_permanent_locality

end
end GaloisForLFunctions.HTGeometry
