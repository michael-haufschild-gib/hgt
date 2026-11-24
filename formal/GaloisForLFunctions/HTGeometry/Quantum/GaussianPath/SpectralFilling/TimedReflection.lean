import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.Reflections.VariablePrecision

/-! # A phase filling horizon bounds first saturation and a zero-gate return -/
open Set Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- The fixed angular clock tracks every reflection to operator error 1/80. -/
theorem phase_interval_approaches_reflection {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n)) (a b : ℝ)
    (hphase : ∀ c : Fin d → ℝ, ∃ t ∈ Icc a b, ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c j) < 1/80)
    (x : Fin d → Bool) :
    ∃ t ∈ Icc a b, ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖unitaryEvolution H.val t-z • anchoredSpectralBooleanReflection e (hermitianEigenbasisUnitary H.2.isHermitian) x‖ ≤ 1/80 :=
  phase_interval_approaches_reflection_at_error (by norm_num : 0 ≤ (1/80:ℝ)) e H a b hphase x

/-- Angular resolution 1/80 ensures a physical empty-circuit visit at error 1/10. -/
theorem phase_interval_contains_zero_gate {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n)) (a b : ℝ)
    (hphase : ∀ c : Fin d → ℝ, ∃ t ∈ Icc a b, ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c j) < 1/80) :
    ∃ t ∈ Icc a b, HasProjectiveCircuitApproximation n (1/10:ℝ) 0 (unitaryEvolution H.val t) := by
  obtain ⟨t,ht,z,hz,C,hC,he⟩ := phase_interval_zero_gate_at_error (by norm_num : 0 ≤ (1/80:ℝ)) e H a b hphase
  exact ⟨t,ht,z,hz,C,hC,he.trans (by norm_num)⟩

/-- A horizon that fills the relative phase torus to 1/80 reaches the robust
9/80 circuit threshold. At double the resulting time the whole unitary is
within 1/10 of a zero-gate circuit. -/
theorem phase_horizon_reaches_robust_threshold {n d P : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n)) (G : ℝ)
    (hent : atMostQuarterCircuitEntropyBound n P < ((2^d:ℕ):ℝ))
    (hphase : ∀ c : Fin d → ℝ, ∃ t ∈ Icc 0 G, ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c j) < 1/80) :
    ∃ t ∈ Icc 0 G, 9/80 ≤ orbitCircuitDistance H P t ∧
      HasProjectiveCircuitApproximation n (1/10:ℝ) 0 (unitaryEvolution H.val (2*t)) := by
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  obtain ⟨x,hx⟩ := exists_anchoredSpectralBooleanReflection_atMostCircuit_fixedError e V hent
  let J := anchoredSpectralBooleanReflection e V x
  obtain ⟨t,ht,z,hz,hclose⟩ := phase_interval_approaches_reflection e H 0 G hphase x
  change ‖unitaryEvolution H.val t-z • J‖ ≤ 1/80 at hclose
  refine ⟨t,ht,?_,?_⟩
  · by_contra! hc
    obtain ⟨a,ha,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val t) P (9/80:ℝ)).mpr hc.le
    have hfar := hx (z⁻¹*a) (by rw [norm_mul,norm_inv,hz,ha,inv_one,one_mul]) C hC
    have hrotate : z • (J-(z⁻¹*a) • (C.eval : Reg n)) = z • J-a • (C.eval : Reg n) := by
      rw [smul_sub,smul_smul,← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)),one_mul]
    have hsep : 3/20 < ‖z • J-a • (C.eval : Reg n)‖ := by rw [← hrotate,norm_smul,hz,one_mul]; exact hfar
    rw [norm_sub_rev] at hclose
    linarith only [hsep,hclose,he,norm_sub_le_norm_sub_add_norm_sub (z • J) (unitaryEvolution H.val t) (a • (C.eval : Reg n))]
  · let w : Circle := ⟨z,by change z ∈ Metric.sphere (0:ℂ) 1; simpa using hz⟩
    obtain ⟨a,ha,C,hC,herr⟩ := spectral_sign_doubled_time_zero_gate e V x H t w
    refine ⟨a,ha,C,hC,herr.trans ?_⟩
    change 2*‖unitaryEvolution H.val t-z • J‖ ≤ (1/10:ℝ)
    linarith only [hclose]

#print axioms phase_horizon_reaches_robust_threshold
end
end GaloisForLFunctions.HTGeometry
