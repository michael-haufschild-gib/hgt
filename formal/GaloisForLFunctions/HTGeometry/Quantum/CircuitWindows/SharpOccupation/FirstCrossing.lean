import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteIntervals

/-! # The first robust Hilbert-scale crossing from the identity -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

private theorem dated_crossing {n j : ℕ} (H : selfAdjoint (Register n)) {p G : ℝ}
    (hp : 0 ≤ p) (hsmall : p < 1) (hG : 0 ≤ G)
    (hocc : ∀ T : ℝ, 0 ≤ T → volume.real (visitSet H j (1/8) ∩ Icc 0 T) ≤ p*(T+G)) :
    ∃ σ : ℝ, 0 < σ ∧ orbitCircuitDistance H j σ = 9/80 ∧
      (∀ t ∈ Ico 0 σ, orbitCircuitDistance H j t < 9/80) ∧
      (1-p)*σ ≤ p*G := by
  let f := orbitCircuitDistance H j
  have hcont : Continuous f := (orbitCircuitDistance_lipschitz H j).continuous
  have hzero : f 0 ≤ 0 := by
    apply (hasProjectiveCircuitApproximation_iff_infDist _ j 0).mp
    refine ⟨1,norm_one,TwoQubitCircuit.one n,Nat.zero_le _,?_⟩
    simp [TwoQubitCircuit.one_eval,unitaryEvolution]
  have hwhole (T : ℝ) (hT : 0 ≤ T) (h : ∀ t ∈ Icc 0 T, f t ≤ 1/8) : T ≤ p*(T+G) := by
    have ht := hocc T hT
    have hsub : Icc 0 T ⊆ visitSet H j (1/8) := fun t ht =>
      (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr (h t ht)
    rw [inter_eq_right.mpr hsub,Real.volume_real_Icc_of_le hT,sub_zero] at ht
    exact ht
  let R := (p*G+1)/(1-p)
  have hden : 0 < 1-p := sub_pos.mpr hsmall
  have hR : 0 ≤ R := div_nonneg (by positivity) hden.le
  have hreach : ∃ v ∈ Icc 0 R, 1/8 < f v := by
    by_contra! hn
    have hh := hwhole R hR hn
    have hpay : R*(1-p) = p*G+1 := div_mul_cancel₀ _ hden.ne'
    linarith only [hh,hpay]
  obtain ⟨v,hv,hh⟩ := hreach
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hv.1 hcont.continuousOn
    (show 9/80 ∈ Icc (f 0) (f v) from ⟨hzero.trans (by norm_num),(by norm_num : (9/80:ℝ) ≤ 1/8).trans hh.le⟩)
  let K := Icc 0 v ∩ f ⁻¹' {9/80}
  obtain ⟨hm,hmin⟩ := (isCompact_Icc.inter_right (isClosed_singleton.preimage hcont) : IsCompact K).isLeast_sInf
    (show K.Nonempty from ⟨t,ht,he⟩)
  let σ := sInf K
  have hσ : f σ = 9/80 := hm.2
  have hpos : 0 < σ := lt_of_le_of_ne hm.1.1 (by
    intro heq
    have hz : f σ ≤ 0 := heq ▸ hzero
    linarith only [hz,hσ])
  have hprior (u : ℝ) (hu : u ∈ Ico 0 σ) : f u < 9/80 := by
    by_contra! hc
    obtain ⟨w,hw,he⟩ := intermediate_value_Icc hu.1 hcont.continuousOn
      (show 9/80 ∈ Icc (f 0) (f u) from ⟨hzero.trans (by norm_num),hc⟩)
    have hle := hmin (show w ∈ K from ⟨⟨hw.1,hw.2.trans (hu.2.le.trans hm.1.2)⟩,he⟩)
    exact (not_lt_of_ge hle) (hw.2.trans_lt hu.2)
  have hh := hwhole σ hpos.le (fun t ht => ((lt_or_eq_of_le ht.2).elim
    (fun h => (hprior t ⟨ht.1,h⟩).le) (fun h => h ▸ hσ.le)).trans (by norm_num))
  exact ⟨σ,hpos,hσ,hprior,by linarith only [hh]⟩

/-- On the same chain and for every budget through D/[16(N+1)], the
genuine first crossing from the identity satisfies the corrected deadline. -/
theorem gaussian_hilbert_first_crossing :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let p := (3/8:ℝ)^D
      let G := (2:ℝ)^(D^c)
      ∀ j ≤ D/(16*(N+1)), ∃ σ : ℝ, 0 < σ ∧ orbitCircuitDistance H j σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H j t < 9/80) ∧ (1-p)*σ ≤ p*G := by
  obtain ⟨c,hc⟩ := gaussian_finite_interval_occupation
  refine ⟨c,?_⟩
  filter_upwards [hc] with ω hw
  filter_upwards [hw] with k hk
  intro N D H p G j hj
  have hD : D ≠ 0 := by dsimp [D]; positivity
  have hp : 0 ≤ p := pow_nonneg (by norm_num : (0:ℝ) ≤ 3/8) D
  have hsmall : p < 1 := pow_lt_one₀ (by norm_num : (0:ℝ) ≤ 3/8) (by norm_num) hD
  apply dated_crossing (j := j) (G := G) H hp hsmall (by dsimp [G]; positivity)
  intro T hT
  simpa only [zero_add] using hk j hj 0 T hT

#print axioms gaussian_hilbert_first_crossing
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
