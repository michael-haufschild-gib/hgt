import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TrajectoryProfiles.ReplayDensity

/-! # The cost of covering all physical gate-distance profiles -/
open Filter Set MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TrajectoryProfiles
open SharpOccupation
noncomputable section

/-- Every finite list of dates representing the entire trajectory at
precision η needs at least the reciprocal of the exact scalar density. -/
theorem number_of_samples {N : ℕ} (H : selfAdjoint (Register N))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) {η : ℝ} (hη : 0 < η) (hsmall : η < sqrt 2)
    {I : Type*} [Fintype I] (u : I → ℝ)
    (hcover : ∀ v : ℝ, ∃ i, HasProjectiveCircuitApproximation N η 0 (unitaryEvolution H.val (v-u i))) :
    1 ≤ (Fintype.card I:ℝ)*(((2^N:ℕ):ℝ)*(physicalArc η)^(2^N-1:ℕ)) := by
  classical
  let p := ((2^N:ℕ):ℝ)*(physicalArc η)^(2^N-1:ℕ)
  let S (i : I) := (fun z : ℝ => z-u i) ⁻¹' visitSet H 0 η
  let f (i : I) (T : ℝ) := volume.real (S i ∩ Icc 0 T)/T
  have hlim (i : I) : Tendsto (f i) atTop (𝓝 p) := by
    simpa only [f,S,sub_zero] using (translated_scalar_fraction H hi hη hsmall (u i)).2 0
  have hsum := tendsto_finsetSum (s:=Finset.univ) (fun i _ => hlim i)
  have hl : Tendsto (fun T : ℝ => ∑ i, f i T) atTop (𝓝 ((Fintype.card I:ℝ)*p)) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hsum
  apply ge_of_tendsto hl
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  have hsub : Icc (0:ℝ) T ⊆ ⋃ i, S i ∩ Icc 0 T := by
    intro v hv
    obtain ⟨i,hi⟩ := hcover v
    exact mem_iUnion.mpr ⟨i,hi,hv⟩
  have hun : (⋃ i, S i ∩ Icc 0 T) ⊆ Icc 0 T := iUnion_subset fun _ => inter_subset_right
  have h := (measureReal_mono (μ:=volume) hsub (measure_ne_top_of_subset hun measure_Icc_lt_top.ne)).trans
    (measureReal_iUnion_fintype_le _)
  rw [Real.volume_real_Icc_of_le hT.le,sub_zero] at h
  dsimp only [f]
  rw [←Finset.sum_div,le_div_iff₀ hT,one_mul]
  exact h

/-- Covering every translated profile with one continuous observation
requires enough scalar balls to cover the orbit after discretizing the
observation at step δ/(1+‖H‖). This holds for every observation origin. -/
theorem duration_of_cover {N : ℕ} (H : selfAdjoint (Register N))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (a : ℝ) {G η δ : ℝ} (hG : 0 ≤ G) (hη : 0 ≤ η) (hδ : 0 < δ) (hsmall : η+δ < sqrt 2)
    (hcover : ∀ v : ℝ, ∃ z ∈ Icc a (a+G), ∀ t : ℝ, ∀ s : ℕ,
      |orbitCircuitDistance H s (v+t)-orbitCircuitDistance H s (z+t)| ≤ η) :
    1 ≤ (1+G*(1+‖H.val‖)/δ)*(((2^N:ℕ):ℝ)*(physicalArc (η+δ))^(2^N-1:ℕ)) := by
  let L := 1+‖H.val‖
  let h := δ/L
  have hL : 0 < L := add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)
  have hh : 0 < h := div_pos hδ hL
  let M := ⌊G/h⌋₊+1
  let u (i : Fin M) := a+(i.val:ℝ)*h
  have hcov (v : ℝ) : ∃ i, HasProjectiveCircuitApproximation N (η+δ) 0 (unitaryEvolution H.val (v-u i)) := by
    obtain ⟨z,hz,hr⟩ := hcover v
    let i : Fin M := ⟨⌊(z-a)/h⌋₊,Nat.lt_succ_of_le (Nat.floor_mono
      (div_le_div_of_nonneg_right (by linarith only [hz.2]) hh.le))⟩
    have hlo : u i ≤ z := by
      have h₀ := (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr hz.1) hh.le))
      dsimp only [u,i]
      linarith only [h₀]
    have hhi : z-u i ≤ h := by
      have h₁ := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one ((z-a)/h))
      dsimp only [u,i]
      linarith only [h₁]
    have hzfit := (hasProjectiveCircuitApproximation_iff_infDist ..).mp ((profile_replay_iff_scalar H v z η).mp hr)
    have hd := (orbitCircuitDistance_lipschitz H 0).dist_le_mul (v-u i) (v-z)
    rw [Real.dist_eq,Real.dist_eq,show v-u i-(v-z)=z-u i by ring,abs_of_nonneg (sub_nonneg.mpr hlo)] at hd
    have hpay : ‖H.val‖*(z-u i) ≤ δ := calc
      _ ≤ L*h := mul_le_mul (le_add_of_nonneg_left zero_le_one) hhi (sub_nonneg.mpr hlo) hL.le
      _ = _ := by dsimp only [h]; field_simp
    refine ⟨i,(hasProjectiveCircuitApproximation_iff_infDist ..).mpr ?_⟩
    have hx := (abs_le.mp hd).2
    change orbitCircuitDistance H 0 (v-u i)-orbitCircuitDistance H 0 (v-z) ≤ ‖H.val‖*(z-u i) at hx
    linarith only [hzfit,hx,hpay]
  have hp := number_of_samples H hi (add_pos_of_nonneg_of_pos hη hδ) hsmall u hcov
  rw [Fintype.card_fin] at hp
  apply hp.trans
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
    (physicalArc_spec (add_pos_of_nonneg_of_pos hη hδ) hsmall).1.1.le _))
  change ((⌊G/h⌋₊+1:ℕ):ℝ) ≤ _
  rw [Nat.cast_add,Nat.cast_one,show G*(1+‖H.val‖)/δ=G/h by dsimp only [h,L]; field_simp]
  linarith only [Nat.floor_le (div_nonneg hG hh.le)]

#print axioms number_of_samples
#print axioms duration_of_cover
end
end GaloisForLFunctions.HTGeometry.TrajectoryProfiles
