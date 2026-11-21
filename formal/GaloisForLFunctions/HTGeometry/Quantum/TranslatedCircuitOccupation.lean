import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SignPacking.Occupation

/-!
# Time occupation of a projective circuit tube

A dense static orbit supplies one physical time shift for each anchored
spectral reflection. At any observation time the shifted evolutions are
projectively separated. A fixed target accepts at most one shift. Comparing
Lebesgue lengths gives a bound uniform in the observation interval's origin.
-/

open MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- One overhead S works for all targets, all time offsets and all observation
intervals on this Hamiltonian. Each projective tube occupies at most the
fraction 2^(−d), up to the additive interval-length correction S. -/
theorem spectral_sign_occupation_bound {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i))) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (W : Reg n) (offset A T : ℝ), 0 ≤ T →
      (2:ℝ)^d * volume.real
        ({t | ∃ c : ℂ, ‖c‖ = 1 ∧ ‖unitaryEvolution (H : Reg n) (t+offset) - c • W‖ ≤ 2/5}
          ∩ Icc A (A+T)) ≤ T+S := by
  classical
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let B := anchoredSpectralBooleanReflection e V
  have visits (x : Fin d → Bool) : ∃ s : ℝ, 0 ≤ s ∧ ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖unitaryEvolution (H : Reg n) s - z • B x‖ < 1/40 := by
    obtain ⟨G,_,hh⟩ := syndetic_approach_spectral_signs e H.2.isHermitian hmax x
    obtain ⟨s,hs,z,hz,hd⟩ := hh 0
    exact ⟨s,hs.1,z,hz,hd⟩
  choose s hs z hz hhit using visits
  let S : ℝ := ∑ x, s x
  have hsS (x) : s x ≤ S := Finset.single_le_sum (fun y _ => hs y) (Finset.mem_univ x)
  have hS : 0 ≤ S := Finset.sum_nonneg fun x _ => hs x
  exact ⟨S,hS,spectral_sign_visits_tube_occupation e H hS
    (fun x => ⟨s x,⟨hs x,hsS x⟩,z x,hz x,hhit x⟩)⟩

/-- Starting times whose following physical window contains some unitary
achievable to fixed error by at most s arbitrary two-qubit gates. -/
def circuitWindowHits (H : Reg n) (s : ℕ) (W : ℝ) : Set ℝ :=
  {u | ∃ t ∈ Icc u (u+W), HasProjectiveCircuitApproximation n (1/10 : ℝ) s
    (unitaryEvolution H t)}

/-- Bound the fraction of window starts with a downward fluctuation at any
time inside the window. The circuit architecture, continuous gates, and
global phase may depend on the time of the fluctuation. -/
theorem spectral_sign_window_occupation {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i))) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (s : ℕ) (W mesh : ℝ), 0 < mesh → ‖(H : Reg n)‖*mesh ≤ 1/40 →
      ∀ A T : ℝ, 0 ≤ T →
      (2:ℝ)^d * volume.real (circuitWindowHits (H : Reg n) s W ∩ Icc A (A+T)) ≤
        (plateauGridCount W mesh : ℝ) * ((atMostQuarterCircuitNet n s).card : ℝ) * (T+S) := by
  classical
  obtain ⟨S,hS,hh⟩ := spectral_sign_occupation_bound e H hmax
  exact ⟨S,hS,circuit_window_occupation_of_tube_bound H hh⟩

/-- A Gaussian path has overwhelming long-time occupation of entire hard
windows. The finite observation correction is uniform in the origin A.
The same draw retains the two-query locality signal at every time. -/
theorem gaussianPath_rare_circuitWindowHits_and_permanentLocality :
    ∀ᶠ L : ℕ in Filter.atTop,
    ∀ᵐ p ∂(centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1),
      let n := L*2
      let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
      let r := excursionGateBudget n
      let W := translatedExcursionWidth n ‖(H : Reg n)‖
      (∃ S : ℝ, 0 ≤ S ∧ ∀ A T : ℝ, 0 ≤ T →
        ((r+1:ℝ)^r) * volume.real (circuitWindowHits (H : Reg n) r W ∩ Icc A (A+T)) ≤ T+S) ∧
      RHTower.NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  have hcof : Filter.Tendsto (fun L : ℕ => L*2) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    exact Filter.eventually_atTop.2 ⟨N,fun L h => by omega⟩
  filter_upwards [Filter.eventually_ge_atTop 1,
    hcof.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier,
    RHTower.eventually_pairQubit_twoLocalPauli_separator] with L hL he hsep
  have hnull := (nearestNeighborPathLocalMaximalSet_dense_residual_fullMeasure (L := L) hL).2.2
  have hμ : centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1 ≪
      (volume : Measure (Fin (nearestNeighborPathLocalParameterCount L) → ℝ)) := by
    simpa [centredProductGaussian] using (productGaussian_absolutelyContinuous
      (nearestNeighborPathLocalParameterCount L) one_ne_zero (fun _ => 0))
  have hgood : ∀ᵐ p ∂(centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1),
      p ∈ nearestNeighborPathLocalMaximalSet L := ae_iff.mpr (hμ hnull)
  filter_upwards [hgood] with p hp
  refine ⟨?_,RHTower.nearestNeighborPath_permanentLocalityHaarSeparation hL hp hsep⟩
  let n := L*2
  let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
  let d := RHTower.nearestNeighborPathProjectiveDimension L
  let e : (Fin n → Bool) ≃ Fin (d+1) := (pairQubitPathConfigurationEquiv L).symm.trans
    (RHTower.nearestNeighborPathConfigChoiEquiv L)
  have hmax : MaximallyProjectiveEnergy (fun i => H.2.isHermitian.eigenvalues (e.symm i)) :=
    (RHTower.pairQubitProjectivePauliSeed_maximallyProjective hp).comp_equiv e.symm
  obtain ⟨S,hS,hh⟩ := spectral_sign_window_occupation e H hmax
  refine ⟨S,hS,?_⟩
  intro A T hT
  let r := excursionGateBudget n
  let M := (r+1)^r
  let m := 1/(40*(‖(H : Reg n)‖+1))
  have hm : 0 < m := by dsimp [m]; positivity
  have hs : ‖(H : Reg n)‖ * m ≤ 1/40 := by
    dsimp [m]; rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  let W := translatedExcursionWidth n ‖(H : Reg n)‖
  have hcount : plateauGridCount W m = M := by
    change ⌈(((M-1 : ℕ) : ℝ)*m)/m⌉₊ + 1 = M
    rw [mul_div_cancel_right₀ _ hm.ne', Nat.ceil_natCast]
    have hp' : 0 < M := by dsimp [M]; positivity
    omega
  have hd : 2^n = 4^L := by dsimp [n]; rw [mul_comm L 2, pow_mul]; norm_num
  have hdim : d = 2^n-1 := by
    have h := RHTower.nearestNeighborPathProjectiveDimension_add_one L
    rw [← hd] at h; dsimp [d]; omega
  have he' : atMostQuarterCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) <
      ((2^d : ℕ) : ℝ) := by simpa only [hdim] using he
  have hN : M * M * (atMostQuarterCircuitNet n r).card < 2^d := by
    rw [show M*M = (r+1)^(2*r) by rw [two_mul,pow_add]]
    exact translated_excursion_square_card (by dsimp [n];omega) he'
  let V := volume.real (circuitWindowHits (H : Reg n) r W ∩ Icc A (A+T))
  let N : ℝ := ((atMostQuarterCircuitNet n r).card : ℝ)
  have hsmall : (M:ℝ)*(M:ℝ)*N ≤ (2:ℝ)^d := by dsimp only [N]; exact_mod_cast hN.le
  have hobs := hh r W m hm hs A T hT
  rw [hcount] at hobs
  change (2:ℝ)^d * V ≤ (M:ℝ)*N*(T+S) at hobs
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have ht : (M:ℝ)*V ≤ T+S := by
    by_cases hMN : 0 < (M:ℝ)*N
    · apply le_of_mul_le_mul_left _ hMN
      calc
        (M:ℝ)*N*((M:ℝ)*V) = ((M:ℝ)*(M:ℝ)*N)*V := by ring
        _ ≤ (2:ℝ)^d*V := mul_le_mul_of_nonneg_right hsmall hV
        _ ≤ _ := hobs
    · have hz : (M:ℝ)*N = 0 := le_antisymm (le_of_not_gt hMN) (by dsimp [N]; positivity)
      rw [hz, zero_mul] at hobs
      have hzero : V = 0 := le_antisymm (nonpos_of_mul_nonpos_right hobs (by positivity)) hV
      rw [hzero,mul_zero]; linarith
  simpa only [M,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using ht

#print axioms gaussianPath_rare_circuitWindowHits_and_permanentLocality

end
end GaloisForLFunctions.HTGeometry
