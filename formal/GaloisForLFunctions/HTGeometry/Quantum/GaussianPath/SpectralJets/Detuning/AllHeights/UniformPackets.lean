import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PrefixModes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.PacketRisk

/-! # A common prefix cutoff for countably many spectral mode packets -/
open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
noncomputable section

/-- The strip width pays for both the packet index and the number of modes. -/
def packetRatio (k j count : ℕ) : ℝ :=
  (1/2:ℝ)^(k+j+1)/(1+(modeStripPrice (2^(k+3)) (2^(k+3)-2) count:ℝ))

def packetMargin (k j count : ℕ) : ℝ :=
  prefixModeAmplitude k*(packetRatio k j count)^(2^(k+3)-2)

private theorem ratio_price (k j count : ℕ) :
    let price := (modeStripPrice (2^(k+3)) (2^(k+3)-2) count:ℝ)
    0 < packetRatio k j count ∧ packetRatio k j count ≤ 1 ∧
      price*packetRatio k j count ≤ (1/2:ℝ)^(k+j+1) := by
  intro price
  let p := (1/2:ℝ)^(k+j+1)
  have hp : 0 < p := pow_pos (by norm_num) _
  have hprice : 0 ≤ price := Nat.cast_nonneg _
  have hden : 0 < 1+price := by linarith only [hprice]
  change 0 < p/(1+price) ∧ p/(1+price) ≤ 1 ∧ price*(p/(1+price)) ≤ p
  refine ⟨div_pos hp hden,(div_le_one hden).mpr
    ((pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).trans (le_add_of_nonneg_right hprice)),?_⟩
  rw [←mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  rw [mul_add,mul_one,mul_comm price]
  exact le_add_of_nonneg_left hp.le

/-- All packets at all heights obey their explicit spectral margin after one
prefix cutoff on almost every draw. The derivative response is shared across
packets. Only the scalar strip probabilities are summed over their indices. -/
theorem gaussian_all_packets (S : (k j : ℕ) → Finset (Fin (2^(k+3)) → ℤ)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      ∀ j, ∀ m ∈ S k j, m ≠ 0 → ∑ i, m i = 0 →
        packetMargin k j (S k j).card ≤
          |∑ i, (m i:ℝ)*sortedEnsembleSpectrum (chainPauliFin_isHermitian N) θ i| := by
  obtain ⟨rows,hlen,hresponse⟩ := gaussian_path_eventually_uniform_mode_response
  let x (k : ℕ) (ω : PathPauliDisorder) := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let r (k j : ℕ) := packetRatio k j (S k j).card
  let bad (k j : ℕ) := finiteWitnesses (k+3) (2^(k+3)-2) (S k j) (rows k) (prefixModeAmplitude k) (r k j)
  have hbad (k j : ℕ) : pathPauliDisorderLaw (x k ⁻¹' bad k j) ≤ (1/2:ℝ≥0∞)^(k+j+1) := by
    have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
    apply (Measure.le_map_apply hmp.measurable.aemeasurable (bad k j)).trans
    rw [hmp.map_eq]
    obtain ⟨hr,hr',hp⟩ := ratio_price k j (S k j).card
    apply (gaussian_finite_witnesses _ _ _ _ (hlen k) (prefixModeAmplitude_pos k) hr hr').trans
    exact (ENNReal.ofReal_le_ofReal hp).trans_eq (by
      rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),one_div,ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
      norm_num)
  filter_upwards [eventually_no_packet _ _ hbad,hresponse] with ω he hr
  filter_upwards [he,hr] with k hk hresp
  intro N θ j m hm hne hbal
  let B := prefixDetectorDegree k
  have hdet : ((1/2:ℝ)^k/(1+2*(B:ℝ)))^B ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    apply (div_le_one (by positivity)).mpr
    exact (pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).trans (le_add_of_nonneg_right (by positivity))
  obtain ⟨hθ,hmode⟩ := sorted_response_of_packet N (rows k) θ _ _ hresp
  obtain ⟨i,w,hi,hw⟩ := hmode m hne hbal
  have ha := response_amplitude_le hdet hw
  by_contra! hsmall
  apply hk j
  change x k ω ∈ finiteWitnesses N (2^N-2) (S k j) (rows k) (prefixModeAmplitude k) (r k j)
  unfold finiteWitnesses
  refine Set.mem_iUnion₂.mpr ⟨m,hm,Set.mem_iUnion₂.mpr ⟨i,Finset.mem_univ _,hθ,?_,?_⟩⟩
  · simpa only [sortedMode_nil,packetMargin,r,x,θ,N] using hsmall
  · simpa only [hi,Option.getD_some,prefixModeAmplitude,B,N,x,θ] using ha

#print axioms gaussian_all_packets
end
end GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
