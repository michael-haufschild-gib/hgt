import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.FiniteModes

/-! # Finite detuning on all long prefixes of one Gaussian Pauli chain -/

open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- The detector lower bound divided by its deterministic derivative scale. -/
def prefixModeAmplitude (k : ℕ) : ℝ :=
  let N := k+3
  let D := 2^N
  let B := prefixDetectorDegree k
  (((1/2:ℝ)^k/(1+2*B))^B) / (1+|pathResponseCap N (D-2) ((N:ℝ)^2)*(D:ℝ)|)

/-- Price a union over the retained integer modes at failure probability 2⁻ᵏ. -/
def prefixStripRatio (k count : ℕ) : ℝ :=
  let D := 2^(k+3)
  (1/2:ℝ)^k / (1+(modeStripPrice D (D-2) count:ℝ))

/-- Absolute lower bound for every retained, nonconstant, balanced spectral mode. -/
def prefixModeMargin (k count : ℕ) := prefixModeAmplitude k*(prefixStripRatio k count)^(2^(k+3)-2)

theorem prefixModeAmplitude_pos (k : ℕ) : 0 < prefixModeAmplitude k := by unfold prefixModeAmplitude; positivity

theorem prefixStripRatio_pos (k count : ℕ) : 0 < prefixStripRatio k count := by unfold prefixStripRatio; positivity

theorem prefixModeMargin_pos (k count : ℕ) : 0 < prefixModeMargin k count :=
  mul_pos (prefixModeAmplitude_pos k) (pow_pos (prefixStripRatio_pos k count) _)

private theorem prefixStripRatio_le_one (k count : ℕ) : prefixStripRatio k count ≤ 1 := by
  unfold prefixStripRatio
  apply (div_le_one (by positivity)).mpr
  exact (pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).trans
    (le_add_of_nonneg_right (Nat.cast_nonneg _))

/-- For any prescribed sequence of finite sets of integer modes, almost surely
all nonzero balanced members on all sufficiently long prefixes obey the explicit
detuning floor. The floor depends on the number of tested modes and the length. -/
theorem gaussian_path_eventually_finite_mode_margin (S : (k : ℕ) → Finset (Fin (2^(k+3)) → ℤ)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      ∀ m ∈ S k, m ≠ 0 → ∑ j, m j = 0 → prefixModeMargin k (S k).card ≤
        |∑ j, (m j:ℝ)*sortedEnsembleSpectrum (chainPauliFin_isHermitian N) θ j| := by
  classical
  obtain ⟨rows,hw,hresponse⟩ := gaussian_path_eventually_uniform_mode_response
  let D (k : ℕ) := 2^(k+3)
  let r (k : ℕ) := prefixStripRatio k (S k).card
  let bad (k : ℕ) := finiteWitnesses (k+3) (D k-2) (S k) (rows k) (prefixModeAmplitude k) (r k)
  let x (k : ℕ) (ω : PathPauliDisorder) := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  have hprob (k : ℕ) : pathPauliDisorderLaw (x k ⁻¹' bad k) ≤ (1/2:ℝ≥0∞)^k := by
    have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
    refine (Measure.le_map_apply hmp.measurable.aemeasurable (bad k)).trans ?_
    rw [hmp.map_eq]
    have hb := gaussian_finite_witnesses (k+3) (D k-2) (S k) (rows k) (hw k)
      (prefixModeAmplitude_pos k) (prefixStripRatio_pos k (S k).card) (prefixStripRatio_le_one k (S k).card)
    apply hb.trans
    let M : ℝ := modeStripPrice (D k) (D k-2) (S k).card
    have hM : 0 ≤ M := Nat.cast_nonneg _
    have hprice : M*r k ≤ (1/2:ℝ)^k := by
      change M*((1/2:ℝ)^k/(1+M)) ≤ _
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity)).mpr
      linarith only [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) k]
    exact (ENNReal.ofReal_le_ofReal hprice).trans_eq (by
      rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),one_div,ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
      norm_num)
  have hgood : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω ∉ x k ⁻¹' bad k := by
    apply ae_eventually_notMem
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hprob)
    simp only [one_div,ENNReal.tsum_geometric_two]
    norm_num
  filter_upwards [hgood,hresponse] with ω hgood' hresp'
  filter_upwards [hgood',hresp'] with k hk hresp
  intro N θ m hm hne hbal
  let B := prefixDetectorDegree k
  let a := (((1/2:ℝ)^k/(1+2*(B:ℝ)))^B)
  have ha : a ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    apply (div_le_one (by positivity)).mpr
    exact (pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).trans
      (le_add_of_nonneg_right (by positivity))
  obtain ⟨hθ,hmode⟩ := sorted_response_of_packet N (rows k) θ _ _ hresp
  obtain ⟨i,w,hi,hr⟩ := hmode m hne hbal
  have hamp := response_amplitude_le ha hr
  by_contra! hsmall
  apply hk
  change x k ω ∈ finiteWitnesses N (D k-2) (S k) (rows k) (prefixModeAmplitude k) (r k)
  unfold finiteWitnesses
  refine Set.mem_iUnion₂.mpr ⟨m,hm,Set.mem_iUnion₂.mpr ⟨i,Finset.mem_univ _,hθ,?_,?_⟩⟩
  · simpa only [sortedMode_nil,prefixModeMargin,r,D,x,θ,N] using hsmall
  · simpa only [hi,Option.getD_some,prefixModeAmplitude,a,B,N,x,θ] using hamp

#print axioms gaussian_path_eventually_finite_mode_margin
end
end GaloisForLFunctions.HTGeometry.SpectralJets
