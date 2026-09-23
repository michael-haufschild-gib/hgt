import GaloisForLFunctions.HTGeometry.InverseSquareChainCubicFirstReturnLaw
import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceEntropy

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.HilbertMetric

noncomputable section

def inverseSquareChainVacuumConfig (L : ℕ) : Config (PairQubit L) :=
  fun _ => false

theorem inverseSquareChainEnergy_vacuumConfig (L : ℕ) :
    inverseSquareChainEnergy (inverseSquareChainVacuumConfig L) = 0 := by
  simp [inverseSquareChainEnergy, inverseSquareMatchingEnergy,
    inverseCubeBridgeEnergy, inverseSquareChainVacuumConfig]

theorem firstInverseCubeBridgeConfig_ne_vacuumConfig
    {L : ℕ} (hL : 2 ≤ L) :
    firstInverseCubeBridgeConfig hL ≠ inverseSquareChainVacuumConfig L := by
  intro h
  have hentry := congrFun h (⟨0, by omega⟩, true)
  simp [firstInverseCubeBridgeConfig, inverseSquareChainVacuumConfig] at hentry

theorem inverseSquareChainCubicReturnSeparation_le_bridgePhaseChord
    {L : ℕ} (hL : 2 ≤ L) {guard t : ℝ}
    (hguard : 0 ≤ guard)
    (ht : t ∈ Set.Icc guard
      (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard)) :
    inverseSquareChainCubicReturnSeparation L guard ≤
      ‖Complex.exp (-(Complex.I * ((t / (L : ℝ) ^ (3 : ℕ) : ℝ) : ℂ))) - 1‖ := by
  let phi := t / (L : ℝ) ^ (3 : ℕ)
  have hden : 0 < (L : ℝ) ^ (3 : ℕ) := by positivity
  by_cases hhalf : t ≤ Real.pi * (L : ℝ) ^ (3 : ℕ)
  · have ht0 : 0 ≤ t := hguard.trans ht.1
    have hphi0 : 0 ≤ phi := div_nonneg ht0 hden.le
    have hphipi : phi ≤ Real.pi := by
      dsimp [phi]
      rwa [div_le_iff₀ hden]
    have hchord := phase_chord_lower hphi0 hphipi
    calc
      inverseSquareChainCubicReturnSeparation L guard =
          2 * (guard / (L : ℝ) ^ (3 : ℕ)) / Real.pi := rfl
      _ ≤ 2 * phi / Real.pi := by
        gcongr
        exact div_le_div_of_nonneg_right ht.1 hden.le
      _ ≤ ‖Complex.exp (-(Complex.I * (phi : ℂ))) - 1‖ := hchord
      _ = _ := by rfl
  · let psi := 2 * Real.pi - phi
    have htop : t ≤ 2 * Real.pi * (L : ℝ) ^ (3 : ℕ) :=
      ht.2.trans (sub_le_self _ hguard)
    have hpsi0 : 0 ≤ psi := by
      dsimp [psi, phi]
      rw [sub_nonneg, div_le_iff₀ hden]
      exact htop
    have hpsipi : psi ≤ Real.pi := by
      have hnot := lt_of_not_ge hhalf
      have hphiPi : Real.pi ≤ phi := by
        dsimp [phi]
        rw [le_div_iff₀ hden]
        exact hnot.le
      dsimp [psi]
      nlinarith
    have hguardPsi : guard / (L : ℝ) ^ (3 : ℕ) ≤ psi := by
      dsimp [psi, phi]
      rw [div_le_iff₀ hden]
      have hcancel : t / (L : ℝ) ^ (3 : ℕ) * (L : ℝ) ^ (3 : ℕ) = t :=
        div_mul_cancel₀ t (ne_of_gt hden)
      rw [sub_mul, hcancel]
      nlinarith [ht.2]
    have hchord := phase_chord_lower hpsi0 hpsipi
    have hreflect := norm_exp_neg_I_mul_two_pi_sub_sub_one phi
    calc
      inverseSquareChainCubicReturnSeparation L guard =
          2 * (guard / (L : ℝ) ^ (3 : ℕ)) / Real.pi := rfl
      _ ≤ 2 * psi / Real.pi := by gcongr
      _ ≤ ‖Complex.exp (-(Complex.I * (psi : ℂ))) - 1‖ := hchord
      _ = ‖Complex.exp (-(Complex.I * (phi : ℂ))) - 1‖ := hreflect.symm
      _ = _ := by rfl

def inverseSquareChainPhasePacket (L : ℕ) (t : ℝ) :
    Config (PairQubit L) → ℂ := fun x =>
  Complex.exp (-(Complex.I * (t * inverseSquareChainEnergy x)))

theorem norm_inverseSquareChainPhasePacket (L : ℕ) (t : ℝ)
    (x : Config (PairQubit L)) :
    ‖inverseSquareChainPhasePacket L t x‖ = 1 := by
  simp [inverseSquareChainPhasePacket, Complex.norm_exp]

theorem inverseSquareChainPhasePacket_bridge_sub_vacuum
    {L : ℕ} (hL : 2 ≤ L) (t : ℝ) :
    inverseSquareChainPhasePacket L t (firstInverseCubeBridgeConfig hL) -
        inverseSquareChainPhasePacket L t (inverseSquareChainVacuumConfig L) =
      Complex.exp (-(Complex.I * ((t / (L : ℝ) ^ (3 : ℕ) : ℝ) : ℂ))) - 1 := by
  simp only [inverseSquareChainPhasePacket,
    inverseSquareChainEnergy_firstInverseCubeBridgeConfig hL,
    inverseSquareChainEnergy_vacuumConfig]
  simp only [mul_zero, Complex.ofReal_zero, mul_zero, neg_zero,
    Complex.exp_zero]
  congr 2
  push_cast
  field_simp

theorem equalPhaseAmplitude_inverseSquareChainPhasePacket_eq_normalizedTrace
    (L : ℕ) (t : ℝ) :
    equalPhaseAmplitude (inverseSquareChainPhasePacket L t) =
      (Fintype.card (Config (PairQubit L)) : ℂ)⁻¹ *
        Matrix.trace (inverseSquareChainEvolution L t) := by
  rw [equalPhaseAmplitude, hilbertCentroid,
    inverseSquareChainEvolution_diagonal, Matrix.trace_diagonal]
  simp only [inverseSquareChainPhasePacket, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast]

/-- One separated spectral pair forces a projective trace-fidelity deficit.
The estimate is uniform over the complete cubic return-free window and is
independent of global phase. -/
theorem inverseSquareChainCubic_projectiveTraceFidelityDeficit
    {L : ℕ} (hL : 2 ≤ L) {guard t : ℝ}
    (hguard : 0 ≤ guard)
    (ht : t ∈ Set.Icc guard
      (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard)) :
    inverseSquareChainCubicReturnSeparation L guard ^ (2 : ℕ) /
        (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ (2 : ℕ)) ≤
      1 - ‖(Fintype.card (Config (PairQubit L)) : ℂ)⁻¹ *
        Matrix.trace (inverseSquareChainEvolution L t)‖ ^ (2 : ℕ) := by
  let phase := inverseSquareChainPhasePacket L t
  let x := firstInverseCubeBridgeConfig hL
  let y := inverseSquareChainVacuumConfig L
  let D : ℝ := Fintype.card (Config (PairQubit L))
  have hsep := inverseSquareChainCubicReturnSeparation_le_bridgePhaseChord
    hL hguard ht
  have hsep0 : 0 ≤ inverseSquareChainCubicReturnSeparation L guard := by
    dsimp [inverseSquareChainCubicReturnSeparation]
    positivity
  have hterm :
      ‖phase x - phase y‖ =
        ‖Complex.exp (-(Complex.I * ((t / (L : ℝ) ^ (3 : ℕ) : ℝ) : ℂ))) - 1‖ := by
    rw [inverseSquareChainPhasePacket_bridge_sub_vacuum hL t]
  have hsepTerm : inverseSquareChainCubicReturnSeparation L guard ^ (2 : ℕ) ≤
      ‖phase x - phase y‖ ^ (2 : ℕ) := by
    rw [hterm]
    exact pow_le_pow_left₀ hsep0 hsep 2
  have hinner : ‖phase x - phase y‖ ^ (2 : ℕ) ≤
      ∑ j, ‖phase x - phase j‖ ^ (2 : ℕ) := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖phase x - phase j‖)
      (Finset.mem_univ y)
  have houter : (∑ j, ‖phase x - phase j‖ ^ (2 : ℕ)) ≤
      ∑ i, ∑ j, ‖phase i - phase j‖ ^ (2 : ℕ) := by
    exact Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖phase i - phase j‖)
      (Finset.mem_univ x)
  have henergy : inverseSquareChainCubicReturnSeparation L guard ^ (2 : ℕ) ≤
      phasePairwiseSqEnergy phase := by
    exact hsepTerm.trans (hinner.trans (by simpa [phasePairwiseSqEnergy] using houter))
  rw [phasePairwiseSqEnergy_eq_two_card_sq_mul_fidelityDeficit phase
      (norm_inverseSquareChainPhasePacket L t)] at henergy
  rw [equalPhaseAmplitude_inverseSquareChainPhasePacket_eq_normalizedTrace] at henergy
  have hD : 0 < 2 * D ^ (2 : ℕ) := by
    dsimp [D]
    positivity
  rw [div_le_iff₀ hD]
  dsimp only [D]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using henergy

theorem norm_trace_le_card_mul_l2OpNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    ‖Matrix.trace A‖ ≤ Fintype.card ι * ‖A‖ := by
  rw [Matrix.trace]
  calc
    ‖∑ i, A i i‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖A‖ :=
      Finset.sum_le_sum fun i _ =>
        GaloisForLFunctions.HTGeometry.norm_entry_le_l2_opNorm A i i
    _ = Fintype.card ι * ‖A‖ := by simp

theorem norm_normalizedTrace_sub_le_l2OpNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Matrix ι ι ℂ) :
    ‖(Fintype.card ι : ℂ)⁻¹ * Matrix.trace A -
        (Fintype.card ι : ℂ)⁻¹ * Matrix.trace B‖ ≤ ‖A - B‖ := by
  rw [← mul_sub, ← Matrix.trace_sub, norm_mul, norm_inv,
    Complex.norm_natCast]
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc
    (Fintype.card ι : ℝ)⁻¹ * ‖Matrix.trace (A - B)‖ ≤
        (Fintype.card ι : ℝ)⁻¹ *
          ((Fintype.card ι : ℝ) * ‖A - B‖) := by
      gcongr
      exact norm_trace_le_card_mul_l2OpNorm (A - B)
    _ = ‖A - B‖ := by field_simp

theorem norm_inverseSquareChain_normalizedTrace_le_sqrt_cubicDeficit
    {L : ℕ} (hL : 2 ≤ L) {guard t : ℝ}
    (hguard : 0 ≤ guard)
    (ht : t ∈ Set.Icc guard
      (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard)) :
    ‖(Fintype.card (Config (PairQubit L)) : ℂ)⁻¹ *
        Matrix.trace (inverseSquareChainEvolution L t)‖ ≤
      Real.sqrt (1 - inverseSquareChainCubicReturnSeparation L guard ^ (2 : ℕ) /
        (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ (2 : ℕ))) := by
  let q := inverseSquareChainCubicReturnSeparation L guard ^ (2 : ℕ) /
    (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ (2 : ℕ))
  let a := ‖(Fintype.card (Config (PairQubit L)) : ℂ)⁻¹ *
    Matrix.trace (inverseSquareChainEvolution L t)‖
  have hdef := inverseSquareChainCubic_projectiveTraceFidelityDeficit
    hL hguard ht
  have hsq : a ^ (2 : ℕ) ≤ 1 - q := by
    dsimp only [a, q]
    linarith
  have hnonneg : 0 ≤ 1 - q := (sq_nonneg a).trans hsq
  rw [show Real.sqrt (1 - inverseSquareChainCubicReturnSeparation L guard ^ (2 : ℕ) /
      (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ (2 : ℕ))) =
      Real.sqrt (1 - q) by rfl]
  rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt hnonneg]
  exact hsq

/-- Projective scalar-return exclusion transfers to every self-adjoint
nearby static Hamiltonian with the same finite Hilbert space. -/
theorem norm_perturbedInverseSquareChain_normalizedTrace_le
    {L : ℕ} (hL : 2 ≤ L)
    (K : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ)
    (hK : IsSelfAdjoint K) {guard t : ℝ}
    (hguard : 0 ≤ guard)
    (ht : t ∈ Set.Icc guard
      (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard)) :
    ‖(Fintype.card (Config (PairQubit L)) : ℂ)⁻¹ *
        Matrix.trace (unitaryEvolution K t)‖ ≤
      Real.sqrt (1 - inverseSquareChainCubicReturnSeparation L guard ^ (2 : ℕ) /
        (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ (2 : ℕ))) +
      |t| * ‖K - inverseSquareChainHamiltonian L‖ := by
  let c : ℂ := (Fintype.card (Config (PairQubit L)) : ℂ)⁻¹
  let UK := unitaryEvolution K t
  let UH := inverseSquareChainEvolution L t
  have hseed := norm_inverseSquareChain_normalizedTrace_le_sqrt_cubicDeficit
    hL hguard ht
  have htraceDiff := norm_normalizedTrace_sub_le_l2OpNorm UK UH
  have hduhamel := GaloisForLFunctions.HTGeometry.norm_unitaryEvolution_sub_le
    K (inverseSquareChainHamiltonian L) hK
    (inverseSquareChainHamiltonian_isSelfAdjoint L) t
  have hdiff : ‖c * Matrix.trace UK - c * Matrix.trace UH‖ ≤
      |t| * ‖K - inverseSquareChainHamiltonian L‖ := by
    exact htraceDiff.trans hduhamel
  calc
    ‖c * Matrix.trace UK‖ ≤
        ‖c * Matrix.trace UH‖ + ‖c * Matrix.trace UK - c * Matrix.trace UH‖ := by
      calc
        ‖c * Matrix.trace UK‖ = ‖c * Matrix.trace UH +
            (c * Matrix.trace UK - c * Matrix.trace UH)‖ := by
          congr 1
          ring
        _ ≤ _ := norm_add_le (c * Matrix.trace UH)
          (c * Matrix.trace UK - c * Matrix.trace UH)
    _ ≤ Real.sqrt (1 - inverseSquareChainCubicReturnSeparation L guard ^ (2 : ℕ) /
          (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ (2 : ℕ))) +
        |t| * ‖K - inverseSquareChainHamiltonian L‖ := add_le_add hseed hdiff

end

end RHTower
