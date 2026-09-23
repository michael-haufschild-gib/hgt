import GaloisForLFunctions.HTGeometry.ContinuousCircuitExponentialPlateauBudgetLaw
import GaloisForLFunctions.RHTower.PairQubitProjectiveSeedLocalCompilerData
import GaloisForLFunctions.RHTower.NearestNeighborNearHilbertContinuousCircuitFirstReturnLaw

/-!
# Static nearest-neighbour exponential continuous-circuit plateau law

One ordinary time-independent nearest-neighbour Hamiltonian simultaneously
has a certified laboratory ramp, consecutive circuit exits and re-entries,
exponentially wide hard plateaux against arbitrary continuous `SU(4)` gates,
and permanent two-query non-Haar locality.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace RHTower

noncomputable section

def NearestNeighborLaboratoryRamp
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) : Prop :=
  ∀ t : ℝ,
    2048 * Real.pi * (1 / 10000 : ℝ) ≤ t →
    t ≤ (1 / 10000 : ℝ) * L →
    ((⌊t / (256 * Real.pi * (1 / 10000 : ℝ))⌋₊ : ℕ) : ℕ∞) ≤
      operatorTwoGateComplexityTo L (1 / 10000 : ℝ)
        (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)

def NearestNeighborNearHilbertContinuousFirstReturn
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) : Prop :=
  ∃ W : ℝ, 0 < W ∧ ∃ gap B : ℝ, 0 ≤ gap ∧ 0 ≤ B ∧
    ∀ a : ℝ, ∃ u tExit tReturn : ℝ,
      u ∈ Icc a (a + gap) ∧
      tExit ∈ Icc (u - B) u ∧
      tReturn ∈ Icc (u + W) (u + W + B) ∧
      (∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (L * 2),
        C.gateCount ≤ nearHilbertContinuousCircuitBudget (L * 2) ∧
        ‖unitaryEvolution (pairQubitProjectivePauliSeed L p) tExit -
          c • (C.eval : Matrix (Fin (L * 2) → Bool)
            (Fin (L * 2) → Bool) ℂ)‖ ≤ (1 / 20 : ℝ)) ∧
      (∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (L * 2),
        C.gateCount ≤ nearHilbertContinuousCircuitBudget (L * 2) ∧
        ‖unitaryEvolution (pairQubitProjectivePauliSeed L p) tReturn -
          c • (C.eval : Matrix (Fin (L * 2) → Bool)
            (Fin (L * 2) → Bool) ℂ)‖ ≤ (1 / 20 : ℝ)) ∧
      tExit < tReturn ∧ W ≤ tReturn - tExit ∧
      ∀ t ∈ Ioo tExit tReturn,
        ProjectiveCircuitSeparated (L * 2) (1 / 20 : ℝ)
          (nearHilbertContinuousCircuitBudget (L * 2))
          (unitaryEvolution (pairQubitProjectivePauliSeed L p) t)

/-- Arbitrarily late, syndetically located hard intervals whose width is
`2^(L/2)`, against half the near-Hilbert gate budget and arbitrary
continuous two-qubit gates. -/
def NearestNeighborNearHilbertExponentialHardPlateaux
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) : Prop :=
  ∃ G : ℝ, 0 ≤ G ∧ ∀ a : ℝ, ∃ T : ℝ,
    T ∈ Icc (a + continuousCircuitPlateauWidth L)
      (a + continuousCircuitPlateauWidth L + G) ∧
    ∀ t ∈ Icc (T - continuousCircuitPlateauWidth L) T,
      ProjectiveCircuitSeparated (L * 2) (1 / 40 : ℝ)
        (nearHilbertContinuousCircuitBudget (L * 2) / 2)
        (unitaryEvolution (pairQubitProjectivePauliSeed L p) t)

/-- **Capstone.** For every sufficiently long path, one static ordinary
nearest-neighbour Hamiltonian carries the ramp, recurrent circuit exits and
re-entries, exponential-width continuous-circuit hardness, a linear norm cap,
and permanent local non-Haar signal. -/
theorem eventually_exists_nearestNeighborPath_exponentialContinuousCircuitPlateau_capstone :
    ∀ᶠ L : ℕ in atTop,
      ∃ p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ,
        p ∈ nearestNeighborPathGaussianControlledGrowthEvent L
          ((1 / 10000 : ℝ) * L) (1 / 10000 : ℝ)
          (1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1))) ∧
        NearestNeighborLaboratoryRamp L p ∧
        NearestNeighborNearHilbertContinuousFirstReturn L p ∧
        NearestNeighborNearHilbertExponentialHardPlateaux L p ∧
        ‖(pairQubitProjectivePauliSeedSelfAdjoint L p :
          Matrix (FiniteQubitConfiguration (Fin (L * 2)))
            (FiniteQubitConfiguration (Fin (L * 2))) ℂ)‖ ≤ (L : ℝ) + 2 ∧
        NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  have hcofinal : Tendsto (fun L : ℕ => L * 2) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    exact Filter.eventually_atTop.2 ⟨N, fun L hL => by omega⟩
  have hentropyRaw := hcofinal.eventually
    eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier
  have hentropy : ∀ᶠ L : ℕ in atTop,
      atMostQuarterCircuitEntropyBound (L * 2)
          (nearHilbertContinuousCircuitBudget (L * 2)) <
        ((2 ^ nearestNeighborPathProjectiveDimension L : ℕ) : ℝ) := by
    filter_upwards [hentropyRaw] with L hL
    have hpow : 2 ^ (L * 2) = 4 ^ L := by
      calc
        2 ^ (L * 2) = 2 ^ (2 * L) := by rw [Nat.mul_comm]
        _ = (2 ^ (2 : ℕ)) ^ L := by rw [pow_mul]
        _ = 4 ^ L := by norm_num
    have hdim : nearestNeighborPathProjectiveDimension L = 2 ^ (L * 2) - 1 := by
      have h := nearestNeighborPathProjectiveDimension_add_one L
      rw [← hpow] at h
      omega
    simpa [hdim] using hL
  filter_upwards [hentropy,
    eventually_two_mul_continuousCircuitPlateauCompilerCost_le_nearHilbert,
    Filter.eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2048 * Real.pi),
    eventually_pairQubit_twoLocalPauli_separator] with
      L hEntropy hbudget hL hLlarge hsep
  have hLpos : 0 < L := by omega
  letI : NormedRing
      (Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) :=
    Matrix.instL2OpNormedRing
  have heventPos := measure_nearestNeighborPathGaussianControlledGrowthEvent_pos
    hLpos
    (T := (1 / 10000 : ℝ) * L)
    (ε := (1 / 10000 : ℝ))
    (ρ := 1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1)))
    (by positivity) (by norm_num) (by norm_num)
    (by
      have hmass : 0 ≤ nearestNeighborPathLocalGeneratorMass L := by
        unfold nearestNeighborPathLocalGeneratorMass
        exact Finset.sum_nonneg fun i _ => norm_nonneg _
      positivity)
    (by
      let M := nearestNeighborPathLocalGeneratorMass L
      have hM : 0 ≤ M := by
        dsimp [M, nearestNeighborPathLocalGeneratorMass]
        exact Finset.sum_nonneg fun i _ => norm_nonneg _
      have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
      have hM1 : 0 < M + 1 := by linarith
      have hratio : M / (M + 1) ≤ 1 := (div_le_one hM1).2 (by linarith)
      calc
        (1 / 10000 : ℝ) * L *
              ((1 / ((L : ℝ) * (M + 1))) * M) =
            (1 / 10000 : ℝ) * (M / (M + 1)) := by field_simp
        _ ≤ (1 / 10000 : ℝ) * 1 := by gcongr
        _ = 1 / 10000 := by ring)
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero (ne_of_gt heventPos)
  have hgrowth : NearestNeighborLaboratoryRamp L p := by
    intro t htMin htLab
    exact hp.1.2 t htMin htLab htLab
  let d := nearestNeighborPathProjectiveDimension L
  let e : (Fin (L * 2) → Bool) ≃ Fin (d + 1) :=
    (pairQubitPathConfigurationEquiv L).symm.trans
      (nearestNeighborPathConfigChoiEquiv L)
  have hmax : MaximallyProjectiveEnergy
      (fun i => (pairQubitProjectivePauliSeed_isHermitian L p).eigenvalues
        (e.symm i)) :=
    (pairQubitProjectivePauliSeed_maximallyProjective hp.1.1).comp_equiv e.symm
  have hfirstRaw :=
    maximallyProjective_unitaryEvolution_continuousCircuitTarget_consecutiveVisitGaps_of_entropy
      e (pairQubitProjectivePauliSeed_isHermitian L p) hmax hEntropy
  have hfirst : NearestNeighborNearHilbertContinuousFirstReturn L p := by
    simpa [NearestNeighborNearHilbertContinuousFirstReturn,
      ProjectiveCircuitSeparated] using hfirstRaw
  have hnorm := norm_pairQubitProjectivePauliSeed_le_length_add_two hL hp.2
  have hlocal := pairQubitProjectivePauliSeed_hasPauliWeightAtMost_two L p
  have hplateau : NearestNeighborNearHilbertExponentialHardPlateaux L p := by
    rcases hfirst with ⟨W, hW, gap, B, hgap, hB, hepisodes⟩
    refine ⟨gap + W, by positivity, ?_⟩
    intro a
    obtain ⟨u, tExit, tReturn, hu, hExit, hReturn,
      hExitApprox, hReturnApprox, hExitReturn, hWidth, hhard⟩ :=
        hepisodes (a + continuousCircuitPlateauWidth L)
    let T := u + W / 2
    have hTin : T ∈ Ioo tExit tReturn := by
      constructor
      · dsimp [T]
        linarith [hExit.2]
      · dsimp [T]
        linarith [hReturn.1]
    have hlate : ProjectiveCircuitSeparated (L * 2) (1 / 20 : ℝ)
        (nearHilbertContinuousCircuitBudget (L * 2))
        (unitaryEvolution (pairQubitProjectivePauliSeed L p) T) :=
      hhard T hTin
    have hr : 0 < continuousCircuitPlateauRepetitions L :=
      continuousCircuitPlateauRepetitions_pos L
    have hcost : continuousCircuitPlateauRepetitions L *
        Fintype.card (PauliTracelessLabel (L * 2) 2) ≤
          nearHilbertContinuousCircuitBudget (L * 2) := by
      change continuousCircuitPlateauCompilerCost L ≤
        nearHilbertContinuousCircuitBudget (L * 2)
      omega
    have hinterval := twoLocal_projectiveCircuitHard_backwardInterval
      (n := L * 2) (by omega)
      (pairQubitProjectivePauliSeedSelfAdjoint L p) hlocal
      (T := T) (W := (continuousCircuitPlateauWidth L : ℝ))
      (εearly := (1 / 40 : ℝ)) (εincrement := (1 / 100 : ℝ))
      (εlate := (1 / 20 : ℝ))
      (P := nearHilbertContinuousCircuitBudget (L * 2))
      (r := continuousCircuitPlateauRepetitions L)
      hr hcost
      (by
        intro τ hτ
        exact continuousCircuitPlateau_compiler_small
          (L := L) (B := ‖(pairQubitProjectivePauliSeedSelfAdjoint L p :
            Matrix (FiniteQubitConfiguration (Fin (L * 2)))
              (FiniteQubitConfiguration (Fin (L * 2))) ℂ)‖)
          (by simpa [abs_of_nonneg hτ.1] using hτ.2)
          (norm_nonneg _) hnorm)
      (by
        intro τ hτ
        exact continuousCircuitPlateau_compiler_error
          (L := L) (B := ‖(pairQubitProjectivePauliSeedSelfAdjoint L p :
            Matrix (FiniteQubitConfiguration (Fin (L * 2)))
              (FiniteQubitConfiguration (Fin (L * 2))) ℂ)‖)
          (by simpa [abs_of_nonneg hτ.1] using hτ.2)
          (norm_nonneg _) hnorm)
      hlate (by norm_num)
    refine ⟨T, ?_, ?_⟩
    · constructor
      · dsimp [T]
        linarith [hu.1]
      · dsimp [T]
        linarith [hu.2]
    · intro t ht
      have hh := hinterval t ht
      apply ProjectiveCircuitSeparated.mono_budget hh
      change nearHilbertContinuousCircuitBudget (L * 2) / 2 ≤
        nearHilbertContinuousCircuitBudget (L * 2) -
          continuousCircuitPlateauCompilerCost L
      omega
  have hnonHaar : NearestNeighborPathPermanentLocalityHaarSeparation L p :=
    nearestNeighborPath_permanentLocalityHaarSeparation hLpos hp.1.1 hsep
  exact ⟨p, hp, hgrowth, hfirst, hplateau, hnorm, hnonHaar⟩

end

end RHTower
