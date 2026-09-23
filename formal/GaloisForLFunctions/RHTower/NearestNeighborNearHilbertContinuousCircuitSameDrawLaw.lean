import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw
import GaloisForLFunctions.RHTower.NearestNeighborUniformFixedErrorContinuousCircuitSameDrawLaw

/-!
# Same-draw near-Hilbert continuous-circuit hard intervals

One draw from an ordinary static nearest-neighbour Gaussian ensemble has the
proved laboratory-time complexity ramp and syndetically recurring intervals
that exclude every continuous two-qubit circuit below Hilbert-space dimension
divided by one logarithmic factor, at universal operator error `1/10`.  The
same evolution stays efficiently distinguishable from Haar at every time.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace RHTower

noncomputable section

/-- **Near-Hilbert same-draw law.**  All sufficiently long ordinary
nearest-neighbour chains admit one static two-local Hamiltonian with a robust
laboratory ramp, perpetual fixed-error hard intervals against every continuous
two-qubit circuit of gate count at most `2^(2L)/(64(2L+1))`, and permanent
non-Haar locality. -/
theorem eventually_exists_nearestNeighborPath_sameDraw_growth_nearHilbertContinuousCircuitHardIntervals :
    ∀ᶠ L : ℕ in atTop,
      ∃ p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ,
        (∀ t : ℝ,
          2048 * Real.pi * (1 / 10000 : ℝ) ≤ t →
          t ≤ (1 / 10000 : ℝ) * L →
          ((⌊t / (256 * Real.pi * (1 / 10000 : ℝ))⌋₊ : ℕ) : ℕ∞) ≤
            operatorTwoGateComplexityTo L (1 / 10000 : ℝ)
              (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)) ∧
        ((⌊((1 / 10000 : ℝ) * L) /
            (256 * Real.pi * (1 / 10000 : ℝ))⌋₊ : ℕ) : ℕ∞) ≤
          operatorTwoGateComplexityTo L (1 / 10000 : ℝ)
            (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p)
              ((1 / 10000 : ℝ) * L)) ∧
        (∃ W : ℝ, 0 < W ∧ ∃ gap : ℝ, 0 ≤ gap ∧
          ∀ a : ℝ, ∃ u ∈ Set.Icc a (a + gap),
            ∀ t ∈ Set.Icc u (u + W),
              ∀ C : TwoQubitCircuit (L * 2),
                C.gateCount ≤ nearHilbertContinuousCircuitBudget (L * 2) →
                  (1 / 10 : ℝ) ≤
                    ‖unitaryEvolution (pairQubitProjectivePauliSeed L p) t -
                      (C.eval : Matrix (Fin (L * 2) → Bool)
                        (Fin (L * 2) → Bool) ℂ)‖) ∧
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
  filter_upwards [hentropy, Filter.eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2048 * Real.pi),
    eventually_pairQubit_twoLocalPauli_separator] with
      L hEntropy hL hLlarge hsep
  have hLpos : 0 < L := by omega
  letI : NormedRing
      (Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) :=
    Matrix.instL2OpNormedRing
  have heventPos := measure_nearestNeighborPathGaussianGrowthMaximalEvent_pos
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
  have hgrowth : ∀ t : ℝ,
      2048 * Real.pi * (1 / 10000 : ℝ) ≤ t →
      t ≤ (1 / 10000 : ℝ) * L →
      ((⌊t / (256 * Real.pi * (1 / 10000 : ℝ))⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L (1 / 10000 : ℝ)
          (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t) := by
    intro t htMin htLab
    exact hp.2 t htMin htLab htLab
  have hend := hgrowth ((1 / 10000 : ℝ) * L)
    (by nlinarith : 2048 * Real.pi * (1 / 10000 : ℝ) ≤
      (1 / 10000 : ℝ) * L) le_rfl
  let d := nearestNeighborPathProjectiveDimension L
  let e : (Fin (L * 2) → Bool) ≃ Fin (d + 1) :=
    (pairQubitPathConfigurationEquiv L).symm.trans
      (nearestNeighborPathConfigChoiEquiv L)
  have hmax : MaximallyProjectiveEnergy
      (fun i => (pairQubitProjectivePauliSeed_isHermitian L p).eigenvalues
        (e.symm i)) :=
    (pairQubitProjectivePauliSeed_maximallyProjective hp.1).comp_equiv e.symm
  have hhard :=
    maximallyProjective_unitaryEvolution_circuitHardIntervals_uniformError_of_entropy
      e (pairQubitProjectivePauliSeed_isHermitian L p) hmax hEntropy
  have hnonHaar : NearestNeighborPathPermanentLocalityHaarSeparation L p :=
    nearestNeighborPath_permanentLocalityHaarSeparation hLpos hp.1 hsep
  exact ⟨p, hgrowth, hend, hhard, hnonHaar⟩

end

end RHTower
