import GaloisForLFunctions.HTGeometry.MaximallyProjectivePhysicalRandomizedCircuitHardIntervalLaw
import GaloisForLFunctions.RHTower.PairQubitProjectiveSeedWeakTwoLocalSameDrawLaw
import GaloisForLFunctions.RHTower.NearestNeighborPolynomialCircuitSameDrawLaw

/-!
# Same-draw local growth and randomized-circuit hard intervals

One ordinary time-independent nearest-neighbour Hamiltonian drawn once from the fixed local
Gaussian ensemble simultaneously has a certified laboratory-time linear complexity ramp and
syndetic positive-width intervals of exponential continuous-circuit hardness.  Every finite
classical randomization over short continuous circuits has a fixed pure-Choi fidelity deficit on
the same late-time intervals, independent of its number of branches.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator BigOperators NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

universe u

/--
**Closed same-draw growth--randomized-hard-interval law.**  For every sufficiently large path,
one draw from the ordinary static nearest-neighbour Gaussian ensemble has:

* the fixed-error laboratory-time linear circuit lower bound throughout its full nonempty
  certified window; and
* syndetic positive-width intervals on which every continuous two-qubit circuit of depth at most
  `nearestNeighborPathProjectiveDimension L / 32` has a fixed Choi error, while every finite
  randomized mixture of such circuits has a fixed fidelity deficit.

The late-time budget is exponential because
`nearestNeighborPathProjectiveDimension L + 1 = 4 ^ L`.  The Hamiltonian in both clauses is the
same draw, with `pairQubitProjectivePauliSeed` its canonical `2L`-qubit relabelling.
-/
theorem eventually_exists_nearestNeighborPath_sameDraw_growth_randomizedCircuitHardIntervals :
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
        ∃ ε : ℝ, 0 < ε ∧ ∃ W : ℝ, 0 < W ∧ ∃ gap : ℝ, 0 ≤ gap ∧
          ∀ a : ℝ, ∃ v ∈ Set.Icc a (a + gap),
            ∀ t ∈ Set.Icc v (v + W),
              (∀ C : TwoQubitCircuit (L * 2),
                C.gateCount ≤ nearestNeighborPathProjectiveDimension L / 32 →
                  ε ≤ choiDist
                    (unitaryEvolution (pairQubitProjectivePauliSeed L p) t)
                    (C.eval : Matrix (Fin (L * 2) → Bool)
                      (Fin (L * 2) → Bool) ℂ)) ∧
              ∀ {C : Type u} [Fintype C]
                (circuit : C → TwoQubitCircuit (L * 2)),
                (∀ i, (circuit i).gateCount ≤
                  nearestNeighborPathProjectiveDimension L / 32) →
                ∀ (weight : C → ℝ≥0), (∑ i, weight i) = 1 →
                  (∑ i, (weight i : ℝ) *
                    ‖inner ℂ
                      (choiVector
                        (unitaryEvolution (pairQubitProjectivePauliSeed L p) t))
                      (choiVector ((circuit i).eval :
                        Matrix (Fin (L * 2) → Bool)
                          (Fin (L * 2) → Bool) ℂ))‖ ^ 2) ≤
                    1 - ε ^ 2 := by
  filter_upwards [Filter.eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2048 * Real.pi)] with
      L hL hLlarge
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
  have hd : 0 < d := by
    have hdim := nearestNeighborPathProjectiveDimension_add_one L
    have hpow : 1 < 4 ^ L := Nat.one_lt_pow (Nat.ne_of_gt hLpos) (by norm_num)
    dsimp [d]
    omega
  have hs : (d / 32) * 16 < d := by
    have hdiv := Nat.div_mul_le_self d 32
    omega
  have hmax : MaximallyProjectiveEnergy
      (fun i => (pairQubitProjectivePauliSeed_isHermitian L p).eigenvalues
        (e.symm i)) :=
    (pairQubitProjectivePauliSeed_maximallyProjective hp.1).comp_equiv e.symm
  have hhard :=
    maximallyProjective_unitaryEvolution_randomizedCircuitHardIntervals_syndetic.{u}
      e (pairQubitProjectivePauliSeed_isHermitian L p) hmax hs
  exact ⟨p, hgrowth, hend, hhard⟩

end RHTower
