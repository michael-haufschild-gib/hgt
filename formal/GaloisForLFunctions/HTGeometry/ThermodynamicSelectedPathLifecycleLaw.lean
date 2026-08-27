import GaloisForLFunctions.HTGeometry.OrthoEigenBasisCanonicalProjective
import GaloisForLFunctions.HTGeometry.ThermodynamicSelectedPathRampLaw
import GaloisForLFunctions.HTGeometry.UniformProjectiveContinuousCircuitFirstReturnLaw

/-!
# One-field thermodynamic path lifecycle

One bounded, static, nearest-neighbour Pauli field is selected once on the countable path.  Every
literal finite prefix has a maximally projective spectrum.  The same prefixes obey the quantitative
laboratory gate ramp, and all sufficiently large prefixes undergo arbitrarily late consecutive
excursion--re-entry episodes relative to the complete continuous two-qubit circuit image at a
near-Hilbert gate budget.  No fresh finite-volume draw is made.
-/

open Filter Matrix Set
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open StaticLocalLaboratoryComplexityGrowthLaw

/-- Complete first-return lifecycle relative to all continuous two-qubit circuits of gate count at
most `s`, with global phase operationally invisible. -/
def ContinuousCircuitExcursionLaw
    (n s : ℕ) (H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : Prop :=
  ∃ W : ℝ, 0 < W ∧ ∃ gap B : ℝ, 0 ≤ gap ∧ 0 ≤ B ∧
    ∀ a : ℝ, ∃ u tExit tReturn : ℝ,
      u ∈ Icc a (a + gap) ∧
      tExit ∈ Icc (u - B) u ∧
      tReturn ∈ Icc (u + W) (u + W + B) ∧
      (∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
        C.gateCount ≤ s ∧ ‖unitaryEvolution H tExit - c • C.eval‖ ≤ (1 / 20 : ℝ)) ∧
      (∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
        C.gateCount ≤ s ∧ ‖unitaryEvolution H tReturn - c • C.eval‖ ≤ (1 / 20 : ℝ)) ∧
      tExit < tReturn ∧ W ≤ tReturn - tExit ∧
      ∀ t ∈ Ioo tExit tReturn, ∀ c : ℂ, ‖c‖ = 1 →
        ∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
          (1 / 20 : ℝ) < ‖unitaryEvolution H t - c • C.eval‖

/-- Canonical eigenvalues of every selected literal path prefix are maximally projective. -/
theorem infinitePathPrefixHamiltonian_eigenvalues_maximallyProjective
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ k, coefficientRestrict (numberedPathToInfinite k) p ∈ chainProjectiveGood k)
    (k : ℕ) :
    let hH : (pathHamiltonian (infinitePathPrefixShell k p)).IsHermitian := by
      exact isSelfAdjoint_pathHamiltonian _
    MaximallyProjectiveEnergy hH.eigenvalues := by
  dsimp only
  let hH : (pathHamiltonian (infinitePathPrefixShell k p)).IsHermitian := by
    exact isSelfAdjoint_pathHamiltonian _
  obtain ⟨e, energy, heb, hmax⟩ :=
    infinitePathPrefixShell_orthoEigenBasis_maximal hp k
  exact maximallyProjectiveEnergy_eigenvalues_of_orthoEigenBasis hH heb hmax

/-- All sufficiently large literal prefixes of the same selected field undergo perpetual genuine
excursions from, and consecutive re-entry into, the complete near-Hilbert continuous-circuit
target. -/
theorem eventually_infinitePathPrefix_continuousCircuitExcursions
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ k, coefficientRestrict (numberedPathToInfinite k) p ∈ chainProjectiveGood k) :
    ∀ᶠ k : ℕ in atTop,
      ContinuousCircuitExcursionLaw (k + 3)
        (nearHilbertContinuousCircuitBudget (k + 3))
        (pathHamiltonian (infinitePathPrefixShell k p)) := by
  have hcofinal : Tendsto (fun k : ℕ => k + 3) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    exact Filter.eventually_atTop.2 ⟨N, fun k hk => by omega⟩
  have hentropy := hcofinal.eventually
    eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier
  filter_upwards [hentropy] with k hEntropy
  let n := k + 3
  let d := 2 ^ n - 1
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hdim : 2 ^ n = d + 1 := by
    dsimp [d]
    omega
  let e : (Fin n → Bool) ≃ Fin (d + 1) :=
    (qubitConfigFin n).trans (finCongr hdim)
  let hH : (pathHamiltonian (infinitePathPrefixShell k p)).IsHermitian := by
    exact isSelfAdjoint_pathHamiltonian _
  have hcanon : MaximallyProjectiveEnergy hH.eigenvalues :=
    infinitePathPrefixHamiltonian_eigenvalues_maximallyProjective hp k
  have hmax : MaximallyProjectiveEnergy
      (fun i => hH.eigenvalues (e.symm i)) :=
    hcanon.comp_equiv_relabel e.symm
  have hfirst :=
    maximallyProjective_unitaryEvolution_continuousCircuitTarget_consecutiveVisitGaps_of_entropy
      e hH hmax (by simpa [n, d] using hEntropy)
  simpa [ContinuousCircuitExcursionLaw, n] using hfirst

/-- **One-field ramp--excursion--re-entry law.**  There exists one countable, static,
nearest-neighbour Pauli field, fixed before volume and time are chosen, whose every finite prefix
is maximally projective; whose pair-grouped prefixes obey a linear laboratory two-gate lower ramp;
and whose sufficiently large prefixes have arbitrarily late genuine hard excursions followed by
consecutive re-entry into the complete near-Hilbert continuous-circuit target. -/
theorem exists_nestedCentered_staticPath_ramp_and_continuousCircuitLifecycle :
    ∃ p : InfinitePathLabel → ℝ,
      (∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i) ∧
      (∀ k, MaximallyProjectiveEnergy
        (pathEigenValues k (infinitePathPrefixShell k p))) ∧
      (∀ (N K : ℕ) (c : List (LocalGate (PairQubit (N + 2)))) (t ε : ℝ),
        8 ≤ K → 8 * K ≤ N + 2 →
        0 < ε → ε ≤ 1 / 100 →
        128 * Real.pi * ε * K ≤ t →
        t < 128 * Real.pi * ε * (K + 1) →
        ‖circuitMatrix c - unitaryEvolution (thermodynamicPairHamiltonian N p) t‖ ≤ ε →
        K ≤ StaticLocalLaboratoryComplexityGrowthLaw.twoGateCount c) ∧
      ∀ᶠ k : ℕ in atTop,
        ContinuousCircuitExcursionLaw (k + 3)
          (nearHilbertContinuousCircuitBudget (k + 3))
          (pathHamiltonian (infinitePathPrefixShell k p)) := by
  obtain ⟨p, hpclose, hpgood⟩ := exists_nestedCentered_allPrefixes_projective
  refine ⟨p, hpclose, fun k => infinitePathPrefixShell_maximallyProjective hpgood k,
    ?_, eventually_infinitePathPrefix_continuousCircuitExcursions hpgood⟩
  intro N K c t ε hK hKL hε hεsmall htlo hthi hclose
  exact StaticLocalLaboratoryComplexityGrowthLaw.thermodynamicPairHamiltonian_twoGateCount_ge
    c hK hKL hpclose hε hεsmall htlo hthi hclose

end

end GaloisForLFunctions.HTGeometry
