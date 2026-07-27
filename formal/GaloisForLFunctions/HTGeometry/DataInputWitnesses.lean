import GaloisForLFunctions.HTGeometry.QuantumTorusPrincipalSymbol
import GaloisForLFunctions.HTGeometry.KolchinFrequencyBudgetPhase
import GaloisForLFunctions.HTGeometry.NormalCrossingCriticalDerivedPhase
import GaloisForLFunctions.HTGeometry.GammaPhaseCompletion

/-!
# Inhabitants of the bundled data inputs

A theorem whose hypothesis is a bundled datum says nothing until such a datum exists.  This file
supplies inhabitants for three input bundles that are consumed as hypotheses but constructed
nowhere, and in one case shows that the bound the bundle carries is attained.

* `quantumLawPair_of_lt`, `infinite_quantumLawPair_nat` — increasing law pairs exist for every
  strict inequality, and there are infinitely many of them over `ℕ`, so the quantum-torus symbol
  layer is not empty;
* `singularKolchinFrequencyInput_diagonal` and **`singularKolchin_frequencyRank_le_sharp`** — the
  budget `frequencyRank ≤ 2 · kolchinCapacity` is attained, so it cannot be improved;
* `normalCrossingKoszulGradeInput_witness` — a grade-two Koszul input in every corank, obtained from
  the amplitude concentrated in the single degree `r − 1`.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ### Increasing law pairs -/

/-- Every strict inequality is an increasing law pair. -/
def quantumLawPair_of_lt {ι : Type*} [LT ι] {a b : ι} (h : a < b) : QuantumLawPair ι :=
  ⟨a, b, h⟩

@[simp]
theorem quantumLawPair_of_lt_lower {ι : Type*} [LT ι] {a b : ι} (h : a < b) :
    (quantumLawPair_of_lt h).lower = a := rfl

@[simp]
theorem quantumLawPair_of_lt_upper {ι : Type*} [LT ι] {a b : ι} (h : a < b) :
    (quantumLawPair_of_lt h).upper = b := rfl

/-- Two coordinates already carry an increasing law pair. -/
instance nonempty_quantumLawPair_fin (n : ℕ) : Nonempty (QuantumLawPair (Fin (n + 2))) :=
  ⟨quantumLawPair_of_lt (a := (⟨0, by omega⟩ : Fin (n + 2))) (b := ⟨1, by omega⟩)
    (by simp)⟩

/-- The consecutive pairs `(k, k + 1)`. -/
def consecutiveQuantumLawPair (k : ℕ) : QuantumLawPair ℕ :=
  quantumLawPair_of_lt (Nat.lt_succ_self k)

theorem consecutiveQuantumLawPair_injective :
    Function.Injective consecutiveQuantumLawPair := by
  intro k l h
  have : (consecutiveQuantumLawPair k).lower = (consecutiveQuantumLawPair l).lower := by rw [h]
  simpa [consecutiveQuantumLawPair] using this

/-- **There are infinitely many increasing law pairs.**  The quantum-torus principal-symbol layer is
therefore not a statement about an empty index. -/
theorem infinite_quantumLawPair_nat : Infinite (QuantumLawPair ℕ) :=
  Infinite.of_injective consecutiveQuantumLawPair consecutiveQuantumLawPair_injective

/-! ### The singular Kolchin frequency budget -/

/-- The input with frequency rank exactly twice the Kolchin capacity. -/
def singularKolchinFrequencyInput_diagonal (c : ℕ) : SingularKolchinFrequencyInput where
  frequencyRank := 2 * c
  hullCoverDimension := 2 * c
  kolchinCapacity := c
  rank_eq_coverDimension := rfl
  coverDimension_le := le_rfl

/-- **The Kolchin frequency budget is attained.**  For every capacity there is an input whose
frequency rank equals twice it, so `singularKolchin_frequencyRank_le` is sharp. -/
theorem singularKolchin_frequencyRank_le_sharp (c : ℕ) :
    ∃ input : SingularKolchinFrequencyInput,
      input.kolchinCapacity = c ∧ input.frequencyRank = 2 * input.kolchinCapacity :=
  ⟨singularKolchinFrequencyInput_diagonal c, rfl, rfl⟩

/-! ### Normal-crossing Koszul inputs -/

/-- An amplitude concentrated in one degree is exact there. -/
theorem hasExactHomologicalAmplitude_eq (a : ℕ) :
    HasExactHomologicalAmplitude (fun n => n = a) a := by
  refine ⟨rfl, fun i hi hcon => ?_⟩
  omega

/-- **A grade-two normal-crossing Koszul input in every corank.**  Its homology is concentrated in
the single degree `(r + 1) − 2`, which is exactly the amplitude the grade-two hypothesis demands. -/
def normalCrossingKoszulGradeInput_witness (r : ℕ) : NormalCrossingKoszulGradeInput r where
  homologyNonzero := fun n => n = (r + 1) - 2
  grade := 2
  grade_eq_two := rfl
  gradeSensitivity := hasExactHomologicalAmplitude_eq _

/-- The derived-amplitude law applies to an explicit input in every positive corank. -/
theorem normalCrossing_exactDerivedAmplitude_witness {r : ℕ} (hr : 1 ≤ r) :
    HasExactHomologicalAmplitude (normalCrossingKoszulGradeInput_witness r).homologyNonzero
      (r - 1) :=
  normalCrossing_exactDerivedAmplitude hr (normalCrossingKoszulGradeInput_witness r)

/-! ### Exterior coherence witnesses -/

/-- **A truncated exterior coherence witness in every corank.**  The coordinate basis of the
function space on the truncated face index is linearly independent, so the exterior classes it
carries realize the witness bundle. -/
noncomputable def normalCrossingExteriorCoherenceWitness_basis (F : Type*) [Field F] (r : ℕ) :
    NormalCrossingExteriorCoherenceWitness F
      ({J : Finset (Fin r) // J.Nonempty ∧ J.card < r} → F) r where
  exteriorClass := fun j => Pi.basisFun F {J : Finset (Fin r) // J.Nonempty ∧ J.card < r} j
  independent := (Pi.basisFun F {J : Finset (Fin r) // J.Nonempty ∧ J.card < r}).linearIndependent

/-- The exterior-coherence capacity law applies to an explicit witness in every positive corank. -/
theorem normalCrossing_exteriorCoherence_exactCapacity_witness {F : Type*} [Field F] {r : ℕ}
    (hr : 1 ≤ r) :
    LinearIndependent F (normalCrossingExteriorCoherenceWitness_basis F r).exteriorClass ∧
      (∑ p ∈ Finset.Icc 1 (r - 1), r.choose p) = 2 ^ r - 2 :=
  normalCrossing_exteriorCoherence_exactCapacity hr (normalCrossingExteriorCoherenceWitness_basis F r)

/-! ### The Barnes reflection threshold -/

/-- The threshold input carried by the predicate `2 ≤ N` itself. -/
def barnesReflectionAnalyticThresholdInput_canonical : BarnesReflectionAnalyticThresholdInput where
  multipleSineHypertranscendental := fun N => 2 ≤ N
  logDerivHypertranscendental := fun N => 2 ≤ N
  sine_threshold := fun _ => Iff.rfl
  logDeriv_threshold := fun _ => Iff.rfl

/-! ### The Gauss-channel Schatten endpoint -/

/-- The endpoint input carried by the strict inequality `2m < q` itself: weak membership holds,
strong membership fails, and Schatten membership is exactly the range above the critical index. -/
noncomputable def gaussChannelSchattenEndpointInput_canonical {J : Type*} [Fintype J] (m : ℕ)
    (prime : J → Nat.Primes) : GaussChannelSchattenEndpointInput J m prime where
  weakEndpoint := True
  strongEndpoint := False
  schattenMembership := fun q => 2 * m < q
  endpointResidue := GaloisForLFunctions.RHTower.gaussPairedChannelResidue m prime
  weakEndpoint_holds := trivial
  strongEndpoint_fails := not_false
  aboveCritical := fun _ hq => hq
  atOrBelowCritical := fun _ hq => not_lt.mpr hq
  residue_exact := rfl

end GaloisForLFunctions.HTGeometry
