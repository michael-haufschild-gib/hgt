import GaloisForLFunctions.HTGeometry.SharpControlledPhaseChoiCutGap
import GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiLaboratoryGrowthLaw

open scoped BigOperators Matrix Kronecker
open Matrix

/-!
# Harmonic-matching Choi laboratory ramp at the sharp error radius

The fixed time-independent matching Hamiltonian

`H_L = ∑_{j<L} (1/(j+1)) |11⟩⟨11|_j`

has fixed-error Choi circuit complexity at least `⌈K/2⌉` throughout the whole laboratory shell
`πK ≤ t < π(K+1)`, at the *sharp* error radius `ε⋆ = √((1 - 2^{-1/2})/2)`.

`HarmonicMatchingChoiLaboratoryGrowthLaw` proves the same implication at the rational radius
`√(1/8)`; the sharp radius here is the exact Gram-eigenvalue threshold of the controlled-phase cut
gap, which is what makes the ramp metrically composable with the Choi plateau and complete-circuit
first-reentry laws.
-/

namespace GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiSharpRamp

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ControlledPhaseChoiCutGap
open GaloisForLFunctions.HTGeometry.SharpControlledPhaseChoiCutGap
open GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiLaboratoryGrowthLaw
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.RHTower

theorem choiDist_ge_of_reindex_eq_kronecker_controlledPhase_sharp
    {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    (e : ι ≃ ControlledPhaseChoiCutGap.ProductIndex γ)
    (W U : Matrix ι ι ℂ)
    (A : Matrix Bool Bool ℂ)
    (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (z : ℂ) (r : Bool × γ → ℂ)
    (hWre : Matrix.reindexAlgEquiv ℂ ℂ e W = A ⊗ₖ B)
    (hUre : Matrix.reindexAlgEquiv ℂ ℂ e U =
      productControlledPhaseTarget z r)
    (hW : Wᴴ * W = 1)
    (hz : ‖z‖ = 1) (hre : z.re ≤ 0) (hr : ∀ y, ‖r y‖ = 1) :
    epsilonStar ≤ choiDist W U := by
  have hWprod : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1 := by
    rw [← hWre]
    change star (Matrix.reindexAlgEquiv ℂ ℂ e W) *
        Matrix.reindexAlgEquiv ℂ ℂ e W = 1
    rw [← reindexAlgEquiv_star, ← map_mul]
    have hWstar : star W * W = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using hW
    rw [hWstar, map_one]
  have hgap := choiDist_kronecker_productControlledPhaseTarget_ge_sharp
    A B z r hz hre hr hWprod
  rw [← hWre, ← hUre] at hgap
  rw [choiDist_reindexAlgEquiv e W U] at hgap
  exact hgap

theorem choiDist_circuit_harmonicMatchingEvolution_ge_of_separates_sharp
    {L : ℕ} (c : List (LocalGate (PairQubit L))) (j : Fin L) (t : ℝ)
    (hsep : SeparatesAcross ({(j, false)} : Finset (PairQubit L))
      (circuitMatrix c))
    (hlo : Real.pi / 2 ≤ t * harmonicPairWeight j)
    (hhi : t * harmonicPairWeight j ≤ Real.pi) :
    epsilonStar ≤
      choiDist (circuitMatrix c) (harmonicMatchingEvolution L t) := by
  classical
  letI : DecidableEq (PairCutRest (pair_true_ne_false j)) := Classical.decEq _
  rcases reindex_matchingCutEquiv_eq_kronecker_of_separates
      (pair_true_ne_false j) (circuitMatrix c) hsep with ⟨A, B, hWre⟩
  apply choiDist_ge_of_reindex_eq_kronecker_controlledPhase_sharp
    (matchingCutEquiv (pair_true_ne_false j))
    (circuitMatrix c) (harmonicMatchingEvolution L t) A B
    (harmonicSelectedPhase j t) (harmonicRestPhase j t)
  · exact hWre
  · exact reindex_harmonicMatchingEvolution_eq_productControlledPhaseTarget j t
  · let W : Matrix.unitaryGroup (Config (PairQubit L)) ℂ :=
      ⟨circuitMatrix c, circuitMatrix_unitary c⟩
    simpa [W, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self W
  · exact harmonicSelectedPhase_norm j t
  · exact harmonicSelectedPhase_re_nonpos j t hlo hhi
  · exact harmonicRestPhase_norm j t

theorem harmonicMatching_twoGateCount_activeSet_lower_sharp
    {L : ℕ} (c : List (LocalGate (PairQubit L)))
    (S : Finset (Fin L)) (t : ℝ)
    (hactive : ∀ j ∈ S,
      Real.pi / 2 ≤ t * harmonicPairWeight j ∧
        t * harmonicPairWeight j ≤ Real.pi)
    (hclose : choiDist (circuitMatrix c) (harmonicMatchingEvolution L t) <
      epsilonStar) :
    S.card ≤ 2 * twoGateCount c := by
  by_contra hnot
  have hcost : 2 * twoGateCount c < S.card := Nat.lt_of_not_ge hnot
  have htouched := circuitTouchedPairs_card_le c
  have hsmall : (circuitTouchedPairs c).card < S.card := lt_of_le_of_lt htouched hcost
  have hnsub : ¬S ⊆ circuitTouchedPairs c := by
    intro hsub
    exact (not_lt_of_ge (Finset.card_le_card hsub)) hsmall
  rcases Finset.not_subset.mp hnsub with ⟨j, hjS, hjnot⟩
  have hdisj : Disjoint ({j} : Finset (Fin L)) (circuitTouchedPairs c) := by
    simpa [Finset.disjoint_left] using hjnot
  have hsep := circuitMatrix_separates_firstEndpoints c ({j} : Finset (Fin L)) hdisj
  have hcut : firstEndpointSites ({j} : Finset (Fin L)) =
      ({(j, false)} : Finset (PairQubit L)) := by
    ext q
    rcases q with ⟨k, b⟩
    simp [firstEndpointSites, Prod.ext_iff]
  rw [hcut] at hsep
  have hgap := choiDist_circuit_harmonicMatchingEvolution_ge_of_separates_sharp
    c j t hsep (hactive j hjS).1 (hactive j hjS).2
  linarith

/-- **Harmonic-matching Choi laboratory ramp at the sharp radius.**  For every complete
laboratory shell `πK ≤ t < π(K+1)` with `2K ≤ L`, a circuit whose normalized Choi trace distance
to `U_L(t)` is smaller than `ε⋆` must use at least `K/2` two-qubit gates. -/
theorem harmonicMatching_twoGateCount_shell_lower_sharp
    {L K : ℕ} (c : List (LocalGate (PairQubit L)))
    (hKL : 2 * K ≤ L) {t : ℝ}
    (htlo : Real.pi * K ≤ t) (hthi : t < Real.pi * (K + 1))
    (hclose : choiDist (circuitMatrix c) (harmonicMatchingEvolution L t) <
      epsilonStar) :
    K ≤ 2 * twoGateCount c := by
  rw [← harmonicActiveBlock_card hKL]
  apply harmonicMatching_twoGateCount_activeSet_lower_sharp c
    (harmonicActiveBlock hKL) t
  · intro j hj
    exact harmonicActiveBlock_phase_bounds hKL htlo hthi hj
  · exact hclose

/-! ## Fixed-error Choi two-qubit-gate complexity -/

/-- Fixed-error Choi circuit complexity in two-qubit gates, `⊤` when the target is unreachable
inside the given error radius. -/
noncomputable def choiTwoGateComplexity (L : ℕ) (ε : ℝ)
    (U : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) : ℕ∞ :=
  ⨅ c ∈ {c : List (LocalGate (PairQubit L)) | choiDist (circuitMatrix c) U < ε},
    (twoGateCount c : ℕ∞)

theorem le_choiTwoGateComplexity_iff (L : ℕ) (ε : ℝ)
    (U : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) (G : ℕ∞) :
    G ≤ choiTwoGateComplexity L ε U ↔
      ∀ c : List (LocalGate (PairQubit L)),
        choiDist (circuitMatrix c) U < ε → G ≤ (twoGateCount c : ℕ∞) := by
  rw [choiTwoGateComplexity, le_iInf_iff]
  constructor
  · intro h c hc
    exact le_iInf_iff.mp (h c) hc
  · intro h c
    exact le_iInf fun hc => h c hc

theorem choiTwoGateComplexity_le_of_circuit {L : ℕ} {ε : ℝ}
    {U : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    {c : List (LocalGate (PairQubit L))} (hc : choiDist (circuitMatrix c) U < ε) :
    choiTwoGateComplexity L ε U ≤ (twoGateCount c : ℕ∞) := by
  refine le_trans (iInf_le _ c) ?_
  exact iInf_le
    (fun _ : c ∈ {c : List (LocalGate (PairQubit L)) | choiDist (circuitMatrix c) U < ε} =>
      (twoGateCount c : ℕ∞)) hc

/-- **Uniform ⌈K/2⌉ Choi complexity floor on the whole laboratory shell.** -/
theorem ceil_half_le_choiTwoGateComplexity_harmonicMatchingEvolution
    {L K : ℕ} (hKL : 2 * K ≤ L) {t : ℝ}
    (htlo : Real.pi * K ≤ t) (hthi : t < Real.pi * (K + 1)) :
    (((K + 1) / 2 : ℕ) : ℕ∞) ≤
      choiTwoGateComplexity L epsilonStar (harmonicMatchingEvolution L t) := by
  rw [le_choiTwoGateComplexity_iff]
  intro c hc
  have hK := harmonicMatching_twoGateCount_shell_lower_sharp c hKL htlo hthi hc
  have hnat : (K + 1) / 2 ≤ twoGateCount c := by omega
  exact_mod_cast Nat.cast_le (α := ℕ∞) |>.mpr hnat

end GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiSharpRamp
