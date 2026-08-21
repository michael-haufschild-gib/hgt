/-
# Common-time hardness against a gate-word dictionary

Specialising the common-time law to the dictionary of states reachable from the seed by words of
`s` unitary gates.  An alphabet of at most `M` padded gate choices makes the dictionary satisfy the
counting condition, and unitarity makes each of its members a unit vector, so both hypotheses of
the fixed-time law are met.  With the identity gate available the dictionary also contains every
endpoint of a shorter word, so hardness against it is hardness against the whole depth-`s` circuit
ball.

Main results:
* `le_limsup_quenchedFixedTimeProb_gateWord` — **`(9)` against the depth-`s` circuit ball**.
* `exists_restricted_goodSet_gateWord` — **`(8a)`** in the same form.
-/
import GaloisForLFunctions.HTGeometry.CommonTimeCircuitHardness
import GaloisForLFunctions.HTGeometry.GateWordDictionary

open MeasureTheory Filter Set Matrix
open scoped ENNReal Topology Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n q : ℕ}

/-- The depth-`s` dictionary of states reachable from the all-zero product state. -/
abbrev circuitBallDictionary {Γ : Type}
    (g : Γ → Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ)
    (s : ℕ) : (Fin s → Γ) → (FiniteQubitConfiguration (Fin n) → ℂ) :=
  wordState g (zeroProductState (Fin n))

/-- **`(9)` against the depth-`s` circuit ball.**  At an unbounded sequence of common deterministic
times, a fraction at least `(1-2^{-r/2})/2` of the Gaussian ensemble evolves the all-zero product
state to a point farther than `eps` from every state reachable by `s` gates. -/
theorem le_limsup_quenchedFixedTimeProb_gateWord
    {Γ : Type} [Fintype Γ] [Nonempty Γ]
    (g : Γ → Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ)
    (hg : ∀ c, g c ∈ Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hwsupp : SupportInvariantWeight w)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0)
    (hcard0 : 0 < Fintype.card (Fin n → Option (Fin 3)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : 2 * Real.log (8 * Fintype.card (Fin n → Option (Fin 3))) ≤ B ^ 2)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    {r : ℕ} (hr : 1 ≤ r)
    (hscale : 16 * (4 * (2 / 3 : ℝ) ^ n) / (1 - eps ^ 2) ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) (hΓ : (Fintype.card Γ : ℝ) ≤ M) {s : ℕ}
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    (1 - ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))) / 2
      ≤ limsup (fun t => quenchedFixedTimeProb
          (centredProductGaussian (Fin n → Option (Fin 3)) 1)
          (hardCircuitEvent w (zeroProductState (Fin n)) eps
            (circuitBallDictionary g s)) t) atTop := by
  have hOmega : finiteComplexInner (zeroProductState (Fin n)) (zeroProductState (Fin n)) = 1 := by
    rw [finiteComplexInner_self_eq_sum_normSq, sum_normSq_zeroProductState]
    norm_num
  exact le_limsup_quenchedFixedTimeProb_pauliEnsemble w hq hwsupp hw hwne hcard0 hB0 hB
    (circuitBallDictionary g s)
    (fun κ => finiteComplexInner_wordState_self hg hOmega κ) heps0 heps1 hr hscale hM
    (card_wordIndex_le_pow hΓ hM.le s) hs

/-- **`(8a)` against the depth-`s` circuit ball.** -/
theorem exists_restricted_goodSet_gateWord
    {Γ : Type} [Fintype Γ] [Nonempty Γ]
    (g : Γ → Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ)
    (hg : ∀ c, g c ∈ Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hwsupp : SupportInvariantWeight w)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0)
    (hcard0 : 0 < Fintype.card (Fin n → Option (Fin 3)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : 2 * Real.log (8 * Fintype.card (Fin n → Option (Fin 3))) ≤ B ^ 2)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    {r : ℕ} (hr : 1 ≤ r)
    (hscale : 16 * (4 * (2 / 3 : ℝ) ^ n) / (1 - eps ^ 2) ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) (hΓ : (Fintype.card Γ : ℝ) ≤ M) {s : ℕ}
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    ∃ G : Set ((Fin n → Option (Fin 3)) → ℝ), MeasurableSet G ∧
      G ⊆ gaussianGoodSet w B 4 ∧
      1 / 2 ≤ centredProductGaussian (Fin n → Option (Fin 3)) 1 G ∧
      (1 - ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))) / 2
        ≤ liminf (fun T => quenchedWindowAverage
            (centredProductGaussian (Fin n → Option (Fin 3)) 1)
            (hardCircuitEvent w (zeroProductState (Fin n)) eps (circuitBallDictionary g s) ∩
              G ×ˢ (Set.univ : Set ℝ)) T) atTop ∧
      (1 - ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))) / 2
        ≤ limsup (fun t => quenchedFixedTimeProb
            (centredProductGaussian (Fin n → Option (Fin 3)) 1)
            (hardCircuitEvent w (zeroProductState (Fin n)) eps (circuitBallDictionary g s) ∩
              G ×ˢ (Set.univ : Set ℝ)) t) atTop := by
  have hOmega : finiteComplexInner (zeroProductState (Fin n)) (zeroProductState (Fin n)) = 1 := by
    rw [finiteComplexInner_self_eq_sum_normSq, sum_normSq_zeroProductState]
    norm_num
  exact exists_restricted_goodSet_common_time_hardness w hq hwsupp hw hwne hcard0 hB0 hB
    (circuitBallDictionary g s)
    (fun κ => finiteComplexInner_wordState_self hg hOmega κ) heps0 heps1 hr hscale hM
    (card_wordIndex_le_pow hΓ hM.le s) hs

end GaloisForLFunctions.HTGeometry

end
