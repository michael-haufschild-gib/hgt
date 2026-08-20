/-
# The fixed-shell mean collision

The Clifford coefficient map is a signed permutation, so the fixed-shell coefficient law is
invariant under it, and the Clifford-orbit averaging bound applies verbatim: the mean spectral
collision of the all-zero product input under the fixed-shell Pauli ensemble is at most `(2/3)ⁿ`.
No radius is randomized -- every member of the ensemble has the same normalized interaction rate.

Main results:
* `measurePreserving_cliffordCoefficientMap_shell` — the shell law is Clifford invariant.
* `integral_spectralCollision_shell_le` — **the fixed-shell mean collision is at most `(2/3)ⁿ`**.
-/
import GaloisForLFunctions.HTGeometry.ShellProbabilityMeasure
import GaloisForLFunctions.HTGeometry.CliffordEnsembleCollisionMean

open Matrix MeasureTheory
open QuantumAlg

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **The fixed-shell coefficient law is invariant under product-Clifford conjugation.** -/
theorem measurePreserving_cliffordCoefficientMap_shell
    (g : σ → QubitTwoDesign.BinaryOctahedral) :
    MeasurePreserving (cliffordCoefficientMap g)
      (shellProbability (σ → Option (Fin 3))) (shellProbability (σ → Option (Fin 3))) :=
  measurePreserving_signedPerm_shellProbability (productCliffordRelabelEquiv g).symm
    (ε := fun Q => productCliffordSign g ((productCliffordRelabelEquiv g).symm Q))
    (fun _ => productCliffordSign_eq_one_or_neg_one g _)

variable {n : ℕ}

/-- **The fixed-shell mean spectral collision of the all-zero product input is at most `(2/3)ⁿ`.** -/
theorem integral_spectralCollision_shell_le
    (w : (Fin n → Option (Fin 3)) → ℝ) (hw : SupportInvariantWeight w)
    {e : ((Fin n → Option (Fin 3)) → ℝ) →
      FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ}
    {lam : ((Fin n → Option (Fin 3)) → ℝ) → FiniteQubitConfiguration (Fin n) → ℝ}
    (hae : ∀ᵐ J ∂(shellProbability (Fin n → Option (Fin 3))),
      IsOrthoEigenBasis (pauliEnsemble w J) (e J) (lam J) ∧ Function.Injective (lam J)) :
    (∫ J, spectralCollision (e J) (zeroProductState (Fin n))
        ∂(shellProbability (Fin n → Option (Fin 3)))) ≤ (2 / 3 : ℝ) ^ n :=
  integral_spectralCollision_zeroProductState_le_of_invariant w hw
    (fun g => measurePreserving_cliffordCoefficientMap_shell g) hae

/-- **Markov bound on the fixed shell.**  The quenched collision exceeds `L (2/3)ⁿ` with shell
probability at most `1/L`. -/
theorem measureReal_spectralCollision_shell_ge_le
    (w : (Fin n → Option (Fin 3)) → ℝ) (hw : SupportInvariantWeight w)
    {e : ((Fin n → Option (Fin 3)) → ℝ) →
      FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ}
    {lam : ((Fin n → Option (Fin 3)) → ℝ) → FiniteQubitConfiguration (Fin n) → ℝ}
    (hae : ∀ᵐ J ∂(shellProbability (Fin n → Option (Fin 3))),
      IsOrthoEigenBasis (pauliEnsemble w J) (e J) (lam J) ∧ Function.Injective (lam J))
    {L : ℝ} (hL : 0 < L) :
    (shellProbability (Fin n → Option (Fin 3))).real
        {J | L * (2 / 3 : ℝ) ^ n ≤ spectralCollision (e J) (zeroProductState (Fin n))}
      ≤ 1 / L :=
  measureReal_spectralCollision_ge_le (fun x y => measurable_pauliEnsemble_entry w x y)
    (sum_normSq_zeroProductState (Fin n)) hae (by positivity)
    (integral_spectralCollision_shell_le w hw hae) hL

end

end GaloisForLFunctions.HTGeometry
