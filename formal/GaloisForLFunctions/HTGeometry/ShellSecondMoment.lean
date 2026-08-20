/-
# The fixed-shell second moment, with the almost-sure hypothesis discharged

Combining the shell-invariant Clifford-orbit bound with the shell-almost-sure simple spectrum gives
the card's `(23)` and `(24)` with no hypotheses beyond the ones the setup already places on the
weight function: support invariance, support inside the nonidentity strings of bounded weight, and
non-vanishing there.

Main results:
* `integral_spectralCollision_shell_le_of_weights` — **`(23)` on the fixed shell**.
* `measureReal_spectralCollision_shell_ge_le_of_weights` — **`(24)` on the fixed shell**.
-/
import GaloisForLFunctions.HTGeometry.ShellCliffordCollisionMean
import GaloisForLFunctions.HTGeometry.ShellSimpleSpectrum

open Matrix MeasureTheory
open QuantumAlg

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n q : ℕ}

/-- **The mean spectral collision of the all-zero product input on the fixed shell is at most
`(2/3)ⁿ`.** -/
theorem integral_spectralCollision_shell_le_of_weights (w : (Fin n → Option (Fin 3)) → ℝ)
    (hsupp : SupportInvariantWeight w) (hq : 2 ≤ q)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0) :
    (∫ J, spectralCollision
        (hermitianEigenBasis (pauliEnsemble w J) (isHermitian_pauliEnsemble w J))
        (zeroProductState (Fin n)) ∂(shellProbability (Fin n → Option (Fin 3))))
      ≤ (2 / 3 : ℝ) ^ n :=
  integral_spectralCollision_shell_le w hsupp
    (isOrthoEigenBasis_injective_pauliEnsemble_shell_ae (q := q) w hq hw hwne)

/-- **The good angular set of the fixed shell has measure at least `1 − 1/L`.** -/
theorem measureReal_spectralCollision_shell_ge_le_of_weights (w : (Fin n → Option (Fin 3)) → ℝ)
    (hsupp : SupportInvariantWeight w) (hq : 2 ≤ q)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0)
    {L : ℝ} (hL : 0 < L) :
    (shellProbability (Fin n → Option (Fin 3))).real
        {J | L * (2 / 3 : ℝ) ^ n ≤ spectralCollision
          (hermitianEigenBasis (pauliEnsemble w J) (isHermitian_pauliEnsemble w J))
          (zeroProductState (Fin n))}
      ≤ 1 / L :=
  measureReal_spectralCollision_shell_ge_le w hsupp
    (isOrthoEigenBasis_injective_pauliEnsemble_shell_ae (q := q) w hq hw hwne) hL

end

end GaloisForLFunctions.HTGeometry
