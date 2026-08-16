import GaloisForLFunctions.HTGeometry.LogNormalDifferentiatedEquation

/-!
# `(14)`: the exact differentiated cutoff identity

Cutting off a solution of the differentiated equation produces a source with three extra terms, all
of them harmless: the cutoff's own derivative appears twice, multiplied by the profile, and the
Gamma commutator appears once differentiated and once evaluated at the cutoff's derivative.  No
derivative of the profile ever sits inside a commutator — that is the point of the identity, and it
is what makes the right-hand side belong to the block source class.

The identity is exact and purely algebraic: it needs only that the transport is additive, commutes
with differentiation, and that multiplication by the cutoff obeys Leibniz.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The Gamma commutator of the transport with a multiplication operator. -/
def gammaCommutator (χ F : ℝ → ℝ) (L : ℝ) : ℝ :=
  gammaTransport (fun y => χ y * F y) L - χ L * gammaTransport F L

/-- **`(14)`: the exact differentiated cutoff identity.** -/
theorem gammaCutoff_differentiated_identity {F F' χ χ' G' : ℝ → ℝ}
    (hRF : ∀ L : ℝ, HasDerivAt (gammaTransport F) (gammaTransport F' L) L)
    (hRW : ∀ L : ℝ, HasDerivAt (gammaTransport fun y => χ y * F y)
      (gammaTransport (fun y => χ' y * F y + χ y * F' y) L) L)
    (hadd : ∀ L : ℝ, gammaTransport (fun y => χ' y * F y + χ y * F' y) L
      = gammaTransport (fun y => χ' y * F y) L + gammaTransport (fun y => χ y * F' y) L)
    (hχ : ∀ x : ℝ, HasDerivAt χ (χ' x) x)
    (heq : ∀ L : ℝ, 2 * L * F' L + F L + gammaTransport F' L = G' L)
    (L : ℝ) :
    2 * L * (χ' L * F L + χ L * F' L)
        + gammaTransport (fun y => χ' y * F y + χ y * F' y) L + χ L * F L
      = χ L * G' L
        + deriv (gammaCommutator χ F) L
        + (2 * L * (χ' L * F L) + gammaTransport (fun y => χ' y * F y) L)
        - gammaCommutator χ' F L := by
  have hcomm : HasDerivAt (gammaCommutator χ F)
      (gammaTransport (fun y => χ' y * F y + χ y * F' y) L
        - (χ' L * gammaTransport F L + χ L * gammaTransport F' L)) L := by
    have h := (hRW L).sub ((hχ L).mul (hRF L))
    exact h
  rw [hcomm.deriv, gammaCommutator, hadd L, ← heq L]
  ring

end GaloisForLFunctions.HTGeometry
