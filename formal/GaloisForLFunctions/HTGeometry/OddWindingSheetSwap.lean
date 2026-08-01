import GaloisForLFunctions.Bottcher.Pi1CMinusZero
import Mathlib.Tactic

/-!
# Odd winding forces a two-sheeted return to the opposite sheet

This file isolates the topological mechanism behind simple quadratic
spectral monodromy.  A continuous nonzero square-root lift over a closed
loop cannot itself close when the radicand loop has odd winding.  Since the
two possible endpoints have equal squares, the lift must return with the
opposite sign.

The statement is independent of analyticity and of any particular
Hamiltonian.  It is the path-level parity law needed to turn a simple
quadratic branch divisor into an actual spectral transposition.
-/

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

open Pi1CMinusZero

/-- A continuous nonzero square-root lift over an odd-winding closed
radicand loop returns on the opposite sheet.

`rootSquareClosed` supplies the endpoint dichotomy.  `normalizedSquare`
identifies the pointwise square of the normalized lift with the based loop.
If the lift closed, that loop would be a pointwise square and therefore
have even degree, contradicting `oddDegree`. -/
theorem squareRootPath_endpoint_eq_neg_of_oddDegree
    (root : C(I, ℂ))
    (root_ne_zero : ∀ s : I, root s ≠ 0)
    (rootSquareClosed : (root 1) ^ 2 = (root 0) ^ 2)
    (radicand : Path Pi1CMinusZero.one_cs Pi1CMinusZero.one_cs)
    (normalizedSquare :
      ∀ s : I, (root s / root 0) ^ 2 = (radicand s : ℂ))
    (oddDegree :
      ∃ k : ℤ, Pi1CMinusZero.degZ ⟦radicand⟧ = 2 * k + 1) :
    root 1 = -root 0 := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp rootSquareClosed with same | opposite
  · exfalso
    let normalizedRoot : Path Pi1CMinusZero.one_cs
        Pi1CMinusZero.one_cs :=
      { toFun := fun s =>
          ⟨root s / root 0,
            div_ne_zero (root_ne_zero s) (root_ne_zero 0)⟩
        continuous_toFun :=
          (root.continuous.div_const _).subtype_mk _
        source' := by
          apply Subtype.ext
          show root 0 / root 0 = (1 : ℂ)
          exact div_self (root_ne_zero 0)
        target' := by
          apply Subtype.ext
          show root 1 / root 0 = (1 : ℂ)
          rw [same]
          exact div_self (root_ne_zero 0) }
    have squarePath :
        Pi1CMinusZero.sqLoop normalizedRoot = radicand := by
      apply Path.ext
      funext s
      apply Subtype.ext
      show (root s / root 0) ^ 2 = (radicand s : ℂ)
      exact normalizedSquare s
    obtain ⟨k, hk⟩ := oddDegree
    have evenDegree :
        Pi1CMinusZero.degZ ⟦radicand⟧ =
          2 * Pi1CMinusZero.degZ ⟦normalizedRoot⟧ := by
      rw [← squarePath, Pi1CMinusZero.degZ_sqLoop]
    omega
  · exact opposite

end GaloisForLFunctions.HTGeometry
