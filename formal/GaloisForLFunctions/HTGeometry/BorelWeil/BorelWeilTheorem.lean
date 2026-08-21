import GaloisForLFunctions.HTGeometry.BorelWeil.CompleteReducibility
import GaloisForLFunctions.HTGeometry.BorelWeil.TorusWeight
import GaloisForLFunctions.HTGeometry.BorelWeil.PolyVanishing

/-!
# The Borel–Weil theorem

Let `k` be a field, `G = GL(N,k)`, and `B ≤ G` the Borel subgroup of invertible upper-triangular
matrices.  For a weight `lam : Fin N → ℕ` the line bundle `L_lam = G ×^B k_lam` on the flag
variety `G/B` has, in the associated-bundle description, the space of global sections

`H⁰(lam) = polySections lam = { p ∈ k[X_{ij}] : p(g B) = (∏ i, B i i ^ lam i) · p(g) }`,

on which `G` acts by left translation `substLeft`.  This file collects the statements of the
Borel–Weil theorem proved in this directory.

## Main results

* `borelWeil_ne_bot_iff_dominant` — `H⁰(lam) ≠ 0` exactly for dominant (antitone) `lam`.
* `borelWeil_finiteDimensional` — `H⁰(lam)` is finite dimensional.
* `borelWeil_highest_weight_line` — the lower unitriangular invariants form a line, spanned by the
  product of leading principal minors.
* `borelWeil_highest_weight` — the torus acts on that line by the character `lam`.
* `borelWeil_irreducible` — in characteristic zero `H⁰(lam)` is an irreducible `G`-module.
* `borelWeil_group_model_ne_bot_iff_dominant` — the same dominance criterion in the group model
  `SL(N,k)`.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- **Borel–Weil, non-vanishing.**  The sections of `L_lam` are nonzero exactly for dominant
`lam`. -/
theorem borelWeil_ne_bot_iff_dominant [Infinite k] {lam : Fin N → ℕ} :
    polySections (k := k) lam ≠ ⊥ ↔ Antitone lam :=
  polySections_ne_bot_iff_antitone

/-- **Borel–Weil, finite dimensionality.** -/
theorem borelWeil_finiteDimensional [Infinite k] (lam : Fin N → ℕ) :
    FiniteDimensional k (polySections (k := k) lam) :=
  finiteDimensional_polySections lam

/-- **Borel–Weil, the highest weight line.**  The vectors of `H⁰(lam)` invariant under left
translation by the lower unitriangular group form a one-dimensional space, spanned by the product
of leading principal minors. -/
theorem borelWeil_highest_weight_line [Infinite k] {lam : Fin N → ℕ} (hlam : Antitone lam) :
    lowerUniInvariants (k := k) lam = Submodule.span k {bwPoly (multOfWeight lam) k} ∧
      Module.finrank k (lowerUniInvariants (k := k) lam) = 1 :=
  ⟨lowerUniInvariants_eq_span hlam, finrank_lowerUniInvariants hlam⟩

/-- **Borel–Weil, the highest weight.**  The diagonal torus acts on the highest weight vector by
the character `lam`. -/
theorem borelWeil_highest_weight [Infinite k] {lam : Fin N → ℕ} (hlam : Antitone lam)
    (t : Fin N → k) :
    substLeft (Matrix.diagonal t) (bwPoly (multOfWeight lam) k)
      = (∏ i : Fin N, (t i) ^ (lam i)) • bwPoly (multOfWeight lam) k := by
  rw [substLeft_diagonal_bwPoly, weightOfMult_multOfWeight hlam]

/-- **The Borel–Weil theorem.**  In characteristic zero the space of sections of the Borel–Weil
line bundle attached to a dominant weight is an irreducible representation of `GL(N,k)`: every
nonzero `GL`-stable subspace is the whole space. -/
theorem borelWeil_irreducible [CharZero k] {lam : Fin N → ℕ} (hlam : Antitone lam)
    {M : Submodule k (MvPolynomial (Fin N × Fin N) k)} (hle : M ≤ polySections lam)
    (hstab : IsGStable M) (hM : M ≠ ⊥) : M = polySections (k := k) lam :=
  polySections_irreducible hlam hle hstab hM

/-- **Borel–Weil in the group model.**  The same dominance criterion for regular functions on
`SL(N,k)` transforming by a character of the Borel. -/
theorem borelWeil_group_model_ne_bot_iff_dominant [Infinite k] {lam : Fin N → ℕ} :
    bwSections (k := k) lam ≠ ⊥ ↔ Antitone lam :=
  bwSections_ne_bot_iff_antitone

end GaloisForLFunctions.HTGeometry.BorelWeil
