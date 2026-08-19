# Deninger Q8 actual group representation

- **ID:** deninger-q8-actual-group-representation
- **Stage:** 3-formalized
- **Type:** LITERATURE FRONTIER / LEAN
- **Source:** Deninger, *A note on arithmetic cohomology*, Theorem 2.13; finite `Q₈` representation-theoretic input
- **Status:** `[LEAN-PROVED] [NO ARITHMETIC ROOT-NUMBER CLAIM]`

## Exact formal theorem

`DeningerQ8ActualGroupRepresentation.lean` defines
`deningerQ8Representation : QuaternionGroup 2 →* Module.End ℂ (ℂ × ℂ)` and proves:

- literal multiplication compatibility for all group elements;
- `a 1` acts by Deninger's `I` transition and `xa 0` by the `K` transition;
- central `a 2` acts as `-1`;
- every group element preserves the standard nondegenerate alternating form.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/DeningerQ8ActualGroupRepresentation.lean` — green.
- `lake build GaloisForLFunctions.RHTower.DeningerQ8ActualGroupRepresentation` — green.
- `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`.

## Remaining literature boundary

This is not a finite Galois extension, an Artin `L`-function, or a root-number computation.
The remaining theorem needed for Deninger's global no-go is an explicit quaternion number-field
witness with Artin root number `-1`, followed by formalization of property 2.12 and real-descent
multiplicity identification.  None is inferred from the finite representation.

## 2026-08-19 Artin-Galois bridge

The pre-existing `DeningerQ8ArtinGaloisRealization.lean` module has been repaired for the current
Lean parser and wired into the RHTower umbrella.  It pulls the literal Q8 action through any actual
field-Galois identification `Gal(L/K) ≃ Q8`.  It proves the resulting degree-two symplectic Artin
representation, scalar `-1` action of the distinguished central involution, and
`[L : K] = 8`.  For a number-field instance it also instantiates the literal finite-place Artin
Euler product and proves its holomorphy and nonvanishing in `Re(s) > 1`.

This is a `[LEAN-PROVED]` Artin realization bridge, not new arithmetic, and not the missing explicit Q8 number field or
the required global root-number computation.  Both `lake env lean
GaloisForLFunctions/RHTower/DeningerQ8ArtinGaloisRealization.lean` and its targeted `lake build`
leaf passed after wiring; `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`.
