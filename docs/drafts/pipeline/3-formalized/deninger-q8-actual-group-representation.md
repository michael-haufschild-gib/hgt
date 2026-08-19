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
