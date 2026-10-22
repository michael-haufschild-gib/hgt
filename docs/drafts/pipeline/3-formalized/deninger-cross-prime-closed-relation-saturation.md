# Calderón--Witt dense-core closed-relation saturation

- **ID:** `deninger-cross-prime-closed-relation-saturation`
- **Stage:** 3-formalized
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/deninger/deninger-cross-prime-closed-relation-saturation.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittCrossPrimeClosedRelationNoGo`

## Formalized capstones

- `closedLinearRelation_eq_top_prod_vertical_of_dense_zeroCore`:
  every closed linear relation containing a dense zero graph is the full
  source space times its vertical fibre;
- `deningerCalderonWittCrossPrimeClosedRelation_eq_top_prod_vertical`:
  specialization to the dense actual ordered Calderón--Witt witness span;
- `deningerCalderonWittCrossPrimeClosedRelation_eq_zeroGraph_of_singleValued`:
  every single-valued such closed relation is the full zero graph;
- `deningerCalderonWittCrossPrimeClosableExtension_closure_eq_zero`:
  every closable partial operator agreeing with the old zero boundary on the
  actual source core has zero closure.

All statements are unconditional.  No RH, zero-location, positivity,
spectral-synthesis, or source-annihilation premise occurs.

## Verification

- direct foreground check:
  `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerCalderonWittCrossPrimeClosedRelationNoGo.lean`
  passed;
- umbrella import added to `GaloisForLFunctions/RHTower.lean`;
- targeted final audit:
  `lake build GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittCrossPrimeClosedRelationNoGo`
  passed;
- `#print axioms` for all four capstones reports exactly
  `propext`, `Classical.choice`, and `Quot.sound`;
- `scripts/formal_tools.py lint` passed.

## Scientific consequence

The former continuous-extension wall is now a closed-relation
classification.  Strict/unbounded Hilbert completion of the old oriented
boundary cannot be the missing Route-L transgression.  A nonzero closed
relation extending that dense zero core is maximally nonselective: all its
outputs are vertical at zero and at every source input.  The live
annihilator must therefore introduce a new horizontal arithmetic action on
finite actual witnesses, or change the source topology and relation before
the `ell2` completion.
