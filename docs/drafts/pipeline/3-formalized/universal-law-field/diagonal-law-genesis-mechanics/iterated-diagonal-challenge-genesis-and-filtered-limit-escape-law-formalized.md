# Iterated diagonal challenge genesis and filtered-limit escape -- Lean certification

- **ID:** ULF-DJG-1
- **Paper card:**
  `2-fully-proven/universal-law-field/diagonal-law-genesis-mechanics/iterated-diagonal-challenge-genesis-and-filtered-limit-escape-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveDiagonalLawGenesis`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-PROVED] [AXIOM-AUDITED] [ROUTE-INDEPENDENT] [NOT RH]

## Certified surface

Lean defines:

- `BooleanSelfEvaluator`, `evaluatorAntiDiagonal`, and generic diagonal novelty;
- one-point conservative `evaluatorSuccessor`;
- `BooleanEvaluatorExtension` and the theorem that every anti-diagonal realization lies outside
  the old carrier image;
- `BooleanEvaluatorEquiv`, inverse equivalence, and successor naturality;
- `finiteDiagonalEvaluator` and `finiteDiagonalSuccessorEquiv`;
- `diagonalLimitEvaluator`, finite row support, finite-column realization, and global
  nonrealization;
- the top-row invariant separating the limit from its successor;
- infinite support of the successor's fresh row on the old carrier; and
- unconditional capstone `diagonalLawGenesis_unconditional`.

## Exact theorem

Every Boolean self-evaluator produces an unrepresented challenge by complementing its diagonal.
One fresh reporter realizes that challenge conservatively and minimally.  Iteration is canonically
the strict-order tower on `Fin n`.  At the `Nat` limit every finite column set is matched by some
row, while no row realizes the all-true challenge.  Every limit row has finite support, but the
successor has a top row with infinite old support, so the limit and successor are not
evaluator-isomorphic.  Finite diagonal succession therefore fails exact exchange with this
cofinal formation.

## Verification

- direct `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveDiagonalLawGenesis.lean`: pass,
  no warnings;
- leaf `lake build GaloisForLFunctions.HTGeometry.ConstitutiveDiagonalLawGenesis`: 2,997 jobs,
  pass;
- axiom prints on generic novelty, no-isomorphism, and capstone: only `propext`,
  `Classical.choice`, and `Quot.sound`;
- module imported by `HTGeometry.UniversalLawField`; umbrella audit passes, with unrelated replay
  warnings outside the owned module.

## Scope

This certifies a source-normal grammar-update mechanism and a formation/cofinal nonexchange law.
It does not prove a new diagonal theorem, identify every open-genesis mechanism, realize an RH
route, or prove RH.  Cross-doctrine realizations and recursive challenge semantics remain open.
