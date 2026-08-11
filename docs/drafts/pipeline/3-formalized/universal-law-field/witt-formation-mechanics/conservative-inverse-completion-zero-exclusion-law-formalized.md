# Conservative inverse completion and zero exclusion — Lean certification

- **ID:** ULF-WFM-3-LEAN
- **Stage:** 3-formalized
- **Paper parent:**
  `../../../2-fully-proven/universal-law-field/witt-formation-mechanics/conservative-inverse-completion-zero-exclusion-and-rh-selection-gate-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.WittConservativeInverseCompletion`
- **Status:** `[LEAN-CERTIFIED ABSTRACT CORE] [UMBRELLA WIRED] [NO AXIOMS ADDED] [NOT RH]`

## Certified surface

Lean proves:

1. exact right inverses survive joint convergence in a Hausdorff topological monoid with continuous
   multiplication;
2. in a nontrivial monoid with zero, the completed formation is nonzero;
3. every unital multiplicative receiver sees a nonzero completed formation;
4. one pointwise jointly convergent inverse family excludes zeros at every receiver index;
5. the complex-valued universal law is an unconditional closed theorem.

Principal declarations:

- `wittConservativeInverse_limit`;
- `wittConservativeInverse_limit_ne_zero`;
- `wittConservativeInverse_receiver_ne_zero`;
- `wittConservativeInverse_pointwise_ne_zero`;
- `wittConservativeInverseCompletion_closed`.

## Boundary

No formal declaration asserts existence of a source-generated Euler-shell completion on the
critical half-plane.  No Xi or zeta zero premise, analytic-continuation placeholder, or RH theorem
is imported.  Lean certifies exactly the abstract selection consequence that any future source
construction must discharge.

## Verification

- direct elaboration:
  `lake env lean GaloisForLFunctions/HTGeometry/WittConservativeInverseCompletion.lean`;
- final compiled audit:
  `lake build GaloisForLFunctions.HTGeometry.WittConservativeInverseCompletion`;
- module wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`;
- axiom audit reports only standard quotient/extensionality infrastructure and no project axiom;
- no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or computation certificate occurs in the module.
