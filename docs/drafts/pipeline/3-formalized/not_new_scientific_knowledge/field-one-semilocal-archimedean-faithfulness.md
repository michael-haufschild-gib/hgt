# Archimedean faithfulness of the semilocal Weyl tensor

- **ID:** `field-one-semilocal-archimedean-faithfulness`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-finite-adele-integral-bruhat-test`
- **Statement:** equality of semilocal Weyl tensor operators forces equality of their real
  coordinates; consequently, the rational diagonal Weyl representation is faithful.

## Proof

Test two equal semilocal operators on \(f\otimes1_U\), then apply finite-zero contraction.
Because every finite multiplier has value one at zero on \(1_U\), contraction recovers exactly
the normalized real multiplier \(W^\infty_{2\pi a_\infty}f\). Archimedean faithfulness and
\(2\pi\ne0\) imply \(a_\infty=b_\infty\). On diagonal rational parameters, equality of real
coordinates implies equality of the rationals.

This does not assert full finite-adele self-duality or separation of arbitrary pairs with the
same real coordinate.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneSemilocalArchimedeanFaithfulness`
- **Core theorems:** `fieldOneSemilocalArchimedeanWeylMultiplier_injective`,
  `fieldOneSemilocalBruhatWeylMultiplier_eq_imp_fst_eq`,
  `fieldOneRationalDiagonalBruhatWeylMultiplier_injective`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved for final
  audit.

## Gates

- [x] 0 → 1: exact contraction statement typed
- [x] 1 → 2: dependency-closed faithfulness proof
- [x] 2 → 3: unconditional Lean theorem, direct leaf check, and axiom audit
- [ ] 3 → 4: publication-ready integration
