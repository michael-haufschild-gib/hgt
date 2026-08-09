# Route R pre-polar horizontal-carrier annihilation

- **ID:** `route-r-prepolar-horizontal-carrier-annihilation`
- **Stage:** 1 — in progress
- **Type:** CONJECTURE / SOURCE PRODUCER
- **Route:** R
- **Scientific status:** `[OPEN CORE] [NOT RH PROOF]`
- **Statement:** Derive `BurnolXiCartierDividedShiftHeadFluxDissipativity` from a literal
  pre-divisor Euler--Gamma--Stokes law acting before polar completion, without importing an
  RH-equivalent annihilation, sewing, norm, or critical-line premise.

## Exact frontier

`SourceZeroHorizontalCarrier.lean` constructs and orients the multiplicity-exact, prime-labelled,
reflection-odd horizontal carrier and proves that its global vanishing is equivalent to RH.
`BurnolBocksteinLimit.lean` proves the Bockstein limit, forward/reflected residue landing, fixed
head-flux landing, and same-fibre Stokes transgression. These are closed receivers.

For every hypothetical right-half Xi divisor, Lean proves the landed current is strictly positive.
Consequently the desired nonpositive current cannot be obtained from post-landing positivity or
from an identity that already factors through critical-line placement. A valid producer must
independently make the hypothetical right-half source configuration inadmissible.

## Open claim

Construct a source-defined, pre-polar operation or pairing `A` on the two retained ordered cofinal
orientations such that:

1. `A` is defined from Euler, Gamma, rational-adelic/Stokes source data before Xi scalarization;
2. `A` retains prime, depth, divisor, multiplicity, and reflection provenance;
3. source exactness/positivity forces the fixed Burnol two-head defect to be nonpositive;
4. comparison with the already-formalized Bockstein/Stokes landing yields
   `BurnolXiCartierDividedShiftHeadFluxDissipativity`;
5. construction does not use RH, `Re rho = 1/2`, source-horizontal vanishing, source-dagger or
   same-fibre norm identity, forward/reflected sewing, or an equivalent endpoint predicate.

## Hostile falsifiers

- Completed-collar moment zero is insufficient: its kernel differs from Bockstein kernel and acts
  after the residue has been erased.
- Common determinant correction preserves the Bockstein zero radical and cannot create it.
- Fourier/reflection-invariant scalar readers erase the required odd orientation.
- Any claimed inequality obtained only after substituting an actual Xi divisor must be audited for
  equivalence to RH rather than accepted as source derivation.

## Gates

- [x] 0 → 1: exact source-pure question and circularity exclusions isolated
- [ ] conjecture survives internal and external audit
- [ ] complete dependency-closed paper proof
- [ ] Lean formalization
- [ ] RH

## Conjecture / proof-or-failure ledger

Active loop begins from the constructed horizontal carrier and the exact Burnol Bockstein/Stokes
landing. Each failed conjecture must record its killing mechanism and a stronger replacement.

## Log

- 2026-08-09 — reoriented after carrier construction and full Bockstein/Stokes formalization;
  independent pre-polar annihilation isolated as sole Route-R source producer.
