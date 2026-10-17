# Source-admitted full-half-line signed Chebyshev transport

- **ID:** signed-prime-polar-halfline
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** `1-in-progress/signed-prime-polar-transport-2026-10-17.md`
- **Ledger:** `docs/reports/BiScaleUncertainty/SignedPrimePolarTransport-FACTS.md`

## Mathematical obligation

Construct the literal infinite von Mangoldt sum minus the full positive-half-line
polar integral for every compact continuous source. Derive absolute summability,
work-term integrability, a common source cutoff for all right-annular averages,
and disappearance of the upper endpoint. Transfer the verified signed Gram
transport to this actual global scalar pairing without adding analytic premises.

## Proof plan

- [x] Search current corpus and inspect newly added neighboring Chebyshev modules.
- [x] Identify remaining gap: existing neighboring results retain finite cutoff/tail
  terms or use stronger source classes; none retrieved supplies this source-only domain closure.
- [x] Critique: totalized Lean integrals/tsums alone do not establish convergence;
  prove admission explicitly. Scalar tail vanishing says nothing about packet norm tails.
- [x] Dependency-closed paper proof: `docs/reports/BiScaleUncertainty/SignedPrimePolarHalfLine.md`.
- [x] Source cutoff and domain leaf verified by direct Lean check without diagnostics.
- [x] Prove common tail vanishing for h, H, and its constructed derivative V.
- [x] Prove finite atom support, absolute summability, and polar half-line integrability.
- [x] Identify full pairing with its stabilized finite expression.
- [x] Verify global work admission, endpoint removal, and transport leaf.
- [x] Prove global source-only signed transport, audit leaves, wire, and update ledger.

Both leaves pass direct `lake --old env lean <leaf> -o <leaf.olean>` without
diagnostics. Seven endpoint axiom reports contain only propext, Classical.choice,
and Quot.sound; main signatures require only the source and numerical parameters.
Evidence: `/tmp/spp3-final-axioms.log`, `/tmp/spp3-domain-build.log`,
`/tmp/spp3-transport-build.log`. Current global lint status is in the ledger.

## Significance and limits

The theorem closes the global scalar domain requested by the research program.
It is one package, not separate counts for convergence, support, and corollaries.
No full-half-line signed source packet or cutoff-uniform Gram bound is asserted.
