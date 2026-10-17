# Signed prime–polar transport and Chebyshev coupling

- **ID:** signed-prime-polar-transport
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Scope:** Independent BiScaleUncertainty; 100 substantial contributions requested.
- **Ledger:** `docs/reports/BiScaleUncertainty/SignedPrimePolarTransport-FACTS.md`

## Current mathematical target

Obtain quantitative control of the actual signed prime–polar packet energy while
retaining both mixed terms and the source correlation geometry. The literal
full-half-line scalar pairing and Chebyshev work are now admitted and coupled.
Scalar support stabilization does not imply packet norm stabilization.
The coherent collar Schur constraint now gives joint lower control of packet
energy. A source-only upper bound now retains the explicit roughness remainder.
Next: quantify its gauge cost and roughness using original-source translation geometry.

Authoritative field direction: `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`.
Read all 242 lines on 2026-10-17; read-only by user instruction. Section 3.3 directly
supports this topic. Preserve arbitrary correlation signs and actual prime weights.

## Proof plan and verification

- [x] Read field motivation and Pillars XIV–XV; inspect existing corpus.
- [x] Identify missing actual arithmetic coupling and rough-source admission.
- [x] Prove the collar average differentiable, with explicit derivative and local Lévy penalty.
- [x] Prove exact finite-window Chebyshev identity with all boundary terms.
- [x] Combine uniform Krein averaging error with actual signed prime–polar pairing.
- [x] Write dependency-closed paper proof and precise contribution boundary.
- [x] Audit new leaves using `lake --old env lean`, check axioms in `/tmp`, wire umbrella.
- [x] Construct actual signed prime–polar source packet and justify mixed Fubini.
- [x] Prove exact signed Gram identity and Q_L≤M_L²h(0).
- [x] Transfer signed packet chords through annular averaging to Chebyshev work.
- [x] Write dependency-closed packet paper proof; audit and wire both new leaves.
- [x] Run formal lint and refresh indexes for the first two packages.
- [x] Close the literal full-half-line scalar domain and endpoint obligations.
- [x] Verify both half-line leaves and seven endpoint axiom reports; wire imports.
- [x] Construct the coherent collar source and its full double Gram energy.
- [x] Prove joint Schur transport and packet-energy lower certificates, finite and global.
- [x] Audit both coherent-Schur leaves, ten axiom reports, and main signatures.
- [x] Establish the rough-source upper bound, deriving C¹ regularity from the actual
  continuous source; verify both leaves, endpoint/dependency axioms, and signatures.
- [ ] Quantify gauge cost and smoothing error directly from source correlations.

## Current frontier

Five substantive contributions are formalized:
- `3-formalized/annular-signed-prime-polar-chebyshev-coupling-2026-10-17.md`.
- `3-formalized/signed-prime-polar-packet-gram-2026-10-17.md`.
- `3-formalized/signed-prime-polar-halfline-2026-10-17.md`.
- `3-formalized/signed-prime-polar-coherent-schur-2026-10-17.md`.
- `3-formalized/signed-prime-polar-rough-gauge-2026-10-17.md`.

The overall target remains 100, with 95 further distinct contributions unproved.
Packet construction, exact Gram representation, mass comparison, and transport
corollaries form one contribution. Likewise the coherent collar construction,
Schur constraint, and energy certificate are one contribution, not separate counts.

## Research discipline

Count theorem packages resolving distinct mathematical issues, never helper lemmas.
Search found local collar transport and kernel-specific Chebyshev identities;
no retrieved result supplies this complete rough-source coupling. Search coverage
and partial results are recorded per package in the facts ledger; no external
novelty claim follows.
The 100-contribution goal remains active after any individual package.

## State

Current turn made verified progress. The 100-contribution goal remains active.
The full-half-line scalar theorem is complete; a uniform signed-packet estimate
remains unproved. Latest lint and index results are recorded in the facts ledger.
`update_plan` is unavailable; this card carries the executable plan.
Serena cannot extract Lean symbols (active language Python); use precise patches.
