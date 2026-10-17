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
The exact gauge energy and its support budget now eliminate the constructed
gauge norm. Signed scalar compensation is now optimized exactly, including
degenerate cases. Trap 10 has now led to an explicit producer: the factorial
bi-null stencil is lifted to the actual signed prime–polar measure, with real-ratio
continuum cutoffs and an unconditional harmonic correction bound. A compact
continuous producer now preserves every prime-grid value with 1≤∫S_N²≤16.
Actual source factorization now preserves the grid with nonvanishing contrast size
and equal source origin energies in [6sqrt(N),46sqrt(N)].
Next: quantitative archimedean jump cost of these explicit sources.
Multiple-collar receivers are parked; width selection and residual control remain open.

Authoritative field direction: `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`.
Read fully on 2026-10-17, then read the complete update adding Section 3.5 and
Trap 10; read-only by user instruction. Section 3.3 directly supports this topic.
Preserve arbitrary correlation signs and actual prime weights; construct explicit
producers with unconditional bounds before extending receiver machinery.

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
- [x] Derive exact collar gauge energy, position invariance, actual support budget,
  and the resulting correlation-based packet and global transport bounds.
- [x] Optimize signed scalar collar compensation, classify all minimizers, and
  prove exact gain and strict-improvement criteria with global transport.
- [x] Construct and certify an explicit factorial producer for the actual signed
  measure, including domain admission, harmonic correction and unconditional rate.
- [x] Construct a continuous producer preserving the prime grid and nonvanishing L² size.
- [x] Factor an explicit producer through actual compact continuous sources and quantify cost.
- [ ] Establish quantitative archimedean jump energies of the balanced factorial sources.
- [ ] Derive a useful coherent multiple-collar certificate, retaining all cross terms (parked).
- [ ] Quantify width selection and the remaining smoothing error.

## Current frontier

Ten substantive contributions are formalized:
- `3-formalized/annular-signed-prime-polar-chebyshev-coupling-2026-10-17.md`.
- `3-formalized/signed-prime-polar-packet-gram-2026-10-17.md`.
- `3-formalized/signed-prime-polar-halfline-2026-10-17.md`.
- `3-formalized/signed-prime-polar-coherent-schur-2026-10-17.md`.
- `3-formalized/signed-prime-polar-rough-gauge-2026-10-17.md`.
- `3-formalized/signed-prime-polar-gauge-correlation-2026-10-17.md`.
- `3-formalized/signed-prime-polar-optimal-collar-2026-10-17.md`.
- `3-formalized/signed-prime-polar-factorial-producer-2026-10-17.md`.
- `3-formalized/signed-prime-polar-grid-preserving-smoothing-2026-10-17.md`.
- `3-formalized/signed-prime-polar-factorial-source-factorization-2026-10-17.md`.

The overall target remains 100, with 90 further distinct contributions unproved.
Packet construction, exact Gram representation, mass comparison, and transport
corollaries form one contribution. Likewise the coherent collar construction,
Schur constraint, and energy certificate are one contribution, not separate counts.

Parked uncounted candidate: `0-backlog/signed-prime-polar-multiple-collars-2026-10-17.md`.
Initial search `/tmp/spp7-next-search.json` reports partial=false/errors=[];
it also retrieves current source-only declarations, not proof certification.
Target a full coherent mixture transport certificate, not a polarization identity alone.

Contribution 8 constructs R_K(x)=exp(x/2) sum_{j=1}^K 1_[0,log(K/j)](x), with
real K/j. Its normalized bi-null combination has literal fullPairing bounded by
(10 log(4N+1)+3)/sqrt(N), with no assumed Chebyshev estimate or adjustable weights.
The test is discontinuous and cannot be an autocorrelation: its origin is zero,
but its value at log(4N) is 2. The complete producer package counts once.

Contribution 9 constructs the actual C_c producer with exact grid values,
pairing [2B_N−(1+1/(8N))C_N]/sqrt(N), and 1≤∫S_N²≤16. All five final leaf
checks and fourteen standard-axiom audits pass. Imports and index are updated;
global lint reports eight unrelated unwired modules and no package-local error.
Construction, exact arithmetic preservation, and nonvanishing energy count once.

Contribution 10 constructs actual compact continuous source pairs with equal origin
energy in [6sqrt(N),46sqrt(N)]. Their autocorrelation contrast preserves every
positive integer grid value, has squared L² norm in [2,32], and satisfies the
unconditional bound [10log(4N+1)+3+1/(4N)]/sqrt(N). Thirteen direct leaf checks
and fifteen standard-axiom audits pass; imports and index are updated. Global
lint reports nine unrelated unwired modules, listed in the ledger.

Next uncounted candidate:
`1-in-progress/signed-prime-polar-factorial-archimedean-cost-2026-10-17.md`.
Quantify actual jump-energy growth and signed differences of these balanced sources.
Existing logarithmic-tail and parallelogram results require C²; the concrete ramp
and tent require direct increment bounds and integrability. No uniform packet
control follows from the current scalar cancellation.

Secondary uncounted candidate: reduce B(d) to the triangular correlation integral
2d⁻²∫₀ᵈ(d-t)h(t)dt, then derive width response and reconstruction from d²B(d).
The existing double-average theorem is the starting point. A classical integral
rearrangement alone does not qualify as another contribution: pursue only if it
closes a distinct width-selection or signed-transport question. Follow-up semantic
search disconnected; lexical fallback returned 52 declarations, including the
existing double average and unrelated triangular Gram/pair-count results.
Evidence: `/tmp/spp6-next-search.json`, `/tmp/spp6-next-lexical.json`.

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
