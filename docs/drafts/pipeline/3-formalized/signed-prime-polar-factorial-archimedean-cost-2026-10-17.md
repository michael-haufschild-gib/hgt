# Archimedean cost of the balanced factorial sources

- **ID:** signed-prime-polar-factorial-archimedean-cost
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Count:** Contribution 11, one package including domains, growth and cancellation.
- **Scope:** Unconditional signed prime–polar transport; actual factorial sources.
- **Statement:** The balanced sources have finite jump energies of order
  sqrt(N) log N, signed difference O(log N/sqrt(N)), and explicit normalized
  logarithmic lower cost.

## Exact endpoint

Paper: `docs/reports/BiScaleUncertainty/SignedPrimePolarFactorialArchimedeanCost.md`.
Lean: `SignedPrimePolarSourceArchimedeanCertificate.lean:97`, theorem
`SignedPrimePolar.factorialSourceArchimedean_certificate`, with only n:ℕ as input.
Let N=n+1, r=sqrt(N), L=log(4N+1), Q=10^6 N^5,
B=[6L+7+2log Q]/r and
U=2r[6+32(log(6Q)+π)+60(log(24000N)+π)].

For the actual P_N and M_N, the literal jump integrands are absolutely integrable,

6exp(−1/2)r log N−B ≤ E(P_N), E(M_N) ≤ U,
E(P_N)−E(M_N)=−2∫H_N w,   |E(P_N)−E(M_N)|≤2B.

For either source V,
E(V)/h_V(0)≥(3/23)exp(−1/2)log N−[41+2log(10^6)]/6.
The coefficient in the signed difference is two. This is a statement about the
constructed family, not a universal lower bound for all possible factorizations.

## Mechanism and positive content

Explicit clamp/tent regularity gives global Lipschitz constants 10000 N^4 and
2000 N², with L¹ budgets 20N and 2. Linear correlation increments admit the
literal jump integrals without a C² assumption. The narrow tent's correlation
support gives the lower bound; the admitted parallelogram identity gives the
balanced sum. The causal contrast gives the exact signed difference and its
much smaller bound. Small scalar prime–polar pairing therefore coexists with
quantified growing source jump cost, while the exact cancellation survives.
No route is retired and no receiver interface is counted as a separate result.

## Verification

- [x] Prior-source and increment audit; dependency-closed paper proof.
- [x] Actual source domains and numeric-index-only complete Lean endpoint.
- [x] Nine final direct `lake --old env lean <leaf> -o <olean>` checks passed.
- [x] Eleven scratch axiom audits: only propext, Classical.choice, Quot.sound.
- [x] All current source hashes match; all nine imports are wired exactly once.
- [x] Index refresh passed and lists the endpoint.
- [x] Formal lint run: 22 unrelated unwired modules, no package-local error.

Leaves: CompactProfileLipschitz, CompactLipschitzLevyEnergy,
SignedPrimePolarTentRegularity, SignedPrimePolarRampRegularity,
SignedPrimePolarSourceJumpDomain, SignedPrimePolarSourceJumpUpper,
SignedPrimePolarTentJumpLower, SignedPrimePolarCausalJumpBounds,
SignedPrimePolarSourceArchimedeanCertificate.
Evidence: `/tmp/spp11-final-manifest.json`, `/tmp/spp11-*.log`,
`/tmp/spp11_final_axioms.lean`. Eight final leaf logs are empty; the tent
regularity log has an informational ring suggestion and no error.
The facts ledger lists all unrelated lint errors.
No full/umbrella build, numerical experiment, heartbeat change, commit or push.
README stayed read-only. API scratch files were removed after verification;
final audit evidence is retained.

## Prior-work boundary and next question

The existing logarithmic-tail and energy parallelogram theorems require C²;
those hypotheses do not admit these explicit nonsmooth profiles. Generic
Lipschitz admission and classical logarithmic estimates are ingredients of this
single actual-source theorem, not separate contributions.
`/tmp/spp11-source-increment-search.json` reports partial=false/errors=[], full
inventory, predominantly pending/source-only compiler metadata and deferred
refresh. Candidate statements and source arguments were inspected; no external
novelty claim follows from retrieval.

Next uncounted candidate:
`0-backlog/signed-prime-polar-factorial-local-packet-2026-10-17.md`.
The overall 100-contribution goal remains active, now 11 verified and 89 remaining.
