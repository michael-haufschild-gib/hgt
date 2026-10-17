# Explicit factorial producer for the signed prime–polar measure

- **ID:** signed-prime-polar-factorial-producer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** Signed prime–polar transport, verified package 8; counted once.
- **Statement:** For N≥1 the actual normalized rectangle bi-null producer W_N
  satisfies |fullPairing W_N|≤(10 log(4N+1)+3)/sqrt(N).

## Construction and proof plan

Set R_K(x)=exp(x/2) sum_{j=1}^K 1_[0,log(K/j)](x), using real ratios.
Set W_N=(R_(4N)−4R_(2N)+4R_N)/sqrt(N).
Atomic evaluation gives T(K); continuum evaluation gives
K H_K−K+K log K−T(K). The bi-null pairing is
[2 B_N−4N(H_(4N)−2H_(2N)+H_N)]/sqrt(N).
Adjacent reciprocal pairing bounds the harmonic correction between 0 and 1.
Existing factorial producer bounds |B_N| by 5 log(4N+1)+1.

- [x] Check corpus and exact existing producer definitions.
- [x] Dependency-closed paper proof in `SignedPrimePolarFactorialProducer.md`.
- [x] Prove explicit rectangle support, integrability, and actual atomic admission.
- [x] Formalize exact atomic and continuum evaluations and harmonic bound.
- [x] Formalize normalized bi-null endpoint with numeric input only.
- [x] Direct leaf builds, scratch axiom/signature audit, umbrella, lint and index.
- [x] Update lane ledger and move this card after all local checks pass.

## Scope boundary

These are compact step-weighted tests, not autocorrelations. A small scalar pairing
does not imply a uniform packet bound or Weil positivity. No RH claim is made.
The real-ratio continuum endpoint is essential: flooring it would change the
continuum measure and reintroduce the divisor contamination forbidden by Trap 10.
No pre-floor subtraction of the arithmetic counterterm occurs.

## Search audit

`/tmp/spp8-producer-search.json` and `/tmp/spp8-lift-search.json`: partial=false,
complete file inventory; compiler metadata mostly source-only/pending and semantic
coverage unmeasured. Existing Nyquist/factorial producer and causal response found;
no retrieved statement supplies this real-ratio lift plus harmonic correction.
This is a local corpus distinction, not an external novelty claim.

## Verification

All three direct final leaf checks exit 0 with empty logs:
`/tmp/spp8-harmonic.log`, `/tmp/spp8-lift.log`, `/tmp/spp8-producer.log`.
Scratch `/tmp/spp8_final_axioms.lean` passes twelve axiom checks using only
propext, Classical.choice and Quot.sound. The printed main signature takes only
`n : ℕ`. The test also has certified origin value 0, top value 2, and cannot be
the autocorrelation of any compact continuous real source.

Imports are wired; index refresh exits 0; scoped whitespace checks pass.
Global lint exits 1 for eleven unrelated concurrent unwired modules, listed in
the lane facts ledger. No task-local error. Evidence:
`/tmp/spp8-final-axioms.log`, `/tmp/spp8-index.log`, `/tmp/spp8-lint.log`.

Disappearing shared objects required passing direct restores of Coupling and
GramTransport and a temporary field-object fallback. All actual dependencies
were present in the shared tree before cleanup. The fallback and obsolete probes
are removed; no owned process remains active. No dependency source was modified.

Next uncounted producer candidate:
`0-backlog/signed-prime-polar-grid-preserving-smoothing-2026-10-17.md`.
