# Explicit factorial producer for the signed prime–polar measure

- **ID:** signed-prime-polar-factorial-producer
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper; Lean pending)
- **Scope:** Signed prime–polar transport, package 8 candidate; uncounted.
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
- [ ] Prove explicit rectangle support, integrability, and actual atomic admission.
- [ ] Formalize exact atomic and continuum evaluations and harmonic bound.
- [ ] Formalize normalized bi-null endpoint with numeric input only.
- [ ] Direct leaf builds, scratch axiom/signature audit, umbrella, lint and index.
- [ ] Update lane ledger and move this card only after all local checks pass.

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

## Verification state (temporary; replace after certification)

- Harmonic leaf: direct final check passes with empty `/tmp/spp8-harmonic.log`.
- Lift: complete proof checked; an unused simp argument was removed. Final recheck
  was interrupted by disappearing shared dependency artifacts, not a proof error.
- Producer: first check found a cast rewrite and an integral elaboration mismatch;
  both are fixed. Final recheck and `/tmp/spp8_final_axioms.lean` remain pending.
- `SignedPrimePolarCoupling.olean` was restored by a passing direct check.
  GramTransport also passes its direct restore check. Final lift recheck is running
  as exec session 52502.
- Relevant field artifacts are preserved in `/tmp/spp8-lean-overlay` (about 96 MiB).
  Prefix checks with `LEAN_PATH=/tmp/spp8-lean-overlay`; `lake --old env lean`
  retains normal package paths and uses this overlay for missing local objects.
  `HyperbolicGaugeChebyshevEnergyRepresentation.olean` has also been preserved.
- One owned Lean process at a time. Copy restored/new output objects into the
  overlay after each successful check. Restore any still-missing shared objects
  from the preserved copies before cleanup; remove only this task's temporary files.
- Next uncounted producer candidate is recorded in
  `0-backlog/signed-prime-polar-grid-preserving-smoothing-2026-10-17.md`.
