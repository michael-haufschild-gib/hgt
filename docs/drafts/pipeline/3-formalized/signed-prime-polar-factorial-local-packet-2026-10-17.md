# Localized signed packet energy of the factorial sources

- **ID:** signed-prime-polar-factorial-local-packet
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE / VERIFIED
- **Completed:** 2026-10-18
- **Source:** Signed prime–polar transport; actual factorial-source family.
- **Count:** One contribution, package 12. Helpers and transport corollaries count together.

## Exact result

Set N=n+1, r=sqrt(N), δ=log(1+1/(4N))/3, L=log(4N+1),
J=[−3δ,L], and K=10N+k. The actual reflected balanced sources are
V±(u)=sqrt(r) R_N(u) ± Gδ(−u)/sqrt(r).

`SignedPrimePolar.factorialLocalPacket_certificate (n : ℕ)` proves for both
signs and every k: local signed packet energy at most 300000r, origin energy
between 6r and 46r, scalar pairing squared at most 50000h(0)², and increment
pairing squared at most 600000r(h(0)−h(y)) whenever |y|≤δ. The local energy
ratio is at most 50000. There is no assumed discrepancy or packet budget.
The packet stabilizes on J for K≥10N.

Paper: `docs/reports/BiScaleUncertainty/SignedPrimePolarFactorialLocalPacket.md`.
Endpoint: `formal/GaloisForLFunctions/BiScaleUncertainty/SignedPrimePolarFactorialLocalCertificate.lean`.

## Proof and scope

The real-scale factorial stencil has bound 9log(4v+1)+1. Its finite clamped
prime sum retains both caps; cap redundancy is proved in the exact collar.
Smoothing adds at most two logarithmic carries per dilation. The actual atomic
packet has envelope coefficient 19. Full harmonic cancellation and partial
polar moments give coefficient 5, hence signed broad coefficient 24.
The squared normalized envelope integrates to at most 130; the broad packet
budget is 100000 and the reflected narrow packet budget is 9/N. Reciprocal
source balancing yields the stated 300000r bound.

Signed prime and polar packets are formed before energy is taken. Triangle
estimation follows the factorial cancellation; no optimal mixed-term claim is
made. No linear counterterm is subtracted before floor summation. This result
is local: it does not imply full-real-line packet norm stabilization or a
cutoff-uniform global energy estimate. No route is retired.

## Gates and verification

- [x] Prior-work audit and exact support/cutoff choice.
- [x] Dependency-closed paper proof with explicit unconditional constants.
- [x] Actual-source Lean endpoint; all nine direct leaf checks pass.
- [x] Fourteen scratch axiom reports contain only propext, Classical.choice and Quot.sound.
- [x] All nine imports wired once; source hashes recorded; API index refreshed.
- [x] Authoritative repository lint run and unrelated failures recorded.
- [x] Ledger, parent card and memory updated; implementation/API scratch removed.

Verified leaves: SignedPrimePolarRealFactorialStencil, SignedPrimePolarClampedPrimeSum,
SignedPrimePolarFactorialAtomicPacket, SignedPrimePolarFactorialPacketEnvelope,
SignedPrimePolarFactorialPolarPacket, SignedPrimePolarReflectedTentPacket,
SignedPrimePolarLocalizedPacket, SignedPrimePolarFactorialLocalEnergy,
SignedPrimePolarFactorialLocalCertificate. Each passed `lake --old env lean -j 1`
with its own output object. Seven logs are empty; envelope and local-energy
logs have harmless unused-tactic warnings and no errors.

Evidence: `/tmp/spp12-final-manifest.json`, `/tmp/spp12_final_axioms.lean`,
`/tmp/spp12-final-axioms.log`, `/tmp/spp12-index.log`, `/tmp/spp12-lint.log`,
and the nine direct-check logs named in the manifest. No full/umbrella build,
numerical experiment, commit or push. The read-only field README was not edited.

Global lint exits 1 solely for five unrelated unwired modules:
CompactFiniteJumpWeilFormula, FactorialCompleteFormCoercivity,
FactorialWeilCoercivity, SchurSquareCorrelation, SeparatedCopySquareClassification.
No package-local lint error occurs. Other lanes' work is preserved.

## Prior-work coverage and closure

Searches `/tmp/spp11-next-packet-search.json`,
`/tmp/spp11-next-local-packet-search.json` and `/tmp/spp12-real-scale-search.json`
report partial=false, errors=[] and complete file inventories. The third
inventory is 73830/73830. Compiler metadata is predominantly pending, stale or
source-only; semantic completeness is unmeasured. All candidate/source-argument
statements and relevant neighboring factorial, coprime and Plancherel–Laplace
producers were inspected. They did not supply this actual-source local endpoint.
No external novelty or absence claim follows from the searches.

The user cleared the broader 100-contribution goal. This closes the already-open
package under the subsequent cleanup request. No new package is opened and no
unfinished or unwired implementation remains in this package. Publication work
and the global packet question are outside this closure.
