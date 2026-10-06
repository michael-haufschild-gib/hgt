# BAG: actual support integrals, both gap signs and the complete hole

2026-10-06,22az. Three new leaves prove actual source estimates, without
analytic premises. The complete ordered packet is a subsequent target.

`ChiCubicHyperbolicPrimeIntegral.lean` defines the literal support integral
and proves integrability, exact finite decomposition of the original kernel,
zero for inactive d²>Mr cells, the all-cell bound8pi M/(dlogN), and the
exact bulk outer-minus-hole identity. Actual phase-preserving freezing and
complete integer periods imply the bulk bound
C M²/(d²logN)+4pi d/(NlogN). Both signs, full amplitudes and sharp endpoints
remain. Its seven public declarations are at18,40,48,65,78,142,161.

`ChiCubicHyperbolicPrimeGapIntegrals.lean` proves exact reindexing of BOTH
orientations by the actual positive-gap prime count:

    sum_{p,r in band,p≠r,|p-r|<=D} f(|p-r|) = 2 sum_{1<=d<=D} P_N(d) f(d).

No sign or positivity hypothesis on f is needed. The positive orientation
uses (p,r)↔(p-r,r), inverse(d,r)↦(r+d,r); the other uses pair exchange.
The actual small-gap support-integral norm sum is at most
C_M N(1+logD)/log³N for EVERY natural cutoff D. Public API69,75,103,108.

`ChiCubicHyperbolicPrimeHole.lean` retains the actual central integral
over[r-d,r+d] intersect[N,2N] for EVERY active original prime pair d²<=Mr.
Its norm is at most4pi d/(NlogN), including clipped band-edge holes. Both
gap signs and the actual prefix bound pay the entire mass: its product
withlog²N/N tends to zero for every natural M. The first moment obeys
sum_{d<=D}dP(d)<=D sum_{d<=D}P(d), withD=floor(sqrt(2MN)).
Public API18,24,29,33,42,82.

## Validation

All final checks used one foreground `lake --old env lean <leaf> -o <olean>`
at a time; no umbrella/full build.

- Integral49931 exit0, empty `/tmp/bag-hyperbolic-prime-integral-03az.log`.
- GapIntegrals14178 exit0, empty `/tmp/bag-hyperbolic-prime-gap-integrals-03az.log`.
- Hole49596 exit0, empty `/tmp/bag-hyperbolic-prime-hole-02az.log`.

Imported axiom/API audits3108,81038,46110 passed. All17 public declarations
and the two newly exposed Kernel proofs use only propext,Classical.choice,
Quot.sound. Logs `/tmp/bag-hyperbolic-gap-integrals-api-22az.log`,
`/tmp/bag-hyperbolic-edge-api-22az.log`,
`/tmp/bag-hyperbolic-moments-api-22az.log`.
The existing Kernel support measurability169 and amplitude continuity177
were made public with unchanged bodies; kernel42580 exit0, empty log.
Each new leaf wired once. Index25383 passed and all17 public rows checked.
Integral-stage lint4603 exited1:367 large-file warnings,23 unrelated
unreachable modules; no owned BAG finding. Final-session lint11134 exit1:
367 large-file warnings and18 unrelated unreachable modules, no owned
BAG finding. Global lint is not clean.

No new axiom, admission, heartbeat override, numerical experiment, subagent,
commit or push. The new endpoint-window mechanism, both moment bounds and
complete ordered-packet cancellation subsequently passed all leaf/axiom
audits: see `bag-hyperbolic-prime-ordered-cancellation.md`. Transpose/ties
for the full fixed-radius packet, full cubic/tail cancellation and RH
remain open.
