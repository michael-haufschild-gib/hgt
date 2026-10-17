# Localized signed packet energy of the factorial sources

- **ID:** signed-prime-polar-factorial-local-packet
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / UNCOUNTED
- **Source:** Signed prime–polar transport; actual factorial-source family.
- **Statement:** Obtain an explicit numeric-index-only bound for the actual
  signed translation packet restricted to the support of reflected balanced
  factorial sources, retaining arithmetic–polar cancellation.

## Goal

The scalar factorial producer and its source/jump-energy certificates do not
bound the full translated packet norm. Investigate the smaller physical region
actually used by source pairings and local source chords. The endpoint must
instantiate the constructed family and an explicit arithmetic cutoff; a generic
Cauchy–Schwarz receiver with an assumed local packet budget is insufficient.

Candidate scale, not proved: local squared packet norm O(sqrt(N)) for the
balanced sources, hence a bounded ratio to their origin energy. All constants,
domains, cutoff stabilization, and consequences for actual pairings remain open.

## Gates

- [x] 0 → 1: audit precedents; fix the exact window and numeric cutoff.
- [ ] 1 → 2: dependency-closed paper proof, including real-ratio factorial and
  partial polar-moment bounds; no Chebyshev-error hypothesis.
- [ ] 2 → 3: exact actual-source Lean endpoint, direct leaf checks, scratch axiom
  audit and formal lint. User forbids full or umbrella builds.
- [ ] 3 → 4: standalone paper and certificate.

## Approach under investigation

Let N=n+1, δ=sourceFactorialWidth N, ε=sourceFactorialCollar N,
L=log(4N+1), and r=sqrt(N). Reflect P_N and M_N. Their broad factor then lies
on [0,L], their narrow factor on [−2δ,0]. Prove preservation of correlations
under this reflection and localize to J=[−3δ,L]. The extra collar accommodates
source chords of length at most δ. Use arithmetic cutoff 10N.

The reflected narrow factor should have no prime translate on I, since
log(2)>2δ. Its remaining polar translate is supported in the small left collar.
For the broad factor, express the prime packet at physical position u through
the real-ratio factorial stencil at scale N exp(−u). The clamp admits an average
of sharp cutoffs over [1,1+ε]. Divisor summation should then produce an average
of T(floor(4av))−4T(floor(2av))+4T(floor(av)), where v=N exp(−u).
Control that stencil directly by elementary factorial estimates. A simpler
finite-sum alternative avoids layer-cake integration: sandwich each clamped
prime sum between T(floor(v)) and T(floor((1+ε)v)). In this window εv≤5/4
even at the largest dilation, so smoothing adds at most two logarithmic terms.

Compute or bound the corresponding partial polar moments with the same
normalization. A useful proposed envelope is
exp(u/2)/sqrt(N) times a constant times [1+log(1+N exp(−u))]. Its square is
integrable over the physical source window with a uniform bound before source
balancing. This envelope and its cancellation are conjectural, not established.

Critical boundary: the lift sums only j≤K. Replacing it by an unrestricted floor
count at arbitrary negative shifts is false. Prove cap redundancy in the exact
small collar using the existing dilation budget. Do not infer full-half-line
packet-energy stabilization from a compact scalar or localized identity.
Never subtract a discrete linear counterterm before divisor summation.

## Prior-work audit

Inspected `SignedPrimePolarPacket.lean`: actual `atomicSource`, `polarSource`,
`signedSource`, and `packetEnergy`; translations are f(u+t), and the signed
packet is formed before its norm. `SignedPrimePolarRampMoments.lean` gives the
two full exponential moments, retaining harmonicCorrection and the factorial
stencil. Neither inspected statement supplies the proposed localized norm bound.

Searches `/tmp/spp11-next-packet-search.json` and
`/tmp/spp11-next-local-packet-search.json` both report partial=false, errors=[],
and complete file inventories. Semantic completeness is unmeasured; compiler
metadata is predominantly pending/stale/source-only, and refresh was deferred
to the running indexer. All candidate and source-argument statements were
inspected. The broad query was mostly unrelated. The field-filtered query found
the factorial grid identities, scalar compact-support lemmas and packet mixed
support precedents, but no complete local actual-source energy endpoint.
It also retrieved neighboring factorial/coprime and causal producer modules;
audit their relevant real-ratio identities before starting a paper proof.
No absence theorem or external novelty claim follows from these searches.

The third search `/tmp/spp12-real-scale-search.json` reports partial=false,
errors=[], inventory 73830/73830, predominantly pending/stale/source-only
compiler metadata. Candidate lemmas and source arguments were inspected.
The neighboring coprime and Plancherel–Laplace producers give scalar bounds
or generic gauge budgets, not the proposed actual-source local norm bound.

## Current proof plan

- [ ] Real-scale factorial stencil: integer floor carries cost at most seven
  logarithmic terms, giving |T(floor(4v))−4T(floor(2v))+4T(floor(v))|
  ≤12log(4v+1)+1 for v≥0.
- [ ] Actual clamped prime packet: discharge both finite caps and bound the
  extra smoothing carries; no pre-floor subtraction.
- [ ] Partial polar moments: use the two existing full moments and the
  pointwise ramp envelope to bound the actual truncated polar packet.
- [ ] Integrate the exponential–quadratic envelope over J, then balance
  broad and reflected narrow sources. Target constant 300000 sqrt(N).
- [ ] Prove cutoff stabilization and localized actual-pairing consequences;
  perform direct leaf and axiom audits, index, lint, ledger and cleanup.

No package-12 endpoint is yet proved. Helper lemmas alone do not count.

## No-go closure

No route is retired. If the proposed bound fails, isolate the actual boundary
term or obstruction and prove the strongest nontrivial localized survivor.
An unproved full-packet interface is not a substitute endpoint.

## Log

- 2026-10-17 — Created as an uncounted candidate while package 11's final
  certificate was compiling. No package-12 Lean code or paper theorem exists.
