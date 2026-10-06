# BAG: complete continuous middle-coordinate cubic cancellation

- **ID:** bag-full-band-continuous-cubic-24az
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/bag-full-band-continuous-cubic-cancellation.md
- **Statement:** The sum of norms of ALL literal full-band continuous q-rows over every noncontracting prime pair is O(N/log³N); the complete continuous cubic has normalized complex norm tending to zero.

## Exact result

For each original prime pair p,r in (N,2N], p≠r, integrate the actual
recentered cubic amplitude over the ENTIRE q-band against dq/log q.
Retain the original V/W factors, oscillation and physical reciprocal1/r.
There is no hyperbolic radius, gap truncation or ordering hole.

Lean proves one source constant K such that every such pair satisfies

    |I_full(N,p,r)| ≤ K [1/(|p-r|² log N) + 1/(N log N)].

The ENTIRE sum of these row norms is O(N/log³N). In particular,

    (log²N/N) * |chiCubicPrimeFullContinuousCubic(N)| -> 0

as REAL N tends to infinity. The asymptotic producer has no arithmetic,
regularity or cancellation premise.

## Source mechanism

The actual profile is F(ξ,l,x)=W(ξx)V(x)/(1+l log x). Joint smoothness
follows from the literal source factors and the positive denominator
on ξ∈[1/2,2],l∈[0,1],x∈[1,2]. Parameter differentiation and compactness
give uniform bounds for EVERY fixed spatial jet. Constants may depend
on the derivative order; no growing-order budget is asserted.

At x=1,2, the actual W vanishes. Its compact Lipschitz bound therefore
pays the moving profile endpoints by a constant times |ξ-1|. The
moving endpoint values are not set to zero. Two signed integrations,
retaining both boundaries at each step, prove

    |integral_1^2 F(ξ,l,x) exp(iτx) dx|
      ≤ C [|ξ-1|/|τ| + 1/τ²].

Substitute ξ=p/r,l=1/log N,τ=2πN(p-r)/r. The exact change q=Nx
retains the recentering phase, whose norm is one. The literal prefactor
has norm at most2π/(N log N). The ratio defect divided by frequency is
EXACTLY1/(2πN); N<r≤2N pays the inverse-square remainder. This proves
the displayed all-pair estimate, including the large gaps.

Choose D=floor(2N), which contains every original prime gap. The exact
two-sign reindexing, actual prefix bound and reciprocal-square moment
give

    sum P_N(d)/d² ≤ A N/log²N,
    sum_{d≤D} P_N(d) ≤ E D N/log²N.

Thus the entire row-norm sum is bounded by
K(2A+4E)N/log³N. Finite sum/integral interchange is justified by the
actual amplitude's continuity on [N,2N]. This completes the continuous
producer across every original prime pair.

## Precise remaining arithmetic problem

The discrete full prime cubic is NOT proved negligible here. Its complete
prime-sampling discrepancy must be controlled with q=r subtracted. That
point has zero measure in the continuous integral but is a literal
contraction in the prime sum. The existing exact prime-only Vaughan
identity keeps both exclusions in one shared signed weight; it supplies
no saving by itself. Fixed-M hyperbolic transfer cannot be substituted
at a growing radius without a new uniform proof.

Full compensated prime sampling/cubic-tail cancellation, growing
moments/cofactors, deterministic common-height self-return and RH remain
open. The active RH goal is not achieved.

## Lean and audits

- ChiCubicMovingProfileJets.lean,95 lines: actual jet smoothness69 and
  source-derived uniform fixed-order bounds79. Final7646 exit0, empty02az.
- ChiCubicMovingProfileFourier.lean,172 lines: actual moving-profile
  Fourier cancellation129. Final10608 exit0, empty03az.
- ChiCubicPrimeFullPairIntegral.lean,164 lines: literal full-row
  integral21 and all-pair cancellation bound100. Final3239 exit0, empty02az.
- ChiCubicPrimeFullContinuousCancellation.lean,133 lines: complete row
  mass21, continuous cubic26, mass bound33, normalized mass limit95,
  complete continuous cubic limit116. Final11416 exit0, empty03az.

All final commands used `lake --old env lean <leaf> -o <olean>`, one
owned foreground Lean process at a time. Every leaf is wired exactly
once. Imported axiom46903 exit0: all TEN public declarations use only
propext, Classical.choice and Quot.sound. No admissions, new axioms or
heartbeat overrides. Index30963 passed; all ten API rows checked.
Authoritative lint85403 exit1:367 large-file warnings and29 unrelated
unreachable modules; no finding on the four new leaves. Global lint is
not clean. No full/umbrella build, numerical experiment, subagent,
commit or push.

Evidence: /tmp/bag-moving-profile-jets-02az.log,
/tmp/bag-moving-profile-fourier-03az.log,
/tmp/bag-full-pair-integral-02az.log,
/tmp/bag-full-continuous-cancellation-03az.log,
/tmp/bag-full-continuous-axioms-24az.log,
/tmp/bag-full-continuous-index-24az.log,
/tmp/bag-full-continuous-lint-24az.log.

## Gates

- [x] 0 → 1: literal source, exact full-band target, corpus-based mechanism.
- [x] 1 → 2: complete source construction, two-boundary proof and actual sieve summation.
- [x] 2 → 3: final leaf and imported axiom audits passed.
- [ ] 3 → 4: standalone publication review.
