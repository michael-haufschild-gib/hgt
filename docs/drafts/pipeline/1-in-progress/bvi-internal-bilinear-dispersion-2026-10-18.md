# Internal bilinear dispersion: isolate the coherent prime prefix

- **ID:** bvi-internal-bilinear-dispersion-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/walls/bezout-wall1-programme.md`, problem 3.
- **Goal:** Develop an unconditional internal estimate for the actual energy-centered pronic Ramanujan bilinear form, with all coherent terms explicitly accounted for. No RH task or claim.

## Scope and constraints

Read the field README completely; it remains read-only. No numerical experiments,
added axioms, assumed cancellation estimates, full builds, heartbeat overrides,
or commits. Existing concurrent changes are outside this task's write scope.
Serena symbol lookup rejects the ignored Lean directory; use source reads and
patches as fallback. `update_plan` is unavailable; this card tracks the plan.

## Plan

1. Audit current corpus and the literal kernel, including the proposed reciprocity.
2. Form conjectures from those definitions; prove or refute them on paper.
3. Formalize dependency-closed positive results in a new BVI leaf, wire only its
   umbrella import, and check the original source with `lake env lean`.
4. Audit axiom closure, lint, index freshness, cleanup, and the remaining analytic
   obligation. Continue the next conjecture; do not equate a reduction with dispersion.

## Corpus evidence

- `PMPowerDampedMobiusRamanujanGram.lean`,
  `pmRamanujanPrimitive_prime`: the prime primitive is exactly `-(N % p)`.
- Same module: `pmRamanujanPrimitiveGram` is the pronic inner product of
  **Ramanujan primitives**, not the product of divisibility indicators written
  in parts of the README. Use the Lean definition as authoritative.
- `PMPowerDampedMobiusRamanujanMoment.lean` defines the energy-centered
  primitive and Gram; inspect these before formalizing.
- Initial hybrid search completed, with stale coverage snapshot and source-only
  candidate signatures. It located the centered Gram and the exact cofactor
  bridge, not a dispersion estimate. Compiler applicability remains to be checked.
- Lexical search found extensive Kloosterman infrastructure. No blanket claim
  that internal bilinear estimates are unknown is justified by this search.

## External source audit

Duke–Friedlander–Iwaniec already bound bilinear Kloosterman fractions for
arbitrary coefficients and fixed numerator, with the two bilinear variables
providing the averaging: [original paper, Theorem 2](https://www.math.ucla.edu/~wdduke/preprints/bilinear.pdf).
Thus an *additional* external character average is not universally required.
This does not supply a bound for the present Gram kernel: a valid conversion,
coherent main terms, and control of the conversion error remain necessary.
No external theorem is imported as an unproved Lean premise.

## Corpus reconciliation after user correction

The user identified that existing work was being missed. New conjecture code was
paused for corpus reconciliation; C9 now uses the verified existing carrier.
Earlier broad deep queries often
returned partial coverage and irrelevant matches; those searches did not justify
treating the jump-sector structure as unexplored. Exact-symbol lexical queries
now cover all 19 centered-Gram hits, all 38 primitive-Gram hits (both pages),
all 17 dilation-profile hits, and all 5 lag-sector hits without per-module caps.

Existing source obligations to reuse:

- `PMRamanujanNearbyPrimeResonance.lean`: exact prime-insertion Hilbert law,
  retained continuous dilation profile, and unbounded nearby-prime covariance.
- `TwoPrimeDilationProfileIdentityAndPrimeStarShearCancellation.lean`:
  exact four-term profile identity and shear-balanced prime-star cancellation.
- `AllDepthHilbertDilationCubeAndHyperCubeGramFactorization.lean`:
  the entire actual-weight cube, including cross-depth terms, already becomes
  a dilation-profile quadratic form. A prime-only packet is not this whole cube.
- `ReciprocalJumpKernelAndDilationLagSectors.lean` and
  `DilationProfileIntegerJumpCoupling.lean`: exact finite jump/lag decomposition
  of the actual profile, with an explicit finite-horizon approximation error.
- `DilationSuccessorFiberReciprocity.lean`: the jump equation turns amplitudes
  into literal additive correlation; complete successor fibers have mass
  `r μ(r)` for invertible scales. No extra character average is needed here.
- **Previously omitted:** `DilationSuccessorSectorHarmonicClassification.lean`
  already parametrizes the full successor sector, classifies the Fourier
  resonance selector (`μ(r)` when both scales are coprime to `r`, otherwise zero),
  and subtracts its exact harmonic term with a uniform explicit remainder and
  the necessary horizon correction. Its adjacent-scale capstone has data only.

Consequently C6 must start beyond the already solved lag-one sector. It must
preserve the arithmetic mean and horizon correction, then control summation
across the remaining lag sectors and prime pairs. C8's local residue-cell
variance is a different identity; it is not a replacement for that existing
arithmetic classification. All seven relevant existing capstones passed
`lake --old env lean -j 1 /tmp/bvi-existing-frontier-audit.lean`; each axiom
closure contains only `propext`, `Classical.choice`, and `Quot.sound`.

Further exact reuse found during reconciliation:

- `InteriorJumpOrbitCenteringAndCompensatedBounds.lean` already computes the
  gcd-selected conditional mean of the endpoint-deleted sawtooth and proves
  its compensated Abel bounds. More strongly,
  `BirthDelayedInteriorJumpCenteringAndUniformPairBounds.lean` starts that
  subtraction at the modulus's birth and proves the pair bound
  `1/d + 2/gcd(d,e)`, uniformly in both finite horizons. Its final theorem
  connects this to the actual arithmetic prefix, retaining the initial-value,
  density, and delayed-mean corrections. The remaining signed modulus sum
  is not controlled by taking absolute values of these pair bounds.
- `HTGeometry/FiniteHilbertDispersion.lean` already proves finite weighted
  variance and conditional negative type; `InfiniteHilbertDispersion.lean`
  supplies the summable extension. C7's generic Hilbert/Cauchy algebra is
  infrastructure, not a missing research tool. Its scratch is not promoted.
- `RHTower/KuznetsovKloostermanSmallModulus.lean` already proves
  `exists_bilinear_kloosterman_small_le`, with explicit Poisson remainder,
  for the actual quadratic Kloosterman form with phase
  `exp(2*pi*i*2*theta*sqrt(m*n)/c)`, `1<=abs(theta)<=2`.
  `KuznetsovKloostermanPhaseEnvelope.lean` proves
  `exists_kloostermanPhaseForm_le_rpow`: for `c<=N` its bound is
  `C_delta sqrt(c) N^(1/2+delta) sum abs(alpha)^2`. These are stronger than
  the fixed-modulus operator baseline; their special phase and parameter
  range must be proved applicable, not dropped.
- `RHTower/KuznetsovLargeSieveTheorem.lean` already proves
  `large_sieve_gamma0`, the spectral bound with
  `card(gamma0Deck L Q)*(K^2+N^(1+epsilon)/Q)` and `Q | L+1`.
  A full spectral sieve is therefore available in the corpus. No conversion
  of the present pronic Gram to its spectral left side has yet been proved.
- `Sieve/KloostermanCoprimeCrossPhaseFrequency.lean` gives an exact CRT
  equivalence from cross-unit pairs to product-modulus units, preserving
  their character ratio, and compresses the reciprocal-chord sum without
  multiplicity loss. `KloostermanProductFrequencyGcdBound.lean` already
  sharpens the chord sum to `gcd(q,r)*q*r*(1+log(q*r))` for unequal moduli.
  `KloostermanCoprimeProductPeriodCompletion.lean` already removes the full
  coprime-period cross block and retains its exact residue-discrepancy
  boundary. All 43 cross-phase/coprime lexical hits were inspected across
  three pages. These absolute bounds do not supply a signed saving.
- `MobiusSquareResidueFourier.lean` already gives the exact least-residue
  Fourier coefficient and reciprocal-chord norm. Its later estimates apply
  to the quadratic path `n^2 mod q`; applying that path estimate to `n mod q`
  or to the present weighted Gram would require a separate identity.
- `BiScaleUncertainty/VasyuninReciprocityAndExactTailGramProducer.lean`
  already supplies exact reciprocal-cell head/tail identities. Its inspected
  Gram theorems express the tail as global minus head; they do not evaluate
  the global Gram in cotangent sums or supply cross-prime cancellation.
- The current all-depth module also retains the base von Mangoldt term in
  the centered primitive and proves alternating-depth Euler-factor
  cancellation. Neither depth-shell cancellation nor the cube reduction
  should be reintroduced as a new conjecture.
- The concurrently added `NaturalCutoffMultiDepthCofactorAndConditionalTailBridge.lean`
  already extends the conditional-tail decomposition to the entire natural-cutoff
  packet, identifies the complete cube with the existing completed aperture,
  and collapses centering across a prime-cofactor head to its single prime term.
  These source-inspected results are not new obligations for this card; their
  author's original-source audit was still running when inspected.

Second reuse audit (seven declarations, including the two analytic estimates,
spectral sieve, birth-delayed bounds, and depth-shell identities):
`/tmp/bvi-corpus-reuse-audit.lean` passed with exit 0. All seven axiom closures
contain only `propext`, `Classical.choice`, and `Quot.sound`. The relevant compiled
artifacts were present and newer than their sources at launch. This is an
import/applicability and axiom check, not a fresh build of those foreign files.

Search records are `/tmp/bvi-dispersion-search-*.json`. The focused bilinear
Kloosterman search had 74,182 inventoried files but `partial=true`, with
unfinished query expansion/reranking and mostly pending compiler metadata.
Exact source inspection, rather than a no-hit or ranking result, establishes
the distinctions above. Unrelated coboundary prime-depth countertransport
and generic negative-covariance hits do not identify the present carrier.

The further deep query `Ramanujan dilation residue gap profile budget` returned
20 candidate lemmas, 20 source arguments, two proposed proof transfers, one
ingredient group, and ten source passages; all returned items were inspected.
It recovered the existing residue coefficient transform, exact lag identities,
and C5. The suggested entire-function gap ingredient concerns a different
carrier and was rejected. Complete-period covariance diagonalization likewise
does not transfer to a pronic weight without an identity. Coverage: 74,185 files
inventoried, `partial=true` because reranking timed out, background refresh
incomplete, semantic coverage unmeasured, and returned signatures source-only.
Raw record: `/tmp/bvi-profile-gap-reuse-search.json`. No absence or novelty claim
is inferred from this search.

## Conjecture log

### C1 — energy centering removes the common prime prefix

**Falsified on paper.** For every prime `p > H`, and `1 ≤ n ≤ H`, the primitive is
`-n`, so its energy-centered version is `log p - n`. Consequently the entire
head of a weighted prime packet depends on only two moments,
`A = Σ a_p` and `L = Σ a_p log p`. Subtracting the global energy mean does
not remove this shared ramp. Any proposed bound must pay for this head.

### C2 — exact conditional projection before dispersion

**PROVED HERE; Lean source check passed.** With pronic weight `w_n=1/(n(n+1))`, split at
`H`. The tail mass is `1/(H+1)`. Let `m` be the weighted head mean of an
energy-centered packet. Its tail mean is `-m`; subtracting the tail's
conditional mean should give the exact identity

`full energy = head energy + (H+1) m² + centered tail energy`.

For a prime packet with all primes exceeding `H`, the first two terms are an
explicit rank-at-most-two form in `(A,L)`. The last term must be represented
by an actual sum of squares, not defined merely as a difference of energies.
This is a candidate positive survivor and a necessary preparation for a
dispersion estimate, not itself that estimate.

### Dependency-closed paper proof of C2

Let `F(n)=Σ_{p∈S} a_p (log p - (n mod p))`. The corpus's prime primitive and
reciprocal-mean theorems prove `Σ w_n F(n)=0`; its centered Gram summability
proves absolute convergence of every finite packet pairing. Put
`m_F=Σ_{n≤H} w_n F(n)` and `R_F(n)=F(n)+(H+1)m_F` for `n>H`.
Telescoping `w_n=1/n-1/(n+1)` gives tail mass `1/(H+1)`, hence

`Σ_{n>H} w_n F(n)=-m_F`, and `Σ_{n>H} w_n R_F(n)=0`.

Expanding the product of two residuals, with absolutely convergent sums,
gives

`Σ_{n>H} w_n R_F(n)R_G(n) = Σ_{n>H} w_n F(n)G(n) - (H+1)m_F m_G`.

Adding the prefix proves the exact bilinear decomposition. For `F=G`, its
last term is an actual sum of nonnegative squares, proving the lower bound.
There is no equidistribution or cancellation premise.

When every prime exceeds `H`, write `A=Σa_p`, `L=Σa_p log p` and
`u_j=Σ_{n=1}^H n^j/[n(n+1)]`. Then `F(n)=L-nA` on the head and

`head energy = u_0 L² - 2u_1 AL + u_2 A²`,
`m_F=u_0 L-u_1 A`.

The complete forced contribution is therefore

`u_0 L² - 2u_1 AL + u_2 A² + (H+1)(u_0 L-u_1 A)²`.

Here `u_0=H/(H+1)`, `u_1=harmonic(H+1)-1`, and
`u_2=H+1-harmonic(H+1)`. For `H>0` it can also be written

`H[L-(H+1)u_1 A/H]² + [u_2-(H+1)u_1²/H] A²`.

The bracket is the weighted variance of `n` on the head, hence nonnegative;
it is strictly positive once the head contains two distinct positive indices.
These last scalar evaluations and strictness are paper observations, not yet
Lean claims.

### C3 — inverse reciprocity itself produces cancellation

**Falsified as a mechanism, by an exact identity.** For coprime positive
`p,q`, choose inverses `p̄ mod q` and `q̄ mod p`. Then

`p p̄ + q q̄ ≡ 1 (mod pq)`,

so for every integer `h`,

`e(h p̄/q)e(h q̄/p)=e(h/(pq))`.

Both phases and the numerator must be retained. The product is a slowly
varying phase when `|h|` is small relative to `pq`; reciprocal rewriting
does not supply a saving by itself. The positive content is the exact phase
constraint, which locates the coherent low-frequency channel. This is
classical CRT infrastructure, not a novelty claim or a retired analytic route.

### C4 — after conditional centering, the remaining tail disperses

**Open.** The decomposition alone proves no quantitative upper bound for
the centered tail. Nearby-prime resonance in the existing corpus makes a
uniform arbitrary-coefficient saving suspect unless further coherent channels
or coefficient moment restrictions are explicitly included. Next: derive a
pointwise prime-pair lower bound from the common ramp, then examine the
actual conditional residual rather than a renamed original energy.

### C5 — nearby-modulus transport gives a gap-sized energy cost

**PROVED HERE; original-source Lean audit passed.** This is an
upper bound for a concrete cancelling packet, not a bound for arbitrary
unmodified prime blocks. Let integers `1≤p<q≤2p`, `h=q-p`, `K=⌊p/h⌋`,
and `r_p(n)=n mod p`. For `1≤k≤K`, split the block
`kp≤n<(k+1)p` at `kq`. Because `kh≤p`, these are precisely the two
quotient cells; the residue difference is `kh-q` on the first and `kh`
on the second. Telescoping the pronic weight gives the exact block identity

`Σ_{kp≤n<(k+1)p} (r_p(n)-r_q(n))²/[n(n+1)]`
`= qh/(pk) - (h²/p)(k+2)/(k+1)`.

Below `p` the difference vanishes. Summing through block `K` and bounding
the remaining tail by `q²/[p(K+1)]` proves

`Σ_{n≥1} (r_p(n)-r_q(n))²/[n(n+1)] ≤ (q/p)h harmonic(K) + q²/[p(K+1)]`
`≤ 2h harmonic(K)+4h`.

Indeed `(K+1)h>p` and `q≤2p`. If `p,q` are prime, energy centering
subtracts `(log p-log q)²` from the left-hand side, so the same upper
bound applies to `Gec(p,p)+Gec(q,q)-2Gec(p,q)`. This exploits actual
integer jump locations and does not use an external character average.

The candidate changes the problem from cancellation of individual Gram
entries to transport between positive and negative coefficient packets.
It does not establish that the requested coefficient families possess
enough cheap transport, nor the full beyond-Nyquist estimate.

**Sharpening during formalization.** The finite correction telescopes exactly:

`Σ_{0≤n<(K+1)p} (r_p(n)-r_(p+h)(n))²/[n(n+1)]`
`= h harmonic(K) - (h²/p) K²/(K+1)` whenever `Kh≤p`.

Indeed the block formula equals
`h/k - (h²/p)(1 - 1/[k(k+1)])`; summing the reciprocal difference gives
`K - 1 + 1/(K+1) = K²/(K+1)`. Thus the full energy lies between
`h harmonic(K)-h` and `h harmonic(K)+q²/[p(K+1)]` for `K=⌊p/h⌋`.
When `h≤p`, the upper bound becomes `h harmonic(K)+4h`.
The matching lower bound identifies the logarithmic gap cost as intrinsic.
This sharper identity, both bounds, and the centered prime-distance conversion
are now formalized in `PronicResidueGapEnergyAndPrimePairDistance.lean`.

The deep overlap search returned partial results (reranking deadline),
including sawtooth dilation primitives and nearby-resonance infrastructure,
but no matching gap-energy estimate. This is not proof of novelty.

External baseline: Báez-Duarte–Balazard–Landreau–Saias study the same
fractional-part autocorrelation geometry and its behavior near rational
dilations ([working paper, §§8–9](https://arxiv.org/pdf/math/0306251)).
Treat the logarithmic continuity scale as classical background; the deliverable
here is a directly proved, explicit discrete jump-cell estimate attached to
the actual BVI Gram kernel, not a claim to have discovered dilation continuity.

### C6 — dispersion of compensated jump intervals

**Next conjecture after C5.** Pairing nearby modes removes their common ramp
and confines the large part of their difference to intervals
`kp≤n<kq`. Cross-pair interactions should therefore be expressed by the
actual overlaps of these intervals, with centers governed by `ap-bq`.
Seek an exact decomposition into smooth drift, coherent overlaps, and a
remaining arithmetic collision term before asserting any bilinear saving.
This is where a modular-inverse estimate might enter without discarding a
second correlated phase. Search the current jump-coupling modules before
opening this conjecture's formalization.

### C7 — an unconditional transport bound for the literal bilinear form

**Dependency-closed baseline corollary; promotion deferred after corpus audit.**
For a finite prime support `S`
and an arbitrary real matrix `c`, define its net charge
`δ_c(p)=Σ_{q∈S}(c(p,q)-c(q,p))`. Its total charge is zero, and its prime
packet is exactly `Σ_{p,q∈S} c(p,q)(f_p-f_q)`, where `f_p` is the actual
energy-centered primitive. Let `D(p,q)` be C5's symmetric gap budget, and set

`M(c)=Σ_{p,q∈S}|c(p,q)|`, `C(c)=Σ_{p,q∈S}|c(p,q)|D(p,q)`.

Finite weighted Cauchy gives pointwise
`F_c(n)² ≤ M(c) Σ|c(p,q)|(f_p(n)-f_q(n))²`.
Absolute summability and C5 give `B(δ_c,δ_c)≤M(c)C(c)`.
Applying weighted Cauchy to finite pronic prefixes and passing to their
proved limits gives

`B(δ_c,δ_d)² ≤ M(c)C(c) M(d)C(d)`.

All inputs are finite supports and real coefficients; no cancellation or
equidistribution hypothesis is supplied. The arithmetic improvement comes
from C5's explicit gap cost. The final Cauchy step itself is classical.
The bound does not assert orthogonality of different transport edges: it
retains their worst-case coherent interaction. Removing that loss is still
C6's open collision problem, not a completed beyond-Nyquist estimate.

### C8 — quotient-cell wavelets expose the harmonic cost

**Paper derivation; corpus overlap audit and Lean pending.** In C5's block
`I_k=[kp,(k+1)p)`, before overlap (`kh≤p`), let `Δ=r_p-r_(p+h)`.
The pronic mass is `1/[pk(k+1)]`. The exact first moment is
`Σ_{n∈I_k}w_n Δ(n)=-h/[pk(k+1)]`, so the conditional mean is exactly `-h`.
Subtracting that mean gives the particularly simple variance

`Σ_{n∈I_k}w_n(Δ(n)+h)² = h/k - h²/p`.

The first moment follows by splitting at `k(p+h)`: it equals
`kh(1/(kp)-1/((k+1)p))-(p+h)(1/(kp)-1/(k(p+h)))`.
The variance follows from C5's exact block energy plus the first moment
and block mass. Different blocks of one pair have disjoint support, so
their mean-zero residuals are exactly orthogonal. Across different prime
pairs, the remaining task is their actual interval overlap geometry.

For all horizons, the exact identity
`Δ(n)=h floor(n/(p+h))-p #{k≥1:kp≤n<k(p+h)}`
also identifies the intervals, but its two terms grow linearly. Their
individual infinite pronic energies diverge. Any decomposition using it
must retain compensation before taking infinite sums.

### C9 — attach the gap tool to the existing dilation-profile carrier

**Paper consequence of existing corpus identities and C5; Lean scratch in progress.**
The search correction exposes a useful bridge that C7 did not provide.
For `r>1`, write `S=r.divisorsAntidiagonal`, `mu_x=mu(x.2)`, and
`X_p(n)=p*Re(pmRamanujanPrimitive r (n/p))`. Existing
`pmRamanujanPrimitive_eq_floor` and `sum_(d|r) mu(d)=0` imply exactly

`X_p(n) = -sum_(x in S) mu_x * (n mod (p*x.1))`.

Indeed `p*x.1*floor(n/(p*x.1)) = n-(n mod (p*x.1))`;
the linear `n` term cancels in the finite divisor sum. No asymptotic or
infinite rearrangement is involved. Finite Cauchy, followed by C5 for
each pair of moduli `p*x.1,q*x.1`, therefore gives

`sum_n (X_p(n)-X_q(n))^2/[n(n+1)] <= C_r*D(p,q)`,
`C_r = card(S)*sum_(x in S) mu_x^2*x.1`,

where `D` is `residueGapPronicBudget`. Its homogeneity is immediate from
the exact formula: `D(dp,dq)=d*D(p,q)` for positive integer `d`, since
both the smaller modulus and its gap scale by `d`, so their quotient
`K=floor(min(p,q)/abs(p-q))` is unchanged. The diagonal case is zero.
All sums of energies converge by boundedness and the pronic tail theorem.

Existing `pm_tsum_floor_dilation` and
`pmRamanujanDilationProfile_eq_integerDilationGram` identify the left side
with the original profile, giving

`(p+q)*G(r,r)-2*sqrt(p*q)*Phi_r(p/q) <= C_r*D(p,q)`.

Equivalently, the nonnegative profile defect obeys

`2*sqrt(p*q)*(G(r,r)-Phi_r(p/q))
 <= C_r*D(p,q)-(sqrt(p)-sqrt(q))^2*G(r,r)`.

This gives an explicit modulus for the exact kernel in the existing cube,
rather than only the unrelated prime-only net-charge packet. The bound is
still a pairwise continuity estimate. It does not provide cancellation of
the cube's signed coefficient sum. Search found the existing continuity,
floor expansion, exact integer-scale identity, and profile identification;
no novelty inference is drawn from the partial search for this combination.

## Formalized contribution

Module: `formal/GaloisForLFunctions/BezoutValuationIncidence/PrimePacketConditionalTailAndCoherentPrefix.lean`.

- `primePacketBilinear_eq_head_add_tail`: exact bilinear decomposition, with
  both finite prime supports and both coefficient sequences arbitrary.
- `hasSum_primePacketTailResidual`: the actual residual tail has zero mean.
- `hasSum_primePacketTailBilinear`: absolute summability and exact value of
  the residual bilinear series. Its diagonal is a genuine sum of squares.
- `primePacket_coherent_lower_bound`: unavoidable prefix energy plus forced
  conditional-tail-mean energy.
- `primePacketValue_above_prefix`, `primePacketHeadMean_above_eq`,
  `primePacketHeadBilinear_above_eq`: exact reduction of a before-jump prefix
  to coefficient mass and logarithmic moment.
- `primePacket_two_moment_lower_bound`: the explicit moment obstruction.
- `primePair_common_prefix_lower_bound`: for every pair of primes, including
  distinct primes,

  `Gec(p,q) ≥ Σ_{0≤n<min(p,q)} n/(n+1) - log p log q`.

All public statements use data parameters only; primes are represented by
`Nat.Primes`. No cancellation, boundedness, summability, or equidistribution
assumption is supplied by the caller. The module has 14 public theorems,
10 definitions, and one private summation helper. No numerical experiments,
`native_decide`, heartbeat overrides, or placeholders were added.

This specializes classical conditional-variance algebra to the literal
non-periodic prime kernel and exposes its exact coherent channels. It is
not a claim that conditional variance itself is new, nor a proof of the
requested dispersion estimate.

## Verification

- Original-source audit passed without warnings:
  `lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/BezoutValuationIncidence/PrimePacketConditionalTailAndCoherentPrefix.olean GaloisForLFunctions/BezoutValuationIncidence/PrimePacketConditionalTailAndCoherentPrefix.lean`.
- Source SHA-256:
  `4a1a2b57f61fedf1b2c632acfb503152b7baa563a629d11748e9f588d2368f33`.
- The leaf is imported by the BVI umbrella; no umbrella or full build ran.
- `scripts/formal_tools.py index` completed.
- `scripts/formal_tools.py lint --check-generated` found three foreign
  errors: unwired `CrossDepthEulerOperatorFactorizationAndPrimePairGramIdentity`,
  unwired `DilationProfileIntegerJumpCoupling`, and package-root
  `TransHorizonIncidenceMechanics.lean`. Existing large-file warnings also
  remain. No finding named the new leaf.
- Axiom audit of all 24 public declarations passed from a `/tmp` file;
  only `[propext, Classical.choice, Quot.sound]` occur (some definitions use
  subsets of these). No additional axioms or compiler reduction axioms.
- README untouched. No commits, numerical experiments, or server changes.

## Next mathematical obligation

Start from the existing all-depth/profile and finite jump-sector identities.
Identify an exact conversion of their signed cross-pair remainder into an
existing analytic estimate, with its phase, coherent modes, and cutoff error
retained. C7 is a classical baseline specialization; C8 is a local identity,
not a substitute for this conversion. Any further local gap estimate must
connect to the existing dilation-profile carrier before claiming progress
on the full cube. The beyond-Nyquist target remains open. Inverse reciprocity
must retain its numerator and both phases.

### C5 source verification

- Leaf: `formal/GaloisForLFunctions/BezoutValuationIncidence/PronicResidueGapEnergyAndPrimePairDistance.lean`.
- Original-source check passed without warnings:
  `lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/BezoutValuationIncidence/PronicResidueGapEnergyAndPrimePairDistance.olean GaloisForLFunctions/BezoutValuationIncidence/PronicResidueGapEnergyAndPrimePairDistance.lean`.
- Source SHA-256: `9dac453a5c826dec6b26e177767de69062899659acffed88855de1355fe73a6b`.
- 399 lines, 13 public declarations. Imported by the BVI umbrella.
- Axiom audit of all 13 public declarations passed in `/tmp`; only
  `[propext, Classical.choice, Quot.sound]` occur. The output is retained in
  `/tmp/bvi-transport-proof.log` (its unrelated transport scratch has one
  finite-product simplification error and is not yet a verified module).
- `scripts/formal_tools.py lint --check-generated` was rerun after corpus
  reconciliation. It reports nine foreign errors: seven unwired `CHMD*`
  modules, unwired `BirthDelayedInteriorJumpCenteringAndUniformPairBounds`,
  and package-root `TransHorizonIncidenceMechanics.lean`; no finding names
  either owned leaf. Existing large-file warnings remain. No global pass
  is claimed. Log: `/tmp/bvi-dispersion-lint-after-search.log`.

## Log

- 2026-10-18 — Initialized from the pasted task. Read field README, local
  instructions, formal guides, programme, wall discussion, and relevant memory.
  Started corpus searches and identified the exact prime primitive formula.
