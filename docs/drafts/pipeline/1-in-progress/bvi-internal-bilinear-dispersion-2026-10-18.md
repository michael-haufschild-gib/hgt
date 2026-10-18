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

**Paper derivation; formalization and overlap audit pending.** This is an
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

Formalize C5's exact two-cell identity and gap-energy upper bound, then
determine whether the conditionally centered tail or structured coefficient
packets admit a genuine internal bilinear saving. Keep the full beyond-Nyquist
target open. Inverse reciprocity must retain its numerator and both phases.

## Log

- 2026-10-18 — Initialized from the pasted task. Read field README, local
  instructions, formal guides, programme, wall discussion, and relevant memory.
  Started corpus searches and identified the exact prime primitive formula.
