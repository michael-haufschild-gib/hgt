# Route T Maynard near-one endpoint exclusion

- **ID:** `route-t-maynard-near-one-endpoint-exclusion`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` · Route T item 56
- **Statement:** Every Perron-relevant degree-60 Heath--Brown box in Maynard's ultra-near-one
  amplitude band is absent at polynomial ordinate height; equivalently its product amplitude has
  a quantitative gap strong enough to absorb the exact raised-Huxley coefficient and label cost.

## Goal

Close the sole remaining high-amplitude endpoint in Route T's Maynard--Peck prime-gap input.  The
result must be unconditional and source-pure: no RH, density hypothesis, unproved exponent pair,
zero-free premise, or abstract large-value premise.  Once composed with the already closed
fixed-Perron-abscissa restriction, exponent-zero trimming, long-factor exclusion, and selection
fibre count, it must supply the smooth-window prime-gap moment used by Route T's RH receiver.

## Gates

- [x] 0 → 1  in-progress: exact endpoint is well-posed; corpus and failed-route audit completed;
  proof interfaces and falsifiable alternatives isolated
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: unconditional Lean theorem, direct check, final module build, lint and
  axiom audit
- [ ] 3 → 4  publication-ready: standalone proof plus Route T composition certificate

## Exact inherited state

Direct-checked Lean already closes:

1. fixed Perron abscissa `c` independent of amplitude `alpha`;
2. arbitrary energy loss `rho > 0` and fibre exponent
   `(1367/2160) * (2 + rho - 2*alpha)`;
3. exact reserve

   ```text
   (mu - 2*(1367/2160))*(1-alpha) - (1367/2160)*rho;
   ```

4. actual amplitude cells and unique logarithmic slack;
5. fixed global deficit from every Perron-relevant long zeta/log factor;
6. exponent-zero trimming, Perron-relevant aggregate restriction, exact box selection, and
   high-amplitude all-short coloring.

For `mu >= 4/3`, the smallest reserve slope is

```text
4/3 - 2*(1367/2160) = 73/1080.
```

For every fixed gap `d <= 1-alpha`, choosing `rho=(73/1367)d` leaves reserve `73d/2160`.
This closes every band separated from `alpha=1` by a fixed positive gap.  It does not close the
endpoint because the reserve vanishes at `alpha=1` for every `rho>0`.

## Hostile source audit

Maynard's original Part 5 has two genuinely different mechanisms.

- For `alpha <= 1-eta`, a grouped factor is raised into the Huxley length window.  The power
  reserve `eta log x` absorbs every polylogarithmic coefficient and label loss.
- For `alpha >= 1-eta`, Vinogradov--Korobov cancellation gives a local deficit `3eta/2` on every
  factor longer than `x^(1/(40k))`; since at most `2k` shorter factors exist, either the large-value
  set is empty or global amplitude is below `1-eta`.

Here `eta = C log(x)^(-2/3) loglog(x)^(-1/3)`.  Canonical degree 60 makes Möbius atoms short relative
to the Route-T Huxley cutoff, but not relative to Maynard's much smaller `x^(1/(40k))` endpoint
cutoff.  Therefore “no long Möbius atom” removes one false branch but does not remove Maynard's
near-one endpoint.

Corpus Bourgain modules do not secretly discharge this: the logarithmic exponent-pair connector
still assumes `HasLogExponentPair (13/84) (55/84)`, and first-spacing elimination still assumes the
sharp `A_6 <= H^(6+epsilon)` theorem.  The unconditional corpus baseline is only `A_6 <=
H^(9+epsilon)`.

Before this card was opened, `5-failed/zero-free-region-below-exponent-one.md` was read in full.
Its killing theorem applies to every fixed/variable-order derivative-test or polynomial zeta-growth
attempt: the resulting growth is linear in `(1-sigma) log t`, so Landau/de la Vallée Poussin cannot
cross exponent one.  That route is not to be retried.  Its positive survivor says precisely that a
sublinear growth law, such as Vinogradov--Korobov/VMVT, is sufficient.

## Higher principle

The endpoint is not a missing label estimate.  It is a **zero-reserve rigidity transition**.
Below the endpoint, a power gap pays arbitrary finite analytic entropy.  At the endpoint, no fixed
energy loss is affordable, so one must prove that a near-maximal product cannot exist before paying
that entropy.  Three representations of the same required rigidity are possible:

1. sublinear near-one zeta growth / a Vinogradov--Korobov zero-free region;
2. uniform polynomial-height cancellation of the relevant Möbius blocks;
3. a coherent aggregate inverse theorem proving that near-maximal box products force impossible
   prime-log phase concentration.

The proof must be allowed to choose among these representations.  VK is sufficient, not assumed to
be logically necessary.

## Conjecture loop

### C1 — Fixed-deficit long-factor closure `[PROVED / FORMALIZED]`

Conjecture: every selected high-amplitude box contains a long zeta/log factor, hence has a fixed
global deficit.

Failure: canonical degree 60 only proves Möbius atoms satisfy the Huxley all-short cutoff.  Boxes
whose every factor is Huxley-short still exist.

Positive survivor: long zeta/log boxes have exact fixed global deficit
`maynardDerivativeDeficit 47 / 380`; the complementary high band has an exact all-short selection
label.  Formalized in `MaynardLongAmplitudeExclusionTrimmed.lean` and
`MaynardPerronAmplitudeSelection.lean`.

### C2 — Fixed-`rho` Huxley closes all-short endpoint `[FALSIFIED]`

Conjecture: choose one small fixed coefficient-energy exponent `rho` and use the arbitrary-amplitude
count uniformly through `alpha=1`.

Killing calculation: reserve equals

```text
(mu - 2b)(1-alpha) - b*rho,  b=1367/2160.
```

At `alpha=1` it is `-b*rho < 0`.  No fixed `rho>0` reaches the endpoint.

Positive survivor: for every explicit amplitude gap `d>0`, the schedule
`rho=(73/1367)d` is optimal at the worst Route-T height slope and leaves exact reserve
`73d/2160`.  Thus all non-endpoint bands are closed uniformly once their gap is supplied.

### C3 — Corpus Bourgain chain supplies missing sublinear growth `[FALSIFIED]`

Conjecture: existing Bourgain decoupling files already close a sufficiently strong logarithmic
exponential-sum estimate.

Killing audit: capstones remain implications from the sharp `A_6` moment or three sixth-power
spacing hypotheses.  `BourgainZetaReduction.lean` only transfers an assumed dyadic partial-sum
bound to zeta.  No unconditional near-one growth theorem is present.

Positive survivor: the exact missing Bourgain node is sharp `A_6`, not its geometric localization
or zeta transfer.  This gives a concrete possible upstream construction, but sharp `A_6` alone is
not yet shown to imply the endpoint theorem.

### C4 — Classical Littlewood strip plus existing Huxley package `[FALSIFIED AS STATED]`

Conjecture: the corpus's `loglog(t)/log(t)` zero-free width gives a Möbius log-power saving, enough
for the endpoint.

Failure: at polynomial height and factor length `x^ell`, the saving is only
`(log x)^(-c*ell)`.  Existing raised-group coefficient energy has a large fixed polylogarithmic
degree, and amplitude/box labels cost additional powers of `log x`.  The explicit Littlewood
constant cannot absorb those losses.

Positive survivor: Littlewood strength could become sufficient only after a genuinely label-free,
quantitatively low-entropy large-values reformulation.  This is a separate coherent-aggregate
candidate, not a proof.

### C5 — Möbius near-maximality forces impossible prime-log coherence `[ACTIVE ALTERNATIVE]`

Use a quantitative Halász inverse theorem to convert a near-maximal dyadic Möbius block into small
pretentious distance from `n^(it)`.  Then prove that the required prime-log phase concentration has
first hitting time larger than every polynomial in the block length.  This would directly make the
endpoint large-value set empty without building a full VK region.

Open core: deterministic growing-dimensional lower hitting-time estimates for the prime-log
Kronecker flow.  The corpus card `prime-log-level-two-entropy-budget-law.md` identifies the stronger
level-2 law; only a near-perfect-coherence exclusion is required here.  Existing recurrence results
give upper hitting times, not the required lower bound.

### C6 — Vinogradov--Korobov endpoint factor exclusion `[ACTIVE BASELINE]`

Build an unconditional sublinear near-one zeta-growth theorem, derive a quantitative zero-free
region and inverse-zeta bound, shift the twisted Möbius Perron contour at polynomial height, and
prove a deficit on every factor longer than `x^(1/(40*60))`.  Propagate local deficits through the
exact amplitude cells; conclude `R=0` in the ultra-near-one band.

This construction may use a different sublinear exponential-sum engine than historical VK, but it
must end in the literal box-factor theorem consumed by `MaynardPerronAmplitudeSelection.lean`.

### C7 — Widen existing Littlewood rectangle by one `loglog` power `[FALSIFIED]`

Conjecture: sharp planar `L^6` input widens the current derivative-test rectangle from
`loglog(t)^2/log(t)` to `loglog(t)^3/log(t)`, improving the de la Vallée Poussin quotient.

Killing algebra: for width `R=(log L)^A/L`, the existing head/tail balance gives
`log Phi=(log L)^(A-1)`.  Hence `log Phi/R=L/log L`, independent of `A`.  Merely widening the
rectangle cannot improve the zero-free width.  The missing input must lower fixed-height growth,
not move the same loss across a wider disc.

### C8 — Growing Heath--Brown degree beats endpoint entropy `[FALSIFIED]`

Conjecture: take degree `k` proportional to `loglog X`; many Möbius factors gain squarefree density
`exp(-c k)`, while few Möbius factors force zeta/log derivative loss.

Killing entropy: dyadic/amplitude selection costs `exp(Theta(k loglog X))`, whereas squarefree
density saves only `exp(-c k)`.  Increasing degree makes the deficit-to-label ratio worse.  Any
viable growing-degree argument needs signed Möbius cancellation, which is precisely the missing
zero-free input.

### C9 — Exact Bourgain Section-1 scale bootstrap `[ACTIVE; NEW LEAN SURVIVOR]`

Primary-source audit of Bourgain (1.18)--(1.26) narrowed the missing analytic node.  Corpus already
had exact Taylor localization, perturbation-stable sharp normalized cells, translation, and finite
grids, but not their global physical-scale conservation law.

`BourgainSectionOneBlockPair.lean` now proves an explicit two-arc block geometry.  For `J` coarse
blocks of `H` samples, denominator `D=4JH`, all left/right blocks remain in `[0,1]`, separation is
at least `1/4`, and `J >= 6*C_Taylor*H^2` discharges cubic Taylor smallness.  Canonical
`J(H)=301989888000 H^2` removes that scale premise.

`BourgainSectionOneGlobalBilinear.lean` proves:

- forward normalized jet norm at most `40`;
- physical `D^2` phase ball fits an explicit anisotropic grid with multiplicities
  `(320JH,80,320JH,80)`;
- exact grid cardinality `(320JH+1)^2*81^2 = O(D^2)`;
- generic translation-uniform cell aggregation;
- reciprocal cell Jacobian times natural cell volume is `O(D^6)`;
- therefore grid multiplicity times cell scale is `O(D^8)`, exactly ambient four-volume, with
  every `H` power canceled;
- a global sharp block-pair moment over the full `D^2` phase ball, with only the planar subpower
  factor remaining.

This is genuine new formal knowledge and closes the covering/Jacobian uncertainty in C3.  Open core
is now only the multiplicative recurrence producer: sum block-pair refinements into the conditional
`b(R) <= R^delta b(R^(2/3))` inequality, feed `BourgainPowerScaleSubpower.lean`, then run Section 2
linearization to sharp `A_6`.

#### C9 continuation — recurrence geometry and exact one-step theorem `[PROVED IN LEAN]`

Primary equations (1.19)--(1.25) require two details absent from the earlier survivor: the two
coarse arcs are translated **independently** in (1.20), and the `K`-cube sum must cancel against
normalized physical volume rather than leave a cover-cardinality loss.  Both are now closed.

`BourgainSectionOneIndependentTranslation.lean` proves that independent left/right translations
are independent unit-character twists of the two full coefficient vectors.  Restriction to every
coarse block commutes exactly with its full-vector twist, all sixth coefficient masses are
unchanged, and the sharp block-pair family estimate is uniform in the two translation vectors.

`BourgainSectionOneRecurrenceGeometry.lean` identifies the paper scales exactly:

```text
fine physical radius   N = (4JH)^2,
coarse physical radius K = (4J)^2,
N/K = H^2.
```

The fine four-cube is exactly the union of `H^8` coarse cubes.  Their closed-boundary overlaps are
Lebesgue-null; Lean proves pairwise a.e. disjointness, exact cube volume, and equality of the fine
integral with the sum of all coarse-cube integrals.

`BourgainSectionOneRecurrenceAveraging.lean` formalizes the anchor averaging behind (1.20).
Multiplying local mass products by one coarse-cube volume, summing, and applying Tonelli converts
them to independent radius-`2K` translates.  Hence the apparent `H^8` count cancels exactly.

`BourgainSectionOneRecurrenceStep.lean` then proves the full one-step inequality corresponding to
(1.19)--(1.26).  If `b` is a valid local decoupling coefficient at scale `(4J)^2`, then the
separated full-arc moment at `(4JH)^2` has:

- coefficient factor `b^12 K^2`;
- sharp planar refinement `H^(4+epsilon)`;
- ambient volume `(4JH)^8`;
- no `J`- or `H`-power from grid localization;
- only absolute factor `256`, since the doubled averaging cube has volume ratio `16` and two
  independent translates square that ratio.

This is the first axiom-free Lean theorem in the corpus matching Bourgain's Section-1 recurrence
exponent-for-exponent.  Remaining C9 core is no longer physical geometry or independent
translation.  It is the **iterable packet coefficient**: construct a scale-indexed local
decoupling coefficient for arbitrary fine packets (not merely scalar terminal samples), prove a
coarse polynomial baseline, apply the new one-step theorem recursively, then discharge the
existing two-thirds subpower closure.

## Required Lean endpoint

Target shape, to be refined against existing definitions:

```lean
theorem eventually_no_perronRelevant_selection_near_one :
  ∀ᶠ T in Filter.atTop, ∀ ...,
    IsHeathBrownPerronRelevantEligibleSelection ... label →
    1 - maynardNearOneGap T < alpha →
    False
```

No analytic premise may remain.  `maynardNearOneGap T` must be explicit, positive eventually, and
large enough that the arbitrary-amplitude Huxley reserve absorbs the exact remaining costs at its
lower boundary.

## Immediate attack order

1. Formalize endpoint reserve collapse and the exact quantitative gap demanded by all current
   coefficient/label costs.
2. Prove a literal factor-mass lemma: any Perron-relevant all-short degree-60 box has enough length
   above Maynard's endpoint cutoff that local near-one deficits force the global gap.
3. Attack C5 and C6 in parallel conceptually; retire either only with a positive survivor.
4. Compose first successful endpoint exclusion into selection fibres and smooth-window receiver.

## Log

- 2026-08-12 — opened after fixed-abscissa correction, long-factor closure, trimming, relevance,
  and high-amplitude selection were direct-checked.  Hostile audit found fixed-`rho` endpoint false
  and corrected frontier claim that canonical short Möbius atoms remove Maynard's Case 2.
- 2026-08-12 — audited original Maynard Part 5, failed exponent-one zero-free route, corpus
  Littlewood/Möbius contour chain, and Bourgain capstones.  Isolated zero-reserve rigidity as higher
  principle and retained two live realizations: prime-log coherence exclusion or VK-strength
  sublinear growth.
- 2026-08-12 — falsified C7 and C8 by exact exponent/entropy algebra.  Built and direct-checked
  `BourgainSectionOneBlockPair.lean` and `BourgainSectionOneGlobalBilinear.lean`; proved exact
  `D^2 * D^6 = D^8` Section-1 scale conservation and global block-pair moment.  Next seam is the
  recurrence producer, not geometry or aggregation.

### C9 hostile endpoint audit — fixed `A₆` and unweighted packets do not close Route T `[FALSIFIED AS ENDPOINT ENGINE; SURVIVOR RETAINED]`

The exact Section-1 recurrence above is correct and remains new formal knowledge.  Two later audits
kill its use as the present endpoint engine.

First, even a sharp fixed-degree `A₆` estimate changes a fixed critical-strip polynomial-growth
exponent but still produces growth linear in `(1-sigma) log t`.  No fixed polynomial-growth
exponent creates a zero-free width `(log t)^(-kappa)` with `kappa < 1`; it therefore cannot absorb
Route-T endpoint polylogarithmic entropy.

Second, literal iteration needs Bourgain's weighted packet norm.  The primary source explicitly
replaces same-cube norms by weights `w_N` satisfying
`1_B <= w_N <= (1+|x|/N)^(-10d)` and Fourier support in `B_(1/N)`.  The current unweighted
`BourgainSectionOneLocalDecouplingAt` is too strong for arbitrary bandlimited packets: high-order
zeros or spatial concentration can make a packet small on one cube and large on its translate.
The density-invariant survivor is therefore weighted wave-packet localization, not an unweighted
arbitrary-packet generalization.

A separate audit of the existing unit-scale `A₆` diagonal recurrence found its off-diagonal term to
be `K^20 N^10 M^(4+epsilon)`, far above the required `H^(6+epsilon)`.  That recurrence is not a
bypass.  C9 remains a valid exact scalar one-step theorem and a future weighted-decoupling asset,
but is retired as the shortest Route-T endpoint producer.

### C10 — polynomial order-loss universality `[ACTIVE BASELINE]`

The source chain reveals a weaker and more universal target than full Vinogradov--Korobov.
Suppose dyadic logarithmic phases at height `t`, with `r` determined by
`N^(r-1) < t <= N^r`, admit any fixed finite-order saving

```text
|sum_(N<n<=N') (n+alpha)^(-it)| <= C N^(1-c/r^q),
```

uniformly in `0 <= alpha <= 1`, for one finite `q > 0`.  Since
`r asymp log t / log N`, this is

```text
N exp(-c (log N)^(q+1)/(log t)^q).
```

Partial summation at `sigma=1-delta` balances

```text
delta log N - c (log N)^(q+1)/(log t)^q,
```

whose maximum is `O(delta^((q+1)/q) log t)`.  Thus the zeta-growth exponent is
`1+1/q > 1`, and the resulting zero-free width has logarithmic exponent

```text
q/(q+1) < 1.
```

Every finite `q` therefore beats every fixed Route-T logarithmic loss.  By contrast, the existing
`k`th-derivative chain loses exponentially in `r`; optimizing that loss gives Littlewood's
`loglog t / log t` width and cannot cross exponent one.  This identifies the exact universal
transition:

> Route T needs polynomial, not exponential, deterioration with phase order.

Historical Chudakov already supplied enough: his original result gives every zero-free exponent
`a > 10/11`, so full modern `2/3` Vinogradov--Korobov strength is unnecessary.  Montgomery--Vaughan
Chapter 24 provides a clean stronger implementation.  Its Theorem 24.13 gives `q=2` from Theorem
24.12; Theorem 24.12 uses only the classical Vinogradov mean-value estimate Theorem 24.5 plus
rational approximation and bilinear endpoint perturbation.  Theorem 24.5 itself is proved by
Newton--Girard rigidity, Linnik's congruence lemma, and a `p`-adic induction.  This is now the active
unconditional construction.

The first formal seam is not an abstract implication theorem.  It is Lemma 24.3(a): for `b <= k`,
equality of the first `k` power sums forces two `b`-tuples to be permutations.  This supplies the
exact diagonal bound `J_k(x,b) <= b! x^b` used as the base case of the unconditional mean-value
induction.

## Log continuation

- 2026-08-12 — hostile audit retired sharp fixed `A₆` as a Route-T endpoint engine and identified
  Bourgain's weighted packet norm as the missing iterable formulation.  The proved scalar
  Section-1 recurrence remains valid.
- 2026-08-12 — source-checked Montgomery--Vaughan Theorems 24.5, 24.12, 24.13, and 24.15.  Derived
  polynomial order-loss universality: any `N^(-c/r^q)` saving with finite `q` yields a sublinear
  near-one growth law and zero-free exponent `q/(q+1) < 1`.  Chudakov-level strength is enough for
  Route T; active core is classical VMVT, beginning with power-sum rigidity.

### C11. Exact Linnik lifting is now unconditional in Lean

The Newton--Girard base case and Linnik's simultaneous-congruence bound are now closed, not merely
recorded as interfaces:

- `VinogradovPowerSumRigidity.lean` proves equality of the first `b` power sums determines a
  `b`-tuple up to permutation;
- `VinogradovDiagonalMoment.lean` proves the exact diagonal estimate
  `J_k(N,b) <= b! N^b` for `b <= k`;
- `VinogradovLinnikLifting.lean` proves that two length-`k` residue tuples modulo `p^k`, distinct
  modulo a prime `p > k`, with equal first `k` power sums modulo `p^k`, have equal multisets;
- `VinogradovLinnikCount.lean` proves the sharp source bound
  `A(p,h) <= k! p^(k(k-1)/2)` for the nested congruences modulo `p, ..., p^k`.

The lifting proof exposes the exact mechanism: Newton identities are valid modulo `p^k` because
`1,...,k` are units; equality of monic root polynomials gives a vanishing product; reduction modulo
`p` selects the unique vanishing factor; every other factor is a unit modulo `p^k`; cancellation
lifts equality from modulo `p` to modulo `p^k`.  Counting compatible full-modulus lifts contributes
exactly

```text
sum_{j=0}^{k-1} (k-j-1) = k(k-1)/2
```

prime-power digits, while each full-signature fibre contributes at most `k!` permutations.

This is genuinely new formal knowledge and the first exact polynomial-order-loss component in the
Route-T endpoint producer.  It does not yet prove a mean-value saving: the remaining hard seam is
the `p`-adic induction assembling the diagonal and Linnik bounds into Montgomery--Vaughan Theorem
24.5 with constants strong enough to retain `r^-2` after Theorems 24.12--24.13.

### C12. Prime-number-theorem dependence can be traded for a weaker sufficient exponent

Hostile source audit found that Montgomery--Vaughan's proof uses a short prime interval only to find
one prime avoiding the Vandermonde product of the first `k` coordinates.  Route T does not require
the source's optimal `r^-2` exponential-sum saving.  Iterating Bertrand gives `O(k^3)` distinct
candidate primes above the natural `k`-th-root scale with

```text
p <= 2^O(k^3) N^(1/k)
```

up to the exact integer-root rounding proved in Lean.  The extra factor contributes
`exp(O(k^5))` per Vinogradov induction step.  After the mean value is raised to the
`1/(4k^2 r^2)` power in Theorem 24.12 and `r ~ k`, this is `exp(O(k^2))`; it is absorbed once
`log N >> k^4`.  Below that threshold the trivial estimate costs only `N^(O(k^-4))`.
Consequently the PNT-free construction predicts a uniform `N^(1-c/r^4)` sum bound and a zero-free
logarithmic exponent `4/5 < 1`.  This remains strictly beyond the exponent-one barrier and is enough
for every fixed Route-T logarithmic loss.

The arithmetic core is now unconditional in Lean:

- `VinogradovBertrandReservoir.lean` constructs the ceiling power root, an explicit iterated-Bertrand
  prime reservoir, and proves that one of `M+1` primes avoids every nonzero `A <= y^M`;
- `VinogradovAvoidingPrime.lean` builds the directed Vandermonde product and proves that every
  injective `k`-tuple has a selected prime `p > k` with `N < p^k`, distinct residues modulo `p`, and
  the explicit reservoir upper bound.

Active core is now the finite incidence recurrence itself: collision split, prime assignment,
Linnik fibre count, and reduction from moment order `kr` to `k(r-1)`.

### C13. Fixed-reservoir Linnik recurrence is unconditional in Lean

The full finite incidence recurrence is now closed.  The decisive correction to the source-level
sketch is to choose one global prime Fourier modulus above both the exact-moment threshold and the
entire Bertrand reservoir.  The original convenient modulus
`2(k+b)N^k+1` can share a factor with a reservoir prime, so affine residue-class scaling need not be
invertible.  `VinogradovReservoirRecurrence.lean` instead constructs

```text
q = BertrandNext(max(2(k+b)N^k, reservoirBound(N,k))).
```

Thus every reservoir prime `p` satisfies `p<q`, hence is a unit modulo `q`, while equality modulo
`q` still equals integer power-sum equality exactly.

The closed chain is:

- `FiniteFiberPartition.lean` partitions each solution pair into injective and colliding leading
  blocks at binary square cost;
- `FiniteFiberCover.lean` covers every injective leading block by the fixed reservoir, at its exact
  cardinal cost;
- `FinitePowerSumHolder.lean` forces all tail variables into one residue class, with factor
  `p^(2b-1)`;
- `VinogradovShiftedCompatibility.lean` extracts the shifted nested Linnik congruences forced by a
  same-residue tail solution;
- `VinogradovResidueGoodCount.lean` bounds every single-class completion by
  `N^k k! p^(k(k-1)/2) J_k(ceil(N/p),b)`;
- `VinogradovResidueGoodEnergy.lean` identifies this count with the relevant fibre energy and sums
  the `p` residue classes, producing the exact `p^(2b)` factor;
- `VinogradovReservoirRecurrence.lean` sums over the reservoir and combines the result with the
  colliding-block term
  `((k^2-k)N^(k-1))^2 J_k(N,b)`.

This proves, without PNT, computation, assumptions, or axioms, a dependency-closed recurrence for
`J_k(N,k+b)`.  Active core has moved from incidence geometry to solving this explicit recurrence
at `r≈k^2` and extracting a uniform polynomial-in-order Weyl saving.

### C14. PNT-free mean-value induction admits an integer-exponent invariant

`VinogradovMeanValueBound.lean` solves the recurrence without introducing real powers.  For moment
length `kr`, define

```text
E(k,r) = k + (2k-2)(r-1).
```

The theorem proves

```text
J_k(N,kr) <= D(k,r) N^E(k,r)
```

for every step budget satisfying

```text
2u + k(k-1)/2 <= (k-1)(k-2)       (1 <= u < r).
```

Mechanism is exact.  Collision branch multiplies by `N^(2k-2)`.  In noncollision branch,
`p ceil(N/p) <= 2N` absorbs the tail scale, while the reservoir estimate `p^k <= C_k N` absorbs
the remaining Linnik power; the same exponent increment `2k-2` results.  If the reservoir itself
exceeds `N`, `VinogradovReservoirScale.lean` proves that `N` lies below an explicit `k`-dependent
threshold and trivial counting is absorbed into `D(k,r)`.

The later Route-T parameters are already closed arithmetically:

```text
k = 100s,
r = 2500s^2 - 200s.
```

Lean proves this entire range admissible.  Since

```text
E(k,r) - (2kr - k(k+1)/2) = O(k),
```

the mean-value excess is linear in phase order.  This is substantially stronger than needed for
the `k^-4` PNT-free Weyl target.  Active core is now the analytic mean-value-to-exponential-sum
bridge (Montgomery--Vaughan 24.7--24.13), not VMVT.

### C15. Exact-box Fejér smoothing closes the multivariate MV24.7 core

The analytic bridge no longer needs a guessed weighted VMVT interface.  A dependency-closed Lean
chain now constructs the exact smoothing used in Montgomery--Vaughan Theorem 24.7:

- `PhaseGeometricBound.lean` identifies phase distance with the additive-circle norm, proves the
  chord lower bound `4||x|| <= |e(x)-1|`, and derives the exact Fejér-scale estimate
  `(2/H)|sum_{n<H}e(nx)|^2 <= min(2H, (2H||x||^2)^-1)` off resonance;
- `VinogradovWideDifference.lean` doubles the exact signed-difference box while retaining the same
  uniform Vinogradov fibre bound, so every Fejér pair difference is represented without modular
  aliasing;
- `VinogradovFejerMajorant.lean` proves the new constructive majorant principle: if tuple power sums
  are `A,B <= B0`, then the `B0+1` shifted pairs `(A+t,B+t)` all have the same difference.  With
  `H=2B0+1`, their normalized fibre mass is greater than one.  No absolute-value split or closed
  triangular-coefficient formula is required;
- `VinogradovFejerFourier.lean` tensorizes those fibre weights and proves their Fourier transform is
  exactly the product of one-dimensional Fejér kernels;
- `VinogradovSmoothedMoment.lean` expands the polynomial `2b`-moment, applies the tensorized identity,
  and groups the remaining tuple differences by the proved shifted Vinogradov bound;
- `VinogradovRectangularKernel.lean` inserts coordinate support `|g_j| <= bX^(j+1)` before
  factorization.  This prevents the common-box radius `bX^k` from creating a fatal `X^(k^2)` loss.

Consequently the entire second-Hölder and multivariate smoothing part of MV24.7 is now reduced in
Lean to a product of one-dimensional finite kernel sums, with the sharp coordinate ranges and no
unproved positivity, periodicity, or fibre assumptions.

A further corpus-guided pivot removes the need to duplicate MV Lemma 24.6 literally.  The existing
formal large-sieve chain bounds Fejér mass on every circle-separated block.  If
`|alpha-a/q| <= q^-2`, any block of at most `(q+1)/2` consecutive integer frequencies is
`1/(2q)`-separated.  Applying the existing explicit separated large sieve gives a block cost
`O(H+q log q)` and hence the coordinate sum

```text
O(GH/q + G log q + H + q log q).
```

The extra logarithm is harmless because C14 supplies a fixed polynomial saving after the
`1/(4b^2)` root.  Active core is now formal separation, finite block partition, and the two outer
Hölder steps of MV24.7.

### C16. The complete finite MV24.7 bridge is unconditional in Lean

The remaining analytic seams in C15 are now closed.  The key new principle is that no separate
weighted-VMVT hypothesis is needed: the constructive Fejér weight is at least one on every actual
power-difference vector, so exact wide-box fibre grouping converts actual tuple moments into the
smoothed moment with the single sharp factor `J_k(Y,b)`.

The dependency-closed chain is:

- `PhaseGeometricBound.lean` proves Fejér evenness and its global `2H` bound;
- `VinogradovFejerBlockPartition.lean` partitions `[0,G]` into consecutive blocks of length
  `(q+1)/2`, proves every block has diameter at most `q/2`, and retains the exact quotient count
  `floor(G/((q+1)/2))+1`;
- `VinogradovCoordinateKernelBound.lean` maps the centered signed box to absolute indices with
  fibre cardinality at most two, applies the existing separated large sieve blockwise, and proves

```text
sum_g K_j(g)
  <= 2 (floor(G_j/((q_j+1)/2))+1) BlockCost(H_j,q_j).
```

  It also closes the trivial coordinate estimate used when no rational saving is available;
- `VinogradovActualMoment.lean` proves the pointwise Fejér majorant dominates every actual
  `Y`-tuple difference, groups those differences by exact fibres, and obtains

```text
sum_actual_moments
  <= J_k(Y,b) J_k(X,b) product_j coordinateKernelSum_j.
```

- `VinogradovBilinearHolder.lean` proves both outer Hölder steps from finite sums, expands and
  regroups the first moment exactly, and composes the result with simultaneous rational
  approximations in every coordinate.

Thus the finite bilinear content of Montgomery--Vaughan Theorem 24.7 is now a proved Lean theorem,
including its two outer Hölder steps, both Vinogradov mean-value factors, exact Fejér smoothing,
and explicit rational-approximation product.  No logarithmic endpoint completion, unproved
weighted norm, asymptotic placeholder, computation, or axiom remains in this bridge.

The source theorem's constants are deliberately not copied: the formal large-sieve block cost has
one explicit `log(q+1)` loss.  C14's polynomial-in-order reserve absorbs this after the
`1/(4b^2)` root.  Active core is now quantitative exponent extraction: insert the C14 mean-value
bound at the Route-T parameters, choose the useful rational coordinates, and prove a uniform
`N^(1-c/r^4)` single-sum estimate before transporting it through zeta growth to the near-one
Maynard endpoint.

### C17. Useful-coordinate entropy pays the complete Route-T loss with a strict polynomial reserve

The quantitative extraction is now closed in Lean.  Write the auxiliary Route-T parameter as
`s=4u`, the phase order as `k=400u`, and the moment as
`b=k(2500s^2-200s)`.  The upper half of the coordinates contains at least `200u` indices.  Every
such index has rational-coordinate saving exponent at least `u`, so the product reserve is exactly
bounded below by

```text
sum_useful floor((j+1)/200) >= 200u^2.
```

The two PNT-free Vinogradov mean values and the natural coordinate mass have total excess

```text
2 E(k,r) + k(k+1) - 4b = 2800u + 4.
```

Hence the net reserve is the literal natural number

```text
R(u) = 200u^2 - (2800u+4) >= 100u^2       (u >= 29).
```

This is not an asymptotic bookkeeping claim.  `VinogradovRouteTSaving.lean` now proves, without
axioms, the collected `4b^2`-moment estimate, cancels numerator and denominator powers exactly,
absorbs every finite combinatorial constant once `Q` exceeds one explicit natural threshold, and
takes the exact real root.  The resulting pointwise theorem is

```text
|B_Q(alpha)| <= Q^(2-delta_u),
delta_u = (100u^2-1)/(4b^2) > 0.
```

The important new principle is quantitative: expanding the coordinate window term by term makes
the apparent `P/R` block cost cancel against the `q log q` large-sieve term.  Separately bounding
those factors would destroy the reserve.  After that cancellation, useful-coordinate entropy is
quadratic in `u`, while every mean-value loss is only linear in `u`; the finite MV24.7 bridge
therefore produces a genuine polynomial saving without full VMVT or PNT input.

Active core is no longer the bilinear moment estimate.  It is the MV24.11--24.12 transport problem:
construct simultaneous useful-coordinate rational approximants for Taylor phases, retain the
explicit denominator window and logarithmic absorption hypotheses, and perturb the proved
bilinear bound into a one-dimensional logarithmic-phase sum with exponent strictly below one.

### C18. Arbitrary interval embeddings preserve both Vinogradov fibre bounds

A source audit found a real logical seam: Montgomery--Vaughan 24.7 and 24.11 use the product
interval `(Q,2Q]^2`, whereas C17's finite bridge summed over prefix boxes.  Pointwise domination by
a prefix sum is false for complex exponential sums, so silently replacing one by the other would
invalidate the transport.

The correct universal principle is fibre-monotonicity, not sum-monotonicity.  If `e : A ↪ [0,N)` is
any injective interval embedding, then the induced map on every `b`-tuple pair is injective.
Consequently each exact power-difference fibre of the restricted interval embeds into the
corresponding full-box fibre.  This works independently at both Fejér groupings.

`VinogradovEmbeddedActualMoment.lean` and `VinogradovEmbeddedBilinear.lean` now prove this complete
embedded MV24.7 bridge.  Outer Hölder costs the actual interval cardinalities, while both
Vinogradov mean values and all coordinate kernels use the chosen ambient boxes.  Specializing the
embedding to

```text
Fin Q -> Fin (2Q),       n |-> Q+n
```

gives the exact source interval.  `VinogradovUpperHalfSaving.lean` proves the resulting unconditional
bound

```text
|sum_{Q<l,m<=2Q} e(sum_j alpha_j (lm)^j)|
  <= (2Q)^(2-delta_u),
delta_u = (100u^2-1)/(4b^2) > 0,
```

under the explicit useful-coordinate denominator windows and a single explicit natural threshold.
No cancellation comparison with a prefix sum occurs.

`VinogradovTaylorPerturbation.lean` additionally proves that a uniform phase error `|epsilon_lm|<=eta`
costs at most `2*pi*eta*Q^2`.  Thus Taylor remainder is cleanly separated from Diophantine saving:
the former is an additive perturbation budget, the latter remains the exact C17 power reserve.

Active core is now the denominator-production theorem.  For logarithmic derivatives one must prove,
uniformly over Taylor centres, simultaneous reduced rational approximants in the exact useful
windows required by C17, including absorption of the explicit `log(q+1)` term.  Once produced, the
compiled upper-half theorem is already in the form consumed by MV24.11.

### C19. Taylor compatibility forces a narrow coordinate band and closes the full log phase

The height-shell audit disproved C17's original choice of every degree `200u <= d <= 400u`.
This was a substantive obstruction, not a constant loss.  Write the Taylor centre as
`N=B^200`, ambient bilinear length as `P=B^99`, and height shell as

```text
N^(4u-1) <= t <= N^(4u).
```

For a rational saving exponent `e=floor(d/200)`, denominator transport requires

```text
200(d-(4u-1)) + O(1) <= 198(d-e),
```

while Taylor decay requires `2*99<200`.  At `d=400u` these conditions conflict.  The compatible
band is instead

```text
200u <= d <= 240u.
```

It contains `40u` coordinates and retains aggregate saving `40u^2`.  After the exact mean-value
loss `2800u+4`, this leaves at least `20u^2` reserve for `u>=141`, hence the revised unconditional
pointwise saving

```text
delta_u = (20u^2-1)/(4b^2) > 0.
```

This narrow-band law is the first higher compatibility principle exposed by Route T: useful
coordinates cannot be selected from Diophantine entropy alone.  Their degree support must lie in
the intersection of the rational-denominator cone and Taylor-remainder cone.

The entire intersection is now formalized:

- `VinogradovUsefulCoordinates.lean` proves the `40u^2` band reserve;
- `VinogradovRouteTSaving.lean` proves the revised rooted saving and the useful quantitative bound
  `0<delta_u<=1/100`;
- `VinogradovLogHeightWindow.lean` proves both reciprocal denominator windows from the exact shell,
  constructs all simultaneous reduced approximants, absorbs `log(q+1)`, and feeds them into the
  true upper-half bilinear theorem;
- `VinogradovLogTaylorRemainder.lean` proves the exact logarithmic series remainder.  Since
  `lm/x<=B^-2`, order `400u` contributes `B^(-2(400u+1))`, which cancels the height
  `B^(800u)` and leaves the sharp uniform error `B^-2`;
- the same module restores the Taylor constant and proves the source phase estimate

```text
|sum_{Q<l,m<=2Q} e((t/2pi) log(x-lm))|
  <= 2 * (B^99)^(2-delta_u),
Q = (B^99)/2,
```

under one explicit natural base threshold, uniformly for `N<=x<=2N` and the full height shell.
All statements are axiom-free and contain no numerical computation.

Active core has moved beyond Taylor and denominator production.  Next step is the exact
MV24.11 convolution receiver: transfer this bilinear block saving to the one-dimensional
Dirichlet polynomial with divisor-convolution coefficients, preserve the `delta_u` gain through
dyadic decomposition and coefficient norms, then feed that exponent into the Maynard/Huxley
near-one zero-free receiver.

### C20. The convolution receiver forces a wider centre window and admits an exact finite Fejer law

Auditing Montgomery--Vaughan Lemmas 24.8--24.11 exposed a second real compatibility condition.
The convolution centre ranges to `2N+2Q^2`, so C19's `x<=2N` window did not contain every Taylor
centre consumed by the receiver.  Enlarging to `x<=4N` is sufficient.  It changes the uniform
coefficient cost from `2^d` to `4^d`, absorbed by the explicit threshold

```text
32(240u+1)4^(240u) <= B,
```

without changing the useful-coordinate reserve or `delta_u`.  The widened height-window and both
twisted logarithmic phase theorems are Lean-closed.

The finite coefficient-smoothing mechanism is also now explicit and formalized in
`MontgomeryVaughanCoefficientSmoothing.lean`.  With the project's twice-classical Fejer kernel,
the difference kernel

```text
K_(M,L) = (M+L)/(2L) Delta_(M+L) - M/(2L) Delta_M
```

has multiplier exactly one on `|h-H|<=M`, tapers between `M` and `M+L`, vanishes outside, and has
the exact `L1` cost

```text
integral_0^1 |K_(M,L)(beta)| dbeta <= 2M/L + 1.
```

Consequently the source's Lemma 24.8 is proved for every finite coefficient sequence, with the
boundary annulus retained rather than hidden in `O` notation.  For coefficients dominated by the
number of divisors in `[Q,2Q]`, direct divisor swapping gives the new local law

```text
sum_(A<n<=B) tau_[Q,2Q](n) <= 2(B-A)+Q+1,
```

and hence the two annuli cost at most `4L+2Q+2`.  Arbitrary intervals `(Y,Z]` reduce to the symmetric
kernel with only one endpoint coefficient loss.  These statements are unconditional, finite, and
direct-check clean in Lean.

Active core is now sharply isolated: choose and verify the square-root smoothing length, prove the
finite MV24.10 convolution rearrangement, and specialize its full twisted polynomial to C19's
uniform logarithmic block.  No Taylor, Diophantine, or coefficient-smoothing premise remains open.

### C21. Product-box mass closes MV24.10 and yields a strict one-dimensional saving

The feared coefficient lower bound does not require a divisor asymptotic.  The explicit injection

```text
(a,b) in [0,Q/4)^2  |->  (Q+a+1,Q+b)
```

lands inside `Q^2 < lm <= 2Q^2` for `Q>=8`.  Thus Route T's product multiplicity has receiver-block
mass at least `Q^2/64`.  This endpoint-shifted box is the exact positive survivor of the convolution
geometry: it both avoids the excluded lower endpoint and stays uniformly below `2Q^2`.

`MontgomeryVaughanConvolutionReceiver.lean` now proves the full finite MV24.10 chain: product
regrouping by additive centre, exact edge slices, inheritance of balanced-divisor domination,
square-root coefficient smoothing, product-fibre multiplicity, and identification of every full
twisted convolution polynomial with C19's logarithmic bilinear sum.

`MontgomeryVaughanLogPhaseReceiver.lean` supplies a symbolic, non-evaluated base threshold and
proves, unconditionally on the full Route-T height shell,

```text
|sum_(N<n<=2N) exp(i t log n)| <= 6912 N P^(-delta_u/2),
P=(2C)^99,  N=(2C)^200,  delta_u>0.
```

The threshold is explicit:

```text
max(RouteTLogBaseThreshold(u), 8^(4 b(4u)^2)) <= 2C.
```

It guarantees `8<=P^delta_u`, exactly the condition needed for the bilinear saving to fit below
the coefficient-block length.  No computation, asymptotic notation, density premise, or hidden
coefficient hypothesis remains.  This is the first axiom-free strict one-dimensional exponent
saving produced by Route T.

Active core: rewrite `P^(-delta_u/2)` as
`N^(-99 delta_u/400)` and carry this exponent through the Maynard/Huxley near-one zero-free
receiver.  The convolution obstacle itself is closed.
