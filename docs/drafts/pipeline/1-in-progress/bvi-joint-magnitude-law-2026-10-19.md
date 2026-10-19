# BVI: joint magnitude laws across fixed shifts

- **ID:** bvi-joint-magnitude-law-2026-10-19
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean); explicit coercivity sharpening open; uncounted
- **Source:** Verified one-point cofinal source law; existing quotient-product and gradient-coercivity results; corpus search for shifted squarefree producers.
- **Statement:** At every fixed finite horizon ratio, the vector of absolute Möbius source values at any finite list of fixed shifts has an explicit limiting law, with raw masses affine between adjacent integer ratios.

## Goal

For `s_N(n)=sieveSeq N moebiusReal n`, the one-point law does not determine
`(abs(s_N(n+h_i)))_i`. The proposed joint law would resolve magnitude patterns
and supply arithmetic lower bounds for the actual shift-gradient energy.
No signed two-point Möbius cancellation is assumed or claimed. This is a
single candidate, not one contribution per shift, moment, or corollary.

Native consumer: the reverse triangle inequality gives
`(|s_N(n+1)|-|s_N(n)|)^2 ≤ (s_N(n+1)-s_N(n))^2`.
The joint magnitude law would give the exact limiting mean on the left.
This can strengthen the existing odd-squarefree zero-edge coercivity without
requiring the signed successor-correlation limit.

## Gates

- [x] Documented corpus search started before any new Lean code.
- [x] Inspect narrowed squarefree-correlation and BVI quotient-product results.
- [ ] Audit classical Mirsky-type laws and existing applications to this source.
- [x] Complete the paper proof of the finite-residue joint law, including tails and boundaries.
- [x] Formalize the dependency-closed native theorem and original-source audit.
- [ ] Establish significance beyond a restatement of squarefree pattern density.

## Approach

Fix a list of nonnegative shifts, positive even exponents, and `A=B+2+t`,
where `t∈[0,1]`. At each shifted sample, expand the even source power using
the existing bounded complementary-quotient tuple formula. Reindex each
tuple by its lcm. Its even Möbius product reduces to a fixed coefficient
times a coprime squarefree indicator, using the already verified dilation
identity. Across shifts, the divisibility conditions form one finite CRT
system. Incompatible systems vanish.

On a compatible CRT progression, the remaining squarefree indicators are
evaluated at fixed integer affine forms. Their simultaneous mean is a
classical squarefree-pattern density, not a new theorem to count. The exact
version needed must handle nonprimitive forms, repeated shifts, finite
coprimality exclusions, and local obstructions; inspect existing producers
before proposing a new one.

The common lower band endpoint is `max_i(q_i*N-h_i)`. For fixed shifts,
its difference from `N*max_i(q_i)` stays bounded. Thus the candidate raw
moment profile is affine in A between integer endpoints. Fixed endpoint
errors disappear after division by N. Finite interpolation on squared
source values then extracts the literal joint magnitude frequencies.
This uses the verified finite source alphabet, not moment determinacy.

A complete producer can in principle truncate the excluded prime squares:
finite-prime conditions are periodic, while the tail is controlled by
`sum_{p>K}(N/p^2+1)` up to the square-root range of the affine forms.
This outline still needs exact constants and all degenerate cases checked.

## Concrete coercivity check

On the first octave the magnitude is `mu(n)^2`. Write D for the squarefree
density and C for the consecutive-squarefree density. The zero/nonzero
transition count has candidate mean `2*(D-C)`. Its Euler product would give
`C/D = product_p (p^2-2)/(p^2-1) < 2/3`, using the factor at two and one
further prime. Hence `2*(D-C)>2*D/3`, improving the existing odd-squarefree
zero-edge constant. This comparison is a paper target, not a verified result
or numerical experiment. The full multi-shift law, rather than this generic
inequality alone, must carry any proposed contribution credit.

## Prior-work audit

The broad deep query at `/tmp/bvi100-joint-magnitude-research.json` completed
with `partial=false`; all 20 candidate and 20 source records were reviewed.
Most were unrelated meanings of source, clock, or moment. Useful hits were
`EulerDeletionTruncatedDivisorPairCorrelation` and
`RHTower.Sieve.JointCongruenceEmpty`. Its proposed logarithmic-moment recipe
does not address these literal shifted counts. Two unrelated returned
statements were truncated and were not used as mathematical inputs.

Narrowed searches completed at
`/tmp/bvi100-mirsky-inventory-0.json`,
`/tmp/bvi100-squarefree-pair-density-research.json`,
`/tmp/bvi100-bvi-joint-square-research.json`,
`/tmp/bvi100-joint-local-state-research.json`, and
`/tmp/bvi100-periodic-squarefree-research.json`. All 20 candidate and 20
source statements in each of the last four deep searches were reviewed.
The two newest runs report `partial=false` but semantic coverage unmeasured;
compiler evidence is predominantly source-only. No absence or priority claim
follows from those results.

All 137 names/docstrings from lexical `squarefree affine` were inspected
across offsets 0, 20, ..., 120. Most concern unrelated affine Euler clocks.
`AffinePairSieve.lean` was read in full: it gives finite congruence counts and
prime-pair upper bounds, not simultaneous squarefree asymptotics.
`AffinePairFullDensity.affinePair_rootDensity_full` concerns its finite root
density. `MRInterface.tendsto_squarefreePairCount_of_MR` requires the supplied
`MRBilinear` analytic premise and concerns a different balanced-pair count;
it is not an unconditional fixed-additive-shift producer.

Reusable inspected sources: `ResiduePartitionCount` (full source),
`TruncatedPairCount`, `JointCongruence`, `JointCongruenceClass`,
`SquarefreeTailTruncate`, `AveragedSquarefreeTail`, and the first 156 lines
of `HorizonRadicalStateAndDefectNormalForm`. The truncated pair expansion
does not itself remove the truncation error. Existing source clock support
and full-radical reduction should be reused rather than reimplemented.

Classical primary baseline: Cellarosi--Sinai, *Ergodic properties of
square-free numbers*, JEMS 15 (2013),
https://ems.press/content/serial-article-files/31903, sections 1--3 through
equation (17), explicitly records the classical Mirsky correlation limit
and product `prod_p (1 - #{h_i mod p^2}/p^2)`. Its compact-group realization
and pure-point spectrum also rule out treating a generic local arithmetic
process as a new contribution. Zhang--Liu (2014),
https://doi.org/10.1155/2014/537606, gives stronger quantitative tuple laws;
the HTML omits displayed formulas, so it was not used for exact constants.
The original 1949 AMS PDF returned HTTP 403. No claimed access to that proof.

## Direct local-state route under audit

The quotient-moment route may require unnecessary affine-form machinery.
For a fixed band bound H, write `n=u*v`, with u supported on primes at most
H and v coprime to their primorial. Every complementary quotient q at this
horizon is at most H. Multiplicativity then gives
`mu(n/q)=mu(u/q)*mu(v)` whenever q divides n. Consequently the source
magnitude is a finite small-prime expression times `mu(v)^2`.

If a small-prime exponent in u exceeds every exponent that q can remove
plus one, every term vanishes. Thus the small-prime expression has a finite
prime-power residue modulus. Large-prime squares are the only remaining
nonlocal obstruction. This suggests a direct periodic approximation with
error bounded by a union of shifted large-square divisibility events,
avoiding signed correlations and interpolation of all mixed moments.
The construction below resolves the caps, unit exception, band endpoints,
and tail without the general affine-form machinery.

## Dependency-closed paper construction

The following replaces the proposed affine-form producer. All limits below
follow from finite periodic counts and an elementary tail bound; no Mirsky
theorem or signed correlation is an input. Their classical nature remains
part of the novelty audit. This construction is a paper proof, not yet Lean.

**Band observable.** For j >= 0 and n >= 1, put
`b_j(n) = abs(sum_{1<=q<=j, q|n} mu(n/q))`.
Complementary-divisor reindexing gives `abs(s_N(n))=b_j(n)` whenever
`j*N<n<=(j+1)*N`, `N>=1`, and `n>1`. Indeed, the full divisor sum is zero
for n>1, and `d>N` corresponds exactly to the complementary divisor
`q=n/d<=j` in that band. The exception n=1 contributes at most one sample.
Also `0<=b_j(n)<=j`, and b_j is integer-valued. The band j=0 is identically
zero. All these are finite identities or the triangle inequality.

**Finite periodic approximation.** Fix R>=max(1,j), let
`P_R=primorial(R)`, `Q_R=P_R^2`, and
`mu_R(n)=mu(gcd(n,Q_R))`. Define
`b_{j,R}(n)=abs(sum_{1<=q<=j, q|n} mu_R(n/q))`.
This is periodic with positive period `T_{j,R}=j!*Q_R`: q divides j!,
so translating n by T preserves q-divisibility and translates n/q by
an integer multiple of Q_R; gcd with Q_R is unchanged.

Write n=u*v using the existing smooth/rough factorization at R. The factors
are coprime, u has only primes <=R, and v only primes >R. For q<=j<=R,
q|n iff q|u, and then
`mu(n/q)=mu(u/q)*mu(v)`.
Furthermore `mu_R(n/q)=mu(u/q)`: gcd with Q_R preserves every small prime
factor and detects exactly whether any exponent is at least two; the two
integers therefore have equal Möbius values. Hence the exact identity is
`b_j(n)=abs(mu(v))*b_{j,R}(n)`.
In particular they agree unless some prime p>R has p^2|n. This handles
arbitrarily large small-prime exponents without a separate valuation cap.

**Anchored tail bound.** For X>=1 and shift h>=0, the number of n in [1,X]
for which some p>R satisfies p^2|(n+h) is at most `(X+h)/R`. To prove this,
inject n into [1,X+h], enlarge primes to integers d in [R+1,X+h], apply
the union bound, then use
`#{1<=m<=X+h: d^2|m}=floor((X+h)/d^2)` and
`sum_{d>R} 1/d^2<=1/R` (the inspected finite tail lemma suffices).
There is no per-divisor +1 and no square-root remainder.

**Every finite pattern has a mean.** Fix m shifts h_i, H=max_i h_i (zero
for an empty list), and target nonnegative magnitudes a_i. Let E_X be the
frequency of `b_j(n+h_i)=a_i` for all i. Let c_R be the frequency of the
same pattern for b_{j,R} in one period T_{j,R}. A mismatch requires a
large square in at least one shifted input. Periodic residue counting gives

`abs(E_X-c_R) <= m*(1+H/X)/R + T_{j,R}/X`.

For R,S>=max(1,j), let X tend to infinity in the triangle inequality to get
`abs(c_R-c_S)<=m/R+m/S`. Thus c_R is Cauchy, defines a real number c_j(h,a),
and `abs(c_R-c_j(h,a))<=m/R`. The displayed bound then proves
`E_X -> c_j(h,a)` by first choosing R and then X. This is an explicit
convergent finite-residue formula, with a certified error m/R; an Euler
product is not required to construct the full pattern law. Nonnegativity,
normalization, repeated-shift consistency, and finite support follow from
the finite distributions and finite sums. This includes impossible patterns
without an admissibility assumption.

**Native real-horizon law.** Fix K>=2, t in [0,1], A=K+t, and the same
shifts. Apart from at most `1+(K+1)*sum_i h_i` positions, every n<=floor(A*N)
and all n+h_i lie in the same integer band. Outside these positions the
literal source-magnitude vector equals `(b_j(n+h_i))_i` on band j. Bounded
boundary counts disappear after division by N. Prefix convergence for each
fixed b_j-pattern, followed by subtraction of the two band endpoints, gives
the raw limiting mass

`sum_{j=0}^{K-1} c_j(h,a) + t*c_K(h,a)`.

Dividing by A gives the probability law. Consequently raw masses interpolate
affinely between adjacent integer horizons. No moment-determinacy argument
is needed. The proof discards boundedly many boundary positions and does NOT
identify positive-density support with cofinal attainability.

**Native gradient consumer.** For shifts (0,1), the finite law gives the
limit of the mean squared magnitude difference. The pointwise reverse
triangle inequality makes that limit a lower bound on the liminf of the
literal signed source-gradient energy. Already band j=1 has b_1=mu^2,
so its mean squared difference is `2*(D-C)`, with D the squarefree density
and C the consecutive-squarefree density. The finite-prime CRT products
give `C/D=prod_p (p^2-2)/(p^2-1)`. The factors at 2 and 3 alone give
`C/D<=7/12`, hence `2*(D-C)>=5*D/6>2*D/3`. This last product identification
is a classical auxiliary proof obligation for Lean, not an assumed API or
new contribution by itself. The complete multi-band law has no dependence
on this optional closed-form comparison.

## Formalization plan

1. Reuse smooth/rough and Möbius APIs to prove the exact periodic magnitude
   factorization and its large-square exceptional set.
2. Reuse anchored counts, inverse-square tails and residue partition counts
   to prove finite-pattern approximation and its limit.
3. Transport to literal cofinal source bands, then real horizons and the
   magnitude-gradient lower bound. Audit every public declaration, wiring,
   indexing, lint and significance. No supporting lemma earns separate credit.

The additional THIM and whole-corpus factorization queries completed at
`/tmp/bvi100-magnitude-rough-thim-research.json` and
`/tmp/bvi100-truncated-mobius-factor-research.json`. All 20 candidate records
and 20 source records in each were reviewed. One unrelated source signature
in the latter was truncated after `let t` and was not used. Both report
`partial=false`, unmeasured semantic coverage and an older coverage snapshot.
`RHTower.Sieve.SmoothRough` is an existing producer, read in full; its exact
factorization and prime-support lemmas replace any new smooth/rough machinery.
`AveragedSquarefreeTailSharp` and `ShiftedCongruenceCount` were read in full.

The periodic-pattern query `/tmp/bvi100-periodic-pattern-count-research.json`
also completed (`partial=false`, semantic coverage unmeasured, older coverage
snapshot); all 20 candidate and 20 source statements were reviewed. Its useful
Mathlib hit `Nat.filter_Ico_card_eq_of_periodic` and the companion
`Function.Periodic.map_mod_nat` were inspected in installed source. The existing
`ResiduePartitionCount` supplies the incomplete-period count estimates.

Further primary-source checks: Coppola--Laporta, *Sieve functions in arithmetic
bands* (2016), https://hrj.episciences.org/2635/pdf, introduction, Theorem 1.1,
Corollary 1.7 and its proof, concern shift-averaged correlations; the Q^2 error
in Corollary 1.7 does not produce this fixed-shift proportional-cutoff law.
Green--Tao, *Linear equations in primes*, Appendix D, Theorem D.3,
https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n3-p08-p.pdf,
requires a smooth divisor cutoff at a sufficiently small power of the ambient
scale. That theorem does not cover the present sharp proportional cutoff.
These regime distinctions do not establish novelty. The requested Murty
Ramanujan-expansions PDF redirected to a personal homepage and was not read.

The finite mismatch estimate also bounds total variation under the natural
coupling: the two vector samples are equal off the exceptional set. Passing
to limits should yield total-variation error at most m/R for the complete
finite-band law, not merely a separate error bound for each pattern. This is
part of the same candidate, with no additional contribution credit.

## No-go closure

If the full joint law is already known or its native application is routine,
record that finding without contribution credit. If an analytic premise
remains, identify it exactly and seek a nontrivial unconditional survivor;
do not present a conditional theorem as completion.

## Finite-observable transfer and gradient consumer: paper proof

For A=K+t with K>=1 and t in [0,1], let H=sum_i h_i. If N>=max(1,H),
every sampled n+h_i is at most (K+2)N. The proved source-band identity and
integer-valued band bound therefore put every magnitude in {0,...,K+1}.
Consequently any function Phi on the magnitude vector, with no continuity
or global boundedness assumption, is exactly a finite linear combination of
pattern indicators on this alphabet. Sum first over patterns, then over n,
and apply the joint-frequency theorem to each term. The raw mean divided
by N tends to `sum_a Phi(a) * cofinalMobiusJointMagnitudeMass(K,t,h,a)`.
The extra endpoint alphabet value K+1 has limiting mass zero, although it
can occur at finitely many moving-boundary samples.

For h=(0,1) and Phi(x)=(x_1-x_0)^2 this gives the exact limiting squared
magnitude-gradient mean. The elementary inequality
`(|v|-|u|)^2 <= (v-u)^2` follows from `u*v <= |u|*|v|` and
`|u|^2=u^2`, `|v|^2=v^2`. Sum and divide by positive N. Hence for every
epsilon>0, the literal signed-source gradient mean is eventually at least
the explicit magnitude-gradient mass minus epsilon. No unproved signed
Möbius correlation enters this comparison. This paper argument is closed
relative to the proved joint law and is now formalized in
`CofinalMobiusMagnitudeObservablesAndGradient.lean`. The
sharper explicit 5D/6 comparison still needs the separate squarefree-pair
product or progression argument described above.

## A smaller explicit coercivity target

The full Euler formula is unnecessary for a strict improvement over the existing
odd-squarefree constant. Let C be the already-established density of consecutive
squarefree pairs, and D=6/pi^2. Every such pair avoids the two forbidden classes
0,-1 modulo four and modulo nine. CRT therefore bounds C by
`(1-2/4)*(1-2/9)=7/18`. Its squared magnitude-difference mean is
`2*(D-C) >= 2*D-7/9`. This exceeds `2*D/3` because `D>7/12`, which follows
from the standard bound pi<22/7. This is an analytic argument, not a finite
enumeration certificate. Formalization should reuse the existing congruence
count estimates and prove the two-prime inclusion-exclusion identity.

At horizon 2N, the literal source's first trans-horizon band is -mu; the
remaining initial band has only a bounded exceptional contribution. Thus the
new magnitude-gradient mean should imply the eventual signed-gradient floor
`(2*D-7/9-epsilon)*N`, and nonnegativity extends it to all longer horizons.
At each fixed finite horizon ratio, the existing exact renormalized-defect
identity then gives the corresponding negative linear defect bound after its
endpoint error vanishes. This target
is weaker than 5D/6 but already strictly improves the previous arithmetic
edge bound. Its Lean proof and native significance assessment remain open;
the generic CRT sieve estimate itself earns no novelty credit.

The finite congruence estimate also suggests a direct native inequality before
passing to density. Write W_N for the squarefree count in (N,2N], and E_N(M)
for the literal signed-source gradient energy through M. For N>=1 and M>=2N,
the target is `E_N(M) >= 2*W_N - (7/9)*N - 18`. Indeed, restrict to edges
n=N+1,...,2N-1, where both source endpoints equal -mu. Reverse triangle
inequality bounds their energy below by the sum of the two squarefree endpoint
indicators minus twice the adjacent-pair indicator. The endpoint sum differs
from 2*W_N by at most two. The proved finite pair bound is
`(7/18)*(N-1)+8 <= (7/18)*N+8`, producing the total constant eighteen.
This argument handles N=1 via the empty edge interval. The resulting density
floor uses the existing one-point dyadic squarefree mean, without requiring
an Euler-product identification of C. The native finite inequality remains
to be formalized and checked for duplicate corpus work.

## Proposed sharpening: exact Euler formula and positive support

This is a new conjectural sharpening exposed by the proved rough-factor identity,
not an accepted contribution or completed Lean theorem. Its paper and novelty
audits remain open; the ongoing source-band transport remains the immediate task.

Fix J=max(1,j), T=j! primorial(J)^2, and a residue r modulo T. Write
u_i=b_{j,J}(r+h_i). Compatibility requires each target a_i to be either 0 or
u_i. If compatible, let S={i:a_i=u_i and u_i≠0} and
Z={i:a_i=0 and u_i≠0}. The exact rough factor suggests the residue contribution

`(1/T) * sum_{U subset Z} (-1)^|U| * product_{p>J} (1-nu_{S union U}(p)/p^2)`,

where nu_I(p) counts distinct shift residues h_i modulo p^2 for i in I.
Incompatible residues contribute zero. Summing over r should identify the
already-defined density. The ingredients are finite-prime CRT, inclusion-exclusion,
the proved tail approximation, and the classical Mirsky products. Each prime
dividing T is at most J, so the remaining prime-square constraints are coprime
to the fixed residue modulus. This is not a new generic squarefree-correlation
principle; native novelty and significance require separate evaluation.

Proposed positive-support criterion: some compatible r has no equal-shift pair
between S and Z, and nu_S(p)<p^2 for every p>J. Only p^2≤m can obstruct the latter.
Necessity is immediate. For sufficiency, assign a different sufficiently large
square prime to each distinct shift in Z, avoiding all differences to S; CRT
forces these nonsquarefree coordinates while keeping S squarefree at those
primes. Positivity of the remaining admissible Mirsky product is the outstanding
dependency to audit explicitly. This concerns positive density, not cofinal
attainability at band boundaries.

Corpus query `/tmp/bvi100-joint-magnitude-euler-support-research.json` completed
with `partial=false`; all 20 candidate and 20 source-argument statements were
inspected. It recovered the new rough-factor identity, existing finite
quadratic-root Euler products, and one-point squarefree densities. Semantic
coverage remains unmeasured and compiler records predominantly source-only;
these retrievals neither establish absence nor establish novelty.

Further audit: Kułaga-Przymus--Lemańczyk--Weiss,
[On invariant measures for B-free systems](https://arxiv.org/pdf/1406.3745),
introduction and Section 1.1, state the pairwise-coprime summable setting,
identify admissible configurations, and give the Mirsky cylinder product.
Section 2.3 explicitly uses full topological support of the Mirsky measure.
Thus the underlying admissibility/positive-support principle is classical;
the proposed native finite-amplitude classification cannot be counted as a
new generic support theorem. Its precise arithmetic transport still needs
its own proof and significance audit.

Two further corpus hits were inspected at the relevant source passages:
`PrimeSquareMobiusComplementaryRecord.lean` (introduction and lines 580--645)
already supplies the local three-valued Möbius factor and squarefree occupation
on ZMod(p^2). `EulerSquarefreeDyadicStateFactorization.lean` (introduction
through its squarefree Möbius lemma) gives the Euler-weight factorization
under n=m^2 d. Neither inspected statement is being presented as new work.

Further classical audit: Reuss, [Pairs of k-free Numbers, consecutive square-full
Numbers](https://arxiv.org/pdf/1212.3150), Theorems 2--3 and their introductory
discussion, supplies quantitative pair and affine-tuple laws. It also explicitly
notes that Heath-Brown's squarefree-pair method is uniform for shifts of size
O(x). Thus a moving-shift squarefree asymptotic, or its direct native transport,
cannot be treated as a newly discovered generic principle. This is a novelty
constraint; no claim is made that the stronger analytic estimates are already
formalized. The attempted direct AMS access to Mirsky's original paper returned
403 and was not used as evidence of its contents.

Exploratory corpus queries `moving shifts cutoff proportional horizon joint
magnitude profinite residue subsequence limit` and `squarefree correlation
uniform shift` each returned 20 candidate and 20 source statements, all reviewed.
Both report `partial=false` with semantic coverage unmeasured. The lexical
`profinite limit` inventory returned two unrelated declarations, both reviewed.
No new implementation is justified by those sparse profinite retrievals. The
additional `squarefree pair count upper bound local prime squares` query was
also reviewed across all 20 candidate and 20 source statements; its existing
congruence and squarefree-tail mechanisms remain the relevant building blocks.
Records are `/tmp/bvi100-{moving-shift-hull,squarefree-uniform-shift,
squarefree-pair-local-upper}-research.json` and
`/tmp/bvi100-profinite-limit-inventory.json`.

## Log

- 2026-10-19 — Created after completing original-source audits of the one-point real-horizon law. No new Lean code yet. Accepted count remains 0/100.
- 2026-10-19 — Completed the direct periodic-approximation paper proof and prior-work checks above. `MobiusMagnitudePeriodicApproximation.lean` passes its original-source check without diagnostics; all seven public declarations pass the axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`. The exact rough factor, explicit period, literal source-band identity and finite joint disagreement bound are wired into the BVI umbrella. All eight index-readback names/docstrings were inspected, including all seven public declarations. Logs: `/tmp/bvi100-magnitude-periodic-{canonical,axioms,index-readback,formal-lint}.*`. Plain lint reports nine unreachable concurrent `BiScaleUncertainty.SieveParity*` leaves, with no owned error. Pattern-density limits and native real-horizon transport remain unfinished. Accepted count remains 0/100.
- 2026-10-19 — Additional actual corpus queries: `periodic approximation pattern density Cauchy limit` and `Besicovitch periodic squarefree pattern natural density`, saved as `/tmp/bvi100-{pattern-density-limit,besicovitch-pattern}-research.json`. All 20 candidate and 20 source-argument statements from each result were reviewed. Both completed with `partial=false`, unmeasured semantic coverage and a background index refresh; most compiler records are source-only. The first query found the reusable public `SelbergCompactTestApproximation.exists_limit_of_eventual_approximation`; its complete 84-line source was inspected. This generic convergence-transfer theorem can replace a bespoke Cauchy construction. The second query recovered known one-point squarefree densities and the already-rejected conditional MR interface. These searches establish neither absence nor priority.
- 2026-10-19 — `MobiusMagnitudePatternDensity.lean` now passes both its scratch and original-source checks without diagnostics. It reuses the discovered generic convergence-transfer theorem and proves unconditional pattern frequencies, the explicit m/R finite-residue error, convergence of local probabilities, finite integer support, nonnegativity, upper bound one and normalization. All 13 public names/docstrings were read back from the actual lexical corpus index. The leaf is wired. Plain formal lint now passes (381 size warnings); the earlier concurrent wiring gaps have cleared. Public axiom audit remains running at this checkpoint. The native source-band transport is a separate unverified `/tmp/bvi100-magnitude-band-transport.lean` draft. Accepted count remains 0/100.
- 2026-10-19 — Supporting searches `/tmp/bvi100-{magnitude-finite-alphabet,pattern-band-transport,pattern-prefix-scaling}-research.json` were inspected across all 20 candidate and 20 source-argument records each. Some unrelated long statements were truncated by the index; none was relied on. The described-goal deep search `/tmp/bvi100-pattern-prefix-deep-research.json` returned usable retrievals but `partial=true`: `filter_and_judge` reported incomplete/malformed model JSON. All returned candidate/source statements and the proposed ingredient set were inspected; its Cesàro/sphere-packing/continuous-average suggestions do not establish the needed arithmetic-prefix scaling. Installed Mathlib source supplies `tendsto_nat_floor_mul_atTop`, `tendsto_nat_floor_mul_div_atTop`, and `Finset.sum_Ioc_consecutive`. No search-coverage or novelty claim follows.
- 2026-10-19 — Pattern-density axiom audit completed successfully: all 13 public declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. Logs `/tmp/bvi100-magnitude-pattern-density-{canonical,axioms,lint}.*`; index readback `/tmp/bvi100-magnitude-pattern-density-index-readback.json`. The source-band transport draft is now undergoing its first Lean check. Accepted count remains 0/100.
- 2026-10-19 — `CofinalMobiusJointMagnitudeLaw.lean` (364 lines) completes native real-horizon transport. Its original-source check has no diagnostics; all 11 public declarations pass the standard-three-axiom audit. It proves the bounded band-boundary error, each fractional-band limit, the affine raw mass, literal normalized joint-frequency convergence for every K>=1 and t in [0,1], total mass one, nonnegativity and finite support. It is wired. The exact `moebius` index query returned six public names; broadening to `magnitude` recovers the complete public surface. Latest plain lint reports only the concurrent THIM `FermiDyadicAntichainCoordinates` wiring gap. Logs `/tmp/bvi100-joint-magnitude-law-{canonical,axioms,lint}.*`; index readback files `/tmp/bvi100-joint-magnitude-law-index-readback*.json`. Completed transport/audit scratch files were removed. The finite-observable and gradient consumer is now the unverified `/tmp/bvi100-joint-magnitude-observables.lean` draft. Accepted count remains 0/100.
- 2026-10-19 — Gradient-consumer audit: `/tmp/bvi100-squarefree-progression-gradient-research.json` returned 20 candidate and 20 source statements, all inspected (`partial=false`, unmeasured semantic coverage, background refresh). Hits include existing coprime-squarefree means, periodic coprime masks, and conditional MR pair-density routes; none supplies the required single-residue squarefree mean as stated. The documented lexical query `squarefree progression` returned zero; this is not an absence claim. No conditional MR theorem is being used.
- 2026-10-19 — Reviewed all 252 unique names/docstrings returned by the actual lexical `squarefree residue` query, across offsets 0 through 240. Most hits use analytic residues or quadratic residue gauges; the relevant coprime-squarefree means do not state a single progression mean. The additional hybrid query `squarefree arithmetic progression mean residue coprime density` returned 20 candidate and 20 source statements, all reviewed. It completed with `partial=false`, semantic coverage unmeasured and background refresh running; no absence claim follows. Records: `/tmp/bvi100-squarefree-residue-lexical-*.json` and `/tmp/bvi100-squarefree-residue-mean-research.json`.
- 2026-10-19 — Observable/gradient scratch check passed without diagnostics. The canonical leaf `CofinalMobiusMagnitudeObservablesAndGradient.lean` is written but its original-source audit encountered missing transitive dependency objects. A targeted `lake --old build` of its imported joint-law leaf is restoring the dependency closure before the audit is repeated. No canonical pass is claimed yet.
- 2026-10-19 — `CofinalMobiusMagnitudeObservablesAndGradient.lean` (141 lines) passes the original-source check without diagnostics. All five public declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; the leaf is wired, and all seven index names/docstrings (five public, two private) were reviewed. It transfers the joint law to every fixed real observable, proves the squared magnitude-gradient limit, and supplies an eventual lower bound for literal signed-source gradient energy. During concurrent dependency rebuilds, source checks used `lake env lean --setup ...` with hardlinked compiled inputs; the source and compiler options were unchanged. The previously removed periodic-approximation object was restored by another clean original-source check. Latest plain lint reports only three other-owner wiring gaps: `BiScaleUncertainty.SieveLinearVisibility`, `BiScaleUncertainty.SievePrimePowerVisibility`, and `TransHorizonIncidenceMechanics.FermiBooleanPrimeCube` (381 size warnings). Logs: `/tmp/bvi100-joint-magnitude-observables-{canonical,axioms,lint}.*`; index readback: `/tmp/bvi100-joint-magnitude-observables-index-readback.json`. The two-prime coercivity sharpening is a separate unverified `/tmp/bvi100-two-prime-pair-bound.lean` draft. Accepted count remains 0/100.
- 2026-10-19 — The two-prime interval estimate now passes its scratch check without diagnostics: every interval of length L contains at most `7L/18+8` consecutive squarefree pairs. This uses existing congruence-count error bounds and a symbolic indicator expansion, with no residue-table enumeration. The same scratch file is now extended by native first-band count and density capstones, which are undergoing verification. Completed observable/audit scratch Lean files were removed.
