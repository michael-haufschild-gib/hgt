# BVI: complete cofinal source-value law

- **ID:** bvi-cofinal-full-source-law-2026-10-19
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean); significance candidate, uncounted
- **Source:** Existing quadratic quotient profile, odd-moment cancellation, and positive/negative frequency results; their recorded full-distribution gap.
- **Statement:** For every fixed real horizon ratio at least two, every individual value of the growing-cutoff Möbius divisor source has a limiting frequency. The complete finite law is a sample-size weighted mixture of adjacent integer laws, with exact positive support.

## Native question

Write `s_N(k)=sieveSeq N moebiusReal k`. Existing results give the exact asymptotic quadratic energy, cancellation of every fixed odd moment, and lower bounds for the total frequency of either sign. They do not supply the individual densities of `s_N(k)=j`. The proposed result determines all amplitude classes on the actual horizon `(B+1)N`, with fixed `B≥1`, rather than on a full common period. It is one conceptual candidate, not one contribution per moment or value.

The prior cofinal programme was paused historically. The current explicit 100-contribution goal authorizes this new candidate; no old pause is treated as a current prohibition.

## Prior work and gates

- [x] Documented research search started before new Lean code.
- [x] All 18 lexical `cofinal moment` hits inspected; relevant existing interfaces identified.
- [x] Inspect the first deep-search candidate/source inventory and fresh current tree; further support-classification search remains pending.
- [ ] Audit external prior work on truncated Möbius divisor sums and value distributions.
- [ ] Confirm that the full law adds substantive native knowledge, rather than routine repackaging of moment convergence.
- [ ] Complete the dependency-closed paper proof and adversarial edge-case audit.
- [ ] Formalize the exact surviving statement, with data-only public capstones, original-source Lean checks, standard-axiom audit, wiring, index and lint.

Formalization order: first prove the exact finite source alphabet and its cofinal
attainment, reusing THIM's radical-state reduction and band complement formula.
The leaf is `CofinalMobiusSourceAlphabet.lean`; it is a dependency of this single
candidate, not a separately counted contribution. Then prove literal level counts
converge to the positive arithmetic law and establish the stronger horizon-threshold
statement. The 252-line alphabet leaf passes the original-source `lake env lean`
audit and the scratch axiom audit: all three public declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. Selected dependencies passed
`lake --old build`. The leaf is wired into the BVI umbrella, and documented
research readback retrieved all 12 declarations. The latest plain lint snapshot
failed only on two concurrent THIM leaves unreachable from their umbrella:
`FermiHomogeneousEnergyAndPronicComparison` and `FermiPrimeExponentGramBounds`.
No full-law or contribution credit follows from this supporting leaf.

Existing sources under `formal/GaloisForLFunctions/BezoutValuationIncidence/`:

- `CofinalMobiusQuadraticQuotientProfile.lean`: exact quotient-band expansion and quadratic Euler-product limit.
- `CofinalMobiusOddMomentsAndQuotientProducts.lean`: arbitrary finite tuple lcm reindexing, exact odd moment expansion, all fixed odd moment limits.
- `CoprimeSquarefreeDensityAndMobiusDilationMeans.lean`: coprime squarefree density producer.
- `CoprimeMobiusCancellationAndOddDilationMeans.lean`: coprime Möbius cancellation and odd products.
- `CofinalMobiusPositiveNegativeSourceFrequency.lean`: positive frequency of both signs; no complete individual-value law.

All these are prior work and earn no credit in the current programme.

## Proposed arithmetic formula

Let `D(a)=(6/π²)∏_{p|a}p/(p+1)`. For a positive even integer m, sum over all tuples `q=(q₁,…,q_m)` with `1≤q_i≤B`. Put

`L=lcm(q₁,…,q_m)`, `Q=max(q₁,…,q_m)`, `a_i=L/q_i`,

`E_m(B)=Σ_q ((B+1−Q)/L) (∏_i μ(a_i)) D(∏_i a_i)`.

Set `E_0(B)=B+1`, and `E_m(B)=0` for positive odd m. The proposed full moment law is

`(1/N) Σ_{1≤k≤(B+1)N} s_N(k)^m → E_m(B)`.

Repeated multipliers and nonsquarefree multipliers must be retained. The formula must not assume pairwise coprimality of the `a_i`; a nonsquarefree multiplier makes its Möbius factor zero.

For each integer `j∈[-B,B]`, let `P_(B,j)(X)` be the exact Lagrange cardinal polynomial on the integer nodes `-B,…,B`. Define

`p_B(j)=(1/(B+1)) Σ_{m=0}^{2B} coeff_m(P_(B,j)) E_m(B)`.

The target is convergence of the literal count divided by `(B+1)N` to `p_B(j)`, together with `p_B(j)≥0`, total mass one, symmetry `p_B(j)=p_B(-j)`, and zero mass outside these integer nodes. In Lean, encode `B≥1` through a natural parameter plus one instead of adding it as a public premise. The first sample `k=1` is included and contributes only a vanishing boundary correction.

## Paper mechanism under audit

1. For arbitrary finite multipliers, multiplicativity with the coprimality indicator gives
   `∏_i μ(a_i n)=(∏_i μ(a_i))*μ(n)^m*1_(coprime(n,∏_i a_i))`.
   When m is positive even, `μ(n)^m=μ(n)^2`. The existing coprime-squarefree density then gives the explicit product mean. Odd m uses the existing cancellation theorem.
2. Reuse the exact finite tuple common-multiple reindexing. Each quotient tuple contributes the difference of product prefixes at `floor((B+1)N/L)` and `floor(QN/L)`. This produces the factor `(B+1−Q)/L`; no full-period averaging or shifted-Möbius correlation estimate is introduced.
3. Expand the literal positive even moment by finite distributivity. The odd expansion already exists. Fixed B and m make every resulting sum finite, so its limit passes through term by term.
4. Existing linear-window bounds place the integer-valued source in `[-B,B]`. Thus each literal value indicator equals its cardinal polynomial in the source. Taking the already established moments yields each frequency limit, with no moment-determinacy or compactness hypothesis.
5. Nonnegativity and total mass follow from actual counts. The cardinal polynomial identity `P_(B,-j)(X)=P_(B,j)(-X)` and vanishing odd moments give exact symmetry.

Merely formalizing polynomial interpolation would not by itself meet the significance criterion. The stronger arithmetic formulation below is now the main candidate; the moment formula is a consistency check and alternative route to existence.

## Stronger candidate: positive local-state law and exact support

This is a paper derivation awaiting source and novelty audit, not a verified Lean result.

Put `A=B+1`, with `B≥1`. For integers `w,l≥1` satisfying `w*l≤B`, let

`P(w,l)={primes p≤l} ∪ {prime divisors of w}`.

For each subset `S⊆P(w,l)` containing every prime divisor of w, put `d_S=∏_(p∈S)p` and

`H_l(S)=Σ_(d≤l, d|d_S) μ(d)`.

Every factor below is positive:

`W_B(w,l,S) = D(∏_(p∈P(w,l))p)/(2*A*d_S) * (min(l+1,A/w)−l)`.

For each nonzero integer j the proposed complete formula is

`p_B(j)=Σ_(w*l≤B) Σ_(S admissible, |H_l(S)|=|j|) W_B(w,l,S)`.

Zero receives the remaining mass. This formula makes symmetry and positivity of every included state explicit; all nonzero level densities are nonnegative rational multiples of `6/π²`.

**Exact state decomposition.** For a positive sample n, write `R=rad(n)` and `w=n/R`. Squarefree support gives `s_N(n)=s_N(R)`. If R≤N and n>1, the response is zero. Otherwise set `l=floor((R−1)/N)`. Then `l*N<R≤(l+1)*N` and `w*l≤B`. Complementing divisors inside squarefree R gives

`s_N(n)=−μ(R) Σ_(d≤l,d|R) μ(d)`.

The sum is precisely `H_l(S)`, where S records which primes of P(w,l) divide R. Since `rad(w)|R`, S contains every prime divisor of w. Writing `R=d_S*m` leaves m squarefree and coprime to the squarefree product of P(w,l), and fixes one Möbius sign of m whenever `j≠0` and `|H_l(S)|=|j|`.

Conversely every such m gives exactly that state and source value, with

`l*N/d_S < m ≤ min((l+1)*N/d_S, A*N/(w*d_S))`.

The indicators of the two signs of a coprime Möbius value are `(μ²+μ)/2` and `(μ²−μ)/2`. The existing squarefree density and coprime cancellation therefore give each sign density `D(∏P)/2`. The interval length and normalization by A*N yield W. All states are finite and disjoint. The exceptional sample n=1 has zero limiting mass. This supplies a direct arithmetic proof, without a new moment-determinacy argument.

**Complete support and optimal envelope.** Define

`E_B=max_(1≤l≤B, S⊆{primes≤l}) |H_l(S)|`.

Then E_B≥1. Every literal source value on `1≤n≤(B+1)N` has magnitude at most E_B for N≥1. For the reverse inclusion, take w=1: every displayed l,S state has strictly positive weight. Consequently a nonzero integer j has positive limiting frequency exactly when `|j|=|H_l(S)|` for some such l,S. In particular both signs of E_B occur with positive limiting frequency. Nonsquarefree samples create no additional amplitude classes.

This would identify the optimal universal envelope at every integer horizon ratio, while the existing corpus has the coarse bound B and special sharp low-band boundaries. It also shows why an amplitude-bound theorem and an asymptotic frequency theorem belong to one candidate: the same finite arithmetic states give both.

No growth asymptotic for E_B is asserted. Choosing S to consist of primes in `(sqrt(B),B]` suggests the elementary lower bound `E_B≥π(B)−π(sqrt(B))−1`; this is an additional conjecture until its exact finite statement and prior work are checked.

## Search and external baseline checkpoint

The first deep request completed with `partial=false`, no errors, and 74,301 inventoried files. All 20 candidate and 20 source statements were inspected. Its suggested prefix/logarithm ingredient chain does not prove a distribution law. A separate whole-corpus even-product request returned the useful existing general identity `moebius_dilation_product_eq_coprime_power`; its proposed odd-mean-zero recipe is inapplicable to even powers. Both candidate and source inventories were reviewed.

The precise source audit found a needed distinction: `tendsto_coprimeSquarefreeMean_of_squarefree` presently requires a squarefree modulus. The local-state formulation uses a product of distinct primes and satisfies that condition directly. The earlier moment-product formulation must first reduce repeated prime factors; it cannot silently invoke the squarefree theorem on an arbitrary multiplier product.

[Granville–Koukoulopoulos–Maynard, *Sieve weights and their smoothings*](https://smf.emath.fr/system/files/filepdf/ens_ann-sc_54_1089-1177.pdf) studies the same general truncated divisor-sum observables and higher moments. Its moment expansion and asymptotic regimes must be compared before claiming novelty; merely introducing higher Möbius moments is not new. The author manuscript's opening moment expansion has error of size `R^k`, and its displayed interval theorem assumes `R^(2k)≤x`; these do not by themselves settle the present fixed `x/R` regime. The published version is being checked, and no worldwide absence or priority claim follows.

The published Theorem 1.3, Remark 1.2, Theorems 1.4 and 1.6, and their regime discussion have now been read. The moment asymptotics use the long-average regime, while several upper bounds hold for every `x≥R`. Remark 1.2 explicitly warns that their moment growth does not immediately identify the value distribution. Those statements do not supply the finite law above at fixed `x/R`; this is a comparison of inspected statements, not a priority claim about all literature.

The THIM source audit found existing `sieveSeq_horizonRadicalState`, the exact radical-state image, uniform complementary-band normal forms, sharp unit envelopes through `5N`, and a bound of two before `6(N+1)`. These are essential prior ingredients. Their finite state depends on N; the proposed distribution and amplitude alphabet depend only on the fixed horizon ratio. No credit is assigned to radical reduction itself.

[Helfgott–Thompson, Proposition 3.2](https://link.springer.com/article/10.1007/s40993-022-00408-8) uses exactly the same truncated Möbius divisor observable and gives its prime-deletion recursion with an average operation bound. The observable and recursion are established mathematics; the inspected proposition is not a source-value distribution or fixed-ratio support classification.

The additional BVI deep request completed with all 74,304 files inventoried and `partial=false`; all 20 candidate and 20 source entries were reviewed. Its prime-deletion ingredient recipe does not prove a source law. The whole-corpus request also completed (`74,307` files, `partial=false`), but its 20+20 entries were largely unrelated uses of prime density and linear horizons. Its proposed route through `linHorizon_level` is inapplicable. Semantic coverage was unmeasured and most compiler metadata pending. Neither request supports an absence claim. All 46 hits from the broader cofinal source/frequency lexical query were paged and inspected, including the existing positive/negative lower bounds.

## Common-modulus formulation and horizon-threshold rigidity

Use one modulus `Q=primorial(B)` and let d range over its positive divisors. Put

`H_l(d)=sieveSeq l moebiusReal d`.

Replacing the earlier varying prime set by all primes at most B yields the equivalent formula

`p_B(j)=D(Q)/(2*(B+1)) * Σ_(w*l≤B) Σ_(d|Q, rad(w)|d, |H_l(d)|=|j|)
  (min(l+1,(B+1)/w)−l)/d`, for `j≠0`.

To justify this version directly, write `R=d*m`, where d contains precisely the prime factors of R at most B. Then m is squarefree and coprime to Q, and `rad(w)|d` is exactly the remaining condition for `rad(w*d*m)=d*m`. Every source class is a finite union of these disjoint states. Summing over the extra, irrelevant small primes gives the earlier varying-modulus expression by the Euler-factor identity `(p/(p+1))*(1+1/p)=1`.

For N≥1 the boundary sample n=1 has value one, and all `2≤n≤N` have value zero. Thus the proposed zero-level limit is at least `1/(B+1)`. A nonzero state fixes exactly one sign of μ(m), including when `μ(d)*H_l(d)` is negative. The upper interval endpoint is closed and the lower endpoint open; using `l=(R−1)/N` prevents duplication at `R=(l+1)N`. Squarefree R and the forced prime support of w make the converse state parametrization exact. These checks remove the apparent extra coprimality and endpoint obligations; no shifted Möbius correlation is used.

The same paper argument extends to real A>1 by retaining precisely states with `w*l<A`. On each bounded A interval, choose one fixed primorial containing every needed prime. For every nonzero j, **A times its limiting frequency is continuous and piecewise affine in A, with possible breakpoints only at positive integers**: each state contributes a positive constant times

`max(0,min(l+1,A/w)−l)`.

The zero-level function follows by subtracting the finitely many nonzero classes from A. Furthermore, every attainable nonzero amplitude |j| first acquires positive limiting frequency immediately after the least integer l for which some divisor d of `primorial(l)` satisfies `|H_l(d)|=|j|`. If no such state exists, the amplitude never occurs. Nonsquarefree clocks w cannot create an earlier birth. This generalizes the already known sharp ratio five into an exact integer-threshold classification; it does not claim a closed expression for those integers or that every integer amplitude is attained. This strengthening remains a paper candidate until its exact statement is formalized and audited.

Equivalently, for an integer K≥2 and K≤A≤K+1, the proposed entire law satisfies

`A*p_A(j) = (K+1−A)*K*p_K(j) + (A−K)*(K+1)*p_(K+1)(j)`.

After division by A this is a convex mixture of the two adjacent integer-ratio
laws. A moment-based proof can use one common alphabet at ratio K+1: the bounded
quotient tuple formula is affine in A throughout that interval, including its
zero boundary weights. Cardinal interpolation then transports every individual
value count. This transport law is now formalized as part of the same candidate.

For the direct Lean transport route, encode `A=B+2+t` with
`t : Set.Icc (0:ℝ) 1`. Keep quotient tuples through B+2 throughout this
interval. Existing tuple reindexing then gives affine coefficients
`(A−max(q))/lcm(q)`; tuples touching B+2 have zero lower-endpoint weight.
The needed floor identity `Nat.floor_div_natCast` is present in this toolchain
(`Mathlib/Algebra/Order/Floor/Semifield.lean:36`) and passes the local API
scratch check. Once every moment is the affine blend of endpoint moments,
use the upper endpoint's cardinal polynomial on the common finite alphabet.
Its lower endpoint average is identified with the lower literal count by
limit uniqueness. This avoids any moment-determinacy or regularity premise.
The zeroth moment also supplies the floor-denominator normalization. The owned
`CofinalMobiusRealHorizonMoments.lean` now proves the full moment-transport
statement for `A=B+2+t`. Original-source Lean and the public axiom audit both
pass; only `propext`, `Classical.choice`, and `Quot.sound` occur. The leaf is
wired and its public theorem was retrieved by the corpus research tool.
Plain lint still fails only on the two concurrent THIM wiring gaps. Logs:
`/tmp/bvi100-real-moments-canonical.log`,
`/tmp/bvi100-real-moments-axioms.log`,
`/tmp/bvi100-real-moments-index-readback.json`, and
`/tmp/bvi100-real-moments-formal-lint.log`.

A useful simplification avoids a separate tuple-boundary comparison: define
one affine moment profile using the fixed upper tuple set, prove its limit
for all t in the interval, then identify both endpoint profiles with the
already verified integer moments by limit uniqueness. The finite-sum affine
identity gives the whole interval. Thus no manual cancellation of the extra
lower-endpoint tuples is required. Generic positive exponent m can use the
existing even/odd dilation means after a parity split, while m=0 follows from
the existing `tendsto_nat_floor_mul_div_atTop` (source inspected at
`Mathlib/Analysis/SpecificLimits/Basic.lean:724`). The minimal API scratch
passes for these floor names. The new real-horizon corpus deep query completed
with `partial=false`; all 20 candidates and 20 source statements were reviewed.
It recovers the existing quotient-product machinery and our own integer
moments; its recipe adds no real-parameter transport proof. Log:
`/tmp/bvi100-real-horizon-source-research.json`.

The individual-level extraction is now verified in the 270-line
`CofinalMobiusRealHorizonSourceLaw.lean`. It uses the
upper alphabet's cardinal polynomial for both endpoints and the literal
floor-sized sample denominator. It proves total mass one and the
exact support transition: the lower alphabet at t=0, the upper alphabet at
every t>0. Original-source Lean passes without diagnostics; all six public
declarations have only the standard three axioms. The leaf is wired and all
15 declarations were retrieved by research. Plain formal lint still reports
only the same two concurrent THIM wiring gaps. Logs:
`/tmp/bvi100-real-source-law-canonical.log`,
`/tmp/bvi100-real-source-law-axioms.log`,
`/tmp/bvi100-real-source-law-index-readback.json`, and
`/tmp/bvi100-real-source-law-formal-lint.log`.
This covers real ratios at least two; the interval 1<A<2 remains separate.
A fresh deep research query, logged at
`/tmp/bvi100-real-value-law-research.json`, completed with `partial=false`;
all 20 candidate and 20 source statements were reviewed. It recovers the
existing sign counts, quotient machinery, and our own new endpoint laws.
Its proposed Ramanujan-dilation transfer does not prove this value law.
Compiler coverage is mostly pending/stale and semantic coverage is unmeasured;
retrieval does not establish absence or novelty.

The follow-up BVI lexical inventory for `cofinal` returned 150 hits. All names
and docstrings were inspected across offsets 0,20,...,140, with the per-module
cap removed (`/tmp/bvi100-cofinal-inventory-*.json`). It includes the prior
quadratic profile, odd moments, sign-frequency lower bounds, and gradient and
discrepancy estimates as well as this candidate's own leaves. A whole-corpus
amplitude query mostly confused unrelated uses of amplitude; all 20 candidates
and 20 source statements were reviewed. A narrowed THIM query then recovered
the sharp five-horizon envelope, its exact additive improvement, and known
radical/roughness laws; again all 20+20 statements were reviewed. Logs:
`/tmp/bvi100-amplitude-frontier-research.json` and
`/tmp/bvi100-amplitude-thim-research.json`. Both finished with `partial=false`,
older coverage snapshots and unmeasured semantic coverage. No completeness or
novelty conclusion follows from these rankings.

## Exact alphabet: independent elementary attainment proof

For B≥1 define `A_B={0} ∪ {±H_l(d): 1≤l≤B, d|primorial(l)}`.
Every literal value at positive cutoff N and sample `1≤k≤(B+1)N` lies in A_B.
For this inclusion, it is enough to use the existing *visible* radical
`R=horizonRadicalState N k`, rather than constructing the full radical. It is
squarefree, positive, at most k, and has the same response. If R≤N the value is
zero or one. Otherwise complementary divisors give
`s_N(R)=-μ(R)*s_l(R)` with `l=(R−1)/N≤B`. Reducing `s_l` to its existing
radical state gives the displayed alphabet. The unit value is already present
at `l=d=1`.

Every member of A_B occurs at arbitrarily large cutoffs in that same horizon
ratio. For a fixed state l,d, multiply d by a prime exceeding l, d and any
requested size. This preserves its l-response and reverses its Möbius sign.
A second sufficiently large prime reverses the sign again. For either resulting
squarefree endpoint R, take `N=floor((R−1)/l)`. Requiring
`R≥l*(T+l+1)+1` gives `N≥T`, `lN<R≤(l+1)N`. The reflection formula therefore
realizes both signs of H_l(d). Zero is attained at sample two for every cutoff
at least two. This proof uses unbounded primes only; positive limiting frequency
requires the separate analytic counting argument above.

The complete inclusion, elementary attainment, and data-only exact-range
statement pass original-source Lean with exit zero and no diagnostics.
`moebius_source_mem_linear_horizon_alphabet` handles every literal sample;
`moebius_linear_horizon_alphabet_iff_cofinal_source_value` identifies the exact
cofinal alphabet. No theorem from this supporting leaf is counted separately.

Remaining formal proof order after the alphabet gate:

1. Connect the literal source to the existing BVI full radical at every positive
   sample; derive the exact finite clock exclusion.
2. Derive the two coprime Möbius sign means from the existing squarefree and
   signed means, using the squarefree primorial modulus.
3. Prove the finite histogram bijection `n ↔ (w,l,d,m)`: clock w, strict radical
   band l, small-prime radical d, and squarefree coprime remainder m. The inverse
   is `n=w*d*m`; the condition `rad(w)|d` ensures its radical is d*m.
4. Pass through the finite sums, retaining the literal unit-sample correction;
   then prove the positive support and horizon-affine conclusions.

Lagrange interpolation remains a secondary route to existence only. The corpus
query found the standard mathlib cardinal basis API; its suggested non-node
evaluation recipe is inapplicable to the source's finite node set.

The 175-line arithmetic producer `CoprimeMobiusSignAndEvenDilationMeans.lean`
passes original-source Lean with exit zero and no diagnostics. All seven public
declarations have only the standard three axioms; the leaf is wired, and research
readback retrieved all 13 declarations.
It first transports the existing coprime-squarefree mean from `rad(Q)` to every
positive modulus Q. Thus the two literal Möbius-sign counts have means D(Q)/2,
by the exact `(μ²±μ)/2` split. Their rationally scaled prefix limits follow from
the same floor-scaling argument already used for quadratic quotient profiles.
The same extension proves every positive even dilation-product mean
`(∏ μ(a_i))*D(∏ a_i)` without pairwise coprimality or squarefree-product premises.
Zero multipliers are handled by their zero Möbius factor. This closes the
repeated-prime-support issue in the proposed all-moment formula; no source
histogram theorem follows without the remaining reindexing/interpolation step.

The 164-line `CofinalMobiusAllMomentProfiles.lean` now determines every fixed
source moment on `(B+2)N`. Its even profiles retain the exact quotient-tuple
maximum, lcm, and overlapping-prime Euler product; the zeroth and odd cases use
the literal sample count and existing odd-moment cancellation. Original-source
Lean exits zero with no diagnostics. All five public declarations have only
`propext`, `Classical.choice`, and `Quot.sound`. The leaf is wired, and documented
research readback retrieved all eight declarations. Cardinal polynomials
on the verified finite alphabet turn these moments into literal value-frequency
limits; positivity of every alphabet mass still requires arithmetic counting.
This supporting package earns no separate contribution credit.

The 217-line `CofinalMobiusSourceValueLaw.lean` now proves the literal value-count
limits through the standard cardinal basis, using the verified alphabet and
moment profiles. Its arithmetic masses are nonnegative, supported on that
alphabet, sum to one, and are symmetric under sign reversal. Original-source
`lake env lean` exits zero without diagnostics; all eight public declarations
have only the standard three axioms. The leaf is wired and all 18 declarations
were retrieved by documented research. Plain formal lint still fails solely
on the two concurrent THIM wiring gaps recorded below. Logs:
`/tmp/bvi100-source-law-canonical.log`, `/tmp/bvi100-source-law-axioms.log`,
`/tmp/bvi100-source-law-index-readback.json`, and
`/tmp/bvi100-source-law-formal-lint.log`.

Strict positivity on the entire alphabet is now verified. For a state `(l,d)`, map
squarefree coprime m with prescribed Möbius sign and
`l*N/d < m ≤ (l+1)*N/d` to `d*m`. The visible radical law preserves its
l-response, while complementary divisors give the required signed source.
This injection bounds the level count below by the difference of two verified
coprime sign counts, yielding the explicit lower mass
`D(primorial(l))/(2*d*(B+2))`. Zero has mass at least `1/(B+2)` from samples
two through N. The 265-line `CofinalMobiusSourcePositiveSupport.lean` proves
the explicit state lower bound, the zero-atom lower bound, and the data-only
equivalence `0<density(B,a) ↔ a∈alphabet(B+1)`. Original-source Lean passes
without diagnostics; all three public theorems have only the standard three
axioms. The leaf is wired and all nine declarations were retrieved by research.
Plain formal lint still reports only the two concurrent THIM wiring gaps.
Logs are `/tmp/bvi100-positive-canonical.log`, `/tmp/bvi100-positive-axioms.log`,
`/tmp/bvi100-positive-index-readback.json`, and
`/tmp/bvi100-positive-formal-lint.log`. Completed owned scratch files were cleaned.
The full positive state sum and real-horizon threshold/transport conclusions
still require exact proofs; they are not inferred from moment existence alone.

A new whole-corpus deep source/value query and a narrowed BVI `sieveSeq` query
both completed with `partial=false`; all 20 candidate and 20 source statements
from each were inspected. The broad query mostly conflates unrelated meanings
of source. The narrowed query recovers the existing odd-moment theorem and
quadratic lower bound for positive-source counts, plus the newly indexed own
all-moment theorem. Its suggested variance/discrepancy recipe does not identify
individual levels. Coverage reports 74,330 inventoried files but semantic
coverage remains unmeasured, with many compiler records pending or stale.
Lexical `sieveSeq frequency` and `sieveSeq distribution` return no hits; broader
source/frequency queries are dominated by unrelated observables. None of these
outputs certifies absence or priority. Logs are
`/tmp/bvi100-source-value-law-research.json` and
`/tmp/bvi100-source-value-law-bvi-research.json`.

The bibliography audit found a closer classical baseline: de la Bretèche,
Dress and Tenenbaum, *Remarques sur une somme liée à la fonction de Möbius*
(2020), author manuscript <https://tenenb.perso.math.cnrs.fr/PPP/Sxz.pdf>.
Its observable M(n,z) is exactly the truncated source. Equations (2.7)–(2.9)
already use full-radical reduction, complementary divisors, and the residual
factor n/rad(n) to give a finite-ratio quadratic profile, with error
O(x^(3/2)/z). At fixed x/z this supplies the corresponding second-moment
limit and its affine structure. Thus neither that decomposition nor quadratic
affinity is new. The complete individual-level law, positive support, and
all-level adjacent-horizon transport must be judged as extensions of this
baseline; significance is not established by their formalization alone.

Another primary baseline is Patrick Letendre, *Truncated convolution of Möbius
function and multiplicative energy of an integer n* (2020),
<https://arxiv.org/abs/1903.05629>. Its introduction, theorem statements,
Section 3, and references were inspected. It studies the same M(n,z), with
n fixed and the cutoff z averaged over [1,n]; Theorems 1.1–1.2 bound those
moments. It also records radical reduction and classical extremal bounds for
partial divisor Möbius sums. This is a different averaging regime, but it
rules out credit for the observable, radical reduction, or generic moment
expansion. The actual corpus lexical search for `Letendre` returned zero hits
(`/tmp/bvi100-letendre-corpus-research.json`); that citation search does not
exclude unnamed equivalent work.

The primary introduction and theorem statements of de la Bretèche–Tenenbaum,
*Oscillations localisées sur les diviseurs* (2012),
<https://tenenb.perso.math.cnrs.fr/PPP/Delta(n,chi).pdf>, were also inspected.
Their Möbius results concern weighted moments of the maximal localized divisor
sum, rather than this fixed finite-ratio law. Maier, *On the Möbius function*
(1987), introduction and Theorem 2, proves large incomplete divisor Möbius sums
for almost every n after choosing the cutoff. Thus unbounded amplitude and
generic divisor-sum oscillation are also classical; neither can count as new.
These comparisons do not establish priority for the candidate's exact law.

The same audit suggests a sharper native support target within this candidate.
For fixed positive visibility clock w and integer horizon A≥2, its exact
cofinal source alphabet should be zero together with
`±H_l(d)` for `w*l<A`, `d|primorial(l)`, and
`horizonRadicalState l w | d`. Necessity follows from `n=w*rad(n)` and
the forced small-prime factors of w. For sufficiency start from the squarefree
`lcm(rad(w),d)`, whose l-state is exactly d, then use one or two large primes
to prescribe the sign. With R large and `N=floor((R−1)/l)`, the strict gap
`A−w*l≥1` ensures `w*R≤A*N`. Zero is always attainable by taking cutoff at
least the sample. This refines the already verified separate amplitude and
clock support statements into their exact compatibility constraint. It remains
a paper conjecture pending a fresh corpus audit and complete Lean proof; it
earns no new credit.

All 25 cross-field lexical coprime/sign hits were paged and inspected. The
actual `RHTower/Sieve/CoprimeSignDensity.lean` results count balanced pairs of
prescribed product sign and give MR-based lower bounds. They are prior work
on a different observable, not the fixed-modulus single-variable mean above.
The BVI deep sign query returned 20 candidates and 20 source arguments, all
reviewed, with `partial=false` and unmeasured semantic coverage. Its useful
inputs are the already existing squarefree mean, signed mean and general
dilation-product identity; no search-based absence or novelty certification
is claimed.

## Native clock interpretation found by corpus search

The 10-result `radical primeFactors` search exposed an existing bridge that the
formula should use explicitly: `ValuationClockChainBridge.lean` proves
`lagVisibilityClock(n)*primeRadical(n)=n`, and
`TranslatedWindowStrideAnnihilationAndLcmReturnObservability.lean` already defines
the BVI radical and proves it squarefree. Thus the state's w is exactly the
existing **additive translation visibility clock**, not a new auxiliary integer.
`RamanujanRadicalDilationReduction.lean` already uses this decomposition for
dilation profiles; that result is prior work.

The paper state law predicts the joint nonzero source/visibility-clock law by
holding w fixed in the displayed sum. It also gives the literal exclusion:
for A≥2, N≥1 and `1≤n≤A*N`, a nonzero source requires
`lagVisibilityClock(n)<A`. For n>1, nonzero response forces `rad(n)>N`, so
`n=lagVisibilityClock(n)*rad(n)>lagVisibilityClock(n)*N`; n=1 has clock one.
The clock/support deep query returned 20 candidate and 20 source entries, all
reviewed, but marked itself partial after malformed model JSON at the final
judging stage. Its useful hits establish the existing clock/radical and lag
multiplier bridges; the proposed recipe conflates distinct facts and does not
prove the source law. A lexical follow-up had zero name/documentation hits for
both identifiers. Neither result proves absence from the corpus. This is part
of the same candidate.

The clock interpretation gives a useful positive survivor to check inside the
full law. Fix w≥1 and let `r=rad(w)`. On the first *radical* band
`N<rad(n)≤2N`, every sample with clock w has source `±1`. For real A>1, the
frequency of either sign among samples `n≤A*N` in that band should be exactly

`(6/π²)/(2*A*∏_(p|w)(p+1)) * max(0,min(2,A/w)−1)`.

Indeed `n=w*r*m` with m squarefree and coprime to r, and its radical is r*m.
The admissible interval for m has scaled length
`max(0,min(2,A/w)−1)/r`. Each Möbius sign has density D(r)/2, and
`D(r)/r=(6/π²)/∏_(p|w)(p+1)`. Thus every integer clock w<A contributes both
unit source signs with positive limiting frequency. Together with clock
exclusion, this would make the allowed nonzero clocks exactly `1≤w<A`.
The elementary cofinal attainment version follows by taking one or two large
prime extensions of r and cutoff `rad(n)−1`. These are prospective consequences
of the same source/clock law, not separate contribution credits.

A further whole-corpus deep query on full-radical absorption completed with
74,317 files inventoried, `partial=false`, but unmeasured semantic coverage.
All 20 candidate and 20 source statements were inspected. Its proposed recipe
combines unrelated visible-kernel and clock-pairing results and is inapplicable.
All 17 lexical hits in `TransHorizonGramMatrixAndRadicalProjection` were reviewed;
the existing squarefree divisor-multiplication absorption and first-octave
reciprocity are prior ingredients. A targeted BVI clock/squarefree query returned
one existing quotient-squarefreeness theorem. These searches are evidence of
specific reuse, not exhaustive absence certificates. The 208-line leaf
`CofinalMobiusSourceClockSupport.lean` now connects the literal source to the
existing full radical, proves clock exclusion, and proves cofinal attainment
of either unit sign for every allowed clock. Original-source Lean passes with
exit zero and no diagnostics. All four public theorem axiom closures contain
only `propext`, `Classical.choice`, and `Quot.sound`. It is wired, and documented
research readback retrieved all 16 declarations.

The targeted BVI deep clock-fibre query also completed (`partial=false`);
all 20 candidate and 20 source statements were inspected. It finds the existing
radical, quotient-squarefreeness, and dilation-product machinery, with no verified
recipe beyond those ingredients. The proposed data-only support capstone is:
for positive w, `w<B+2` iff either prescribed unit sign occurs cofinally at
samples whose existing visibility clock equals w. The proof chooses arbitrarily
large squarefree multiples R of `rad(w)` with either Möbius sign, then uses
`n=w*R`, `N=R−1`. Since `rad(w)|R`, its full radical is R and its clock is w.
Taking R≥T+B+4 guarantees the literal horizon and cutoff bounds. The auxiliary
fibre identity is `clock(w*R)=w ↔ Squarefree R ∧ rad(w)|R` for positive w,R.
These four data-only public support theorems are verified; they do not determine
frequencies or earn separate contribution credit.

The source search also exposed the existing RHTower
`zeroDetectionMobiusCoefficient`, the integer-valued same truncated observable
at cutoff X+1. Its `ChenGuptaLiClassILargeValues` consumers currently reference
a divisor-count norm bound. This is a possible consumer of the proposed precise
finite-ratio law; no transfer theorem or improved zero-density claim is asserted.

Audit logs: `/tmp/bvi100-alphabet-canonical-final.log` (exit 0),
`/tmp/bvi100-alphabet-axioms.log` (exit 0),
`/tmp/bvi100-alphabet-index-readback.json` (12 results), and
`/tmp/bvi100-alphabet-formal-lint.log` (exit 1, the two concurrent wiring errors
listed above).

## Boundaries

Fixed horizon ratio only. No growing horizon-ratio estimate, uniform convergence rate, successor-correlation limit, RH consequence, numerical experiment, or computation certificate is claimed. The finite alphabet, clock support, all integer-ratio moments, individual value probabilities, exact positive support, and adjacent real-horizon moment and individual-value transport are verified in Lean. The positive state sum and exact joint clock/amplitude alphabet remain prospective. The latter has a fresh corpus audit at `/tmp/bvi100-joint-clock-alphabet-research.json`: all 20 candidates and 20 source statements were reviewed, including the complete source of one truncated statement. It recovers the known clock/radical parametrization and the candidate's own support lemmas; no distinct contribution credit is justified by merely combining these mechanisms.

## No-go closure

If the full claim fails, record the exact obstruction and the strongest corrected arithmetic law. If it is already known or only a routine consequence, retain it as prior knowledge without manufacturing contribution credit. Accepted count remains **0 / 100**.
