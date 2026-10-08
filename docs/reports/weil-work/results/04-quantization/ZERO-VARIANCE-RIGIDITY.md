# C30 — zero-variance rigidity (OPEN)

Cycle30, 2026-10-08. Verdict: SURVIVES PRELIMINARY ATTACK; no paper proof,
no Lean assertion, independent novelty unestablished.

Given the exact internal and external frontier, what would a Fields
Medal-winning mathematician conjecture? The natural next stronger source
law is that nonrigidity cannot hide entirely in a zero logarithmic-density
coefficient defect.

Let hW be any specified WeilPositiveFull lambda, a_n=sourceCoeff lambda n,
beta=sourceCompletion hW 1. The existing unconditional ForwardVariance
module supplies the unique finite V>=0 with

    (sum_(1<=n<=N) |a_n-beta|^2/n) / log N -> V.

C30 states, with no extra source hypothesis:

    [lambda(n)=Lambda(n) for all n>=2 and RH]
       OR
    [the actual centered logarithmic variance V is strictly positive].

Equivalently, V=0 forces arithmetic rigidity. The rigid case gives V=0.
This is weaker as a producer obligation than proving C28, but stronger
than the existing dichotomy obtained by detecting a single nonzero
coefficient: that dichotomy allows a nonrigid zero-variance branch with
physical energy only of order T. C30 would eliminate that branch. With
T29, every nonrigid actual source would then have centered physical energy
of order at least T log T, so o(T log T) would already force rigidity.
Neither C30 nor the source o(T log T) estimate is supplied here.

## Attempt to kill it

1. Generic pole-free continuation and Gaussian coefficient recovery are
insufficient. The ordinary Dirichlet function zeta(s)+2^(-s) has residue1
and one nonzero centered coefficient, hence centered harmonic variance0.
It is not asserted to be a full-positive source. It kills only the
proposed deduction from pole-free centering and coefficient recovery.

2. The actual coprime covariance budget implies, when V=0, that every
finite coprime-mask residue equals beta times its ordinary density. It
does not by itself identify individual coefficients: a singleton integer
has zero logarithmic density. Passing from these residues to a pointwise
coefficient identity requires an additional source argument.

3. Existing LocalPolynomialModels proves zero valuation variance iff the
normalized local polynomial is1. This is a finite local model result,
not a representation theorem for arbitrary full-positive sources.
Neither Euler multiplicativity nor a finite-prime factorization is
available to insert as a premise.

4. The September2026 Hardy embedding preprint controls a different
coefficient norm, as recorded in CENTERED-PHASE-ENERGY.md. It does not
supply the missing coefficient faithfulness or C30.

[OPEN CORE] Show that the full-positive logarithmic convolution and
actual valuation/coprime residue laws make zero harmonic variance
faithful to every positive-index coefficient, or construct an actual
nonrigid full-positive source invisible to all these finite residues.
The two possibilities must remain distinct. Failure of a mask argument
would not disprove C30.

Next audit the exact valuation residue producer and its infinite-prime
tail obligations. Do not write a receiver assuming coefficient
faithfulness, and do not replace the common-full-measure WP04 target by
this conjecture. Continue finishing T28's actual coefficient/Bessel
obstruction while testing this source law.

Exact corpus attack: deep query “zero residual forward coefficient
variance forces coefficient rigidity valuation residues”, module Weil,
completed with partial=false (68,875 indexed files; compiler and semantic
freshness caveats retained in cycle30-search-evidence.json). Its proposed
ingredient set leaves “Variance -> zero” and then cites coefficient
identifications. Those do not prove C30; both implications must be
supplied rather than inferred from retrieval labels.

Inspected actual ValuationAnalytic and ValuationResidueSum statements:
every one-prime normalized residue sequence sums to1, has geometric
decay, and gives a holomorphic generating function on |z|<sqrt(p).
Nonvanishing and arbitrary finite-prime joint exhaustion are not part of
that theorem. A subsequent direct source audit found the stronger
ValuationZeroFree.exists_forward_valuation_zero_free: hW supplies
nonvanishing throughout |z|<sqrt(p), through twisted logarithmic absolute
convergence and the disk Hurwitz theorem. This separate current source
capstone was inspected, not independently rebuilt in this cycle. Thus
local nonvanishing is already represented in the corpus and must not be
listed as a missing producer. One-prime marginals still do not determine joint
composite coefficients. Even after obtaining every finite joint marginal,
the limit exhausting primes would need a uniform tail theorem. This is
the next specific source obligation to attack.

Exact external C30 queries returned no verified matching primary theorem.
The reviewed primary Gaussian/Bessel and Hardy-embedding papers provide
comparisons, not a zero-variance source classification. This is not an
absence or originality claim.

The follow-up exact corpus query (joint valuation masks and zero variance)
also completed, with incomplete refresh and unmeasured semantic coverage.
Its proposed ingredient set confuses zero-index centered coefficients and
unrelated centered matrix vectors with vanishing of the entire source;
it is inapplicable. Two relevant parent statements were inspected directly:

- WeilRegular.RegularDeviation asks for holomorphic continuation of the
  Dirichlet series of lambda-Lambda across the closed critical strip, plus
  growth and symmetry. V=0 has not supplied this. The centered source A
  is a different function, holomorphic only in the open half-plane.
- weilFullCone_exposed_at_vonMangoldt gives L(lambda-Lambda)<=0, with
  equality forcing lambda=Lambda. Its exact fixed functional is
  atomPairing against riemannKernelAutocorr. It does not give equality
  from V=0. This suggests a competing proof target: derive equality of
  this already-faithful functional from zero coefficient variance, rather
  than first recovering every finite joint valuation marginal. That
  implication is still [OPEN CORE], not an available estimate.

## Cycle31: finite-prime confinement and endpoint faithfulness

Candidate: a full-positive source whose deviation from Lambda is supported
on integers generated by a finite prime set must be rigid. Verdict:
**REDISCOVERED**. The exact stronger parent already exists as
`WeilFiniteSupport.eq_vonMangoldt_of_weilPositiveFull`; the original hW
pays its growth and positive-definiteness premises. Its complete source
proof was inspected. No duplicate Lean theorem was written. The strongest
positive survivor is that existing exact rigidity theorem, already in Lean.

Based on what killed this idea, what stronger conjecture can we make that
is not killed by the research? Retain C30 with an unrestricted infinite
prime tail. Replacing finite support by a log-summable normalized deviation
also does not advance the frontier: `WeilLogSummable` already proves that
rigidity and its sparse-support corollary. Their full statements and proofs
were inspected.

The next attempted mechanism was to recover coefficients from canonical
finite-prime valuation endpoints. Direct inspection of
`sourceCoeff_prime_factorization`, `valuation_source_ratio_eq` and
`exists_forward_valuation_endpoints` shows why this stops: each logarithmic
endpoint sums over every cofactor, not just pure prime powers. Canonical
endpoint values do not by themselves isolate individual logarithmic
coefficients. Even all finite bounded masks are insensitive to a finite
coefficient perturbation after division by log N. This is a failure of the
proposed inference, not a full-positive counterexample or a disproof of C30.

The exact deep search returned the already-known uniform divisibility
bound, zero-free local residue producer and prime-deletion variance budget.
Its proposed ingredient set explicitly leaves tail convergence unpaid.
All candidate/source rows were examined. Source inventory was complete
(`partial=false`, 68,897 files), while compiler and semantic freshness were
mixed; metadata is retained in cycle31-search-evidence.json.

External rigidity parents also retain missing structural premises:
[Klurman--Mangerel](https://arxiv.org/abs/1707.07817) assumes multiplicative
functions; [Dixit](https://arxiv.org/abs/1905.04193) requires continuation
and growth conditions for its uniqueness class, with positive coefficients
in its stated extended-Selberg corollary. Neither supplies those premises
for this arbitrary hW. C30 remains **SURVIVES PRELIMINARY ATTACK**, with the
same open core: derive coefficient faithfulness or equality of the actual
exposing functional from V=0 using full positivity itself.

The next stronger, quantitative conjecture is C31 in
EXPOSING-VARIANCE-COERCIVITY.md: one universal constant should bound
|beta|^2 times the squared exposing deficit by V. Its quantifier order
distinguishes uniform stability from the qualitative C30 implication.
The current corpus attack has not supplied this estimate. A proposed
Suzuki-norm argument was rejected because its retrieved theorem assumes
RH; zero forward variance cannot be substituted for that hypothesis.
