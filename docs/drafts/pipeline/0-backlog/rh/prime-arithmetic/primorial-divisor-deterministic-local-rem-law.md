# Primorial-divisor deterministic local-REM law

- **ID:** `primorial-divisor-deterministic-local-rem-law`
- **Stage:** 0-backlog
- **Type:** CONJECTURE / MULTIPLICATIVE NUMBER THEORY / DETERMINISTIC NUMBER PARTITIONING /
  LOCAL SPECTRAL STATISTICS
- **Scientific status:** `[CONJECTURE] [DEPRIORITIZED] [NOVELTY UNVERIFIED]`
- **Statement:** In every fixed bulk energy band, the logarithms of complementary divisors of the
  primorial have unit-intensity Poisson local statistics, and the prime-sign partitions producing
  neighboring levels have asymptotically zero overlap.

## Why this is the frontier object

The unresolved arithmetic mechanism behind finite prime-phase clocks is not ordinary
equidistribution.  It is the microscopic spacing of rational prime products.  The cleanest exact
slice is obtained from the divisors of the primorial.

Let

```text
P_X={p prime:p<=X},             d_X=#P_X,
Sigma_X^2=sum_(p<=X)(log p)^2,
C_X={-1,+1}^P_X /(sigma~-sigma),
N_X=#C_X=2^(d_X-1).                                             (1)
```

For a sign class `[sigma] in C_X`, define its normalized complementary-divisor energy

```text
E_X([sigma])=
  |sum_(p<=X) sigma_p log p|/Sigma_X
= |log(D_sigma^2/P_X#)|/Sigma_X,                                (2)
```

where `D_sigma` is either complementary divisor selected by the sign vector and
`P_X#=product_(p<=X)p`.

Unique factorization proves an exact fact that is essential but far from sufficient:

```text
E_X([sigma])=E_X([tau])  <->  [sigma]=[tau].                     (3)
```

Indeed equality of the absolute logarithmic sums gives a rational prime-product relation, and
all its prime exponents vanish.  Thus `(2)` is a simple deterministic spectrum of `N_X` levels.

Put

```text
g(a)=sqrt(2/pi) exp(-a^2/2),       a>=0,                         (4)
```

the half-normal density.  The Lindeberg central limit theorem and the prime number theorem predict
and, by standard triangular-array arguments, prove the macroscopic counting law

```text
N_X^(-1) #{c in C_X:E_X(c) in I} -> integral_I g(a) da           (5)
```

for every continuity interval `I` in `(0,infinity)`.  The conjecture begins strictly below the
scale visible in `(5)`.

## The conjecture

Fix a compact interval `I=[a,b] subset (0,infinity)` with `a<b`.  For all sufficiently large `X`,
choose a root class `C_X^*` uniformly from

```text
C_X(I)={c in C_X:E_X(c) in I}.                                  (6)
```

Conditional on the chosen root, form the rescaled rooted point process

```text
Xi_(X,I)=sum_(c in C_X, c!=C_X^*)
  delta_[N_X g(E_X(C_X^*)) (E_X(c)-E_X(C_X^*))].                 (7)
```

For two sign classes define the projective spin overlap

```text
Q_X([sigma],[tau])=
  |d_X^(-1) sum_(p<=X) sigma_p tau_p|.                            (8)
```

This is independent of the two choices of sign representatives.

`[DEPRIORITIZED CONJECTURE]` As `X->infinity`:

1. `Xi_(X,I)` converges in law, with randomness only from the uniformly chosen root `(6)`, to a
   homogeneous Poisson point process of intensity one on `R`.
2. Local configurations decorrelate: for every `L>0` and `epsilon>0`, the probability that two
   distinct sign classes represented by the root together with the points of `(7)` in `[-L,L]`
   have projective overlap greater than `epsilon` tends to zero.

Equivalently, the rooted primorial-divisor spectrum converges to the Palm version of the
unit-intensity Poisson process, while its finite local cluster carries the zero-overlap mark.

The count formulation is explicit.  For pairwise disjoint bounded Borel sets
`B_1,...,B_m subset R` whose boundaries have measure zero,

```text
(Xi_(X,I)(B_1),...,Xi_(X,I)(B_m))
   => (Pois(|B_1|),...,Pois(|B_m|))                              (9)
```

with independent coordinates, together with the overlap assertion in clause 2.

This two-clause statement is the only active conjecture on this card.

## Universal-law content

The law has three simultaneous interpretations.

1. **Primorial divisors.**  After logarithmic unfolding by the half-normal density, neighboring
   complementary-divisor ratios have exponential spacings of mean one.
2. **Deterministic number partitioning.**  The fixed weights `{log p:p<=X}` have the same bulk
   local energy statistics as the random-energy model, even though no weight is random.
3. **Prime-product resonances.**  Boolean Fourier frequencies
   `sum sigma_p log p` have Poisson microscopic differences at their natural spacing
   `Sigma_X 2^(-d_X)`, and neighboring resonances use asymptotically orthogonal prime choices.

In particular, if the conjecture holds then every fixed finite vector of successive unfolded gaps,
sampled from a bulk band, converges to independent `Exp(1)` variables.  This is a distributional
law, not a bound on the smallest gap or a reformulation of unique factorization.

## Relation to the prime-log entropy programme

The Fourier expansion of a prime-phase Gibbs weight is indexed by integer vectors
`k=(k_p)` and frequencies `sum k_p log p`. Restricting to the Boolean shell
`k_p in {-1,+1}` gives the same spectrum as `(2)`, but the pressure problem selects
frequencies exponentially close to zero. The present conjecture localizes around a fixed
positive normalized energy. It therefore studies a genuine deterministic local-statistics
problem, but it does **not** resolve the Boolean zero-edge shell needed by
`prime-log-level-two-entropy-budget-law.md`.

It does **not** by itself prove that level-two law.  The latter also requires:

- coefficient zero and unbounded integer Fourier modes;
- type-dependent Fourier amplitudes;
- signed cluster pressure rather than only unweighted local counts;
- a uniform passage from finite alphabets to smooth one-site potentials.

The corrected relationship is therefore

```text
bulk primorial local REM
  = an adjacent deterministic universality problem,
not the zero-edge resonance theorem and not the entropy theorem.        (10)
```

## Hostile rediscovery audit

### Random-weight local REM is parent theory, not the claim

Borgs--Chayes--Mertens--Nair prove local REM and overlap decorrelation when the partition weights
are independent random variables.  Their probability is over the weights.  Here the weights are
the single rigid arithmetic vector `(log p)_(p<=X)`; the only randomization selects a typical
spectral root after the deterministic spectrum has been constructed.  Quenched specialization to
one exceptional deterministic sequence is not supplied by their theorem.

### Unique factorization gives simplicity, not Poisson statistics

Equation `(3)` prevents exact collisions.  It gives no control at the mean spacing
`Sigma_X 2^(-d_X)`, no factorial-moment asymptotics, and no overlap decorrelation.  Quantitative
lower bounds for one linear form in logarithms are also too weak and address the wrong statistic:
`(9)` counts the collective local geometry of exponentially many forms.

### Distinct-subset-product extremal theory is adjacent, not equivalent

Results on how large a subset-product-distinct set of integers can be concern exact equality of
products.  The prime set is already exactly subset-product-distinct.  The present problem begins
only after exact distinctness is known and asks for microscopic ratios among all `2^(d_X)` subset
products.

### The existing “Phi, Primorials, and Poisson” theorem is a title collision

Pollack--Pomerance study the normal order of the largest primorial dividing `phi(n)` for a
typical integer `n`, with a tertiary Poisson law for that divisibility statistic.  Their random
variable is `n`; they do not study the `2^(pi(X)-1)` complementary divisors of one primorial,
their logarithmic local spacings, or spin-overlap marks.  The shared words “primorial” and
“Poisson” therefore do not supply or weaken `(7)--(9)`.

### Large-value estimates do not identify the point process

Mean-value and large-value theorems for Dirichlet polynomials bound aggregate mass in ranges of
`t`.  They do not give the Palm local statistics of the static spectrum `(2)`, its Poisson
factorial moments, or the zero-overlap marking.

Primary parent and comparison sources:

- C. Borgs, J. Chayes, S. Mertens, and C. Nair,
  *Proof of the local REM conjecture for number partitioning I: Constant energy scales*,
  <https://arxiv.org/abs/cond-mat/0501760>.
- C. Borgs, J. Chayes, S. Mertens, and C. Nair,
  *Proof of the local REM conjecture for number partitioning II: Growing energy scales*,
  <https://arxiv.org/abs/cond-mat/0508600>.
- R. Raghavan, *Sharp Bounds for Sets with Distinct Subset Products*,
  <https://arxiv.org/abs/2501.02695>.
- P. Pollack and C. Pomerance, *Phi, Primorials, and Poisson*,
  <https://arxiv.org/abs/2001.06727>.
- L. Guth and J. Maynard, *New large value estimates for Dirichlet polynomials*,
  <https://arxiv.org/abs/2405.20552>.

Exact-object searches on 2026-07-20 found no local-REM theorem or conjecture for the deterministic
weights `{log p}`, no Poisson local-spacing law for logarithms of primorial divisors, and no marked
overlap law for the same spectrum.  This is not a priority proof; novelty remains formally
unverified until proof and full ancestry audit.

## Hostile falsity audit

### Exact algebraic correlations

The spectrum has many parallelogram identities inherited from the hypercube.  Random number
partitioning has the same combinatorial source of correlations and nevertheless has a local-REM
phase, but the deterministic prime weights may preserve arithmetic clusters that random weights
destroy.  Clause 1 is false if any such cluster survives with positive bulk density.

### Global sign symmetry

Without the quotient `sigma~-sigma`, every positive energy is exactly doubled and Poisson
statistics are impossible.  The quotient in `(1)` is mandatory, not cosmetic.

### The spectral edge

The conjecture deliberately fixes `I subset (0,infinity)`.  It does not claim a Poisson law for the
least partition discrepancy at energy zero.  Edge statistics are a distinct problem and must not
be smuggled in as a corollary of the bulk law.

### Growing energies

Random-weight local REM has a known breakdown scale for growing target energies.  No uniformity is
claimed when the band `I=I_X` escapes to infinity.  Establishing or refuting an arithmetic
breakdown threshold is a later problem.

### Exact falsifiers

The conjecture fails if any of the following is proved for some fixed bulk interval `I`:

1. an unfolded gap statistic has a non-exponential limiting law;
2. a bounded local count has a non-Poisson factorial moment;
3. a positive-density family of microscopic clusters survives;
4. neighboring levels retain projective overlap bounded away from zero;
5. the rooted local laws have two different subsequential limits as `X` passes through primes.

## Exact open core

For each fixed `r>=2`, prove the arithmetic factorial-moment asymptotic for `r` distinct sign
classes whose normalized energies lie in microscopic windows of width `N_X^(-1)` about one bulk
root, while excluding high-overlap tuples at negligible relative density.

After Fourier inversion of the window indicators, this becomes a cofinal mean-value problem for
the deterministic characteristic product

```text
prod_(p<=X) cos(t log p / Sigma_X),                              (11)
```

at frequencies exponentially large in `d_X`.  Fixed-order central limit theory controls `(11)`
only on bounded frequency scales.  The local law needs uniform control through the saddle where
the number of spectral levels `2^(d_X-1)` is exactly balanced by the microscopic window size.

The first decisive theorem is the two-point law with overlap removal.  It must show that after
bulk unfolding,

```text
pair correlation -> Lebesgue pair correlation                          (12)
```

and that pairs with `Q_X>=epsilon` contribute `o(N_X)` in every microscopic bulk window.  Higher
factorial moments then face genuinely new multi-overlap arithmetic rather than a routine
extension.

## Gates

- [x] exact arithmetic spectrum and symmetry quotient defined
- [x] macroscopic parent law separated from the conjecture
- [x] random-weight local REM separated from deterministic arithmetic local REM
- [x] exact-collision, edge, growing-energy, and overlap attacks recorded
- [x] first Google/arXiv exact-object search completed
- [ ] prove the two-point unfolded correlation law with high-overlap removal
- [ ] prove all fixed factorial moments
- [ ] deduce the rooted Palm point-process and marked-overlap limits
- [ ] complete proof-stage citation ancestry and descendancy audits
- [ ] 1 -> 2 fully-proven: dependency-closed paper proof
- [ ] 2 -> 3 formalized: exact unconditional theorem and axiom audit

## Log

- 2026-07-20 -- Created as the concrete arithmetic core hidden by the broader level-two
  entropy-budget conjecture.  The first hostile audit found the random-weight local REM theorem,
  exact subset-product extremal theory, and Dirichlet-polynomial large-value estimates, but no
  deterministic local-statistics theorem for logarithms of primorial divisors.  The global sign
  quotient, bulk restriction, Palm rooting, and overlap mark were added specifically to eliminate
  immediate false formulations.  Verdict: `[CONJECTURE] [NOVELTY UNVERIFIED]
  [SURVIVES FIRST HOSTILE AUDIT]`.

## Exact overlap-resolved two-frequency reduction

`[PAPER-PROVED REDUCTION] [BRIDGE; NOT THE CONJECTURAL DELTA]`  Enumerate the primes at most
`X`, put

```text
w_p=log(p)/Sigma_X,
S_X(sigma)=sum_(p<=X) sigma_p w_p,
sigma^A_p=-sigma_p for p in A and sigma^A_p=sigma_p otherwise.
```

For `0<=m<=d_X`, define the normalized overlap-stratum characteristic function

```text
C_(X,m)(u,v)
 =2^(-d_X) binom(d_X,m)^(-1)
   sum_sigma sum_(A subset P_X, |A|=m)
     exp(i[u S_X(sigma)+v S_X(sigma^A)]).
```

Then the following identity is exact for every real `u,v`:

```text
C_(X,m)(u,v)
 =binom(d_X,m)^(-1) sum_(|A|=m)
    product_(p notin A) cos((u+v)w_p)
    product_(p in A)    cos((u-v)w_p).                    (13)
```

Indeed, for fixed `A`, the exponent is

```text
sum_(p notin A) (u+v)sigma_p w_p
 +sum_(p in A) (u-v)sigma_p w_p.
```

Averaging independently over each sign gives the two cosine products in `(13)`, and averaging
over `A` gives the formula.  Moreover

```text
d_X^(-1) sum_p sigma_p sigma^A_p=1-2m/d_X.                (14)
```

Thus `(13)` resolves the two-point problem exactly by projective overlap.  Since the energy is
absolute, each projective pair may be represented with `0<=m<=d_X/2` by flipping the second sign
vector when necessary.  On this representative branch, projective overlap at least `epsilon`
corresponds exactly to

```text
m/d_X <= (1-epsilon)/2.                                    (15)
```

For Schwartz test functions, ordinary two-dimensional Fourier inversion turns every smoothed
rooted pair count into the integral of `(13)` against the two Fourier transforms.  No randomness,
independence model, or unproved prime estimate enters this reduction.

The first arithmetic frontier can therefore be stated without point-process language:

```text
[OPEN CORE: OVERLAP-RESOLVED EXPONENTIAL SADDLE]

At bulk localization width 2^(-d_X), prove the independent-Gaussian
pair saddle after summing (13) over m, and prove that the partial sum over
m/d_X <= (1-epsilon)/2 is o(1) for every epsilon>0.          (16)
```

The required Fourier range is exponential in `d_X`; bounded-frequency central-limit estimates do
not reach `(16)`.  Conversely, `(16)` is exactly the two-point Poisson law with high-overlap
removal.  It is the first decisive gate on the card.  Higher Poisson factorial moments replace
`A` by a finite overlap pattern and lead to the corresponding multi-frequency cosine product;
they are not automatic from `(16)`.
