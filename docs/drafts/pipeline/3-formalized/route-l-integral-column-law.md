# Route L: literal integral columns and exact prime-test classification

Date: 2026-09-11.
Status: formalized; all 23 theorems and final audits passed.
Module: `GaloisForLFunctions.RHTower.DeningerGammaSixIntegralColumnLaw`.
RH and the fixed physical-reader comparison remain unproved.

## Question and result

C23 supplies the actual complete Gamma-six tensor integral, but it does not
identify that integral with the required physical or cyclic reader. C24
tests whether dropping the bounded-Hilbert-reader assumption lets this
specific integral escape the previous prime-incidence obstruction.

The answer is negative on its established every-depth domain. The positive
result is an exact classification of the complete source columns, derived
from their own integral values and arithmetic depth decay.

Write `s(w)=1/2+i*w`. Fix both spectral parameters before choosing any
divisor, with `|Im(w)|,|Im(z)|<1` and `Re(s(w)),Re(s(z))>1/3`. Every honest
depth `m>=3` is then in the already proved absolute integral domain. For
internal orders `k,l`, retain

`c=XiC^(k)(w)*XiC^(l)(z)`.

The literal flattened full tensor column at ordinary coordinate `n+216`
is `c/(n+216)` plus the actual flattened tensor-remainder integral. That
complete scalar remainder is absolutely summable across all columns.
Reindexing on positive integers includes the omitted finite head in the
summable correction. The resulting diagonal operator is admitted by every
open Gibbs domain, with Gibbs parameter `tau>1/2` independent of `w,z`.

On this region the following conditions are equivalent:

- the complete scalar diagonal is summable;
- its retained coefficient `c` is zero;
- the actual operator passes every prime-pair cyclicity test in any fixed
  open Gibbs domain.

When `c=0`, every integral column and the whole operator are exactly zero.
When `c!=0`, no absolutely summable correction can cancel its prime-test
outputs, by the previously proved prime-incidence obstruction. Neither a
bounded Hilbert evaluator nor an assumed column bound is used.

At every Xi divisor in the every-depth domain, the pair of multiplicity-top
internal orders has `c=[XiC^(q)]^2!=0`, so its operator fails the prime
tests. This includes every possible strict-right divisor. This is not an
exclusion of those divisors: agreement with the fixed cyclic/physical
reader has not been established.

## Exact source estimate

For every positive ordinary-integer label `p`, the corpus provides

`norm(tailCoefficient_(p,m,j)(w))
  = abs(mu(p+j+1))*(p/(p+j+1))^(m*Re(s(w)))`.

Its existing complete majorant has finite sum

`K_p=sum_j (p/(p+j+1))^(3/2)`.

When `m*Re(s(w))>=3/2`, split the exponent at `3/2`. Since
`p/(p+j+1)<=p/(p+1)`, every term and then the full admitted tail satisfy

`norm(M_p(m,w)-mu(p))
  <= K_p*(p/(p+1))^(m*Re(s(w))-3/2)`.

For every fixed `Re(s(w))>0`, the right side is geometrically summable in
depth. The complete tail multiplier therefore has summable norms over
all natural depths; the estimate is used only on its eventual convergence
domain, so the finitely many early scalar values do not affect this series
claim. Actual *integral* admission at every depth is imposed separately
by `Re(s)>1/3` above, rather than treating undefined integrals as a physical
finite-head correction.

For six, `mu(6)=1`. The complete two-variable tensor multiplier is

`C_m(w,z)=M_6(m,w)*M_6(m,z)-1
  = delta_m(w)+delta_m(z)+delta_m(w)*delta_m(z)`.

Both correction sequences have summable norms; their pointwise product
does too. Consequently `sum_m norm(C_m(w,z))` converges. The exact
ordinary-integer shell contains `5*6^m` columns, whereas each tensor
carries forced half-density `6^(-m)`. Their cancellation sends every
nonnegative summable depth profile to a summable column profile. The
flattening factor is at most one, giving the stated norm control of the
actual remainder integral without a global operator-norm bound.

## Dependency-closed proof

1. Split the source coefficient's exact real exponent and bound its
   remaining base by the first strict-tail ratio. Apply the existing
   summable majorant and norm bound for complete series.
2. Rewrite the depth rate as a constant times a geometric sequence. The
   actual multiplier agrees with its full tail sum on an eventual domain;
   this yields absolute depth summability.
3. Establish the elementary product correction law for two complex
   sequences with summable deviations from one, then apply it to the
   actual complete multipliers. No numerical estimate is required.
4. Partition every ordinary-integer column by its literal depth fibre.
   Finite fibre cardinality is exactly `5*6^m`; multiplication by the
   existing shell eigenvalue cancels its exponential factor.
5. C23's admitted factor and tensor integrals retain all internal orders,
   both spectral variables, cross terms and Fourier normalizations. Apply
   the fixed flattening profile to both principal and remainder. The
   principal profile is exactly reciprocal, giving the column identity
   and norm majorant from steps 3--4.
6. Reindex including the finite head. The harmonic diagonal is not
   summable, so full summability is equivalent to `c=0`. Weighted remainder
   admission plus the ordinary Gibbs partition admits the full operator.
7. If prime cyclicity held at `c!=0`, scaling the admitted operator by
   `c^-1` would produce a prohibited summable repair of the reciprocal
   Green diagonal. Conversely, `c=0` makes every source integral zero and
   therefore gives the zero, cyclic operator.
8. Specialize to each admissible Xi divisor only now. Its first nonzero
   derivative is nonzero by the existing multiplicity theorem, so step 7
   excludes prime cyclicity for that literal top-jet reader.

## Scope and next obstacle

Removing a boundedness assumption is insufficient for this particular
comparison: the full arithmetic source itself forces a summable error
class and a nonzero retained prime obstruction. The result does not say
that every singular reader has this behavior. It neither replaces the
existing Burnol/Deninger reader nor identifies its physical conormal
marginal with the present tensor-product derivative coefficient.

The current Gibbs domain excludes the critical endpoint. A next source
construction can test the actual normalized critical Abel limit while
retaining its first parameter variation; declaring its endpoint value
cyclic is not yet a comparison preserving horizontal information. The
fixed-reader agreement gate remains open.

## Corpus and external checks

Three deep/method searches covered geometric spectral tails, prime
classification and weighted trace compression. They reported partial
source/compiler coverage (706108 ready, 779 stale method records).
Several hits were unrelated finite-group cyclicity or generic weighted
trace constructions. The actual spectral majorant, exact Gamma-six depth
fibres, integral source identities and prime-incidence obstruction were
read directly; every used declaration is checked in the Lean scratch.

Broad arXiv terms were `dilation`, `renewal`, and `transfer`, with recent
2026 preference. The [September 6 multiscale recovery paper](https://arxiv.org/html/2609.06661v1)
uses finite spectral sums, noncolliding sampled nodes, incommensurate
scales and an additional matching condition for exact recovery
(Theorem 3.5). Those assumptions do not reconstruct this complete source
or supply a physical reader. The [September 6 Frobenius-dilation paper](https://arxiv.org/html/2609.06767v1)
uses fixed homogeneous generators, reduction at good primes and Hilbert
function control (Section 1 and Theorem 2.3). It supplies no estimate of
this source's infinite arithmetic columns. Neither paper is imported as
an RH premise; no numerical experiment was performed.

## Verification

- `lake env lean /tmp/route_l_integral_columns.lean`: all 23 theorems passed without warnings.
- `lake build GaloisForLFunctions.RHTower.DeningerGammaSixIntegralColumnLaw`: passed.
- All 23 theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/formal_tools.py lint`: passed; existing repository warnings remain.
- Umbrella import wired; no full or umbrella build or numerical evaluation.
