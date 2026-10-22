# Prime--archimedean exchangeability, de Finetti mixing, and RH

- **ID:** `prime-arch-exchangeable-de-finett-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [EXCHANGEABILITY ASSEMBLY]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`,
  `formal/GaloisForLFunctions/RHTower/EulerSquarefreeWickDefect.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeArchThetaCumulantMinor.lean`, and
  `formal/GaloisForLFunctions/RHTower/PrimeArchMomentMeasureRH.lean`
- **Statement:** `[CONJECTURE]` After one source-defined compact rescaling, the normalized canonical
  prime--archimedean moment tower is the all-success probability sequence of an infinitely
  exchangeable Bernoulli field built from completed prime-word support packets.  De Finetti mixing
  then gives a positive compact moment measure, strict Hankel positivity, and RH.

## Exact probabilistic consumer

Write

```text
m_n=normalizedPrimeArchMoment(n),
m_0>0.                                                     (1)
```

Lean proves `m_0>0` and proves that positivity of every leading Hankel determinant

```text
det [m_(i+j)]_(0<=i,j<n)>0                                (2)
```

is equivalent to RH.  Fix `R>0` and normalize

```text
a_n=m_n/(m_0 R^n),
a_0=1.                                                     (3)
```

Suppose there is an infinitely exchangeable `{0,1}`-valued sequence `(B_j)` such that

```text
P(B_1=...=B_n=1)=a_n.                                     (4)
```

By de Finetti, there is a probability measure `lambda` on `[0,1]` with

```text
a_n=integral_0^1 y^n dlambda(y).                          (5)
```

Pushing `lambda` forward by `y->R y` and multiplying its mass by `m_0` gives a positive measure
`mu` on `[0,R]` whose moments are exactly `m_n`.  Therefore every finite Hankel block is positive
semidefinite.  If the mixing support is infinite, every finite block is positive definite, giving
`(2)` and hence RH.  The last implication is now formalized directly as
`riemannHypothesis_of_primeArchInfiniteSupportMomentRepresentation`.

The normalizing radius is not allowed to use a zero ordinate.  It must come from a source-proved
zero-free neighborhood of the seam or a direct growth bound for the canonical moment germ.

## Finite extendibility equations

For an exchangeable law on `n` bits, let `q_(n,k)` be the probability of exactly `k` successes.  Its
all-success probabilities satisfy

```text
q_(n,k)=binom(n,k) integral y^k(1-y)^(n-k) dlambda(y)
       =binom(n,k) sum_(j=0)^(n-k) (-1)^j binom(n-k,j) a_(k+j).  (6)
```

Thus the low-aperture test is exact: all values in `(6)` must be nonnegative, sum to one, and obey
the deletion consistency law

```text
q_(n,k)=((n+1-k)/(n+1)) q_(n+1,k)
       +((k+1)/(n+1)) q_(n+1,k+1).                       (7)
```

These are finite-difference inequalities and projective consistency, not numerical guesses.
Infinite extendibility of the same family supplies the compact positive measure in `(5)`.

## Why the prime-word corpus fits this detour

`PrimeWordEnsembleBoundaryTomography.lean` proves that the `r`th boundary jet of a finite weighted
prime-word ensemble extracts exactly the words with `r+1` distinct labels.  Hence the completed
boundary germ already gives lossless support-cardinality data, the same statistic as “exactly `k`
occupied labels” in `(6)`.

The shared-Rademacher successor to the four-point Wick no-go adds a latent-variable clue.  Raw even
squarefree support moments are exactly the moments of one shared sign.  Passing from
`epsilon in {-1,+1}` to `(1+epsilon)/2 in {0,1}` gives an endpoint-valued latent bias.  That rank-one
law is too small for strict Hankel positivity, but it identifies the correct positive operation:
mix shared biases rather than close the packet by Gaussian pairings.

The conjectural completion replaces the two endpoint biases by a source-defined infinite mixture of
biases indexed by coupled theta atoms, prime supports, and the Gamma/polar boundary.

## The large two-ended chain

```text
multivariate squarefree prime-word supports                       [PROVED LEAN]
  -> every support-cardinality slice from boundary jets           [PROVED LEAN]
  + shared latent-sign realization of the rank-four even packet   [PROVED LEAN]
  -> completed nonnegative occupancy weights q_(N,n,k)
       [OPEN CORE A: finite probability assembly]
  -> exchangeability and deletion consistency across apertures
       [OPEN CORE B: infinite extendibility]
  -> one exchangeable Bernoulli field                             [KOLMOGOROV]
  -> positive de Finetti mixing measure lambda on [0,1]           [DE FINETTI]
  -> exact moment identity (3)--(5)
       [OPEN CORE C: prime--arch comparison]
  -> infinite support of lambda
       [OPEN CORE D: strictness]
  -> every canonical source Hankel determinant is positive
  -> RH.                                                          [PROVED LEAN CONSUMER]
```

## Candidate source assembly

At each finite prime aperture, retain actual squarefree support labels until the last step.  Couple
the signed Euler word weights to positive theta integer atoms and the polar correction, then
aggregate only by support size.  The resulting completed weights should be normalized into
`q_(N,n,k)` with the following order of proof:

1. entrywise nonnegativity from the completed finite packet;
2. total mass one;
3. invariance under relabelling of the `n` observation slots;
4. deletion consistency `(7)` under `n+1 -> n`;
5. equality of the first `n` all-success probabilities with `(3)` for the same aperture;
6. stabilization or convergence as the prime aperture grows.

The prime labels themselves need not be exchangeable; they index the source mixture.  Exchangeability
is required only for the auxiliary observation slots whose occupancy count is read from the completed
support packet.  Confusing those two index sets is a route error.

## Hard attacks and positive residues

1. **Finite exchangeability is not infinite extendibility.**  Every symmetric law on `n` bits is
   exchangeable, but many do not extend to `n+1`.
   **Positive residue:** `(7)` is a proof-bearing aperture law.  A failed extension yields an exact
   negative completed occupancy coordinate and identifies the first incompatible support stratum.
2. **Support tomography preserves signed weights, not probabilities.**  The formal boundary theorem
   accepts arbitrary integer word weights.
   **Positive residue:** tomography supplies the sufficient statistic only.  Nonnegativity must be
   created by theta--Euler--Gamma completion before normalization; it is an explicit open core.
3. **The shared Rademacher law has finite latent support.**  Its induced Bernoulli bias lies in
   `{0,1}`, so its moment Hankel matrices have rank at most two and cannot provide all strict minors.
   **Positive residue:** it proves a positive latent-variable realization of the no-go packet and
   forces the completion to create an infinite bias spectrum.
4. **Defining `q_(n,k)` from target moments can be circular.**  Formula `(6)` always computes formal
   finite differences, but their nonnegativity is already a Hausdorff-moment condition.
   **Positive residue:** acceptable `q_(N,n,k)` are defined from completed support weights first;
   `(6)` is proved afterward as the source comparison.
5. **Arbitrary symmetrization discards arithmetic.**  Averaging prime labels can erase their
   logarithmic weights and Gamma coupling.
   **Positive residue:** symmetrize only auxiliary observation slots.  Prime labels and support sets
   stay inside the latent mixing variable until scalar occupancy is read out.
6. **Compact rescaling can hide zero data.**  Choosing `R` from the largest reciprocal divisor atom
   reads the target.
   **Positive residue:** obtain `R` from a source zero-free seam disk or a direct analytic radius
   bound, both available in principle before any zero localization.
7. **Positive semidefinite is not the strict Lean consumer.**  A finite-support de Finetti measure
   gives eventually singular Hankel blocks.
   **Positive residue:** prove the mixing measure has infinite support from a source-side
   nonrationality or no-finite-recurrence theorem for the canonical moment germ.
8. **Finite prefixes do not select RH.**  Consistent laws through any fixed `n` do not force an
   infinite exchangeable extension.
   **Positive residue:** one projective family satisfying `(7)` at every rank is mandatory.

## Low-aperture protocol

Compute `(6)` symbolically through `n=4` using the already-formalized formulas for `m_0,m_1,m_2`
and the next source recurrence.  Do not use approximate zero ordinates.  Each negative `q_(n,k)`
retires the direct scalar occupancy normalization at that aperture.  The positive successor is the
smallest auxiliary latent block whose marginal restores `(7)`; if no source-prescribed block exists,
record the failed finite-difference inequality as the exact no-go theorem.

## Exact open cores

- `[OPEN CORE A]` Construct nonnegative completed occupancy weights from prime-word supports and
  theta--Gamma completion before referencing the canonical moment tower.
- `[OPEN CORE B]` Prove exchangeability and exact deletion consistency for all ranks and apertures.
- `[OPEN CORE C]` Prove the all-success probabilities equal one common compact rescaling of
  `normalizedPrimeArchMoment` at every order.
- `[OPEN CORE D]` Prove the limiting de Finetti measure has infinite support, giving strict rather
  than merely semidefinite Hankel blocks.

## Kill conditions

Retire a construction if its finite laws are defined by inverting the target moments; if it
symmetrizes prime labels rather than auxiliary slots; if consistency holds only through a fixed
rank; if `R` is chosen from zeros; if the Gamma/polar term is omitted; if the limiting mixing law has
finite support; or if finite exchangeability is presented as de Finetti extendibility.

## Parent boundary

De Finetti's theorem, the Hausdorff finite-difference criterion, Kolmogorov extension, and strict
Hankel positivity from infinite support are parent theory.  The only possible proof-bearing content
is the completed source-first projective probability family and its exact comparison with the
canonical prime--arch moment tower.

## Gates

- [x] exchangeable-to-positive-moment-to-RH consumer chain closed
- [x] infinite-support moment-measure consumer and RH capstone formalized in Lean
- [x] exact finite extendibility and deletion equations stated
- [x] formal support tomography and shared-spin positive successor connected
- [x] finite exchangeability, target inversion, hidden-radius, and finite-support attacks stated
- [ ] symbolic rank-four completed occupancy test performed
- [ ] all-rank source probability family constructed
- [ ] projective consistency and moment comparison proved
- [ ] infinite mixing support proved
- [ ] RH capstone composed
