# Prime-source monomer--dimer polynomials and RH

- **ID:** `prime-source-monomer-dimer-matching-limit-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [FORMALIZED SOURCE NO-GO AND REPAIR]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeSupportMultivariateLiftMarker.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordMatchingIncidenceNoGo.lean`,
  `formal/GaloisForLFunctions/RHTower/EulerSquarefreeWickDefect.lean`, and
  `formal/GaloisForLFunctions/XiLaguerrePolya.lean`
- **Statement:** `[CONJECTURE]` The completed prime--theta source admits cofinal finite
  nonnegative monomer--dimer realizations whose rotated matching polynomials converge locally
  uniformly to a zero-free entire factor times centered Xi.  Heilmann--Lieb real-rootedness then
  implies RH.

## Why this is a genuinely different graph detour

The Ihara route uses nonbacktracking cycles and needs a Ramanujan spectral bound.  The present route
uses disjoint interaction edges and needs no adjacency spectral estimate: every finite matching
polynomial with nonnegative dimer activities already has the required one-dimensional zero
geometry.

It is also unrelated to the failed prime-triplet matching/Mertens route.  No matching of integer
states across a cutoff is sought.  “Matching” here means the coefficient system of a finite
monomer--dimer partition polynomial, with the classical Heilmann--Lieb zero theorem as consumer.

## The closed chain

For a finite weighted graph `G=(V,E)` with dimer activities `w_e>=0`, let

```text
P_G(x) = sum_(M matching in G)
           (product_(e in M) w_e) x^(|V|-2|M|).
```

The Heilmann--Lieb theorem puts every zero of `P_G` on the imaginary axis.  Equivalently, after a
constant phase normalization,

```text
Q_G(z) = i^(-|V|) P_G(i z)
```

has only real zeros.  Seek a source-defined cofinal graph family `G_P` such that

```text
finite completed Euler prime-word packet
  -> squarefree multivariate support monomials             [PROVED IN LEAN]
  -> disjoint-support incidence complex
  -> nonnegative dimer edge activities w_(P,e)
  -> exact source Wick/matching coefficient identity
       [OPEN CORE A: every retained coefficient is a matching sum]
  -> monomer--dimer polynomial P_(G_P)
  -> every zero of Q_(G_P) is real                         [HEILMANN--LIEB]
  -> source-normalized locally uniform limit
       A_P Q_(G_P)(z) -> E(z) Xi(z), E entire and zero-free
       [OPEN CORE B: completed prime--Gamma/theta comparison]
  -> E Xi has no nonreal zero
  -> Xi has no nonreal zero
  -> RH.
```

Forced powers of `x` coming from unmatched vertices must be removed explicitly.  Since `Xi(0)>0`,
an unremoved monomer zero at the origin cannot disappear into the limiting Xi factor.  The Gamma
completion may contribute only to the separately controlled zero-free factor `E`.

## The exact source packet and its formal obstruction

The one-variable boundary germ is support-cardinality faithful but not incidence faithful.  Lean
now proves this on the smallest matching example:

```text
A = {[0,1], [2,3]},       B = {[0,1], [0,2]}.
```

Both unit-weight ensembles have identical marked deformation polynomials, hence identical boundary
jets of every order.  In `A` the two supports are disjoint and form a size-two matching; in `B` they
intersect.  Thus no scalar support-cardinality packet can determine even the first nontrivial
matching coefficient.

The positive repair is formalized in the same module.  The sum of squarefree multivariate support
monomials distinguishes `A` and `B`.  The source input must therefore be

```text
multivariate support incidence + scalar boundary grading,
```

not the boundary germ alone.

## The load-bearing new identity: source Wick closure

Let `W_(ij)>=0` be the two-label connected weights extracted from the completed source.  At four
distinct labels the matching model predicts

```text
A_(1234) = W_12 W_34 + W_13 W_24 + W_14 W_23.             (W4)
```

More generally every even support coefficient must be the sum over its perfect and partial
pairings, with the same nonnegative edge weights compatible across apertures.  This is an exact
Wick law, not a metaphor.  The first defect

```text
D_(1234) = A_(1234)
  - W_12 W_34 - W_13 W_24 - W_14 W_23
```

decides whether the pairwise monomer--dimer model is even locally plausible.

For the raw squarefree Euler expansion this test is now exact in Lean.  With local coefficients
`a_0,...,a_3`, its four-support coefficient is one copy of `a_0a_1a_2a_3`, while the three pairings
of its raw two-support coefficients give three copies.  Therefore

```text
D_0123 = -2 a_0 a_1 a_2 a_3.
```

Lean proves that the Wick law holds exactly when one local coefficient vanishes.  The direct raw
Euler-to-dimer identification is therefore closed for a genuine four-prime packet.

The positive remaining statement is a canonical four-interaction.  A live route must construct a
new completed prime--Gamma pair kernel whose matching moments are not the raw multiplicative Euler
coefficients, or test a source-defined stable hypergraph matching polynomial in a class with a
proved stability theorem.  Arbitrary hypergraph matchings are not licensed to inherit
Heilmann--Lieb real-rootedness.

## Why the theta source makes the route plausible but not automatic

Centered Xi has a positive theta-cusp cosine representation.  Its even Taylor coefficients have
the alternating sign pattern naturally produced by a rotated matching polynomial.  This removes a
first sign mismatch, but it does not prove `(W4)` or its all-order analogues.  Positive moments need
not be Gaussian pairing moments, and matching coefficient arrays satisfy strong Newton and
negative-root constraints.

The intended arithmetic mechanism is not to fit a graph to a Taylor section.  Prime-support
incidence supplies candidate vertices and edges, while the theta/Gamma weld supplies their weights
and relative normalization.  A graph found by factoring an already real-rooted Xi approximant is
forbidden.

## Hard attacks and positive successors

1. **Scalar-germ incidence attack.**  Identical complete boundary germs can have different matching
   counts; this is formalized.
   **Positive successor:** retain the squarefree multivariate support packet, also formally proved
   to separate the counterexample.
2. **Non-Gaussian source attack.**  Generic connected four- and higher-prime cumulants violate the
   pairing law `(W4)`.
   **Positive successor:** compute the first source Wick defect.  A nonzero defect is a canonical
   higher interaction; test a stability-preserving hypergraph class or retire pairwise dimers.
3. **Sign attack.**  Dimer activities must be nonnegative.  A negative two-prime completed weight
   cannot be hidden by matching orientation.
   **Positive successor:** separate orientation into the global rotation while keeping activities
   nonnegative.  If an individual activity remains negative under every source-canonical gauge,
   record it as a terminal frustration obstruction.
4. **Arbitrary inverse-graph attack.**  Real-rooted polynomials can be represented by factored or
   Jacobi objects after their roots are known.
   **Positive successor:** require vertices, edges, and weights to be computed from prime words and
   theta moments before the Xi comparison.  No spectral factorization of a Xi section is input.
5. **Taylor-section attack.**  Declaring the first `N` Xi Taylor coefficients to be matching numbers
   merely moves the hyperbolicity problem into an inverse matching assertion.
   **Positive successor:** prove the coefficient identity by disjoint-support counting in the
   source complex, and derive cofinal compatibility from prime-aperture inclusions.
6. **Parity/zero attack.**  Unmatched vertices force powers of the activity and zeros at the origin.
   **Positive successor:** use perfect-matching-balanced graphs or split the monomer factor and prove
   its zeros escape under a source-defined scaling.
7. **Finite-depth attack.**  Agreement through any bounded matching size cannot determine the
   entire finite partition polynomial.
   **Positive successor:** use a triangular schedule with aperture and retained matching depth both
   tending to infinity; each finite graph must be determined completely at its stage.
8. **Thermodynamic-limit attack.**  Convergence of normalized logarithms away from zeros is too weak.
   **Positive successor:** prove nonzero locally uniform convergence of the rotated entire
   polynomials on every compact centered-coordinate set.
9. **Degree/weight escape attack.**  Large edge weights can leave no normal family after rotation.
   **Positive successor:** use the Heilmann--Lieb root bound together with source estimates on the
   maximum weighted degree to select the scale and prove compact normality.
10. **Hypergraph repair attack.**  Higher interactions do not automatically preserve matching
    real-rootedness.
    **Positive successor:** restrict to a multivariate stable hypergraph matching construction and
    prove that the completed-source specialization is stability preserving; otherwise the repair
    is closed.

## First decisive calculation

The raw Euler version of the following calculation is complete and negative.  The next decisive
calculation must use a genuinely completed prime--Gamma pair kernel.  At the first aperture
containing four distinct prime labels:

1. extract the six two-support weights from the multivariate marked source packet;
2. compute the four-support coefficient independently from the completed source;
3. evaluate `D_(1234)` exactly;
4. test all six edge weights for nonnegativity.

If the completed-kernel defect vanishes and the weights are nonnegative, construct the first
genuine source graph and compare its full matching polynomial, not just `(W4)`.  If it retains the
raw nonzero defect, move directly to the narrowly specified stable hypergraph test.  No further
work is permitted on the direct raw-Euler pairwise model.

## Primary parent results

- O. J. Heilmann and E. H. Lieb, *Theory of Monomer--Dimer Systems*,
  <https://doi.org/10.1007/BF01877590>;
- N. Amini, *Stable Multivariate Generalizations of Matching Polynomials*,
  <https://arxiv.org/abs/1905.02264>.

The first supplies the finite imaginary-axis/real-rooted consumer.  The second is only a possible
positive successor after a proved higher-interaction defect; it does not show that the arithmetic
source belongs to its stable hypergraph class.

## Kill conditions

Retire the pairwise route if a source Wick defect is nonzero cofinally or a required edge activity
is negative under every admissible source gauge.  Retire the hypergraph repair if its source
specialization leaves the proved stability class.  Retire the limit if the graph is recovered from
Xi roots, if an origin or Gamma factor bears zeros, if only coefficient/free-energy convergence is
available, or if the normalized limit is not exactly a zero-free factor times Xi.

## Gates

- [x] two-ended monomer--dimer-to-RH chain stated
- [x] support-cardinality incidence blindness formalized
- [x] multivariate support repair formalized
- [x] exact first source Wick-defect formula isolated
- [x] raw squarefree Euler Wick defect computed and direct raw-Euler dimer map retired
- [x] finite Heilmann--Lieb consumer and root-bound role identified
- [ ] completed prime--Gamma four-label Wick defect computed
- [ ] first nonnegative source graph constructed or pairwise route retired positively
- [ ] cofinal source matching identity proved
- [ ] locally uniform rotated matching-polynomial limit identified with zero-free factor times Xi
- [ ] RH capstone formalized
