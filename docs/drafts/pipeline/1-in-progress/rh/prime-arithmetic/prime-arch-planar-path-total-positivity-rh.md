# Prime--Gamma planar path total positivity and RH

- **ID:** `prime-arch-planar-path-total-positivity-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [FORMALIZED RH CONSUMER]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/PrimeArchHankelDeterminantCriterion.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeArchThetaAtomMoments.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeArchThetaHankelDegreeTail.lean`, and
  `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`
- **Statement:** `[CONJECTURE]` The canonical all-order prime--Gamma moment matrix is the path matrix
  of one source-defined locally finite planar directed network with nonnegative edge weights and a
  positive disjoint-path family for every leading minor.  Lindstrom--Gessel--Viennot positivity
  then forces every source Hankel determinant to be positive, which is already equivalent in Lean
  to RH.

## Why this detour is not another finite Hankel test

Lean defines the source matrix

```text
H_n(i,j)=normalizedPrimeArchMoment(i+j)
```

and proves

```text
(for every n, det H_n>0) <-> RiemannHypothesis.             (1)
```

Verifying finitely many determinants does not approach the all-order wall.  A single compatible
planar network is different: every minor of every northwest truncation is simultaneously a sum of
weights of vertex-disjoint path families.  Nonnegative local weights therefore produce the whole
infinite total-positivity hierarchy by one structural theorem rather than by an induction whose
next sign remains open.

The proposed object is static.  Its paths enumerate source constraints; no evolution of Xi or its
zeros is used.

## The two-ended chain

Seek a locally finite acyclic planar network `N_src` with ordered sources `a_i`, ordered sinks
`b_j`, and edge weights written functorially from finite theta atoms, prime powers, and the
archimedean completion.  Require

```text
PathWeight_Nsrc(a_i,b_j)=normalizedPrimeArchMoment(i+j).    (2)
```

Then the closed chain is

```text
positive theta-cusp integer atoms                         [PROVED IN LEAN]
  + completed prime-word boundary germs                  [PROVED IN LEAN]
  -> subtraction-free local cells of N_src
       [OPEN CORE A: source network realization]
  -> exact path identity (2) at every finite depth
       [OPEN CORE B: prime--Gamma comparison]
  -> det H_n = sum_(disjoint n-path families) weight(family)
       [CLASSICAL LGV]
  -> det H_n>0 for every n
       [OPEN CORE C: one positive family per n]
  -> PrimeArchSourceMomentHankelDeterminantsPositive
  -> RH                                                    [PROVED LEAN BY (1)].
```

No limit of determinants is needed at the consumer end: the same infinite network supplies every
finite matrix exactly.  A cofinal construction is allowed only if its cells stabilize on every
finite path window and thereby define one exhaustion-independent network.

## Candidate source cells

1. **Theta atom cells.**  `PrimeArchThetaAtomMoments.lean` decomposes each positive theta-cusp raw
   moment into a sum of nonnegative integer-atom moments.  Treat the atom index as a vertical level
   and multiplication by the logarithmic coordinate as an upward step.
2. **Prime-support cells.**  The complete marked boundary germ recovers every positive support-size
   stratum of a finite prime-word ensemble.  Use support creation as a horizontal step and retain
   the actual squarefree support label until the final sink.
3. **Completion cells.**  Encode the polar and Gamma normalization through local series/parallel
   gadgets only if their effective path weights remain subtraction-free.  A signed scalar
   cancellation is not an admissible positive cell.
4. **Cumulant-to-moment production matrix.**  The corpus has all-order theta-cusp cumulant and
   normalized prime--archimedean moment recurrences.  Search for a tridiagonal or planar production
   matrix whose iterated path weights realize those recurrences without negative edges.

The fourth construction is the shortest finite test.  At each depth, solve the recurrence for the
new local cell weights before evaluating any Xi zero.  A negative forced cell is a decisive
obstruction and identifies the first non-planar source interaction.

The direct recurrence has now failed that test already in the first two nonconstant degrees.  Put
`a_j=thetaCuspNormalizedEvenMoment(j)`.  Lean proves the exact identities

```text
m_0=a_1,
m_1=a_1^2/2-a_2/6,
m_2=a_3/120-a_1 a_2/8+a_1^3/4,                         (3)
```

and consequently

```text
m_0 m_2-m_1^2=a_1 a_3/120+a_1^2 a_2/24-a_2^2/36.      (4)
```

Thus the triangular cumulant recurrence is not subtraction-free in its native theta-moment
coordinates.  This retires the naive production matrix whose vertices are just the successive
`a_j`; it does not retire a planar realization with auxiliary states.  The sharpened positive
target is a source-defined sign-reversing involution or completion gadget in which the negative
terms in `(3)--(4)` cancel internally and the surviving path families have nonnegative weights.
The gadget must prove `(3)` entrywise before any determinant sign is used.

## Hard attacks and positive residues

1. **Target-factorization attack.**  Every already-totally-positive matrix has a planar-network
   factorization.  Constructing that factorization after assuming `(1)` is circular.
   **Positive residue:** local cells must be given directly by theta atoms, prime powers, and the
   completion recurrence; the path identity is proved afterward.
2. **Signed-cumulant attack.**  Moments may be positive while their connected cumulants have mixed
   signs.  The exact low-order formulas `(3)--(4)` contain the forced negative terms
   `-a_2/6`, `-a_1a_2/8`, and `-a_2^2/36`; a signed edge destroys the LGV positivity conclusion.
   **Positive residue:** the naive theta-moment production matrix is retired.  Exhibit a
   subtraction-free auxiliary-state realization or a source-defined sign-reversing involution
   whose residual families give `(3)--(4)`.  Schur complements are allowed only with a separate
   total-positivity preservation proof.
3. **Finite-prefix attack.**  A different finite network for each `n` can encode any positive
   prefix and says nothing about the next determinant.
   **Positive residue:** require stabilization under northwest truncation, giving one locally
   finite network and one source rule for every cell.
4. **Intersecting-path attack.**  The determinant expansion is signed unless planarity and the
   source/sink order make the sign-reversing involution cancel all intersecting families.
   **Positive residue:** the embedding and boundary order are proof-bearing source data, not a
   drawing convention.
5. **Non-strictness attack.**  LGV gives nonnegative determinants; Lean's scalar criterion uses
   strict positivity.
   **Positive residue:** construct one canonical positive disjoint family for every leading minor.
   If rank stabilizes, the route fails and the first missing family gives an exact finite rank
   obstruction.
6. **Raw-theta attack.**  The raw theta moments already form a positive moment sequence, but RH is
   controlled by the normalized completed prime--Gamma moments.
   **Positive residue:** the network must realize `normalizedPrimeArchMoment`, not merely the theta
   input.  The completion cells are the entire arithmetic content.
7. **Coordinate-recoding attack.**  Continued fractions, Jacobi parameters, and planar networks can
   be triangular recodings of the function-complete seam jet.
   **Positive residue:** the network advances the proof only when its local nonnegative weights are
   produced independently from the Euler--Gamma source, not recovered from the target Hankel
   determinants.

## Exact open cores

- `[OPEN CORE A]` Derive a subtraction-free finite-depth production network from the all-order
  theta-cusp cumulant and normalized prime--arch moment recurrences.  The direct triangular
  recurrence is excluded by `(3)--(4)`, so auxiliary states or an internal cancellation involution
  are mandatory.
- `[OPEN CORE B]` Prove that its path weights equal the canonical source moments entrywise and are
  compatible under depth enlargement.
- `[OPEN CORE C]` Prove every leading source/sink family admits at least one positive
  vertex-disjoint routing.
- `[OPEN CORE D]` If a forced negative cell appears, characterize the minimal signed gadget and test
  whether a sign-reversing involution leaves a positive residual family sum.

## Kill conditions

Retire the route if local weights are obtained by factoring an already-positive target matrix; if
some finite source recurrence forces a negative edge and no source-defined cancellation-free
gadget exists; if finite networks are incompatible under truncation; if strict path families cease
at finite rank; or if the path matrix matches only raw theta moments rather than the completed
prime--Gamma source moments.

## Parent results

- S. Fomin and A. Zelevinsky, *Total positivity: tests and parametrizations*,
  <https://arxiv.org/abs/math/9912128>;
- the Lindstrom--Gessel--Viennot nonintersecting-path determinant lemma;
- the Stieltjes moment characterization by total positivity of the infinite Hankel matrix.

## Gates

- [x] source all-order Hankel matrix and RH equivalence formalized
- [x] positive theta atom decomposition formalized
- [x] two-ended planar-network chain and circularity firewall stated
- [x] naive subtraction-free theta-cumulant production matrix excluded at the first two
      nonconstant degrees; positive auxiliary-state target isolated
- [ ] finite-depth subtraction-free production cells constructed
- [ ] truncation compatibility proved
- [ ] exact path-weight/source-moment identity proved
- [ ] positive disjoint family in every rank proved
- [ ] RH capstone composed
