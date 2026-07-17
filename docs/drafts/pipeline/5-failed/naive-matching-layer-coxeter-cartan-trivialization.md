# Matching depth does not control the Yang--Baxter Hardy trivialization cost

- **ID:** `naive-matching-layer-coxeter-cartan-trivialization`
- **Stage:** 5-failed
- **Type:** ROUTE KILL / FACTORIZING-F-MATRIX PARENT COLLISION
- **Status:** `[FAILED AS STATED] [POSITIVE RELATIVE-F-MATRIX SUCCESSOR]`
- **Parent:**
  `../1-in-progress/quantitative-coxeter-cartan-hardy-trivialization.md`
- **Statement:** Edge-colouring the complete collision graph into `O(n)` matchings does not by
  itself turn the `O(n^2)` Yang--Baxter trivialization problem into `O(n)` uniformly conditioned
  analytic layers.  The missing data are the shifted-basepoint partial-`F` coherence equations;
  scalar sorting-network depth does not control their operator norm or holomorphic singularities.

## The attempted reduction

The complete graph on `n` particle labels has an edge-colouring by `n-1` perfect matchings for
even `n`, and by `n` near-perfect matchings for odd `n`.  Because disjoint two-body operators on
fixed tensor legs commute, the attempted argument was

```text
O(n^2) collision walls
  -> O(n) matchings of disjoint pairs
  -> O(n) constant-cost Cartan layers
  -> exp(O(n)) global frame.
```

Only the first arrow is graph theory.  The second and third arrows are false without additional
coherence and norm estimates.

## Exact failures

1. **Label edges are not adjacent Coxeter generators.**  A transposition `(i,j)` in the adjacent
   presentation has Coxeter length `2(j-i)-1`.  A complete-graph matching therefore contains
   conjugated braid words, not a set of elementary adjacent two-leg gates.

2. **The relevant commutation is shifted.**  For disjoint transpositions `s,t`, the cocycle law
   gives

   ```text
   A^t(z) A^s(z_t)=A^s(z) A^t(z_s),                       (1)
   ```

   not pointwise commutation of two matrices evaluated at the same base point.  Simultaneously
   splitting the unshifted factors does not imply `(1)` and does not make consecutive layers
   cohere.

3. **Depth is not an operator-norm estimate.**  An adjacent odd--even sorting network has `O(n)`
   depth but `n(n-1)/2` gates.  Approximation errors of the `O(n)` tensor factors in one matching
   can add in operator norm.  A scalar parallel-depth bound supplies neither an `O(1)` layer
   condition number nor a fixed central approximation margin.

4. **Nonadjacent comparators hide Coxeter cost.**  Bitonic and related networks lower depth by
   using nonadjacent comparators.  Expanding those comparators in the adjacent braid
   representation restores the omitted word length and shifted evaluation points.

These failures kill the proposed implication from edge-colouring depth to the Alazzawi--Lechner
bound.  They do not prove that every matching-organized construction fails; any surviving version
must solve `(1)` and prove its norm estimates rather than infer them from graph depth.

## Exact parent theory

Maillet--Sanchez de Santos define a factorizing `F`-matrix by

```text
F_(sigma(q)) R_q^sigma = F_q,                              (2)
```

which is the same cocycle-trivialization form as the desired intertwiner.  Their partial-`F`
relations are precisely the cross-layer coherence omitted above.  In their standard construction,
the two-body determinant contains a factor `b(lambda_1,lambda_2)`, and the full determinant is a
product over pairs.  The frame becomes singular at equal spectral parameters, where the
`R`-matrix reduces to the permutation and retains nontrivial isotropy.

The relative HGT/QFT problem is different at exactly this point.  It trivializes the source
scattering cocycle against its collision value `S(0)`, not against the ordinary permutation
cocycle.  Source and target stabilizers then agree on every collision stratum, so the continuous
chamber frame is regular there.  Standard singular factorizing `F`-matrices therefore neither
solve nor refute the relative problem.

## Positive successor

The correct target is

```text
[CONJECTURE]
Construct a collision-regular relative factorizing F-matrix for (S,S(0))
which satisfies the partial-F shifted coherence equations, is holomorphic
on the Alazzawi--Lechner 1/n tube, and has frame and central-inverse norms
bounded by exp(O(n)).                                      (3)
```

The first nontrivial test is `n=3` for the full `O(N)` centralizer in the Brauer basis.  A pure
pairwise half-factor has already failed the `A_2` braid relation, so `(3)` must permit genuine
three-body Brauer coefficients.  Passing this test would expose the first actual cross-layer
correction; failing it would identify the next exact obstruction rather than another sorting
analogy.

## Novelty and significance gate

- Factorizing `F`-matrices, partial-`F` equations, and their standard collision singularities are
  parent theory.
- Continuity and global Lipschitz control of the relative chamber frame follow elementarily from
  collision-stabilizer cancellation and are a correction/frontier sharpening, not major new
  science by themselves.
- The potentially new and significant result is `(3)`, especially a collision-regular Brauer
  `n=3` solution that extends coherently with `exp(O(n))` control.  No such result was located in
  the focused literature audit.

## Primary literature

- J. M. Maillet and J. Sanchez de Santos, *Drinfel'd Twists and Algebraic Bethe Ansatz*,
  <https://arxiv.org/abs/q-alg/9612012>, especially Definition 2.9, Proposition 2.9, Lemma 3.1,
  Remark 3.3, and Proposition 3.6.
- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>, especially equations (5.3)--(5.5) and
  Definition 5.2.

## Gates

- [x] graph-theoretic matching schedule separated from analytic coherence
- [x] shifted-basepoint cocycle failure identified
- [x] operator-norm accumulation failure identified
- [x] factorizing-`F` parent theory located
- [x] naive matching-depth implication retired
- [ ] collision-regular relative partial-`F` equations solved for `O(N)`, `n=3`
- [ ] coherent `n`-particle construction with `exp(O(n))` control
