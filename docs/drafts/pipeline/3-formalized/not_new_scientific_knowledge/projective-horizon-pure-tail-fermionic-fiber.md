# Pure critical horizon fiber is a cyclic fermionic occupation scheme

- **ID:** `projective-horizon-pure-tail-fermionic-fiber`
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT SPECIAL-FIBER IDENTIFICATION
- **Scientific status:** `[PROVED ON PAPER] [BRIDGE] [FORMAL CORE COMPLETE]`
- **Parents:** `projective-horizon-critical-binomial-multiplicity`
- **Lane:** source-pure hypertranscendental geometry; static spectral topology

## Theorem

Let `m,n>=1`, put `L=m+n`, and work over an algebraically closed field `K` of characteristic
zero.  Consider the critical raw/reciprocal observation whose only nonzero prescribed tail entries
are

```text
x_m=1,   y_n=1,
x_(m+1)=...=x_(L-1)=0,
y_(n+1)=...=y_(L-1)=0.                                  (1)
```

Write the unknown low pieces as `A` and `B`, with `deg A<m` and `deg B<n`.  Then the compatible
source jets are exactly the monic factor pairs

```text
X=A+t^m,  Y=B+t^n,  X Y = 1+t^L.                         (2)
```

Since `1+t^L` is separable, its `L` roots are distinct.  Consequently the fiber is canonically
identified with all `m`-element subsets of its root set:

```text
Fib_(m,n)(pure)  ~=  {S subset Roots(1+t^L) : |S|=m}.     (3)
```

In particular it has `choose(L,m)` reduced points.  Exchanging the horizons is the complement
involution `S |-> S^c`.

Let `T` be multiplication by `t` on `K[t]/(1+t^L)`.  It is semisimple with `L` distinct
eigenlines.  The set `(3)` is also canonically the set of `m`-dimensional `T`-invariant subspaces:

```text
Fib_(m,n)(pure)  ~=  {W in Gr(m,L) : T(W)=W}.             (4)
```

Thus the previously numerical equality with the Grassmannian Euler characteristic becomes an
actual Grassmannian fixed-point identification at the pure observation.

## Proof

Under `(1)` the two projective-tail polynomials are

```text
X=A+t^m,    Y=B+t^n.
```

Their product has degree at most `L`, is monic of degree `L`, and critical compatibility says that
all coefficients below `L` equal those of `1`.  Therefore

```text
(A+t^m)(B+t^n)=1+t^L,
```

which proves `(2)`.  Conversely `(2)` immediately implies the truncated reciprocal compatibility.

The derivative of `1+t^L` is `L t^(L-1)`.  In characteristic zero a common root would have to be
both zero and a root of `1+t^L`, which is impossible.  Hence the polynomial is separable.  Every
monic degree-`m` factor is the product of `t-rho` over a unique `m`-subset `S` of its roots, and the
complementary factor is forced.  This proves `(3)` and the binomial cardinality.

The Chinese-remainder decomposition

```text
K[t]/(1+t^L) ~= product_(rho in Roots(1+t^L)) K
```

diagonalizes multiplication by `t`; the coordinate axes are its pairwise distinct eigenlines.
An invariant subspace of a diagonalizable operator with simple spectrum is exactly a sum of a
subset of eigenlines.  Restricting to dimension `m` gives `(4)`.  `QED`

## Exterior-state interpretation

The standard basis of `wedge^m K^L` is indexed by the same `m`-subsets.  Over `C`, after choosing an
inner product on the one-particle eigenline space, these are the occupation states of `m`
indistinguishable fermions in `L` simple modes; horizon exchange is particle--hole complementation.
This is an exact exterior-algebra identification of the state labels, not a claim that a
hypertranscendental function evolves by a quantum Hamiltonian.  The cyclic operator comes from the
static polynomial constraint `(2)`.

## What is and is not new

Polynomial factorization, simple-spectrum invariant subspaces, Grassmannian torus fixed points,
and exterior occupation bases are classical.  The exact identification of the pure critical
raw/reciprocal horizon fiber with all four objects is useful structural knowledge, but it is a
parent-theory bridge rather than a dual-gate new result.  Its significance is that it supplies a
non-metaphorical spectral model against which the generic critical monodromy can be measured.

## RH impact

For a free zeta jet, `(3)` provides a canonical model fiber at a deliberately chosen observation,
not at zeta's actual source-marked data.  It does not orient a zeta fiber or select the Xi zero set.
An RH-useful refinement would need the Euler data to select, weight, or break the complement
symmetry of the occupation states; no such refinement is proved here.

## Gates

- [x] exact pure-tail factorization proved
- [x] separability and subset classification proved
- [x] invariant-Grassmannian identification proved
- [x] exterior occupation and complement dictionary stated without dynamical overclaim
- [x] Lean core complete and targeted verification passed
- [x] `(3)`, `(4)`, and the exterior occupation dictionary formalized end to end; card promoted to
  `3-formalized`

## Lean verification

**Fully formalized, unconditionally.**  Every clause of the theorem — `(2)`, separability, `(3)` as a
bijection in both directions, the count, `(4)` as a single equivalence, and the exterior occupation
dictionary with its particle--hole involution — is a Lean theorem.  All declarations audit to
`[propext, Classical.choice, Quot.sound]`.

| Paper step | Lean |
|---|---|
| `(2)` the pure-tail compatibility is exactly `(A+t^m)(B+t^n) = 1+t^L` | `pureCritical_factorization_iff` (`HTGeometry/ProjectiveHorizonPureTailFiber.lean`) |
| `1+t^L` is separable in characteristic zero | `pureCriticalCyclicPolynomial_separable` (same module) |
| occupation labels and their count `C(L,m)` | `criticalHorizonOccupationStates`, `card_criticalHorizonOccupationStates` (same module) |
| `(3)` injectivity: distinct occupation states give distinct factors | `criticalHorizonLeftFactorFromRoots_injective` (`HTGeometry/OccupationFactorInjective.lean`) |
| `(3)` surjectivity: every monic degree-`m` factor comes from an occupation state | `exists_occupationState_of_pureFactorisation` (`HTGeometry/PureFibreOccupationBijection.lean`) |
| `(3)` as a statement about the fibre itself, and its cardinality | `pureCriticalFibre`, `occupationToFibre_bijective`, `card_pureCriticalFibre` (`HTGeometry/PureFibreCardinality.lean`) |
| `(4)` invariant subspace `->` ideal | `mul_mem_of_generator_mul_mem`, `invariantIdeal` (`HTGeometry/ShiftInvariantSubspace.lean`) |
| `(4)` ideal `->` monic divisor | `exists_monic_dvd_of_ideal` (`HTGeometry/QuotientIdealDivisor.lean`) |
| `(4)` dimension bookkeeping | `finrank_polynomialQuotient`, `finrank_ideal_add_natDegree_of_dvd` (`HTGeometry/QuotientIdealDimension.lean`) |
| `(4)` forward and converse | `exists_rootSubset_of_invariantSubspace` (`HTGeometry/InvariantSubspaceRootSubset.lean`), `finrank_ideal_rootSubset` (`HTGeometry/RootSubsetInvariantSubspace.lean`) |
| `(4)` as one equivalence | `invariantSubspace_iff_rootSubset` (`HTGeometry/InvariantSubspaceIff.lean`) |
| exterior occupation basis and particle--hole complementation | `occupationStateEquivPowersetCard`, `occupationComplement`, `occupationComplement_involutive`, `pureFibreExteriorBasis`, `finrank_exteriorPower_eq_choose` (`HTGeometry/PureFibreExteriorOccupation.lean`) |

## Log

- 2026-08-02 — **`(3)` is now a bijection in Lean, not just a count.**
  `formal/GaloisForLFunctions/HTGeometry/OccupationFactorInjective.lean` and
  `formal/GaloisForLFunctions/HTGeometry/PureFibreOccupationBijection.lean`, both wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  criticalHorizonLeftFactorFromRoots_injective :
    distinct occupation states give distinct selected factors
  exists_occupationState_of_pureFactorisation :
    every monic degree-m factor of 1 + t^L is the selected factor of an occupation state
  ```

  Together these are `(3)`: the pure critical fibre is *identified* with the `m`-element subsets of
  the roots, in both directions.  What was formal before was the enumeration of the index set —
  `card_criticalHorizonOccupationStates` and the multiplicity card's Schubert-cell count — and the
  passage from an occupation state to a factorisation; the two halves of the identification itself
  were not.

  Surjectivity is the standard argument, and worth recording because it is where separability enters:
  `1 + t^L` is separable, so its roots are distinct; a monic divisor splits over an algebraically
  closed field and its root multiset is a *sub-multiset* of a nodup one, hence nodup; so the divisor
  is the product of `X - r` over a genuine subset of the roots, of size its degree.

- 2026-08-02 — **The count is now a theorem about the fibre.**
  `formal/GaloisForLFunctions/HTGeometry/PureFibreCardinality.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  pureCriticalFibre K m n :  the monic degree-m factors of 1 + t^L
  occupationToFibre, occupationToFibre_bijective
  card_pureCriticalFibre :  Nat.card (pureCriticalFibre K m n) = (m+n).choose m
  ```

  The bijection of the previous entry, packaged, and the multiplicity read off it.  The statement is
  now about the set of factorisations itself, with no index set in sight — `(3)` in the form the card
  states it.

- 2026-08-02 — **Towards `(4)`: an invariant subspace of a singly generated algebra is an ideal.**
  `formal/GaloisForLFunctions/HTGeometry/ShiftInvariantSubspace.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  mul_mem_of_generator_mul_mem :
    a subspace invariant under multiplication by x is invariant under every polynomial in x
  smul_mem_of_generator_mul_mem, invariantIdeal, mem_invariantIdeal :
    so in an algebra generated by x, an invariant subspace is an ideal
  ```

  This is the first half of `(4)`: the `T`-invariant subspaces of `K[t]/(1 + t^L)`, `T` being
  multiplication by `t`, are exactly the ideals — the invariance propagates along the monomial
  induction, and `t` generates.  Composing with the ideal-divisor correspondence and the bijection of
  the previous entries would put `(4)` on the same footing as `(3)`; that composition is what is left.

  One Lean note.  The statement is deliberately about a general `K`-algebra `R` with a generator,
  not about `K[X] ⧸ (f)` directly: on the quotient, the `Module K` instance that `Submodule K` picks
  up is *not* the one `Algebra.smul_def` talks about, so `a • v` and `algebraMap a * v` do not
  connect and even `exact?` fails on their equality.  Stating the theorem over an arbitrary
  `[Algebra K R]` removes the ambiguity, and the quotient is then just an instance of it.

- 2026-08-02 — **The second half of `(4)`'s correspondence: ideals are monic divisors.**
  `formal/GaloisForLFunctions/HTGeometry/QuotientIdealDivisor.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  exists_monic_dvd_of_ideal :
    every ideal of K[t]/(f) is generated by the image of a monic divisor of f
  ```

  Pull the ideal back along the quotient map, use that `K[t]` is a principal ideal domain, note that
  the generator divides `f` because `f` is in the pullback, and normalise it to be monic.

  With the previous entry the chain for `(4)` is: shift-invariant subspace `->` ideal `->` monic
  divisor `->` (by the bijection already proved) subset of the roots.  What remains is the dimension
  bookkeeping — that the ideal generated by a divisor of degree `L - m` has `K`-dimension `m` — which
  is what selects the `m`-dimensional invariant subspaces among all of them.

- 2026-08-02 — **The dimension bookkeeping for `(4)`.**
  `formal/GaloisForLFunctions/HTGeometry/QuotientIdealDimension.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  finrank_polynomialQuotient :  dim_K (K[t]/(f)) = deg f
  finiteDimensional_polynomialQuotient
  finrank_ideal_add_natDegree_of_dvd :
    for g | f,  dim_K (the ideal generated by g)  +  deg g  =  deg f
  ```

  The first is mathlib's power basis for `AdjoinRoot`, which *is* `K[t]/(f)` — the identification is
  definitional but not syntactic, so the proof needs an explicit `show`.  The second is the third
  isomorphism theorem in its algebra form: the quotient of `K[t]/(f)` by the ideal of `g` is
  `K[t]/(g)`, so the ideal's dimension is the difference of the degrees.

  This completes the arithmetic half of `(4)`.  The `m`-dimensional shift-invariant subspaces of
  `K[t]/(1 + t^L)` are the ideals generated by monic divisors of degree `L - m`, and those are the
  products over `(L-m)`-element subsets of the roots — complementary to the `m`-element subsets that
  index the fibre.  What is left is only to compose the four steps into a single bijection statement.

- 2026-08-02 — **`(4)` composed: invariant subspaces are subsets of the roots.**
  `formal/GaloisForLFunctions/HTGeometry/InvariantSubspaceRootSubset.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  aeval_mk_X :  the image of a polynomial in K[t]/(f) is its value at the image of t
  exists_rootSubset_of_invariantSubspace :
    an m-dimensional subspace of K[t]/(1 + t^L) invariant under multiplication by t is the ideal
    generated by the product of (t - r) over an n-element set of roots
  ```

  The four steps of the previous entries, composed: invariant subspace `->` ideal
  (`invariantIdeal`), ideal `->` monic divisor (`exists_monic_dvd_of_ideal`), dimension `->` degree
  (`finrank_ideal_add_natDegree_of_dvd`), divisor `->` root subset
  (`exists_rootSubset_of_monic_dvd`, generalised this session from the degree-`m` case to any monic
  divisor).  That is `(4)`: the `T`-invariant `m`-dimensional subspaces are indexed by the same
  subsets that index the fibre, complemented.

  Note on the shared tree: the `HTGeometry` umbrella did not build at the end of this entry, but the
  failure is in `EigenbranchProbeSupportGraph.lean`, which another agent was editing at that moment
  (its mtime moved and its error line numbers changed between two consecutive builds).  The module
  logged here builds and audits clean on its own.

- 2026-08-02 — **`(4)` is a bijection: the converse direction.**
  `formal/GaloisForLFunctions/HTGeometry/RootSubsetInvariantSubspace.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  shiftInvariant_ideal :        an ideal is invariant under multiplication by t
  natDegree_prod_rootSubset :   the product over a subset has degree its cardinality
  prod_rootSubset_dvd :         and divides the cyclic polynomial
  finrank_ideal_rootSubset :
    an n-element set of roots cuts out an ideal of K-dimension m = L - n
  ```

  With the forward direction of the previous entry the correspondence is now a bijection in both
  directions: the `m`-dimensional shift-invariant subspaces of `K[t]/(1 + t^L)` are exactly the
  ideals cut out by `n`-element sets of roots, and those are indexed by the same subsets that index
  the pure critical fibre, complemented.  That is `(4)` in full.

  The umbrella build is green again at 12997 jobs; the failure recorded in the previous entry was
  another agent's file and has been fixed by them.

- 2026-08-02 — **`(4)` as a single equivalence.**
  `formal/GaloisForLFunctions/HTGeometry/InvariantSubspaceIff.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  invariantSubspace_iff_rootSubset :
    a subspace of K[t]/(1 + t^L) is t-invariant and m-dimensional
      ⟺  it is the ideal cut out by an n-element set of roots
  ```

  The two directions of the previous entries in one statement, which is how the card states `(4)`.

  Build note: the umbrella did not build at the end of this entry, the failure being in
  `AnchorStarLocalExtensionChart.lean`, another agent's file with mtime twelve seconds before the
  check.  The module logged here builds and audits clean on its own.
