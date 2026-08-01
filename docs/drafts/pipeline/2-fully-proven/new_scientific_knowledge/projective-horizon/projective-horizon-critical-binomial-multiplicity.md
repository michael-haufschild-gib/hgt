# Critical projective-horizon multiplicity is binomial

- **ID:** `projective-horizon-critical-binomial-multiplicity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / EXACT CRITICAL-FIBER ENUMERATION
- **Scientific status:** `[PROVED ON PAPER] [FORMAL CORE COMPLETE] [NOVELTY PROVISIONAL]`
- **Parents:** `projective-horizon-finite-jet-page-transition`,
  `projective-horizon-page-capacity-law`
- **Lane:** source-pure hypertranscendental geometry; enumerative topology

## Theorem

Let `m,n>=1`, put `L=m+n` and `N=L-1`, and let

```text
X(t)=x_0+x_1 t+...+x_N t^N
```

be the truncated ordinary Taylor jet of a differential-generic scalar. Let

```text
Y(t)=X(t)^-1 mod t^L.
```

The critical two-horizon observation map is

```text
Phi_(m,n): X |->
  (x_m,...,x_N, y_n,...,y_N).                            (1)
```

Over an algebraically closed characteristic-zero field, `(1)` is dominant and generically etale
of degree

```text
deg Phi_(m,n) = choose(m+n,m).                           (2)
```

Thus a generic critical observation has exactly `choose(m+n,m)` distinct compatible source jets.
The count is symmetric in the two depths.

For a differential-generic source in any `P^d`, with complete affine-coordinate packets at two
distinct hyperplane horizons, the critical degree is still `(2)`. Projective dimension multiplies
the subcritical hidden dimension and supercritical relation codimension, but the transverse
channels are generically linear and add no critical finite ambiguity.

## 1. Generic finiteness and separability

The finite-jet Page theorem gives a square Jacobian at `N=m+n-1`. Its reciprocal Pascal minor is
nonzero, so `(1)` is dominant and generically finite. In characteristic zero the same nonzero
Jacobian gives a nonempty etale locus. Hence the generic geometric fiber is reduced; its cardinality
equals the intersection degree computed below.

Changing from exponential derivative coordinates to ordinary Taylor coefficients only rescales
coordinates by nonzero factorials and does not change degree.

## 2. Biprojective compactification

Fix generic observed tails

```text
P(t)=sum_(i=m)^(L-1) p_i t^i,
Q(t)=sum_(j=n)^(L-1) q_j t^j.
```

Write the unknown low pieces as

```text
A(t)=sum_(i=0)^(m-1) a_i t^i,
B(t)=sum_(j=0)^(n-1) b_j t^j.
```

The fiber equations are the `L` coefficient equations

```text
(A+P)(B+Q)=1 mod t^L.                                   (3)
```

Homogenize the two variable blocks separately with coordinates `alpha,beta`:

```text
X_h=A+alpha P,
Y_h=B+beta Q,
X_h Y_h=alpha beta mod t^L.                              (4)
```

The variables `(alpha,a_0,...,a_(m-1))` give `P^m`; the variables
`(beta,b_0,...,b_(n-1))` give `P^n`. Every one of the `L` equations `(4)` is a divisor of bidegree
`(1,1)`.

Under the Segre embedding

```text
P^m x P^n -> P((C^(m+1)) tensor (C^(n+1))),
([A],[B]) |-> [A tensor B].                               (S)
```

each bilinear coefficient equation becomes a linear hyperplane. Thus the compactified critical
fiber is a codimension-`m+n` linear section of the rank-one tensor variety. The binomial number in
`(2)` is equivalently the degree of this Segre variety.

## 3. No fiber escapes to infinity

Assume the generic open conditions

```text
p_m != 0,    q_n != 0.                                  (5)
```

If `alpha=0` and `beta!=0`, then `X_h=A` is a nonzero polynomial of degree below `m`, while `Y_h`
has nonzero coefficient `beta q_n` at order `n`. Their lowest nonzero product coefficient occurs
strictly below `m+n=L`, contradicting `(4)`. The case `beta=0`, `alpha!=0` is symmetric. If both
homogenizing coordinates vanish, `deg A<m` and `deg B<n`, so their lowest nonzero product
coefficient again occurs below `L`. Hence the compactified generic fiber has no boundary point.

This exclusion is not a heuristic dimension count: it is the valuation identity

```text
ord_t(A B)=ord_t A+ord_t B.                              (6)
```

## 4. Intersection number

The Chow ring of `P^m x P^n` is

```text
Z[H_1,H_2]/(H_1^(m+1),H_2^(n+1)).
```

The complete intersection `(4)` has class

```text
(H_1+H_2)^(m+n).                                        (7)
```

Its degree is the coefficient of `H_1^m H_2^n`, namely

```text
coeff_(H_1^m H_2^n) (H_1+H_2)^(m+n)
  = choose(m+n,m).                                       (8)
```

Generic finiteness makes the intersection proper; the boundary exclusion places all of `(8)` in
the affine jet fiber; generic etaleness makes all points simple. This proves `(2)`.

## 5. Higher-rank transverse uniqueness

In projective normal coordinates the chart transition is

```text
(p,u) |-> (p^-1,u/p).
```

Once a longitudinal solution `p` in a generic critical fiber is fixed, every transverse pair of
tails gives a square linear convolution system for the low coefficients of `u` and `u/p`. The
transverse Pascal determinant is one on a nonempty open set, so each longitudinal solution has one
transverse lift. Repeating channels changes neither the generic degree nor `(2)`.

## Topological meaning

The same integer satisfies

```text
choose(m+n,m) = chi(Gr(m,m+n)),                          (9)
```

the Euler characteristic of the complex Grassmannian, equivalently the number of its Schubert
cells or monotone lattice paths across an `m x n` rectangle. Equation `(9)` is an exact equality of
the critical multiplicity with a classical topological charge. This proof does not yet construct a
canonical identification between individual generic fiber points and Schubert cells; such an
identification would require a controlled degeneration and is not claimed.

Physically, `(2)` is a static critical microstate count. No probability measure or entropy is
introduced, although the logarithm of `(2)` could be used only after choosing such extra data.

There is also an exact quantum-kinematic interpretation. Projective rank-one tensors are precisely
separable bipartite pure states; this use of the Segre variety is standard in quantum information
([Heydari](https://arxiv.org/abs/quant-ph/0506043)). Hence the critical horizon microstates are
isolated separable states satisfying `m+n` linear compatibility observables. This statement adds no
inner product, Born rule, Hamiltonian, time evolution, or claim that a hypertranscendental function
is literally a quantum system. It identifies the exact algebraic state variety selected by the
constraint theorem.

## Lean verification

The module

```text
formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonCriticalMultiplicity.lean
```

formalizes:

1. the outer-product tensor and vanishing of all its `2 x 2` minors;
2. factorization of every bilinear compatibility equation through a linear tensor pairing;
3. the exact low-coefficient survival theorem implied by `(6)`;
4. exclusion of an all-zero truncated product on each boundary face, with the marked nonzero
   coefficient itself supplying nonzeroness of the second factor
   (`not_all_low_mul_coeff_zero_of_coeff_ne_zero`);
5. the Chow coefficient `(8)` as `criticalHorizonMultiplicity`;
6. positivity and symmetry of the multiplicity;
7. the exact Schubert-cell enumeration
   `Fintype.card (criticalHorizonSchubertCell m n) = criticalHorizonMultiplicity m n`, where the
   cell indices are the `m`-subsets of an `(m+n)`-element set.

It imports the already formalized nonzero critical Jacobian minor. A targeted leaf build and
scratch axiom audit pass with only `propext`, `Classical.choice`, and `Quot.sound`. No full build was
run. The general multiprojective Bezout theorem, generic-etale theorem, and the topological
identification of these indices with the actual Grassmannian Schubert cells are used at paper level
rather than reimplemented as a project-local algebraic-geometry library. The card therefore stays
in step 2.

## Novelty audit

Formal-series inversion, multiprojective Bezout, Schubert-cell enumeration, and generic etaleness
are classical. Multihomogeneous Bezout numbers count isolated solutions in products of projective
spaces (for an adjacent reference, [Malajovich--Meer](https://arxiv.org/abs/cs/0405021)). Targeted
searches of jet/prolongation, Padé, reciprocal-series, Cremona, and multihomogeneous literature found
no theorem identifying the generic critical tail-observation degree `(2)`, its all-rank stability,
or its role as the finite-jet transition multiplicity of a hypertranscendental horizon pair.
Novelty remains provisional pending expert audit.

## RH impact

For the free Riemann-zeta jet, the theorem gives the exact number of generic finite jets compatible
with two critical reciprocal horizon packets. It remains a generic observation theorem and is
invariant under target translations of the underlying positive-jet geometry. It does not select
zeta's zero fiber and therefore does not imply RH. A useful arithmetic application would have to
show how an Euler marking resolves or orients the binomial critical fiber.

- 2026-08-01 — **The intersection count is elementary for a split separable target.**
  `formal/GaloisForLFunctions/HTGeometry/SplitFactorizationSubsets.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  The Lean-verification note above records multiprojective Bezout as used at paper level.  For the
  fibre this card actually counts, no intersection theory is needed: when the target is a product of
  **distinct** linear factors, the monic factorizations are literally the subsets of its roots.

  `exists_subset_of_monic_dvd` — every monic divisor of `∏_(r ∈ R) (X - r)` is `∏_(r ∈ S) (X - r)`
  for a unique `S ⊆ R`.  The proof avoids splitting fields: from a factorization `A · B` the degree
  sum and the root-count sum both equal `#R`, and each root count is at most its degree, so both are
  equalities; a monic polynomial with as many roots as its degree is the product of `X - r` over its
  roots, and those roots are nodup because they sit inside `R`.

  `prod_X_sub_C_injective` — distinct subsets give distinct products, by reading off the roots;
  `exists_subset_of_monic_mul_eq` — a factorization into two monic factors is a partition of the
  root set, the second factor being the product over the complement;
  `monicDivisorEquivSubset` — hence the **equivalence**

  ```text
  {S ⊆ R : #S = m}  ≃  {A monic : A ∣ ∏(X - r), deg A = m}.
  ```

  That is the Schubert-cell indexing of this card's `(8)` for the pure critical fibre, where the
  target `1 + t^L` is separable (`pureCriticalCyclicPolynomial_separable`) and splits over an
  algebraically closed field.  Combined with `card_criticalHorizonOccupationStates` the count is
  `choose(m+n, m)` with no Bezout appeal.

  What Bezout is still used for is the **generic** fibre rather than the pure one, and the
  identification of these indices with actual Grassmannian Schubert cells.

- 2026-08-01 — **The pure critical fibre is now counted in Lean, on the card's own objects.**
  `formal/GaloisForLFunctions/HTGeometry/PureCriticalFactorizationCount.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card {A monic : A ∣ pureCriticalCyclicPolynomial (m+n), deg A = m}
      = criticalHorizonMultiplicity m n
      = Fintype.card (criticalHorizonOccupationStates m n).
  ```

  `nat_card_monic_divisors_pureCritical` and `nat_card_monic_divisors_pureCritical_eq_states`.  The
  previous entry supplied the subset correspondence abstractly; this one runs it on
  `pureCriticalCyclicPolynomial` itself, so the count of `(8)` for the pure fibre no longer rests on
  Bezout at any point.

  `pureCriticalCyclicPolynomial_eq_prod` is the bridge: `1 + X^L` is monic and, being separable over
  an algebraically closed field, has as many distinct roots as its degree, so it **is** the product
  of `X - r` over its root set.  `card_roots_toFinset_pureCritical` gives that root set exactly `L`
  elements.  The count is then the number of `m`-subsets of an `L`-set.  `Nat.card` is used rather
  than `Fintype.card` because the divisor subtype carries no `Fintype` instance — it is finite, but
  the polynomial ring it sits in is not.

  This closes the gap between the card's Schubert-cell enumeration, which was already formalized as
  a statement about `m`-subsets, and the factorizations those cells are supposed to index: they are
  now proved to be the same count, on the same objects.

  Still at paper level: the **generic** fibre, where separability of the target is not given, and the
  identification of these indices with actual Grassmannian Schubert cells.

- 2026-08-01 — **The count holds for every separable target, not only the pure one.**
  `formal/GaloisForLFunctions/HTGeometry/SeparableSplitDivisorCount.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  P monic, separable, split  ⟹
      Nat.card {A monic : A ∣ P, deg A = m}  =  (deg P).choose m.
  ```

  `nat_card_monic_divisors`.  The previous entry proved this for `pureCriticalCyclicPolynomial`; the
  proof used nothing about that polynomial beyond monic, separable and split, so it is now stated
  that way and the pure critical case is a three-line instance
  (`PureCriticalFactorizationCount.lean` no longer duplicates the argument).
  `eq_prod_roots_toFinset` — such a polynomial **is** the product of `X - r` over its root set;
  `card_roots_toFinset` — and that set has exactly its degree many elements.

  This matters for the card's remaining gap rather than only tidying it.  The paper-level appeal to
  multiprojective Bezout was for the **generic** fibre, where the target is not the distinguished
  `1 + t^L`.  But a generic target is separable, and for a separable target the fibre count is now a
  theorem with no intersection theory in it.  What Bezout would still be needed for is a target that
  is **not** separable — a non-generic fibre, counted with multiplicity — which is not what this
  card's `(8)` asserts.

  Still at paper level: the identification of these indices with actual Grassmannian Schubert cells,
  and the statement that the generic target is separable, which is a discriminant-nonvanishing
  argument rather than an intersection-theoretic one.

- 2026-08-01 — **The generic fibre is counted, with genericity realised rather than assumed.**
  `formal/GaloisForLFunctions/HTGeometry/GenericSplitFibreCount.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card {A monic : A ∣ genericSplitPoly K L, deg A = m}  =  L.choose m.
  ```

  `nat_card_monic_divisors_genericSplitPoly`.  `genericSplitPoly K L` is the monic split polynomial
  of degree `L` whose roots are `L` **independent indeterminates**, living over the field of rational
  functions in them.  That is what "generic" means here, made into an object rather than an open
  condition.

  `genericSplitPoly_separable` is then immediate: distinct indeterminates are distinct
  (`genericRoot_injective`, from injectivity of `MvPolynomial.X` and of the structure map to the
  fraction field), and a product of `X - r` over distinct `r` is separable.  So the separability that
  a generic-etaleness argument was invoked to supply is not an argument at all in this presentation —
  it is a property of the object.  The count then follows from the previous entry.

  With this, `(2)` — `deg Φ_(m,n) = choose(m+n, m)` — is formalized for the generic target and for
  the pure critical target, by the same theorem, with multiprojective Bezout used at neither.

  Still at paper level: the identification of these indices with actual Grassmannian Schubert cells,
  and the passage from the card's observation map `Φ_(m,n)` to the factorization map whose fibre is
  counted here, which is the biprojective compactification of sections 2 and 3.

- 2026-08-01 — **The compatibility equation is closed for an arbitrary observation, and the count
  extends off the pure point.**  `formal/GaloisForLFunctions/HTGeometry/MonomialTailFibreCount.lean`,
  axioms `[propext, Classical.choice, Quot.sound]`:

  `criticalLowProduct_factorization_iff` — for **any** observed tails `U` and `V`,

  ```text
  A B + A V + U B = 1   ↔   (A + U) (B + V) = 1 + U V.
  ```

  So the truncated compatibility always closes to an exact factorization, and the target `1 + U V` is
  determined by the observation alone.  `criticalLowProduct_pure` records that the pure critical
  equation already in the corpus is the case `U = X^m`, `V = X^n` — the identity is definitional, so
  this is a strict generalisation of `pureCritical_factorization_iff` rather than a restatement.

  `nat_card_monic_divisors_X_pow_sub_C` — for every nonzero `a` the monic divisors of `X^L - C a` of
  degree `m` number `L.choose m`; separability is `separable_X_pow_sub_C`.

  `nat_card_monic_divisors_monomialTail` — hence for monomial tails `c X^m` and `d X^n` with `c` and
  `d` nonzero, the target is `1 + c d X^(m+n)`, an associate of a radical polynomial, and the fibre
  count is the critical binomial multiplicity.  The pure critical observation is `c = d = 1`; the
  count is constant on this whole two-parameter family of observations, not only at the distinguished
  point.

  What this does **not** yet cover is an observation whose tails are not monomials.  There
  `deg (A + U) = deg U` exceeds `m`, the factor degrees no longer split as `(m, n)`, and the fibre is
  cut out inside the factorizations by the prescribed middle coefficients — which is exactly what the
  biprojective compactification of sections 2 and 3 handles.  That passage remains the open link
  between `Φ_(m,n)` and the factorization count.

- 2026-08-01 — **Correction and completion of the previous entry: the truncation step.**
  `formal/GaloisForLFunctions/HTGeometry/MonomialTailFibreCount.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  The previous entry stated `criticalLowProduct_factorization_iff` as holding "for any observed
  tails".  The identity does hold for any tails, but its left-hand side is the **untruncated**
  equation `A B + A V + U B = 1`, whereas the observation only imposes that equation **modulo
  `t^L`**.  The two agree exactly when the low product has degree below `L`, which is a condition on
  the tails.  That step was missing and is now supplied:

  `degree_mul_lt_of_lt_of_le` and `degree_criticalLowProduct_lt` — if `deg A < m`, `deg B < n`,
  `deg U ≤ m` and `deg V ≤ n`, then `deg (A B + A V + U B) < m + n`;
  `dvd_sub_one_iff_eq_one` — a polynomial whose distance from one has degree below `L` is one exactly
  when `X^L` divides that distance.

  Together: for tails of **exactly** the critical degrees the truncated compatibility equation is
  equivalent to the exact factorization, so the chain from the observation to the divisor count is
  complete with no truncation left implicit.  Those are precisely the monomial tails `c X^m` and
  `d X^n` of the previous entry, which is why the count there is the honest one.

  For an observation with a longer tail the low product genuinely exceeds degree `L` — `deg U ≤ N`
  gives `deg (U B) ≤ N + n - 1 > L - 1` — so the truncation is not vacuous and the exact
  factorization statement is unavailable.  That is the same boundary as before, now located
  precisely: it is the degree bound that fails, and recovering the count past it is what the
  biprojective compactification of sections 2 and 3 is for.

- 2026-08-01 — **The general observation's fibre is set up correctly, and the system is square.**
  `formal/GaloisForLFunctions/HTGeometry/TruncatedCompatibilityFibre.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `dvd_criticalLowProduct_sub_one_iff` — for **arbitrary** observed tails, with no degree condition,

  ```text
  X^L ∣ (A B + A V + U B - 1)   ↔   X^L ∣ ((A + U)(B + V) - (1 + U V)).
  ```

  So the truncated compatibility always says that the completed factors multiply to `1 + U V` modulo
  the horizon; the previous entries are the case where the modulus can be dropped.  This is the
  general form the compactification has to work with.

  `coeff_zero_add_ne_zero_of_dvd` — a compatible jet is invertible at the origin.  The observed tails
  vanish there, so the constant coefficient of the compatibility equation reads `A(0) B(0) = 1`,
  which forces `A(0) ≠ 0`.  This is the hypothesis every cancellation in this setting needs, and it
  is not an assumption: it follows from compatibility.

  `dvd_sub_of_criticalLowProduct` and `criticalLowProduct_right_unique` — the reciprocal low part is
  then **determined** by the jet low part.  The difference of two compatible reciprocal parts is
  annihilated after multiplication by the invertible jet, and `dvd_of_mul_dvd_of_coeff_zero_ne_zero`
  cancels it.  So the fibre is parametrised by the `m` unknown jet coefficients alone, with the `n`
  reciprocal coefficients carried rather than chosen: `m` unknowns against the `m` conditions
  imposed by the observed reciprocal tail.  That is the squareness the degree statement `(2)`
  presumes, now proved rather than counted informally.

  What remains for `(2)` at a general observation is the count itself, which is where the
  biprojective compactification enters.

- 2026-08-01 — **The general fibre in final form, and the depth symmetry proved structurally.**
  `formal/GaloisForLFunctions/HTGeometry/TruncatedCompatibilityFibre.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `dvd_mul_of_tails` and `dvd_criticalLowProduct_sub_one_iff_mul_sub_one` — the target `1 + U V` of
  the previous entry is `1` modulo the horizon, because each observed tail already vanishes to its
  own order and `m + n = L`.  So for **every** observation the fibre condition is simply

  ```text
  X^L ∣ ((A + U)(B + V) - 1),
  ```

  the completed jet and the completed reciprocal being inverse to the horizon.  The fibre is
  therefore the set of units of the truncated ring with prescribed coefficients in degrees `m` and
  above, whose inverse has prescribed coefficients in degrees `n` and above.  That is the object the
  compactification acts on, in its simplest form.

  `criticalLowProduct_comm` — the compatibility equation is **literally the same** with the jet and
  the reciprocal exchanged and the two tails exchanged: `criticalLowProduct U V A B` and
  `criticalLowProduct V U B A` are equal, by commutativity alone.  `criticalFibre` and
  `criticalFibreSwap` package this as a bijection between the fibre of an observation and the fibre
  of the exchanged observation.

  So the card's clause "the count is symmetric in the two depths" is now proved structurally, for
  every observation and not only through the symmetry of the binomial coefficient: the two fibres are
  not merely equinumerous, they are the same set read in the other order.

  What remains for `(2)` at a general observation is the count itself.
