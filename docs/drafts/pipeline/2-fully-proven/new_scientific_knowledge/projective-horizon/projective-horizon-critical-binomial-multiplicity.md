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

- 2026-08-01 — **The fibre definition is corrected, and a fibre point is shown to be a
  factorization.**  `formal/GaloisForLFunctions/HTGeometry/TruncatedCompatibilityFibre.lean` and
  `MonomialTailFibreEquiv.lean`, axioms `[propext, Classical.choice, Quot.sound]`:

  The `criticalFibre` introduced in the previous entry omitted the degree conditions on the two
  unknown low parts, so it was not the fibre: without `deg A < m` and `deg B < n` the unknowns are
  not the `m + n` coefficients the observation leaves free.  It now carries them, and
  `criticalFibreSwap` is restated as a bijection

  ```text
  criticalFibre K m n U V  ≃  criticalFibre K n m V U,
  ```

  exchanging the two depths together with the two tails.  The depth symmetry is unaffected — the
  compatibility equation is still literally the same one — but the objects it relates are now the
  right ones.

  `criticalFibre_mul_eq` — at a monomial-tail observation a point of the fibre satisfies the **exact**
  factorization

  ```text
  (A + c X^m) (B + d X^n) = 1 + c d X^(m+n),
  ```

  assembling the degree bound, the vanishing of the truncation, and the factorization identity.  So a
  fibre point *is* a factorization of the target into factors of the two depths, which is the
  statement the divisor count of the earlier entries was waiting for.

  What remains to identify the fibre with the divisor set is the converse — that every monic divisor
  of degree `m` arises from exactly one fibre point — which is a degree and leading-coefficient
  computation on the cofactor, and then `(2)` for the monomial-tail family is a statement about the
  fibre itself rather than about divisors.

- 2026-08-01 — **`(2)` proved for the monomial-tail family, at the level of the fibre.**
  `formal/GaloisForLFunctions/HTGeometry/MonomialTailFibreEquiv.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card (criticalFibre K m n (c X^m) (d X^n)) = criticalHorizonMultiplicity m n
  ```

  `nat_card_criticalFibre_monomialTail`, for all nonzero `c` and `d` and all positive depths.  This
  is the card's degree statement itself for this family — not a count of divisors with the
  identification asserted, but a count of the solution set of the observation's compatibility
  equation.

  `fibreToDivisor` sends a fibre point to `c⁻¹ (A + c X^m)`, monic of degree `m` and dividing the
  target, and `fibreToDivisor_bijective` proves it a bijection onto the monic divisors of degree `m`.
  Injectivity is where the earlier work pays: the jet parts agree by cancelling the unit constant,
  and the reciprocal parts then agree by `criticalLowProduct_right_unique`, whose hypothesis
  `A(0) ≠ 0` comes free from `coeff_zero_add_ne_zero_of_dvd`.  Surjectivity is the cofactor
  computation: from `M ∣ P` the cofactor has degree `L - m = n` and leading coefficient `c d`, so
  `c⁻¹` times it has leading coefficient `d`, and subtracting the two monomials leaves parts of the
  required degrees.

  Combined with `nat_card_monic_divisors_monomialTail` the count is `choose(m+n, m)`.  So for
  monomial tails the whole chain — observation, truncated compatibility, exact factorization, divisor
  set, subset count — is Lean, with no intersection theory at any step.

  Unchanged: an observation with a longer tail, where the truncation is not vacuous.

- 2026-08-01 — **Squareness for every observation, and the chain audited.**
  `formal/GaloisForLFunctions/HTGeometry/TruncatedCompatibilityFibre.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `criticalFibre_fst_injective` — for **every** observation whose tails vanish at the origin, the map
  sending a fibre point to the jet's low part is injective.  So the fibre embeds in the `m` free jet
  coefficients, against the `m` conditions the observed reciprocal tail imposes, with no restriction
  on the tail lengths.  The two ingredients are the ones proved earlier: compatibility forces the jet
  to be invertible at the origin, and the reciprocal low part is then determined.

  Audit.  `lake build GaloisForLFunctions.HTGeometry` completes, `12778` jobs, with every module of
  this chain wired into the umbrella:

  ```text
  SplitFactorizationSubsets, SeparableSplitDivisorCount, GenericSplitFibreCount,
  PureCriticalFactorizationCount, MonomialTailFibreCount, TruncatedCompatibilityFibre,
  MonomialTailFibreEquiv.
  ```

  All depend only on `propext`, `Classical.choice`, `Quot.sound`.  The remaining lint errors name
  modules owned by other work (`RHTower.DeningerPrimeBlockGreenSummability`,
  `HTGeometry.SyndeticDenseOrbitLaw`) and the generated indexes, which go stale under concurrent
  edits.

  State of `(2)` on this card.  Proved in Lean: the count for the pure critical target, for every
  separable split target, for the generic target with genericity realised as independent
  indeterminate roots, and — as a statement about the fibre of the observation map itself — for every
  monomial-tail observation.  Proved for every observation: the compatibility equation's exact
  factorization form modulo the horizon, the depth symmetry, and squareness.  Not proved: the count
  for an observation with a longer tail, where the truncation is not vacuous.

- 2026-08-01 — **Towards the count at a long-tail observation: the inverse-jet numerators.**
  `formal/GaloisForLFunctions/HTGeometry/InverseJetNumerator.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  For a one-deep observation the fibre equation can be eliminated to a single polynomial equation in
  the unknown constant term `a`, and its degree is what gives the count.  Inverting a jet with
  constant term `a` puts a power of `a` in each denominator; clearing it leaves the numerators

  ```text
  p_0 = 1,     p_(k+1) = - Σ_(i ≤ k) u_(i+1) a^i p_(k-i),
  ```

  which is `invNumerator`.  `natDegree_invNumerator_le` — the `k`-th numerator has degree at most `k`
  in `a`; each term of the recursion carries `a^i` against a numerator of index `k - i`, so the
  degrees add to at most `k`.  `natDegree_invNumerator_lt` — in particular the numerator at index
  `L - 1` has degree below `L`.

  That degree bound is the point.  For `m = 1` the fibre condition is
  `[X^(L-1)]((a + U)^(-1)) = d` with `d` the observed reciprocal tail coefficient, which clears to

  ```text
  d · a^L - p_(L-1)(a) = 0,
  ```

  of degree exactly `L` whenever `d ≠ 0`, because the subtracted numerator has degree below `L`.  At
  most `L = choose(L,1)` roots follow.  What remains to connect is the identification of the fibre's
  jet coefficient with a root of that polynomial, which is the elimination itself.

  This is the first line of attack on an observation whose tail is **not** monomial, where the
  truncation is not vacuous and the earlier factorization route does not apply.

- 2026-08-01 — **The elimination itself.**
  `formal/GaloisForLFunctions/HTGeometry/InverseJetNumerator.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `pow_mul_eq_invNumerator_eval` — if a family `g` satisfies the coefficient recursion of an inverse
  jet with constant term `a`,

  ```text
  a · g 0 = 1,      a · g (k+1) = - Σ_(j ≤ k) u_(j+1) · g (k-j),
  ```

  then

  ```text
  a^(k+1) · g k = (invNumerator u k).eval a
  ```

  for every `k`.  So each inverse coefficient, cleared of its denominator, **is** the numerator
  polynomial evaluated at the unknown.  That is the elimination the previous entry was missing: the
  recursion satisfied by the fibre's reciprocal coefficients is exactly the recursion defining the
  numerators, and the induction transports it one power of `a` at a time.

  Combined with the degree bound, the one-deep fibre equation `g (L-1) = d` becomes

  ```text
  d · a^L = (invNumerator u (L-1)).eval a,
  ```

  a polynomial equation of degree exactly `L` in `a` when `d ≠ 0`, since the right-hand side has
  degree below `L`.  At most `L = choose(L,1)` solutions follow, and the fibre is determined by `a`
  by the squareness already proved.

  What remains is bookkeeping rather than mathematics: reading the two recursion hypotheses off
  `X^L ∣ (C a + U)(B + V) - 1` by extracting coefficients, which is `Polynomial.coeff_mul` against
  the vanishing of the low coefficients of a multiple of `X^L`.

- 2026-08-01 — **The truncated inverse relation is read off as the recursion.**
  `formal/GaloisForLFunctions/HTGeometry/InverseJetNumerator.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `coeff_eq_zero_of_dvd_X_pow` — a multiple of the horizon has no coefficients below it;
  `coeff_recursion_of_dvd` — hence reading `X ^ L ∣ F G - 1` in each degree below the horizon gives

  ```text
  F(0) G(0) = 1,     F(0) G_(j+1) = - Σ_(i ≤ j) F_(i+1) G_(j-i)      for j + 1 < L,
  ```

  which are exactly the two hypotheses of the elimination.  Peeling the `i = 0` term off the
  convolution (`Finset.sum_range_succ'`) is what separates the unknown constant term from the tail.

  `pow_mul_eq_invNumerator_eval_of_lt` — the elimination in the bounded form the fibre supplies: only
  the recursion in degrees below the horizon is available, and it determines the numerators in those
  degrees.

  So the chain for a one-deep observation is now complete as separate theorems: the fibre condition
  gives the recursion, the recursion gives `a^L · G_(L-1) = (invNumerator u (L-1)).eval a`, the
  observed reciprocal tail fixes `G_(L-1) = d`, and the numerator has degree below `L`.  For `d ≠ 0`
  that is a degree-`L` equation in the unknown jet coefficient, so at most `choose(L,1)` fibre points,
  and the fibre is determined by that coefficient by the squareness proved earlier.

  What is left is to state that composite as one theorem about `criticalFibre`, which is assembly of
  the pieces above and introduces no new mathematics.

- 2026-08-01 — **The elimination polynomial of a one-deep observation.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `oneDeepEquation U d n = C d * X^(1+n) - invNumerator (fun i => U.coeff i) n` is the equation the
  unknown jet coefficient satisfies at a one-deep observation with observed tail `U` and observed
  reciprocal tail coefficient `d`.

  `degree_oneDeepEquation` and `natDegree_oneDeepEquation` — its degree is exactly the horizon length
  `1 + n`, for every nonzero `d` and **every** `U`, however long its tail.  The numerator has degree
  at most `n`, so the leading term `d X^(1+n)` survives.  `oneDeepEquation_ne_zero` follows.

  Note what the tail is not required to do: `U` is arbitrary.  The degree of the elimination
  polynomial does not depend on it, only on the horizon length, which is why this route reaches
  observations that the factorization route cannot.

  With the recursion extraction and the elimination of the previous entries, the fibre's jet
  coefficient is a root of this polynomial, so a one-deep fibre has at most `1 + n = choose(L,1)`
  points.  Assembling that sentence into a single statement about `criticalFibre` is what is left.

- 2026-08-01 — **The first count at a long-tail observation.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card (criticalFibre K 1 n U (C d * X^n)) ≤ 1 + n
  ```

  `nat_card_criticalFibre_one_le`, for every nonzero `d` and **every** observed tail `U` vanishing at
  the origin — with no restriction on its length.  Since `1 + n = choose(1+n, 1)`, this is the bound
  of `(2)` at depth one, at an observation the factorization route cannot reach.

  `isRoot_oneDeepEquation` is the content: a fibre point's jet coefficient is a root of
  `oneDeepEquation`.  The proof runs the chain built over the previous three entries — the fibre
  condition becomes `X^L ∣ F G - 1`, `coeff_recursion_of_dvd` reads off the recursion,
  `pow_mul_eq_invNumerator_eval_of_lt` turns it into the numerator evaluated at the unknown, and the
  observed reciprocal tail fixes the last inverse coefficient at `d`.  The jet's higher coefficients
  drop out because it has degree below one, which is what makes the tail arbitrary.

  The count then follows from injectivity: the fibre embeds in the roots by the squareness proved
  earlier, and a nonzero polynomial of degree `1 + n` has at most that many roots.

  This closes the depth-one case of `(2)` in full generality.  For `m ≥ 2` the elimination is
  multivariate and the same route does not apply; that case is still where the biprojective
  compactification is needed.

- 2026-08-01 — **Towards exactness at depth one: the converse construction.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  The previous entry bounded the depth-one fibre by the roots of the elimination polynomial.  Going
  the other way needs the reciprocal jet reconstructed from a root, and the pieces are now in place.

  `invCoeff` — the inverse coefficients built from a nonzero constant term by the recursion
  `g_0 = a⁻¹`, `g_(k+1) = -a⁻¹ Σ u_(j+1) g_(k-j)`; `mul_invCoeff_zero` and `mul_invCoeff_succ` — they
  satisfy the two hypotheses of the elimination, so `pow_mul_invCoeff_eq` gives
  `a^(k+1) g_k = (invNumerator u k).eval a` for **all** `k`, this time with the recursion available at
  every index rather than only below the horizon.

  `invCoeff_eq_of_isRoot` — hence at a nonzero root of the elimination polynomial the last
  reconstructed coefficient is exactly the observed one, `g_n = d`.  That is the condition the
  reciprocal low part has to satisfy for the reconstructed pair to lie in the fibre.

  What remains for exactness is to assemble the reconstructed coefficients into a polynomial and
  check the truncated compatibility, which is `Polynomial.X_pow_dvd_iff` against the recursion.  With
  that, the depth-one fibre is in bijection with the nonzero roots, and the bound of the previous
  entry becomes an equality whenever the elimination polynomial is separable with no root at zero.

- 2026-08-01 — **The reconstructed jet satisfies the observation's equation.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `invPoly` assembles the reconstructed inverse coefficients into a polynomial, `coeff_invPoly` reads
  them back below the horizon, and

  `dvd_invPoly_compat` — for any nonzero `a` and any observed tail vanishing at the origin,

  ```text
  X^(n+1) ∣ (C a + U) · invPoly u a n - 1.
  ```

  So the reconstructed pair does satisfy the truncated compatibility equation.  The proof is the
  coefficient computation run in the opposite direction to the extraction: peel the constant term off
  the convolution, and the recursion defining `invCoeff` is exactly what makes every coefficient below
  the horizon vanish, the zeroth giving `a · a⁻¹ = 1`.

  With `invCoeff_eq_of_isRoot` from the previous entry, a nonzero root of the elimination polynomial
  yields a jet and a reciprocal jet whose last coefficient is the observed one — the two conditions
  defining a fibre point, up to packaging the degree bounds.  The depth-one fibre and the nonzero
  roots are therefore in bijection, and the earlier inequality is an equality whenever the elimination
  polynomial is separable and does not vanish at zero.

- 2026-08-01 — **Every nonzero root is a fibre point.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `fibreOfRoot` — from a nonzero root of the elimination polynomial, a point of
  `criticalFibre K 1 n U (C d * X^n)`.  The jet is the constant `a`; the reciprocal low part is the
  reconstructed inverse minus the observed tail.

  The three fibre conditions come out as follows.  The jet has degree below one because it is a
  constant.  The reciprocal part has degree below the second depth because the reconstructed inverse
  has degree exactly `n` with leading coefficient `d` — that is `invCoeff_eq_of_isRoot`, the root
  condition — so subtracting `d X^n` drops the degree (`degree_sub_lt`).  The compatibility is
  `dvd_invPoly_compat` after the two monomials cancel.  `degree_invPoly_le` supplies the degree of
  the reconstruction.

  With the previous entries the depth-one fibre and the nonzero roots of `oneDeepEquation` are now in
  bijection: `isRoot_oneDeepEquation` one way, `fibreOfRoot` the other, and the jet coefficient is a
  common invariant.  The count `≤ 1 + n` of the earlier entry is therefore an equality exactly when
  the elimination polynomial is separable with no root at zero, which is the generic case.

  Depth one of `(2)` is complete.  For `m ≥ 2` the elimination is multivariate and this route does
  not apply.

- 2026-08-01 — **Depth one of `(2)` is closed: the fibre is exactly the nonzero roots.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card (criticalFibre K 1 n U (C d * X^n))
      = Nat.card {a : a ≠ 0 ∧ (oneDeepEquation U d n).IsRoot a}
  ```

  `nat_card_criticalFibre_one_eq`, for every nonzero `d` and every observed tail `U` vanishing at the
  origin, with no restriction on the tail's length.  `range_fibre_coeff` states the same as an
  identification of the range: the jet coefficients occurring in the fibre are exactly the nonzero
  roots of a single polynomial of degree the horizon length.

  `coeff_zero_ne_zero_of_fibre` supplies the nonvanishing, and it is not an assumption: compatibility
  forces the jet to be invertible at the origin, which is `coeff_zero_add_ne_zero_of_dvd` proved
  earlier for arbitrary observations.

  So at depth one the fibre count is a root count.  It is at most `1 + n = choose(1+n, 1)` by the
  degree, and equal to it exactly when the elimination polynomial is separable with no root at zero —
  the generic case, and the same shape of condition as the separability that made the monomial-tail
  and generic-target counts work.

  For `m ≥ 2` the elimination is multivariate and this route does not apply.  That case remains the
  one place on this card where the biprojective compactification of sections 2 and 3 is still needed.

- 2026-08-01 — **The dual depth-one case, free from the symmetry; and an audit.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `nat_card_criticalFibre_snd_one_eq` — the same count when it is the **reciprocal** depth that is
  one:

  ```text
  Nat.card (criticalFibre K m 1 (C d * X^m) V)
      = Nat.card {a : a ≠ 0 ∧ (oneDeepEquation V d m).IsRoot a}
  ```

  for arbitrary `V` vanishing at the origin.  This costs two lines, because `criticalFibreSwap` is a
  bijection of fibres and not merely an equality of counts: exchanging the jet with its reciprocal
  turns an observation whose jet tail is a monomial and whose reciprocal tail is arbitrary into one
  of the shape already settled.  The structural form of the depth symmetry pays for itself here.

  Audit.  `lake build GaloisForLFunctions.HTGeometry` completes, `12798` jobs, with every module of
  this card's chain wired in and every result depending only on `propext`, `Classical.choice`,
  `Quot.sound`.

  State of `(2)` on this card.  Proved: the count for the pure critical target; for every separable
  split target; for the generic target; for every monomial-tail observation at the level of the fibre;
  for every observation of jet depth one with arbitrary tail; and, dually, for every observation of
  reciprocal depth one with arbitrary tail.  Proved for all observations: the exact factorization form
  of the compatibility, the depth symmetry, and squareness.  Open: `m, n ≥ 2` with a tail that is not
  a monomial, where the elimination is multivariate and naive Bezout overcounts.

- 2026-08-01 — **Depth one attains the horizon count exactly; and mathlib does have resultants.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `nat_card_criticalFibre_one_eq_horizon` — over an algebraically closed field,

  ```text
  Nat.card (criticalFibre K 1 n U (C d * X^n)) = 1 + n
  ```

  whenever the elimination polynomial is separable and does not vanish at the origin.  Both are the
  generic conditions, and the second is not an extra assumption in spirit: a root at the origin would
  be a jet not invertible there, which compatibility already excludes.  So `(2)` holds **with
  equality** at depth one, for arbitrary observed tails.

  A correction to the earlier entries on this card.  They record multiprojective Bezout as out of
  reach partly because the elimination tools were assumed absent; mathlib in fact has
  `Polynomial.resultant`, the Sylvester matrix, `resultant_eq_zero_iff` over a field,
  `isUnit_resultant_iff_isCoprime`, `resultant_eq_prod_roots_sub` and `discr`.  The separability
  hypothesis above is therefore checkable as a discriminant condition rather than assumed abstractly,
  and the `m = 2` elimination — two equations in two unknowns, eliminate one by a resultant — is no
  longer blocked on missing machinery.  What it still needs is the degree computation for that
  resultant, which is where `choose(L,m)` would have to come from.

- 2026-08-01 — **`(2)` stated in the card's own notation at both unit depths.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card (criticalFibre K 1 n U (C d * X^n)) = criticalHorizonMultiplicity 1 n
  Nat.card (criticalFibre K m 1 (C d * X^m) V) = criticalHorizonMultiplicity m 1
  ```

  `nat_card_criticalFibre_one_eq_multiplicity` and its dual, for any tail vanishing at the origin,
  under the two generic conditions on the elimination polynomial.  The counts proved in the previous
  entries were stated as `1 + n`; these state them against `criticalHorizonMultiplicity`, the card's
  own `(8)`, so the degree claim `(2)` now reads literally at `m = 1` and at `n = 1`.

  The dual form goes through `criticalFibreSwap` again, and the binomial bookkeeping is
  `Nat.choose_symm` — `(1+m).choose m = (1+m).choose 1`.

  Open on this card: `m, n ≥ 2` with a non-monomial tail.

- 2026-08-01 — **The fibre equations at arbitrary depths.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `fibre_eval_invNumerator` — for **any** pair of depths and any observation whose tails vanish to
  their own orders,

  ```text
  (A + U)(0)^(k+1) · (B + V)_k = (invNumerator (A+U)· k).eval ((A + U)(0))      for k < m + n.
  ```

  Every coefficient of the reciprocal jet, cleared of its denominator, is the corresponding numerator
  evaluated at the jet's constant term.  The depth-one results were the case where the jet's constant
  term is its only unknown; here the numerators' coefficients themselves involve the remaining `m - 1`
  unknowns, so the equations of index `n` and above — where the observed reciprocal tail fixes the
  left-hand side — are the fibre's defining polynomial system, in explicit form.

  This is the launching point for `m ≥ 2`: the system is now written down in Lean rather than
  described.  What it does not yet supply is the elimination, which for `m ≥ 2` is multivariate; with
  mathlib's `Polynomial.resultant` available the `m = 2` case is a resultant computation, and the
  count would come from that resultant's degree.

- 2026-08-01 — **The defining system in terms of the observation alone.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `fibre_system` — for any depths, and for each index `n ≤ k < m + n`,

  ```text
  (A + U)(0)^(k+1) · V_k = (invNumerator (A+U)· k).eval ((A + U)(0)),
  ```

  where `V_k` is **observed**.  Above the reciprocal depth the unknown low part contributes nothing to
  the coefficient, so the `m` equations of index `n` and above read entirely in the observation and the
  `m` unknown jet coefficients.

  That is the fibre's defining system as a square polynomial system, with no auxiliary unknowns left
  in it.  Together with the injectivity of a fibre point into its jet — proved earlier for arbitrary
  observations — the fibre embeds in the solution set of this system.  The remaining content of `(2)`
  for `m, n ≥ 2` is exactly the count of that solution set.

- 2026-08-01 — **The reconstruction generalises to any jet.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `dvd_invPoly_compat_general` — for **any** polynomial `F` whose constant term `a` is invertible,

  ```text
  X^(N+1) ∣ F · invPoly F· a N - 1.
  ```

  The earlier version assumed the jet was a constant, which is the depth-one case.  Inspecting the
  proof showed it never used that: what it used was `F(0) = a` and that the higher coefficients of `F`
  are the recursion's data.  So the hypothesis is invertibility at the origin, not degree.

  This is the converse direction for arbitrary depths.  With `fibre_system` giving the forward
  direction — the fibre satisfies the square system in the observation — and this giving the
  reconstruction, a solution of the system with invertible constant term yields a reciprocal jet
  satisfying the truncated compatibility.  What remains to identify the fibre with the solution set is
  the degree bookkeeping on the reconstructed reciprocal part, the analogue of the step that made
  `fibreOfRoot` work at depth one.

- 2026-08-01 — **The fibre is the solution set of the system, at arbitrary depths.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `fibreOfSystem` — given an unknown jet `A` of degree below the jet depth, invertible at the origin,
  satisfying the `m` observed equations of `fibre_system`, the reconstructed reciprocal
  `invPoly - V` has degree below the reciprocal depth and the pair is a point of
  `criticalFibre K m n U V`.

  The degree bookkeeping is where the system is used: for `n ≤ k < m + n` the equation forces the
  reconstructed coefficient to equal the observed `V_k`, so the difference vanishes there; above
  `m + n` both vanish for degree reasons.  `Polynomial.degree_lt_iff_coeff_zero` then gives the bound.
  Compatibility is `dvd_invPoly_compat_general` once the two reciprocal parts recombine.

  With `fibre_system` in the other direction, this closes the reduction: for **any** depths and any
  observation whose tails vanish to their own orders, the fibre of the observation map is exactly the
  set of solutions of an explicit square polynomial system, with the jet coefficient as the
  coordinate and the observed tail as the data.  `(2)` is now a counting statement about that system
  and nothing else — no jets, no truncations, no compatibility conditions remain in it.

  For `m = 1` that count is proved.  For `m ≥ 2` it is the multivariate elimination.

- 2026-08-01 — **`(2)` reduced to a counting problem, at arbitrary depths.**
  `formal/GaloisForLFunctions/HTGeometry/OneDeepFibreBound.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card (criticalFibre K m n U V) = Nat.card (criticalSystemSolutions K m n U V)
  ```

  `nat_card_criticalFibre_eq_solutions`, for **all** depths and every observation whose tails vanish
  to their own orders and whose reciprocal tail has degree below the horizon.
  `criticalSystemSolutions` is the explicit square system: an unknown jet of degree below the jet
  depth, invertible at the origin, satisfying the `m` observed equations.

  Both directions were proved separately in the previous entries; this packages them as a bijection,
  with injectivity from the squareness of the fibre and surjectivity from the reconstruction.  The
  hypotheses that the tails vanish at the origin are derived from their vanishing to their own
  orders rather than assumed.

  This is the natural stopping point of the reduction.  Everything the card's geometry contributes —
  jets, truncated inverses, compatibility, degrees — is discharged, and `(2)` is now a statement about
  the number of solutions of a square polynomial system in `m` unknowns over an algebraically closed
  field.  At `m = 1` that number is proved to be `choose(1+n, 1)`.  At `m ≥ 2` it is the
  multiprojective count the card computes on paper, and the tools for attacking it —
  `Polynomial.resultant` and its degree theory — are in mathlib.
