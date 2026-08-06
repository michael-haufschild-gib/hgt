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
tails gives a square linear convolution system for the low coefficients of `u` and `u/p`. That
system is not nonsingular for every `p` — at `p=1` the two transverse observations coincide while
the depths differ, and the system degenerates — but its determinant is a nonzero function of `p`,
equal to one at the unipotent jet `p = 1 + t^m`. So on a nonempty open set of longitudinal
solutions each has exactly one transverse lift, and repeating channels changes neither the generic
degree nor `(2)`.

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

It imports the already formalized nonzero critical Jacobian minor.

The count `(2)` is formalized in several regimes, by a route that avoids multiprojective Bezout
entirely.  All statements below are unconditional Lean theorems with axioms
`[propext, Classical.choice, Quot.sound]`.

**Critical-degree packets, all depths.**  When each observed packet's lowest coefficient is its only
one below the horizon, the truncated compatibility equation closes to the exact factorization
`(A + U)(B + V) = 1 + U V`, so a fibre point is a monic divisor of degree `m` of the target.  Hence

- `CriticalFibreNonempty.nat_card_criticalFibre_eq_card_powersetCard` — the **exact** count for
  *every* such observation, separable or not:
  `Nat.card (criticalFibre K m n U V) = card ((1 + U V).roots.powersetCard m).toFinset`,
  the number of distinct sub-multisets of size `m` of the target's roots;
- `CriticalDegreeTailFibre.nat_card_criticalFibre_criticalTails` — for a separable target those are
  the `choose(m+n,m)` subsets of a set of `m+n` distinct roots, giving `(2)` on the nose;
- `CriticalFibreNonempty.nat_card_criticalFibre_eq_iff_separable` — and separability is **necessary**
  as well as sufficient: the count equals `choose(m+n,m)` *iff* the target is separable;
- `CriticalFibreUpperBound.nat_card_criticalFibre_le` — `choose(m+n,m)` is an unconditional ceiling;
- `CriticalFibreNonempty.nonempty_criticalFibre_criticalTails` — and the fibre is never empty, with
  no separability needed;
- `CriticalFibreNonempty.nat_card_criticalFibre_eq_of_target_eq` — the count depends only on the
  target `1 + U V`;
- `CriticalTargetGenericSeparable.finite_scalings_not_exact` — in every scaling family the count is
  exact off a finite set of scalars, the reciprocals of the critical values of `U V`.

**Depth one, arbitrary packets.**  `CriticalDegreeTailFibre.nat_card_criticalFibre_one_eq_of_tail`
gives the exact count as the number of distinct **nonzero roots** of the depth-one equation, over any
field and with no separability;
`CriticalDegreeTailFibre.nat_card_criticalFibre_one_eq_multiplicity_of_tail`
specialises it to `choose(1+n,1)` for a separable depth-one equation; `OneDepthHankelBound.nat_card_criticalFibre_one_le_of_tail`
gives the sharp bound `choose(1+n,1)` unconditionally, by the Padé–Hankel pencil.  Both dualise to
reciprocal depth one in `SwappedFibreBounds.lean`.

**Both depths two, arbitrary packets.**  `DepthTwoGeneralPacketBound`: the eliminated system is two
equations in `(a₀, a₁)`, and eliminating `a₁` leaves a sextic with leading coefficient `v₂³`.  Hence
`nat_card_criticalFibre_two_two_eq_card_roots` — over **any** field and with **no** separability —
puts the fibre in bijection with the *distinct* roots of that sextic, exactly parallel to the
sub-multiset formula in the critical-degree regime; specialising it gives
`nat_card_criticalFibre_two_two = choose(4,2) = 6` for a separable sextic under the explicit
genericity condition `u₂v₃ + u₃v₂ ≠ 0`; `≤ 6` under the condition alone; and
`nat_card_criticalFibre_two_two_le_of_critical` gives `≤ 12` for **every** critical observation,
from either packet.  This is the first case of the card's open core with both depths above one.

**Every pair of depths: finiteness.**  The product obstruction (`FibrePairProductObstruction`) puts
the product of the jets of any two fibre points on a Padé–Hankel hypersurface
(`PadeHankelObstruction`, `MvHankelHypersurface`), of degree `n` in the `m` unknown jet coefficients.
A choice of `m` fibre points therefore gives a square system, and the elimination tower built in
`MvResultantElimination.lean` — resultants, the weighted determinant degree bound, and the
univariate root count — yields
`AnyDepthCoordinateBound.nat_card_criticalFibre_le_of_towers`:
`Nat.card ≤ m + (n^(2^(m-1)))^m` whenever the towers do not degenerate.  The bound is the classical
doubly-exponential elimination bound, not `(2)`.

**Section 5** is formalized in `TransverseChannelLift.lean` and `TransverseChannelGeneral.lean`:
the transverse channel is a square linear convolution system, and
`injective_transverseDifferential_iff` identifies its nonsingular locus exactly as the complement of
the Padé–Hankel hypersurface `det (padeHankel p m n) ≠ 0`.  Over any jet in that locus a transverse
channel lifts uniquely, so `nat_card_criticalFibre_prod_transverse_channels_of_det` counts one
longitudinal and any number of transverse channels by `criticalHorizonMultiplicity m n` itself.

**What is still open** is the *sharp* count for a fully generic observation with `m, n >= 2`.  There
the completed jet has degree up to `L-1` rather than `m`, the truncated equation no longer closes to
an exact factorization, and the divisor bijection is unavailable.  Every elimination-based bound
above is loose for one structural reason: pairwise elimination discards the bilinearity that makes
the honest answer binomial.  That bilinearity is itself now machine-checked —
`BilinearFibreSystem.degreeOf_bilinSysPoly_inl` and `_inr` prove the pre-elimination system has
bidegree `(1,1)`, and `criticalFibre_coeff_eq` gives its `m+n` scalar equations in explicit bilinear
form — so what remains is exactly the multihomogeneous Bezout count for a bidegree-`(1,1)` system on
`P^m x P^n`, whose hypotheses are now verified and whose conclusion needs intersection theory that
mathlib does not have.

What remains at paper level besides that is only the topological identification of the fibre points
with Grassmannian Schubert cells, which the card explicitly does not claim.

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

- 2026-08-01 — **Degree of the fibre equations in a second unknown.**
  `natDegree_coeff_invNumerator_le` in `InverseJetNumerator.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`: if the first datum of the inverse-jet recursion is
  linear in a second variable and the later data are constant in it, then every coefficient of the
  `k`-th numerator has degree at most `k` in that variable.  At depth two the two fibre equations are
  therefore of degrees `n` and `n + 1` in the second unknown jet coefficient, which is the input an
  elimination between them consumes.

## Log

- 2026-08-02 — **The Schubert-cell indices are now identified with actual pure-fibre points.**
  The Lean verification section above notes that "the topological identification of these indices
  with the actual Grassmannian Schubert cells" was used at paper level.  For the *pure* critical
  fibre that identification is now formal, in
  `formal/GaloisForLFunctions/HTGeometry/OccupationFactorInjective.lean` and
  `formal/GaloisForLFunctions/HTGeometry/PureFibreOccupationBijection.lean`
  (axioms `[propext, Classical.choice, Quot.sound]`):

  ```text
  criticalHorizonLeftFactorFromRoots_injective
  exists_occupationState_of_pureFactorisation
  ```

  so `Fintype.card (criticalHorizonSchubertCell m n) = criticalHorizonMultiplicity m n` is now a count
  of fibre points and not only of indices — for the pure observation.

  What remains at paper level for this card is the *generic* fibre: multiprojective Bezout for the
  upper bound.  The matching lower bound is now formal — `exists_injective_deformed_fibre` in
  `DeformedFibreLowerBound.lean` gives at least `C(L,m)` points over an algebraically independent
  observation, by deforming each pure point.  Note that this direction cannot come from the pure
  count by semicontinuity, which runs the other way.

- 2026-08-06 — **The fibre count no longer needs monomial tails.**
  `formal/GaloisForLFunctions/HTGeometry/CriticalTailFibreCount.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  `nat_card_monic_divisors_criticalTails` — for **arbitrary** tails `U, V` of exactly the critical
  degrees (`deg U ≤ m`, `deg V ≤ n`, with `U.coeff m ≠ 0` and `V.coeff n ≠ 0`), whenever the
  target `1 + U V` is separable its monic divisors of degree `m` number
  `criticalHorizonMultiplicity m n`.  With `natDegree_one_add_mul_of_coeff_ne_zero`: the target has
  degree exactly `m + n`, since the constant `1` cannot reach the top.

  The previous entry proved the count only for the two-parameter family of monomial tails
  `c X^m`, `d X^n`.  This replaces that family by every observation of the critical degrees whose
  target is squarefree — an open condition, so the count now holds on a dense open set of
  observations rather than on a surface inside it.  Separability is the *only* way the tail
  coefficients enter: the proof normalises `1 + U V` by its leading coefficient, which preserves
  both divisors and separability, and then applies the separable-split divisor count.

  What is still open is unchanged and is the card's recorded link: tails **longer** than critical,
  where `deg (A + U)` exceeds `m`, the factor degrees no longer split as `(m, n)`, and the fibre is
  cut out by prescribed middle coefficients — a square bilinear system of `L` equations in `L`
  unknowns whose generic count is the multihomogeneous Bezout number.  Mathlib has no
  multiprojective Bezout theorem.

- 2026-08-06 — **The long-tail case is reduced to a finite-dimensional one: an observation is seen
  only through its first `L` coefficients.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `criticalLowProduct_sub` — the low product changes by `A (V - V') + (U - U') B`;
  `dvd_criticalLowProduct_sub_one_congr` — hence if the two tails agree modulo `X ^ L` they impose
  the *same* truncated compatibility equation;
  `fibre_eq_of_dvd_sub` — so the fibres are literally the same set.

  This is the first step of the passage the card records as open.  However long the observed tails
  are, the fibre over them is the fibre over their truncations below the horizon, so the
  factorization count is a question about a finite-dimensional family of observations rather than
  about tails of unbounded degree.  Combined with the previous entry, the count
  `criticalHorizonMultiplicity m n` is now proved for every observation whose truncated tails have
  exactly the critical degrees and squarefree target — no monomial assumption anywhere.

  What is still missing, and is the whole of the remaining link: tails whose truncations have
  degree strictly between the critical degree and the horizon.  There the substitution
  `A ↦ A + U_low` absorbs the tail's low part into the unknown but *also* moves the target
  `1 + U V`, so the case does not reduce to the previous entry; the fibre is a square bilinear
  system of `L` equations in `L` unknowns whose generic solution count is the multihomogeneous
  Bezout number.  The Chow-ring side of that number is already formalized
  (`criticalHorizonMultiplicity_eq_chowCoefficient`); the geometric side — that a generic square
  system of `(1,1)` forms on `P^m x P^n` has exactly that many solutions — is what mathlib lacks
  and what remains to build.

- 2026-08-06 — **The elimination step: the fibre injects into the space of first components.**
  Same module, axioms `[propext, Classical.choice, Quot.sound]`:

  `criticalLowProduct_eq_affine` — the compatibility equation is affine-linear in the second
  unknown once the first is fixed, `(U + A) B + (A V - 1)`;
  `fibre_snd_unique` — hence for a fixed `A` with `(U + A)(0) ≠ 0` there is **at most one** `B`:
  two solutions differ by a multiple of `X ^ L` of degree below the horizon, so by nothing.

  This cuts the fibre from `L` unknowns to `m`: the count is a question about the first components
  alone.  It uses the corpus's own cancellation lemma
  (`dvd_of_mul_dvd_of_coeff_zero_ne_zero` in `HorizonTruncationCancel.lean`), the precise content
  of "invertible modulo `X ^ L`".

  **Where the remaining count actually sits, stated exactly.**  Bihomogenising, the fibre is the
  common zero locus of `L` forms of bidegree `(1,1)` on `P^m x P^n`, whose dimension is `L` — so
  the expected count is the coefficient of `h1^m h2^n` in `(h1 + h2)^L`, which is
  `criticalHorizonMultiplicity m n` and is already formalized as
  `criticalHorizonMultiplicity_eq_chowCoefficient`.  Under the elimination above the same number
  appears a second way: for fixed `a` the conditions on `b` are linear, given by an
  `(m+n) x (n+1)` matrix of linear forms in `a`, and a solution exists exactly where that matrix
  drops rank.  That locus has codimension `m` in `P^m` — so it is finite — and its degree by the
  Giambelli--Thom--Porteous formula is `C(m+n, n)`, again the critical multiplicity.

  So the missing input is one classical theorem, in either of two equivalent forms: multiprojective
  Bezout for `(1,1)` forms, or the degree of a generic determinantal locus.  Mathlib has neither.
  The elimination step above is what reduces the card's link to that single input, and the
  determinantal form looks the more tractable of the two to build, since it needs only the degree
  of one rank-drop locus rather than an intersection theory for products of projective spaces.

- 2026-08-06 — **The elimination is now unconditional: the fibre injects into the first
  components whenever the target is invertible at the origin.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `criticalFibre` — the fibre as a set;
  `coeff_zero_ne_zero_of_mem_criticalFibre` — on the fibre, `U + A` is **automatically** invertible
  at the origin as soon as `1 + U V` is.  If it were not, the constant term of the equation would
  read `A(0) V(0) = 1` with `A(0) = -U(0)`, i.e. `(1 + U V)(0) = 0`;
  `criticalFibre_fst_injOn` — hence `Prod.fst` is injective on the fibre.

  The previous entry's uniqueness needed the invertibility as a hypothesis; it is now a consequence
  of the single nondegeneracy `(1 + U V)(0) ≠ 0`, which is exactly the condition that the target of
  the factorization is a unit.  So for every observation with that nondegeneracy — no degree
  restriction on the tails, no monomial assumption — the fibre is the graph of a function on a
  subset of the `m`-dimensional space of first components.

  That is the whole of the elimination the biprojective passage needs.  What is left is to count
  the first components: the locus where the `(m+n) x (n+1)` matrix of linear forms in `a` drops
  rank, whose degree is `C(m+n, n)` by Giambelli--Thom--Porteous.

- 2026-08-06 — **The fibre is now presented as a solvability locus in the first components.**
  Same module, axioms `[propext, Classical.choice, Quot.sound]`:

  `exists_snd_iff_linear_solvable` — a first component `A` extends to a fibre point exactly when
  the congruence `(U + A) B ≡ 1 - A V (mod X ^ L)` is solvable with `deg B < n`.  The unknown
  second component enters the equation only through multiplication by `U + A`;
  `criticalFibre_fst_image` — hence the image of the fibre under `Prod.fst` is exactly the set of
  `A` of degree below `m` for which that congruence is solvable.

  With the injectivity of the previous entry, the fibre and this locus have the same cardinality.
  The locus is the rank-drop set of the elimination: multiplication by `U + A` is an `F`-linear map
  from the `n`-dimensional space of second components into the `L`-dimensional space of residues
  modulo `X ^ L`, and solvability says the target `1 - A V` lies in its image, i.e. the augmented
  `L x (n+1)` matrix — whose entries are affine in the coefficients of `A` — has rank at most `n`.

  So the card's remaining link is now a single self-contained statement about matrices of linear
  forms, with every polynomial-side reduction discharged: the degree of the locus where a generic
  `(m+n) x (n+1)` matrix of linear forms in `m+1` homogeneous variables drops rank is
  `C(m+n, n)`.  That degree, and nothing else, is what remains to build.

- 2026-08-06 — **The solvability is now a linear range membership.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `mulTruncMap` — multiplication by a polynomial followed by truncation below the horizon, as an
  `F`-linear map `F[X] →ₗ[F] F[X] ⧸ (X ^ L)`;
  `quot_eq_iff_dvd` — divisibility by the horizon power is equality in the truncated ring;
  `exists_snd_iff_mem_range` — a first component extends exactly when
  `1 - A V` lies in the image of `Polynomial.degreeLT F n` under `mulTruncMap (U + A) L`.

  Together with the injectivity and the image description, the fibre is now *literally* a
  linear-algebra object: an `n`-dimensional source, an `L`-dimensional target, and a rank
  condition whose matrix entries are affine in the coefficients of `A`.

  A note on the route, since the obvious one fails.  Presenting the truncation with
  `Polynomial.modByMonic` requires `(c • p) %ₘ q = c • (p %ₘ q)` to get an `F`-linear map, and
  mathlib has no such lemma; passing instead through the quotient `F[X] ⧸ (X ^ L)` makes linearity
  free, since `Ideal.Quotient.mkₐ` is an algebra map and the composite with `LinearMap.mulLeft` is
  linear by construction.

- 2026-08-06 — **The elimination matrix has full column rank.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `mulTruncMap_eq_zero_iff` — vanishing in the truncated ring is divisibility of the product;
  `eq_zero_of_mulTruncMap_eq_zero` — multiplication by a polynomial invertible at the origin is
  injective on the second components: `X ^ L ∣ (U + A) B` cancels the invertible factor, and
  `deg B < n ≤ L` leaves nothing;
  `disjoint_ker_degreeLT` — the same as disjointness of the kernel from `degreeLT F n`.

  This is what makes the rank-drop locus have the expected codimension.  The elimination matrix is
  `L x n` of full column rank `n`, so the augmented `L x (n+1)` matrix drops rank exactly on a
  locus of codimension `L - n = m` in the `m`-dimensional space of first components — which is why
  the fibre is finite and why its count is the determinantal degree rather than something larger.

  With this the linear-algebra side of the elimination is complete: source, target, injectivity,
  and the range criterion.  The one remaining input is unchanged — the degree of the rank-drop
  locus of a generic `(m+n) x (n+1)` matrix of linear forms, `C(m+n, n)`.

- 2026-08-06 — **The fibre condition is now the degeneracy of an augmented system.**  Same module,
  axioms `[propext, Classical.choice, Quot.sound]`:

  `mem_range_iff_exists_nontrivial` — for an injective linear map, a vector lies in the range
  exactly when the system augmented by that vector has a nontrivial relation;
  `exists_snd_iff_augmented_degenerate` — the polynomial form: `A` extends to a fibre point exactly
  when `(U + A) B = c (1 - A V)` modulo `X ^ L` has a solution with `deg B < n` and `(B, c) ≠ 0`.
  The scalar cannot vanish, since that would force `B = 0` by the injectivity of the previous
  entry.

  This is the last reduction before the count itself.  The fibre is now the locus, in the
  `m`-dimensional space of first components, where an `L x (n+1)` matrix whose entries are affine
  in `A` has a nontrivial kernel — a determinantal condition in the literal sense, with the target
  appearing as one further column.

  Two notes on the route.  Writing the scalar as `C c` rather than `c • ·` makes `ring` blow past
  the heartbeat limit on the expansion step; the scalar-action form goes through by rewriting.  And
  the degree bound must avoid `add_le_add_right` in `WithBot ℕ`, whose covariance instances are
  expensive here — `Polynomial.degree_smul_le` gives it directly.

- 2026-08-06 — **The general framework is tied back to the counted case.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `criticalFibre_eq_factorizations` — for tails of the critical degrees the fibre defined by the
  *truncated* equation is exactly the set of exact factorizations `(A + U)(B + V) = 1 + U V`.  The
  low product cannot reach the horizon, so nothing is lost by truncating.

  This closes the loop: the general fibre of the framework built in the entries above specialises,
  at the critical degrees, to the object whose cardinality is already computed to be
  `criticalHorizonMultiplicity m n`.  The truncated and exact pictures are the same set, not merely
  the same count.

  Note the hypothesis `0 < m + n` is necessary and not cosmetic: at `m = n = 0` the horizon power
  is `X ^ 0 = 1`, which divides everything, so the truncated condition is vacuous while the exact
  one is `0 = 1`.

- 2026-08-06 — **The count is proved outright at depth zero, for arbitrary tails.**  Same module,
  axioms `[propext, Classical.choice, Quot.sound]`:

  `exists_truncated_inverse` — a polynomial invertible at the origin has a truncated inverse of
  degree below the horizon, from the coprimality of `X ^ n` with it and reduction of the Bezout
  cofactor;
  `existsUnique_fibre_depth_zero` — hence at `m = 0` the fibre is a **single point** for every
  observation whose tail is invertible at the origin: the first component must vanish and the
  second is that truncated inverse, unique by the elimination.

  This is the first case of the card's count proved with **no restriction on the tails at all** —
  not monomial, not of critical degree, not truncated.  It is `criticalHorizonMultiplicity 0 n = 1`,
  the degenerate edge of the binomial profile, and it confirms the framework computes the right
  number where the answer is independently known.

  The remaining input is unchanged and now has a sharper shape: what is missing is the count for
  `m ≥ 1`, i.e. the degree of the rank-drop locus of the `(m+n) x (n+1)` matrix.  At `m = 0` that
  locus is a point and the degree is one, which is what this entry proves directly.

- 2026-08-06 — **The observation symmetry, and the second degenerate edge.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `criticalLowProduct_comm` — the low product is symmetric under exchanging the two channels,
  `criticalLowProduct U V A B = criticalLowProduct V U B A`;
  `mem_criticalFibre_swap` — hence a point of one fibre is exactly the swap of a point of the
  other, which is the fibre-level form of the symmetry `C(L, m) = C(L, n)` the multiplicity already
  has;
  `existsUnique_fibre_codepth_zero` — so the count at `n = 0` is also a single point, for every
  observation whose other tail is invertible at the origin.

  Both degenerate edges of the binomial profile are now theorems for arbitrary tails, and they are
  the same theorem seen from the two sides.  The symmetry also halves the remaining work: any count
  proved for `m ≤ n` transfers to `m ≥ n` without a second argument.

- 2026-08-06 — **The two dimensions of the elimination are computed.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `finrank_quotient_X_pow` — the residues below the horizon form an `F`-space of dimension `L`,
  through `AdjoinRoot.powerBasis` for `X ^ L` (the quotient by a monic polynomial is defeq to the
  adjoined root);
  `finrank_degreeLT` — the second components form a space of dimension `n`, through
  `Polynomial.degreeLTEquiv`.

  So the elimination map goes from an `n`-dimensional space to an `L`-dimensional one, injectively.
  That is the numerical content behind the expected codimension: the augmented map adds one
  dimension to the source, and it can drop rank only in codimension `L - n = m`, matching the
  dimension of the space of first components.  With `finrank_quotient_X_pow` holding for every `L`
  including zero, no positivity side conditions are needed.

  These are the coordinates the determinantal count will be written in: `AdjoinRoot.powerBasis`
  supplies a basis of the target and `Polynomial.degreeLTEquiv` one of the source, so the
  elimination becomes an explicit `L x n` matrix and its augmentation an `L x (n+1)` one.

- 2026-08-06 — **The fibre condition is now a kernel condition on one explicit linear map.**  Same
  module, axioms `[propext, Classical.choice, Quot.sound]`:

  `elimMap` — the elimination map on the second components, `degreeLT F n →ₗ[F] F[X] ⧸ (X ^ L)`;
  `injective_elimMap` — it is injective when the first component is invertible at the origin;
  `augmentedMap` — the same map together with a scalar on the target,
  `(degreeLT F n) × F →ₗ[F] F[X] ⧸ (X ^ L)`, with `augmentedMap_apply`;
  `exists_snd_iff_ker_augmentedMap` — a first component extends to a fibre point **exactly when the
  augmented map has nontrivial kernel**.

  This is the determinantal condition in its final form before coordinates.  The source has
  dimension `n + 1` and the target dimension `L`, both computed in the previous entry; the map's
  matrix entries are affine in the coefficients of the first component; and the fibre is in
  bijection with the locus where that matrix drops rank.

  Everything on the polynomial side of the card's open link is now discharged.  What is left is
  purely a statement about a family of matrices of linear forms: the degree of its rank-drop locus,
  `C(m+n, n)`.

- 2026-08-06 — **The fibre condition is a rank deficiency.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `finiteDimensional_degreeLT` — the second components are finite dimensional, through
  `Polynomial.degreeLTEquiv`;
  `ker_ne_bot_iff_finrank_range_lt` — the augmented map has nontrivial kernel exactly when its
  range has dimension below `n + 1`, by rank–nullity on a source of dimension `n + 1`;
  `exists_snd_iff_finrank_range_lt` — hence a first component extends exactly when the augmented
  map drops rank.

  The card's fibre is now, verbatim, the rank-deficiency locus of a family of linear maps indexed
  by the first component, of the shape `(n+1)`-dimensional source into an `L`-dimensional target.
  There is nothing left of the polynomial formulation in the statement.

  The remaining input is the degree of that locus, `C(m+n, n)`: Giambelli–Thom–Porteous, or
  equivalently multiprojective Bezout for `(1,1)` forms.  Its Chow-ring side is already formalized
  here as `criticalHorizonMultiplicity_eq_chowCoefficient`; what mathlib lacks is the geometric
  side.

- 2026-08-06 — **At depth one the elimination is square.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `finiteDimensional_quotient_X_pow` — the truncated ring is finite dimensional, from its power
  basis;
  `exists_snd_iff_range_ne_top_depth_one` — at `m = 1` the augmented map has an `(n+1)`-dimensional
  source **and** an `(n+1)`-dimensional target, so a first component extends exactly when that map
  fails to be surjective.

  This is the first case where the rank condition collapses to a single determinant: choosing the
  power basis of the target and the monomial basis of the source turns the condition into the
  vanishing of one `(n+1) x (n+1)` determinant whose entries are affine in the single unknown
  coefficient of the first component.  Its degree in that unknown is `n + 1 = C(n+1, 1)`, which is
  the critical multiplicity at `m = 1` — so the depth-one row of the binomial profile is a
  one-variable root count rather than an intersection-theoretic one.

  With the two degenerate edges already proved, the profile is now established at `m = 0` and
  `n = 0` and reduced to a one-variable determinant at `m = 1`.

- 2026-08-06 — **Degeneracy is the vanishing of a determinant.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `ker_ne_bot_iff_det_eq_zero` — for a linear map between spaces of the same finite dimension with
  chosen bases, the kernel is nontrivial exactly when the determinant of its matrix vanishes.

  Composed with the depth-one entry, this puts the `m = 1` row of the profile in final form: the
  fibre over an observation is the vanishing locus of one determinant whose entries are affine in
  the single unknown coefficient — a polynomial equation, so the count is a root count.

  The lemma is stated for arbitrary spaces and bases rather than for the case at hand, since the
  same step is what will convert the general rank-drop condition into minors once the two bases
  (`AdjoinRoot.powerBasis` for the target, `Polynomial.degreeLTEquiv` for the source) are wired in.

  Naming note for this toolchain: `Basis` is `Module.Basis`, and
  `Matrix.exists_mulVec_eq_zero_iff` is the bridge from a nontrivial kernel to a vanishing
  determinant.

- 2026-08-06 — **The depth-one fibre is the vanishing locus of one explicit determinant.**  Same
  module, axioms `[propext, Classical.choice, Quot.sound]`:

  `truncBasis` — the power basis of the truncated ring, reindexed by the horizon;
  `elimSourceBasis` — the monomial basis of the second components together with the scalar on the
  target, indexed by `Fin n ⊕ Fin 1`;
  `exists_snd_iff_det_eq_zero_depth_one` — in those bases, a first component extends to a fibre
  point **exactly when an explicit `(n+1) x (n+1)` determinant vanishes**.

  The `m = 1` row of the binomial profile is therefore a one-variable root count: the matrix entries
  are affine in the single unknown coefficient of the first component, so the determinant is a
  polynomial in it, and the fibre is its root set.

  Two elaboration notes, both of which cost a round.  `finSumFinEquiv` cannot have its implicit
  arguments inferred from the reindexed type, since that would require inverting `?a + ?b = n + 1`;
  they must be supplied.  And `ker_ne_bot_iff_det_eq_zero` must be given its two bases explicitly
  in the rewrite, or the `DecidableEq` on the index type is stuck on a metavariable.

- 2026-08-06 — **The degree bound for a determinant of polynomials, and a duplication note.**
  Same module, axioms `[propext, Classical.choice, Quot.sound]`:

  `natDegree_det_le` — for a matrix of polynomials with all entries of degree at most `d`, the
  determinant has degree at most `card ι * d`, by the permutation expansion.

  **This generalises a lemma the corpus already had**: `polynomial_det_natDegree_le` in
  `RHTower/GammaShiftZetaJetFlag.lean` is the same statement and the same proof for the special
  case of `Fin q` indices over `ℂ`.  It was written here before that was found.  The general
  version is what this card needs — the index type of the elimination is `Fin n ⊕ Fin 1`, not a
  `Fin q`, and the field is arbitrary — so the existing lemma could not have been used directly;
  but the RHTower special case can now be re-derived from this one if that area is ever touched.

  For the next step the corpus has the right tool and it should be used rather than rebuilt:
  `coeff_det_of_column_natDegree_le` in `ColumnDegreeDeterminant.lean` computes the **leading
  coefficient** of a determinant under per-column degree bounds, as the determinant of the matrix
  of leading coefficients.  That is exactly what shows the depth-one determinant has degree
  *exactly* `n + 1` rather than at most, which is what turns the upper bound into the count.

- 2026-08-06 — **Retraction: the entries above from `criticalFibre` onwards duplicated existing
  work, and the module has been removed.**

  `TruncatedCompatibilityFibre.lean` has held the general fibre framework since earlier work on
  this card, with several of the *same names*:

  ```text
  criticalLowProduct_comm            criticalFibre            criticalFibreSwap
  coeff_zero_add_ne_zero_of_dvd      criticalLowProduct_right_unique
  criticalFibre_fst_injective        eq_zero_of_dvd_of_degree_lt
  dvd_criticalLowProduct_sub_one_iff
  ```

  and `OneDeepFibreBound.lean` already proves the depth-one count —
  `nat_card_criticalFibre_one_le`, "the fibre of a one-deep observation has at most the horizon
  length many points, for any observed tail whatever" — by an explicit elimination polynomial
  (`oneDeepEquation`, `degree_oneDeepEquation`, `isRoot_oneDeepEquation`) rather than by the
  linear-algebra route built above.

  `criticalLowProduct_comm` and `criticalFibre` were declared twice in the same namespace, both
  reachable from the umbrella: a genuine collision, invisible here only because the area build has
  been failing on an unrelated in-flight module.  `CriticalTailFibreCount.lean` has been deleted
  and unwired; `TruncatedCompatibilityFibre` and `OneDeepFibreBound` build clean.

  What was genuinely new in the deleted module, and may be worth re-adding under non-colliding
  names once checked against the corpus properly: the count for arbitrary tails of the critical
  degrees with squarefree target; the truncation-invariance of the fibre; the depth-zero
  `∃!` statement; and the linear-algebra presentation (`mulTruncMap`, `elimMap`, `augmentedMap`,
  the rank and determinant criteria, the two `finrank` computations).  A salvage copy is kept
  outside the tree.

  The card's open link is unchanged by any of this and is what it was before: the count for
  `m, n ≥ 2`, where the corpus has the depth-one row and both degenerate edges but not the general
  determinantal degree.

- 2026-08-06 — **The critical-degree case no longer needs monomial tails.**
  `formal/GaloisForLFunctions/HTGeometry/CriticalDegreeTailFibre.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  `criticalFibre_mul_eq_of_degree_le` — for **any** tails of exactly the critical degrees, a fibre
  point satisfies the exact factorization `(A + U)(B + V) = 1 + U V`.  The truncation is vacuous at
  those degrees, so the compatibility equation closes on the nose;
  `degree_leadingCoeff_add_tail` — and the completed jet has degree the first depth with the
  observed leading coefficient.

  These are the two facts `MonomialTailFibreEquiv` uses to build its bijection with the monic
  divisors of the target, stated without the monomial assumption: that file's proofs use of the
  tails only their degrees.  What remains to lift `nat_card_criticalFibre_monomialTail` to all
  critical-degree observations is the bijection itself, with `1 + U V` in place of
  `1 + c d X^(m+n)`, and the count of its monic divisors, which needs `1 + U V` separable — an open
  condition on the observation rather than the closed one of being monomial.

  Frontier note, recorded because an earlier entry on this card understated it: with
  `nat_card_criticalFibre_eq_solutions` the general case is already reduced to counting solutions
  of the explicit square system `a^(k+1) V_k = (invNumerator u k)(a)` for `n ≤ k < m + n`.  Depth
  one is settled exactly (`nat_card_criticalFibre_one_eq_multiplicity`).  The count for
  `m, n ≥ 2` is the only remaining mathematical content.

- 2026-08-06 — **The fibre-to-divisor map for arbitrary critical-degree tails.**  Same module,
  axioms `[propext, Classical.choice, Quot.sound]`:

  `criticalTailToDivisor` — a fibre point of a critical-degree observation gives a monic divisor of
  `1 + U V` of degree the first depth, by scaling the completed jet by the inverse of its leading
  coefficient;
  `criticalTailToDivisor_injective` — and the divisor determines the fibre point, through the
  corpus's own `criticalFibre_fst_injective`.

  This is the monomial-tail bijection of `MonomialTailFibreEquiv` with the monomial assumption
  removed from the half that does not need it.  What is left for the full count at these degrees is
  surjectivity — that every monic divisor of the right degree arises — and then the divisor count,
  which is `C(m+n, m)` exactly when `1 + U V` is separable.

- 2026-08-06 — **The target of a critical-degree observation.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `degree_leadingCoeff_target_tail` — for arbitrary tails of exactly the critical degrees,
  `1 + U V` has degree the horizon `m + n` and leading coefficient the product of the two observed
  leading coefficients.  The constant `1` cannot reach the top, and the leading coefficient is the
  product because the two tails have exactly their nominal degrees.

  This is the general form of `degree_leadingCoeff_target` in `MonomialTailFibreEquiv`, which
  states the same for the monomial target `1 + c d X^(m+n)`; the name is kept distinct.

  It is the last ingredient for surjectivity of `criticalTailToDivisor`: given a monic divisor `M`
  of degree `m`, the cofactor has degree exactly `n` and leading coefficient the observed one, so
  scaling `M` by `U.coeff m` and the cofactor by its inverse produces a fibre point whose two
  components have the required degrees.

- 2026-08-06 — **The fibre of a critical-degree observation is exactly its set of monic divisors.**
  Same module, axioms `[propext, Classical.choice, Quot.sound]`:

  `criticalTailToDivisor_surjective` — every monic divisor of `1 + U V` of degree the first depth
  arises from a fibre point.  Given such a divisor `M`, its cofactor has degree exactly the second
  depth and leading coefficient the observed one, so scaling `M` by `U.coeff m` and the cofactor by
  the inverse gives a pair whose components sit below their depths, and whose exact factorization
  is the compatibility equation.

  With the injectivity already proved, the fibre-to-divisor map is a bijection for **arbitrary**
  tails of the critical degrees.  That is `MonomialTailFibreEquiv`'s theorem with the monomial
  hypothesis removed: what the argument needs of the tails is only that they attain their nominal
  degrees.

  All that now separates this from the count `criticalHorizonMultiplicity m n` at these degrees is
  the number of monic divisors of `1 + U V` of degree `m`, which is `C(m+n, m)` exactly when the
  target is separable — the same divisor count the monomial case uses, applied to a general target.

- 2026-08-06 — **The count holds at the critical degrees for arbitrary tails.**  Same module,
  axioms `[propext, Classical.choice, Quot.sound]`:

  `nat_card_monic_divisors_of_separable` — the monic divisors of a **not necessarily monic**
  separable polynomial, of a prescribed degree, are counted by the binomial coefficient of its
  degree; normalising by the leading coefficient changes neither the divisors nor separability;
  `nat_card_criticalFibre_criticalTails` — hence

  ```text
  Nat.card (criticalFibre K m n U V) = criticalHorizonMultiplicity m n
  ```

  for **every** observation whose two tails have exactly the critical degrees and whose target
  `1 + U V` is separable.

  This closes the generalisation begun four entries ago: `nat_card_criticalFibre_monomialTail`
  required the tails to be the monomials `c X^m` and `d X^n`; the count now holds on the open set
  where the target is squarefree, which contains that two-parameter family.  Separability is the
  only condition the tail coefficients enter through.

  The card's remaining mathematical content is unchanged and is now the whole of it: for tails
  **longer** than the critical degrees, `nat_card_criticalFibre_eq_solutions` reduces the count to
  the solutions of the explicit square system, settled at depth one and open for `m, n ≥ 2`.

- 2026-08-06 — **An observation is seen only through its coefficients below the horizon.**  Same
  module, axioms `[propext, Classical.choice, Quot.sound]`:

  `criticalLowProduct_sub_tails` — changing the tails changes the low product by
  `A (V - V') + (U - U') B`;
  `dvd_criticalLowProduct_of_dvd_sub_tails` — so tails agreeing to the horizon impose the *same*
  compatibility equation;
  `criticalFibreCongr` — hence the fibre of an observation is equivalent to the fibre of its
  truncation, by the identity on the underlying pairs.

  This is what makes the general count a finite-dimensional question: a tail of any length imposes
  the same condition as its truncation below `X ^ (m+n)`, so the space of observations that matters
  is the space of pairs of truncated tails, not of tails of unbounded degree.  The corpus had no
  such statement.

  Combined with the previous entry, the position on this card is now: the count is proved for every
  observation whose truncated tails have exactly the critical degrees and squarefree target, and
  reduced — by `nat_card_criticalFibre_eq_solutions` — to an explicit square system otherwise,
  settled at depth one and open for `m, n ≥ 2`.

- 2026-08-06 — **The count for observations of any tail length.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `nat_card_criticalFibre_of_truncation` — an observation is counted by
  `criticalHorizonMultiplicity m n` as soon as its **truncation** below the horizon has the
  critical degrees and a separable target, with no bound whatever on the degrees of the observed
  tails themselves.

  This is the card's open link discharged for the whole class of observations whose truncated tails
  are critical.  The entry that opened this link recorded the obstruction as "an observation whose
  tails are not monomials, where `deg (A + U) = deg U` exceeds `m` and the factor degrees no longer
  split as `(m, n)`" — that is now exactly the class this theorem covers, because the excess of the
  tail beyond the horizon is invisible to the fibre.

  What genuinely remains is narrower than the card's text suggests: observations whose *truncations*
  have degrees strictly between the critical degrees and the horizon.  For those the factorization
  is not exact and `nat_card_criticalFibre_eq_solutions` applies, settled at depth one and open for
  `m, n ≥ 2`.

- 2026-08-06 — **The separability hypothesis is satisfiable, and the monomial case is an instance.**
  Same module, axioms `[propext, Classical.choice, Quot.sound]`:

  `separable_C_mul` — separability survives a nonzero scalar multiple.  Mathlib has no such lemma;
  the coprimality witnesses are rescaled by the inverse;
  `separable_one_add_C_mul_X_pow` — a monomial target `1 + e X ^ L` is separable in characteristic
  zero, being a scalar multiple of `X ^ L - C a` with `a` nonzero.

  This settles that the count proved above is not vacuous: the monomial observations, whose count
  `nat_card_criticalFibre_monomialTail` already gives, satisfy its hypothesis.  So the general
  theorem contains the known one rather than running alongside it, and the open set of separable
  targets is nonempty.

  `separable_C_mul` is worth noting on its own: it is used twice here (once inside the divisor
  count, once for the monomial instance) and is a general-purpose gap in mathlib's `Separable` API.

- 2026-08-06 — **Depth one holds for an arbitrary observed reciprocal tail.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `criticalSystemSolutionsCongrOne` — at depth one the observation's square system reduces to the
  single index `k = n`, so it reads the reciprocal tail only through `V.coeff n` and two tails
  agreeing there have the same solution set;
  `nat_card_criticalFibre_one_eq_multiplicity_of_tail` — hence the depth-one count
  `criticalHorizonMultiplicity 1 n` holds for **every** reciprocal tail with that coefficient
  nonzero, not only for the monomial `C d * X ^ n` the corpus's theorem assumes.

  The corpus proved depth one for arbitrary *jet* tails but a monomial *reciprocal* tail; this
  removes the remaining monomial hypothesis there, by transporting along
  `nat_card_criticalFibre_eq_solutions` in both directions and observing that only one coefficient
  of the tail ever enters the system.

  Between this and the critical-degree count, the profile is now established: at `m = 0` and
  `n = 0` outright; at `m = 1` and `n = 1` for arbitrary tails; and at all `(m, n)` for
  observations whose truncated tails attain the critical degrees with separable target.  What
  remains is `m, n ≥ 2` with truncations strictly between the critical degrees and the horizon.

- 2026-08-06 — **Correction: the resultant's vanishing criterion is in mathlib.**
  `Polynomial.resultant_eq_zero_iff` (`RingTheory/Polynomial/Resultant/Basic.lean`) states, over a
  field, `f.resultant g = 0 ↔ (f ≠ 0 ∨ g ≠ 0) ∧ ¬ IsCoprime f g`, and this corpus already uses it
  (`separable_of_resultant_ne` in `U0/U0PhiCard.lean`).

  An earlier note here recorded it as missing and proposed building it from the Sylvester matrix.
  That was wrong: the declaration sits at line 908 of a 900-line file and a truncated listing of
  that file's declarations cut off before reaching it.

  The practical consequence is favourable: elimination for the remaining case needs no new
  infrastructure.  What is still genuinely absent is the *multivariate* step — eliminating one
  unknown at a time from the square system for `m, n ≥ 2` and controlling the degrees, for which
  the resultant criterion is the tool rather than the obstacle.

- 2026-08-06 — **The fibre's system is natural in the coefficient ring.**
  `formal/GaloisForLFunctions/HTGeometry/InverseJetNumeratorMap.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  `invNumerator_map` — a ring map carries the numerators of a jet to the numerators of the image
  jet, by induction on the defining recursion;
  `eval_invNumerator_map` — and the same after evaluation.

  This is what allows the square system of `nat_card_criticalFibre_eq_solutions` to be written
  **universally**, over a polynomial ring in the unknown jet coefficients, and then specialised at
  a point: the system over the ground field is the image of the universal one.  Without it the
  system exists only pointwise and no elimination theory can be applied to it.

  With `Polynomial.resultant_eq_zero_iff` available in mathlib, that is the shape the remaining
  case needs: the equations as elements of `MvPolynomial (Fin m) K`, eliminated one unknown at a
  time.

- 2026-08-06 — **The observation's system, as a universal polynomial system.**
  `formal/GaloisForLFunctions/HTGeometry/UniversalFibreSystem.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  `jetVar` — the coefficients of the completed jet as elements of `MvPolynomial (Fin m) K`: a
  variable shifted by the observed tail below the first depth, a constant above it;
  `eval_jetVar` — specialising at a candidate jet returns the completed jet's coefficient;
  `fibreSysPoly` — the `k`-th equation of the square system as a polynomial in the unknown jet
  coefficients;
  `eval_fibreSysPoly` — specialising it returns the `k`-th equation of
  `criticalSystemSolutions`.

  The fibre's defining conditions are now finitely many polynomials in finitely many variables over
  the ground field, so the count is an ordinary question about their common zeros.  Together with
  the naturality of the previous entry, and with `Polynomial.resultant_eq_zero_iff` available in
  mathlib, the elimination for `m, n ≥ 2` has all its ingredients present; what remains is to
  perform it and control the degrees.

- 2026-08-06 — **The fibre is the common zero locus of the universal system.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `eval_fibreSysPoly_eq_zero_iff` — an equation of the universal system vanishes at a candidate jet
  exactly when the observation's corresponding equation holds there;
  `mem_criticalSystemSolutions_iff` — hence membership in `criticalSystemSolutions` is exactly:
  the jet's constant term does not vanish, and the `m` universal polynomials all vanish.

  Chained with the corpus's `nat_card_criticalFibre_eq_solutions`, the card's `(2)` is now the
  count of points of an explicit affine variety: the common zeros of `m` polynomials in `m`
  variables over the ground field, off the hypersurface where the jet's constant term vanishes.
  Every step from the observed jet down to that variety is machine-checked.

  This is the form in which the remaining case `m, n ≥ 2` should be attacked: eliminate one
  variable at a time with `Polynomial.resultant_eq_zero_iff`, which mathlib supplies, and control
  the degrees along the way.

- 2026-08-06 — **The degrees of the universal system.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `totalDegree_jetVar_le` — each coefficient of the completed jet is of total degree at most one in
  the unknowns;
  `totalDegree_eval_invNumerator_jetVar_le` — the evaluated numerator of index `k` has total degree
  at most `k`, by induction on the recursion: each term carries one tail coefficient, a power of the
  jet's constant term, and a numerator of smaller index, and the exponents add to `k`;
  `totalDegree_fibreSysPoly_le` — hence the `k`-th equation of the system has total degree at most
  `k + 1`.

  So the observation's square system consists of `m` equations of total degrees at most
  `n + 1, …, n + m` in `m` unknowns.  This is the first degree control on it, and it is what any
  elimination must consume: the naive Bezout product of those degrees far exceeds `C(m+n, m)`, so
  the count cannot follow from degrees alone — the multihomogeneous structure has to be used.  That
  is now a statement about an explicit polynomial system rather than about jets.

- 2026-08-06 — **The system in its bilinear form.**
  `formal/GaloisForLFunctions/HTGeometry/BilinearFibreSystem.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  `univA`, `univB` — the unknown jet and unknown reciprocal as universal polynomials whose
  coefficients are the two groups of variables;
  `bilinSysPoly` — the `k`-th equation of the observation as the `k`-th coefficient of the low
  product against one, over `MvPolynomial (Fin m ⊕ Fin n) K`;
  `univA_coeff`, `degree_univA_lt` — the universal jet has the variables as its coefficients and
  degree below the first depth.

  The point of this form: before elimination the compatibility equation is **bilinear** — the jet
  and the reciprocal enter linearly, coupled only through their product — so the `m + n` equations
  have bidegree one in each group of unknowns and their count is the multihomogeneous Bezout
  number `C(m+n, m)`.  The square system of the previous module, obtained by eliminating the
  reciprocal, has degrees `n+1, …, n+m` whose product far exceeds that; the structure carrying the
  answer is visible only before elimination.

  This is the system the remaining case `m, n ≥ 2` should be counted in.

- 2026-08-06 — **Specialising the bilinear system.**  Same module, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `jetOfPoint`, `recipOfPoint` — the jet and reciprocal determined by a point of affine space;
  `map_univA`, `map_univB` — the universal unknowns specialise to them;
  `map_map_C` — the observed tails are unchanged by the round trip through the polynomial ring;
  `map_criticalLowProduct` — the low product is natural in the coefficient ring;
  `eval_bilinSysPoly` — hence evaluating the `k`-th universal equation at a point returns the
  `k`-th coefficient of the observation's low product against one, for the jet and reciprocal that
  point names.

  The bilinear system is therefore a faithful universal model of the fibre: its common zeros in
  `A^(m+n)`, cut by the `m + n` equations of bidegree one in each group of unknowns, are exactly
  the pairs satisfying the truncated compatibility equation.  Both halves of the picture are now
  machine-checked — the eliminated square system in `m` unknowns of rising degree, and the bilinear
  system in `m + n` unknowns whose Bezout number is the answer.

- 2026-08-06 — **The count is an unconditional ceiling, and it is attained generically.**  Two new
  modules, both in the umbrella, both `[propext, Classical.choice, Quot.sound]`:

  `CriticalFibreUpperBound.lean` — `monicDivisor_roots_injective` (a monic split polynomial is
  determined by its root multiset), `roots_mem_powersetCard`, `finite_monic_divisors`,
  `nat_card_monic_divisors_le` (a split polynomial has at most `choose` many monic divisors of a
  prescribed degree), and **`nat_card_criticalFibre_le`**: for *every* observation with tails of the
  critical degrees — no separability, no genericity — the fibre has at most
  `criticalHorizonMultiplicity m n` points.  The separable case is where the injection into monic
  divisors is onto the whole sub-multiset lattice; in general a repeated root of the target merges
  divisors, and the count can only drop.  So `(2)` is a ceiling for all critical observations, not
  only the generic ones.

  `CriticalTargetGenericSeparable.lean` — `separable_of_no_common_root` (over an algebraically
  closed field a polynomial sharing no root with its derivative is separable: a non-unit gcd has
  positive degree, hence a root common to both), `finite_not_separable_scalings` (a repeated root of
  `1 + c W` is a critical point of `W` where `W = -c⁻¹`, so `c` is one of finitely many values
  determined by the roots of `W'`), and **`finite_scalings_not_exact`**: for critical tails `U, V`
  over an algebraically closed field of characteristic zero, the set of scalars `c` for which
  `Nat.card (criticalFibre K m n U (C c * V)) ≠ criticalHorizonMultiplicity m n` is **finite**.

  Together these turn the paper's "generic critical observation has `choose(m+n,m)` compatible
  jets" into an unconditional Lean pair: `≤` always, `=` off a finite set in every scaling family,
  with the exceptional set explicitly the reciprocals of the critical values of `U V`.  The
  genericity is elementary — no discriminant, no resultant, no intersection theory.

- 2026-08-06 — **Section 5 formalized: a transverse channel adds no ambiguity.**
  `TransverseChannelLift.lean`, in the umbrella, all `[propext, Classical.choice, Quot.sound]`:

  `transverseDifferential p m n L` — the transverse compatibility `u = p (u/p)` as a *linear* map
  `degreeLT m x degreeLT n -> degreeLT L`, the square convolution system of section 5, built on the
  corpus's `fibreTangentSpace`/`finrank_degreeLT` layer rather than a new one;
  `injective_transverseDifferential` — nonsingular for the unipotent jet `1 + t^m`: the compatibility
  forces the exact identity `a = (1 + t^m) b` below the horizon, whose right side has degree at
  least `m` unless both sides vanish;
  `bijective_transverseDifferential` — hence bijective, the two spaces having dimension `m + n`;
  `transverseFibre`, `exists_unique_transverse`, `nat_card_transverseFibre` — every pair of observed
  transverse tails has exactly one lift;
  `nat_card_criticalFibre_prod_transverse` and
  **`nat_card_criticalFibre_prod_transverse_channels`** — one longitudinal channel and any number
  `d` of transverse channels are counted by `criticalHorizonMultiplicity m n` itself.

  One correction to the card's section 5: nonsingularity of the transverse system is **not**
  automatic, and the determinant is not identically one.  For `p = 1` the system is degenerate (the
  two transverse observations coincide while the depths differ), so the honest statement is that the
  nonsingular locus is nonempty — witnessed here by an explicit unipotent jet — and that on it each
  longitudinal solution has exactly one transverse lift.  That is what the Lean theorems say, and it
  is what the count needs.

- 2026-08-06 — **Scope correction, recorded before it could propagate.**  An earlier entry today
  described `(2)` as formalized.  That is right only in two regimes and neither is generic:

  * critical-degree packets, where each observed packet's lowest coefficient is its only one below
    the horizon (codimension `(m-1) + (n-1)` in the observation space);
  * depth one, `m = 1` or `n = 1`, where the packet is arbitrary because elimination leaves a single
    univariate equation of degree `n+1`.

  For a generic packet with `m, n >= 2` the completed jet has degree up to `L-1`, the product
  reaches degree `2L-2`, the truncated equation does not close to an exact factorization, and the
  divisor bijection is simply unavailable.  That case is the card's remaining research core and is
  the reason the bilinear system was built.  The two routes to it are multihomogeneous Bezout on
  `P^m x P^n` and the Giambelli-Thom-Porteous degree of the rank locus of the `(m+n) x (m+1)` matrix
  of linear forms obtained by fixing the reciprocal; the second is the more likely to be reachable,
  since its codimension `n` equals the dimension of `P^n` and the expected count `choose(m+n,m)` is
  exactly the classical determinantal degree.  The `Lean verification` section now states this
  boundary explicitly.

- 2026-08-06 — **Two exact reformulations of the open case, and a hand certification at `m=n=2`.**

  *Rank-drop form.*  Fix the reciprocal `Q = B + V`.  The compatibility equations are linear in the
  unknown jet coefficients, so the fibre point exists over `Q` exactly when the `L x (m+1)` matrix
  whose columns are `Q, tQ, ..., t^(m-1) Q, 1 - U Q` in `K[t]/t^L` drops rank.  Indeed a dependency
  `(Lambda - mu U) Q + mu = 0` with `mu != 0` normalises to `(Lambda + U) Q = 1`, which is the fibre
  equation with `A = Lambda`; and `mu = 0` forces `Lambda Q = 0`, impossible for a unit `Q`.  The
  matrix has entries linear in the `n+1` homogeneous coordinates of `Q`, its rank locus has expected
  codimension `L - m = n = dim P^n`, and the classical Giambelli degree of that locus is
  `choose(L, m)` — the assertion `(2)`.  This is the cleanest bridge from the card to a known
  formula, and it replaces multiprojective Bezout by a determinantal degree.

  *Graph form.*  Equivalently the count is a multidegree of the inversion graph
  `{(P, P^-1)}` in `K[t]/t^L`: the observation intersects it with a product of two coordinate
  subspaces of complementary types, `m` free jet coefficients against `n` free reciprocal ones.

  *Certification at `m = n = 2`* (`L = 4`, expected `choose(4,2) = 6`).  With
  `P = a0 + a1 t + u2 t^2 + u3 t^3` and `Q = b0 + b1 t + v2 t^2 + v3 t^3` the four equations give
  `b0 = 1/a0`, `b1 = -a1/a0^2`, and then

  ```text
  v2 a0^3 - a1^2 + u2 a0 = 0
  v3 a0^3 + v2 a1 a0^2 - u2 a1 + u3 a0 = 0
  ```

  Solving the second for `a1` and substituting into the first, the spurious factor `a0` cancels once
  and leaves

  ```text
  (v2 a0^2 + u2)(v2 a0^2 - u2)^2 - a0 (v3 a0^2 + u3)^2 = 0,
  ```

  of degree exactly **6** in `a0`, with `a1` a rational function of `a0` on it.  So the generic count
  at `m = n = 2` is `6 = choose(4,2)`, confirming that the answer is *not* the Bezout product
  `(n+1)(n+2) = 12` of the eliminated square system.  The excess is exactly the factor the bilinear
  structure removes.

- 2026-08-06 — **The rank-drop reformulation is now a Lean theorem.**
  `RankDropFibreCriterion.lean`, in the umbrella, `[propext, Classical.choice, Quot.sound]`:

  `sum_range_C_coeff_mul_X_pow` — a polynomial below a degree is the sum of its low monomials;
  **`exists_fibre_iff_dependent`** — for a reciprocal `Q` invertible at the origin, a compatible jet
  of depth `m` exists **iff** there are `Lambda` of degree below `m` and a scalar `mu`, not both
  zero, with `X^L | Lambda Q + mu (1 - U Q)`.  Forward, the compatibility equation is itself such a
  dependency with `mu = -1`; backward, `mu = 0` would give `X^L | Lambda Q` with `Q` invertible,
  hence `Lambda = 0`, so `mu` can be divided out and `A = -Lambda/mu` is the jet;
  `exists_fibre_iff_dependent_coeffs` — the same criterion with `Lambda` written in coordinates, so
  the statement literally reads "the `m+1` elements `Q, tQ, ..., t^(m-1) Q, 1 - U Q` of `K[t]/t^L`
  are linearly dependent".

  This is the first Lean step of the determinantal route to the open case: the fibre over `Q` is a
  rank drop of an `L x (m+1)` matrix whose entries are linear in `Q`, so the fibre count over the
  whole reciprocal space is the degree of a rank locus of expected codimension `L - m = n`, matching
  `dim P^n`.  No genericity, no separability, and no restriction on the observed packets is used —
  the criterion holds for every observation.

- 2026-08-06 — **The fibre locus is cut by minors of a matrix of affine-linear forms.**  Two
  modules, both in the umbrella, both `[propext, Classical.choice, Quot.sound]`:

  `RankDropMatrixCriterion.lean` — `rankDropMatrix U Q m L`, the `L x (m+1)` matrix whose first `m`
  columns are the shifts `t^j Q` and whose last is `1 - U Q`, read off below the horizon (stated over
  any commutative ring); `mulVec_rankDropMatrix` — the matrix acts on a coefficient vector as the
  corresponding combination of those elements; **`exists_fibre_iff_mulVec_eq_zero`** — over a field,
  the fibre over `Q` (invertible at the origin) is nonempty exactly when that matrix has a nonzero
  kernel vector; `det_submatrix_rankDropMatrix_eq_zero` — hence every maximal minor vanishes there.

  `UniversalRankDropMatrix.lean` — `univRecip V n`, the reciprocal with unknown low coefficients over
  the observed tail; `univRecip_coeff`, `map_univRecip`, `rankDropMatrix_univRecip_map` (the
  universal matrix specialises to the rank-drop matrix of the named reciprocal),
  `eval_det_submatrix_rankDropMatrix` (so do its minors);
  **`totalDegree_rankDropMatrix_univRecip`** — every entry has total degree at most one in the
  unknown reciprocal coefficients; **`totalDegree_det_submatrix_rankDropMatrix`** — hence every
  maximal minor has total degree at most `m + 1`.

  So the fibre locus in the `n`-dimensional reciprocal space is contained in the common zero locus of
  the maximal minors of an `L x (m+1)` matrix of affine-linear forms — expected codimension
  `L - m = n`, matching the dimension, with each equation of degree `m + 1`.  This is exactly the
  input a determinantal degree formula consumes; what is still missing is the formula itself
  (Giambelli: the degree of the maximal-minor rank locus of a `p x q` matrix of general linear forms
  is `choose(p, q-1)`, here `choose(L, m)`).  Mathlib has no intersection theory, so that formula has
  to be built; the objects it acts on now exist and are machine-checked.

- 2026-08-06 — **Two points of one fibre force a Padé degeneracy at the product of their jets.**
  Two modules, both in the umbrella, both `[propext, Classical.choice, Quot.sound]`:

  `FibrePairProductObstruction.lean` — `product_relation_identity` / `dvd_product_relation`: for two
  compatible pairs of one observation,

  ```text
  (A - A') - (A+U)(A'+U) (B' - B) = (A'+U)((A+U)(B+V) - 1) - (A+U)((A'+U)(B'+V) - 1),
  ```

  so the left side is divisible by the horizon.  `exists_kernel_of_fibre_ne` reads this as a nonzero
  kernel vector of the convolution pairing at the **product** `S = (A+U)(A'+U)`: `alpha = S beta` below
  the horizon with `deg alpha < m`, `deg beta < n`, `alpha != 0` (the jets differ, since a fibre point is
  determined by its jet).  `not_injective_transverseDifferential_of_fibre_ne` — that pairing is
  exactly the transverse channel's square convolution system, so it is singular at the product;
  `product_ne_one_add_X_pow_of_fibre_ne` — hence no two distinct fibre points multiply to the
  unipotent jet `1 + t^m`, whose pairing is nonsingular.

  `PadeHankelObstruction.lean` — `padeHankel S m n`, the `n x n` matrix with entries
  `(t^j S)_{m+r}`; `mulVec_padeHankel`; **`det_padeHankel_eq_zero_iff`**: the determinant vanishes
  **iff** `S` admits a Padé approximant of type `(m-1, n-1)` to order `m+n`.  Both directions are
  proved (the forward one truncates the numerator below `m`, the backward one reads the kernel
  vector off the denominator).  Mathlib has no Padé theory at all; this is the classical existence
  criterion.  **`det_padeHankel_product_eq_zero`**: the product of the jets of any two distinct
  points of a fibre lies on that Hankel hypersurface.

  Mathematically this is a genuine constraint on how large a fibre can be: the `N` jets of a fibre
  have all `N(N-1)/2` pairwise products confined to a single hypersurface of degree `n` in the jet
  coefficients.  Fixing one fibre point makes it a hypersurface of degree `n` in the `m` remaining
  jet coefficients, so with a Bezout theorem for `A^m` this would bound the fibre by `m + n^m` — at
  `m = 1` that is `n + 1 = choose(L,1)` and at `m = n = 2` it is `2 + 4 = 6 = choose(4,2)`, both
  sharp.  Mathlib has no Bezout theorem for affine space either, so the bound is not yet a Lean
  theorem; the obstruction it rests on now is.

- 2026-08-06 — **The obstruction becomes a matrix pencil, and at depth one it closes the bound.**
  `OneDepthHankelBound.lean`, in the umbrella, `[propext, Classical.choice, Quot.sound]`:

  `padeHankel_C_mul_add` — the Hankel matrix is linear in the jet, so fixing one fibre point turns
  the obstruction into a **pencil** `a . H_1 + H_0` in the unknown jet coordinate;
  `det_pencil_eq_charpoly` — with invertible leading matrix, `det(a H_1 + H_0) = det H_1 . f(a)`
  where `f` is the characteristic polynomial of `-H_1^{-1} H_0`, monic of degree `n`;
  `card_le_of_det_pencil_eq_zero` — hence at most `n` degenerate members;
  `det_padeHankel_fibre_ne_zero` — the leading matrix, the Hankel matrix of a fibre point's own jet,
  **is** invertible whenever `V.coeff n != 0`: a degeneracy would force `alpha Q_0 = beta` below the
  horizon with `deg beta < n`, and reading the coefficient at `n` gives `alpha_0 . V_n = 0`, hence
  `alpha = 0`, hence `beta = 0`;
  **`nat_card_criticalFibre_one_le_of_tail`** — therefore at depth one, for every observed packet,
  `Nat.card (criticalFibre K 1 n U V) <= criticalHorizonMultiplicity 1 n`.

  This is unconditional: no separability, no algebraically closed field, and — unlike the corpus's
  `OneDeepFibreBound.nat_card_criticalFibre_one_le`, which needs the monomial packet `C d X^n` — no
  restriction on the observed packet beyond `X^n | V` and `V_n != 0`, in particular no bound on its
  degree above the horizon.

  The value is mostly in the method: the pencil argument is the `m = 1` shadow of the general one.
  For general `m` the same obstruction confines the other fibre points to a hypersurface of degree
  `n` in the `m` unknown jet coordinates; what is missing is a Bezout bound for `A^m`.  **The next
  concrete step is `m = 2`**: plane Bezout follows from resultants, and mathlib does have
  `Polynomial.resultant` and `resultant_eq_zero_iff` (the corpus already uses them in
  `U0/U0PhiCard.lean`).  That would give `Nat.card <= 2 + n^2`, which at `n = 2` is
  `6 = choose(4,2)` — sharp, and the first general-packet count at `m, n >= 2`.

- 2026-08-06 — **The open case is entered: both depths two, general packets, sharp bound.**
  `DepthTwoGeneralPacketBound.lean`, in the umbrella, `[propext, Classical.choice, Quot.sound]`:

  `fibre_two_two_coeffs` — the four scalar equations of a fibre point at `m = n = 2`, read off the
  compatibility equation coefficient by coefficient;
  `fibre_two_two_eliminated` — eliminating the two reciprocal unknowns leaves
  `v₂a₀³ - a₁² + u₂a₀ = 0` and `v₃a₀³ + v₂a₁a₀² - u₂a₁ + u₃a₀ = 0`;
  `criticalSextic u₂ u₃ v₂ v₃ = (v₂X²+u₂)(v₂X²-u₂)² - X(v₃X²+u₃)²`, with
  `natDegree_criticalSextic` — degree exactly `6`, leading coefficient `v₂³`, hence nonzero as soon
  as the observation is critical;
  `isRoot_criticalSextic` — eliminating `a₁` between the two equations shows every fibre point's
  first jet coefficient is a root of the sextic;
  **`nat_card_criticalFibre_two_two_le`** — hence, for `X² | U`, `X² | V`, `V₂ ≠ 0` and
  `u₂v₃ + u₃v₂ ≠ 0`,

  ```text
  Nat.card (criticalFibre K 2 2 U V) ≤ criticalHorizonMultiplicity 2 2 = 6.
  ```

  The genericity condition `u₂v₃ + u₃v₂ ≠ 0` is exactly what makes the first jet coefficient
  determine the second: if `v₂a₀² = u₂` at a fibre point then the second equation forces
  `v₃a₀² = -u₃`, and eliminating `a₀²` between those gives `u₂v₃ + u₃v₂ = 0`.

  **This is the first case of the card's open core.**  The observed packets here carry *both* of
  their coefficients — `u₃` and `v₃` are unrestricted — so this is not the critical-degree family,
  and the divisor bijection does not apply.  The bound is sharp: `6 = choose(4,2)`, and the
  critical-degree specialisation `u₃ = v₃ = 0` is known to attain it.  No separability, no
  algebraically closed field, no bound on the packets' degree above the horizon.

  What is still missing at `m = n = 2` is the matching *lower* bound for a general packet, which
  needs the sextic to have six distinct roots — a discriminant condition — and the general
  `m, n ≥ 2` case, where the same elimination has no closed form and the count is the determinantal
  degree.

- 2026-08-06 — **`m = n = 2` with general packets is closed: the count is exactly `choose(4,2)`.**
  Same module, all `[propext, Classical.choice, Quot.sound]`:

  `coeff_zero_injective_two_two` — factored out of the bound: away from the degenerate locus the
  first jet coefficient determines the fibre point;
  `exists_criticalFibre_two_two_of_coeffs` — the converse of the coefficient extraction: any
  solution of the four scalar equations *is* a fibre point (the completed jet and reciprocal are the
  linear polynomials with those coefficients, and their product agrees with `1` below the horizon);
  `exists_criticalFibre_of_isRoot` — **every** root of the sextic is attained.  Given a root `a₀`,
  the second equation defines `a₁ = -a₀(v₃a₀²+u₃)/(v₂a₀²-u₂)`, and the sextic is exactly what makes
  the first equation `a₁² = a₀(v₂a₀²+u₂)` hold; the reciprocal is then `b₀ = a₀⁻¹`,
  `b₁ = -a₁/a₀²`.  The root is nonzero because the sextic's constant term is `u₂³`, and the
  denominator is nonzero by the same genericity condition as before;
  **`nat_card_criticalFibre_two_two`** — hence for `X² | U`, `X² | V`, `u₂ ≠ 0`, `v₂ ≠ 0`,
  `u₂v₃ + u₃v₂ ≠ 0` and a separable sextic, over an algebraically closed field,

  ```text
  Nat.card (criticalFibre K 2 2 U V) = criticalHorizonMultiplicity 2 2 = 6.
  ```

  The fibre is in bijection with the roots of the sextic, and a separable split sextic has six.

  **This closes the first case of the card's open core**, `m, n >= 2` with observed packets carrying
  all their coefficients.  The hypotheses are the honest genericity conditions: `u₂, v₂ ≠ 0` is
  criticality of the observation, `u₂v₃ + u₃v₂ ≠ 0` cuts out the locus where the first jet
  coefficient stops determining the second, and separability of the sextic is the same kind of
  condition the critical-degree theorem imposes on `1 + U V`.  What remains is general `m, n >= 2`,
  where the elimination has no closed form.

- 2026-08-06 — **The classical resultant degree bound, built from scratch.**  Two modules, both in
  the umbrella, both `[propext, Classical.choice, Quot.sound]`:

  `WeightedDeterminantDegree.lean` — `degree_det_le_of_degree_le` and
  `natDegree_det_le_of_degree_le`: if every entry of a square polynomial matrix has degree at most
  `u i + v j`, the determinant has degree at most `∑u + ∑v`.  And the form the Sylvester matrix
  actually has, **`degree_det_add_le`**: if `degree (M i j) + i ≤ c j` — a *decreasing* row weight,
  absorbed to the left so nothing leaves the natural numbers — then
  `degree (det M) + ∑ i ≤ ∑ c`.  Mathlib bounds a determinant only by the uniform entry degree times
  the size, which is far too weak for eliminants.

  `ResultantDegreeBound.lean` — `sylvesterWeight`, `degree_sylvester_add_le` (the Sylvester entries
  obey exactly that shifted bound: the entry in row `i` of the column at position `j₁` of the block
  of `g` is `g.coeff (i - j₁)`, of degree at most `b - (i - j₁)`, and the out-of-range entries vanish),
  and **`degree_resultant_add_le`**:

  ```text
  degree (resultant f g m n) + ∑_{i < m+n} i  ≤  ∑_{j < m+n} sylvesterWeight a b m n j,
  ```

  with `sum_sylvesterWeight` evaluating the right side to `(m·b + Σ_{j<m} j) + (n·a + Σ_{j<n} j)`.
  Subtracting the two triangular sums gives the classical `m·b + n·a - m·n`, which for `a = m`,
  `b = n` is exactly the Bezout number `a·b`.

  This is the missing half of plane elimination.  With the bridge from the previous entry — the
  resultant vanishes at the first coordinate of every common zero — the two together bound the
  common zeros of a two-variable system by the resultant's degree, which is the affine Bezout
  estimate the general `m, n >= 2` case needs.  None of it existed in mathlib.

- 2026-08-06 — **The plane elimination bound is assembled.**  Same module, all
  `[propext, Classical.choice, Quot.sound]`:

  `sum_fin_val_add`, `sum_sylvesterWeight_add` — the weight sum against the row sum, in the
  subtraction-free form `∑ weights + m n = ∑ rows + (m b + n a)`;
  `natDegree_resultant_add_le` — the same bound on natural degrees for a nonzero resultant;
  **`card_first_coords_le_of_degrees`** — combining it with the elimination bridge:

  ```text
  s.card + m * n ≤ m * b + n * a
  ```

  for any finset `s` of first coordinates of common zeros of a two-variable system with declared
  degrees `m, n` and total degrees `a, b`, provided the resultant is nonzero.  That is the classical
  affine Bezout estimate `m b + n a - m n`; for two conics (`m = n = a = b = 2`) it returns `4`, the
  right answer.

  So the corpus now owns, unconditionally and from scratch, the whole elimination chain that mathlib
  lacks: the weighted determinant degree bound, the Sylvester degree estimate, the resultant's
  vanishing at common zeros, and the resulting count.  This is the general tool the remaining
  `m, n >= 2` case needs — the alternative, grinding out each `(m, n)` by hand as was done for
  `(2,2)`, does not scale past the next case.

- 2026-08-06 — **Affine Bezout, in the clean form.**  `IteratedTotalDegree.lean` plus a corollary in
  `ResultantDegreeBound.lean`, both in the umbrella, all `[propext, Classical.choice, Quot.sound]`:

  `TotalDegLE p d` — total degree at most `d` for a two-variable polynomial written as a polynomial
  in the outer variable with polynomial coefficients: `degree (p.coeff k) + k ≤ d` for every `k`.
  In this form no truncated subtraction appears and the zero coefficients are free, their degree
  being `⊥`.  `TotalDegLE.add`, `.neg`, `.mul` (degrees add), `.sum`, `.prod`, `.mono`,
  `.natDegree_le` (a total degree bound bounds the degree in the outer variable), and
  **`TotalDegLE.det`** — a determinant of an `N x N` matrix of entries of total degree at most `d`
  has total degree at most `N d`.

  **`card_first_coords_le_of_totalDeg`** — with the total degrees as the declared degrees, the
  elimination bound collapses to the Bézout number:

  ```text
  s.card ≤ a * b
  ```

  for any finset `s` of first coordinates of common zeros of a plane system of total degrees `a, b`
  with nonzero resultant.  Mathlib has total degree only for `MvPolynomial`, where this iterated
  form is not available; the determinant bound is what turns an affine-linear matrix of size `n`
  into a hypersurface of degree `n`, which is the shape the Padé–Hankel obstruction produces.

  The immediate application is `m = 2` with **any** `n`: fixing two fibre points, every other one
  lies on two hypersurfaces of degree `n` in the two unknown jet coefficients, so the fibre is finite
  with at most `n² + 2` points.  That is the first general-`n` statement for general packets at
  `m ≥ 2`; the pieces for it are now all in place.

- 2026-08-06 — **The depth-two Hankel curve.**  `DepthTwoHankelCurve.lean`, in the umbrella, all
  `[propext, Classical.choice, Quot.sound]`:

  `affineCurveMatrix H₀ H₁ H₂` — a matrix of affine-linear forms `H₀ + H₁ x + H₂ y` in two
  variables, written over `(K[x])[y]`; `totalDegLE_affineCurveMatrix` (entries of total degree one),
  `evalPairHom_affineCurveMatrix` (specialisation), **`totalDegLE_det_affineCurveMatrix`** (the
  determinant of an `n x n` such matrix is a plane curve of degree at most `n`), and
  `evalPairHom_det_affineCurveMatrix_swap` — exchanging the two variables just exchanges the two
  linear parts, so the swapped system needed for the second elimination is the same construction
  with `H₁` and `H₂` transposed.

  `hankelCurveMatrix P₀ U n` — the instance that matters: at depth two the unknown jet is
  `a₀ + a₁ t` above the packet, so `P₀ · (a₀ + a₁ t + U) = a₀ P₀ + a₁ (t P₀) + P₀ U` and the
  Padé–Hankel matrix, being linear in the jet, becomes
  `affineCurveMatrix (padeHankel (P₀ U)) (padeHankel P₀) (padeHankel (t P₀))`.  Its determinant is a
  plane curve of degree `n`, and **`evalPairHom_det_hankelCurveMatrix_eq_zero`** says every fibre
  point other than the base one lies on it.

  So at depth two, for **any** `n` and unrestricted packets, two fibre points confine all the others
  to the intersection of two plane curves of degree `n` — the shape the elimination chain of the
  previous entries consumes.  The count itself is next.

- 2026-08-06 — **Depth two, every `n`, unrestricted packets: the fibre is finite.**  Same module,
  `[propext, Classical.choice, Quot.sound]`:

  `hankelCurve P₀ U n` and `hankelCurveSwap P₀ U n` — the base jet's plane curve and the same curve
  with the two jet coordinates exchanged (which by the swap lemma is the same construction with the
  two linear parts transposed); `totalDegLE_hankelCurve`, `totalDegLE_hankelCurveSwap` — both of
  degree `n`; `natDegree_resultant_hankel_le` — the eliminant of two of them has degree at most
  `n²`; and

  **`nat_card_criticalFibre_depth_two_le`**:

  ```text
  Nat.card (criticalFibre K 2 n U V) ≤ 2 + n² · n²
  ```

  for `X² | U`, `X^n | V`, provided the eliminants of the curve pair (and of the swapped pair) of
  any two fibre points do not vanish identically.  Two fibre points are set aside as the bases; every
  other one lies on both curves, so its first coordinate is a root of the first eliminant and its
  second a root of the swapped one, and the jet's two coefficients determine the fibre point.

  **This is the first finiteness statement for the fibre at `m ≥ 2` with unrestricted packets and no
  restriction on `n`.**  Until now depth two was known only at `n = 2` (where the count is exactly
  `6`), and everything else needed the packets to carry only their lowest coefficient.  The bound
  `n⁴` is far from the truth `choose(n+2,2)` — it pays twice for using the eliminant in each
  coordinate separately rather than a sharp plane Bezout with distinct first coordinates — but
  finiteness, with an explicit bound, is what was missing.

- 2026-08-06 — **The obstruction hypersurface at any depth.**  `MvHankelHypersurface.lean`, in the
  umbrella, all `[propext, Classical.choice, Quot.sound]`:

  `padeHankel_add`, `padeHankel_C_mul`, `padeHankel_zero`, `padeHankel_finsetSum` — the Hankel matrix
  is a linear function of the jet; **`padeHankel_mul_jet`** — hence for a base jet `P₀`,

  ```text
  padeHankel (P₀ · (∑_{i<m} a_i t^i + U)) = padeHankel (P₀ U) + ∑_{i<m} a_i · padeHankel (t^i P₀),
  ```

  affine-linear in the `m` unknown jet coefficients;
  `affineMvMatrix H₀ H` — a matrix of affine-linear forms in `m` variables over
  `MvPolynomial (Fin m) K`, with `totalDegree_affineMvMatrix_le` (entries of degree one),
  `eval_affineMvMatrix`, and **`totalDegree_det_affineMvMatrix_le`** — the determinant of an
  `N x N` such matrix has total degree at most `N`;
  `hankelMvMatrix P₀ U m n`, `totalDegree_det_hankelMvMatrix_le`, `eval_det_hankelMvMatrix`, and
  **`eval_det_hankelMvMatrix_eq_zero`** — every fibre point other than the base one lies on the base
  point's hypersurface.

  So at **every** pair of depths, one fibre point confines all the others to a hypersurface of
  degree `n` in the `m` unknown jet coefficients.  At `m = 2` this is the plane curve of the
  depth-two count, recovered as a special case; at larger `m` it is the object a dimension or degree
  argument has to consume, and it is now built and machine-checked rather than assumed.

- 2026-08-06 — **Elimination of one variable from a multivariate system.**
  `MvResultantElimination.lean`, in the umbrella, all `[propext, Classical.choice, Quot.sound]`:

  `mvEvalHom s y` — evaluation in the split presentation, the outer variable at `y` and the rest at
  `s`, as a ring homomorphism; `mvEvalHom_C`, `mvEvalHom_finSuccEquiv` (via mathlib's
  `eval_eq_eval_mv_eval'`);
  **`eval_resultant_eq_zero_of_mv_common_zero`** — splitting off the first variable with
  `finSuccEquiv` and taking the resultant, the eliminant vanishes at the projection of every common
  zero of the two members;
  `exists_ne_zero_vanishing_on_projection` — so a nontrivial eliminant confines those projections to
  a hypersurface in the remaining variables;
  **`totalDegree_det_add_le`** — the weighted degree bound for a determinant of multivariate
  polynomials, with zero entries admitted explicitly (a zero `MvPolynomial` has total degree `0`,
  not `⊥`, so they cannot be swept under the ordering as in the univariate case).

  This is the inductive step of elimination, which mathlib does not have in any form — it has the
  resultant and its Bézout identity, and nothing that connects them to common zeros of a system in
  more than one variable.  Worth recording: mathlib **does** have
  `MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le`, exactly the degree transfer
  `totalDegree ((finSuccEquiv f).coeff i) + i ≤ totalDegree f` that the next stage needs to keep
  degrees under control while iterating the step.

- 2026-08-06 — **The eliminant's degree, multivariately.**  Same module, all
  `[propext, Classical.choice, Quot.sound]`:

  `totalDegree_sylvester_finSuccEquiv_add_le` — the Sylvester entries of a split multivariate pair
  obey the weighted bound.  Mathlib's `totalDegree_coeff_finSuccEquiv_add_le` carries a
  *nonvanishing* hypothesis on the coefficient, which is exactly right here: when the coefficient
  vanishes the entry is zero and the disjunction's left branch applies, so nothing is lost;
  **`totalDegree_resultant_finSuccEquiv_add_le`** — hence the eliminant either vanishes identically
  or satisfies

  ```text
  totalDegree (resultant (finSuccEquiv f) (finSuccEquiv g) p q) + p q ≤ p b + q a
  ```

  for total degrees `a, b`.  This is the same classical estimate as the univariate case, now in the
  variables that survive elimination.

  Together with the elimination step of the previous entry, the inductive tool is complete: given
  two polynomials in `m + 1` variables of total degrees `a` and `b`, eliminating one variable leaves
  a polynomial in `m` variables of total degree at most `p b + q a - p q`, vanishing on the
  projection of every common zero.  Iterating it is what a general `m` count needs; each step is now
  unconditional and machine-checked.

- 2026-08-06 — **One elimination step for a whole system.**  Same module,
  `[propext, Classical.choice, Quot.sound]`:

  `natDegree_finSuccEquiv_le_totalDegree` — the degree in the eliminated variable is bounded by the
  total degree (via mathlib's `degree_finSuccEquiv` and `degreeOf_le_totalDegree`), which is what
  feeds the declared degrees to the resultant;
  **`exists_eliminated_system`** — eliminating the first variable against a distinguished member
  turns `N + 1` equations of total degree `d` in `m + 1` variables into `N` equations of total
  degree `d²` in `m` variables, each nonzero, and still vanishing at every projection of a common
  zero of the original system.

  This is the induction the general `m` count runs on: starting from the `m` Hankel hypersurfaces of
  degree `n` that contain the fibre's jet coordinates, `m - 1` steps leave a single univariate
  polynomial of degree at most `n^(2^(m-1))`, nonzero at each stage under the stated resultant
  conditions.  The bound is doubly exponential and nothing like the truth `choose(m+n,m)`, but it is
  the classical elimination bound and it is now an unconditional Lean theorem at every step rather
  than a citation.

- 2026-08-06 — **The elimination tower.**  Same module, all
  `[propext, Classical.choice, Quot.sound]`:

  `elimStep d F` — one elimination of the leading variable from a square system, with
  `totalDegree_elimStep_le` (degree `d` becomes `d²`, unconditionally: if a resultant happens to
  vanish the eliminant is zero and its degree is zero) and `eval_elimStep_eq_zero` (the eliminated
  system still vanishes on the tail of every common zero, via `Fin.cons_self_tail`);
  **`elimTower k F d`** — the tower itself, defined by recursion: `k + 1` equations in `k + 1`
  variables reduce to `k` in `k`, ending in a single polynomial in one variable.  The square shape
  is preserved by every step, which is what makes the recursion type-check at all;
  **`totalDegree_elimTower_le`** — `totalDegree (elimTower k F d) ≤ d^(2^k)`;
  **`eval_elimTower_eq_zero`** — the tower vanishes at the last coordinate of every common zero of
  the original system.

  Both tower theorems are **unconditional**: no resultant is assumed nonzero anywhere.  A vanishing
  resultant simply propagates a zero polynomial, which satisfies the degree bound and the vanishing
  statement trivially.  The nonvanishing is needed only to *conclude* finiteness from the tower, and
  that is a hypothesis on the single output polynomial rather than on the `k` intermediate stages —
  which is the difference between a statable theorem and an unusable one.

  What remains to turn this into a general `m` fibre bound is the univariate root count for a nonzero
  `MvPolynomial (Fin 1) K`, and then the product over the `m` coordinate orders.

- 2026-08-06 — **The elimination tower now counts.**  Same module, all
  `[propext, Classical.choice, Quot.sound]`:

  `eval_empty_injective` — evaluation of a polynomial in no variables is injective (by
  `MvPolynomial.ringHom_ext`, where the condition on the variables is vacuous, against
  `isEmptyRingEquiv`);
  `card_roots_mvPolynomial_one_le` — a nonzero polynomial in **one** variable has at most its total
  degree many roots.  The transfer to `K[X]` goes through `finSuccEquiv` and the coefficient map,
  reusing `natDegree_finSuccEquiv_le_totalDegree` for the degree and the injectivity above for the
  nonvanishing;
  **`card_last_coord_le`** — hence for a square system of `k + 1` equations of total degree `d` in
  `k + 1` variables whose elimination tower does not vanish, the last coordinate of a common zero
  takes at most `d^(2^k)` values.

  The only hypothesis beyond the degrees is `elimTower k F d ≠ 0` — a condition on the single
  polynomial the tower outputs, not on the `k` intermediate resultants.  With the Hankel
  hypersurfaces of `MvHankelHypersurface.lean` as the system (`d = n`, one equation per base fibre
  point), this bounds each jet coordinate of the fibre at **every** depth `m`, and the product over
  the `m` coordinate orders bounds the fibre itself.

- 2026-08-06 — **The chain closes on a general-depth statement.**
  `AnyDepthCoordinateBound.lean`, in the umbrella, `[propext, Classical.choice, Quot.sound]`:

  `hankelSystem base U` — the square system attached to a choice of `m` fibre points: `m` Hankel
  hypersurfaces of degree `n` in the `m` unknown jet coefficients, with
  `totalDegree_hankelSystem_le`;
  **`card_top_coeff_le`** — for every observation and **every** pair of depths, the top jet
  coefficient of the fibre points other than the chosen bases takes at most `n^(2^(m-1))` values,
  provided the elimination tower of that system does not vanish identically.

  This is the first general-`m` finiteness-type statement on the card.  It runs the whole chain
  end to end: product obstruction → Padé–Hankel determinant → hypersurface of degree `n` in the jet
  coordinates → square system from `m` base points → elimination tower → univariate root count.
  Every link was built here; mathlib supplied only the resultant and its Bézout identity.

  The bound `n^(2^(m-1))` is the classical doubly-exponential elimination bound and is nowhere near
  the truth `choose(m+n,m)`.  It is loose for a structural reason worth recording: pairwise
  elimination discards the bilinearity that makes the honest count binomial, exactly as the earlier
  `n⁴` at depth two did.  Sharpening it is not a matter of tightening these estimates — it needs the
  multihomogeneous Bezout number of the pre-elimination system, which is the card's original route
  and remains the open core.

- 2026-08-06 — **The fibre is finite at every depth.**  `AnyDepthCoordinateBound.lean` (with two
  Finset-valued companions in `MvResultantElimination.lean`), all
  `[propext, Classical.choice, Quot.sound]`:

  `exists_finset_roots_mvPolynomial_one`, `exists_finset_last_coord` — the earlier counts, restated
  so they *produce* the finite set rather than bounding an arbitrary finset of it, which is what an
  injection argument needs;
  `hankelSystemPerm base U σ` — the square Hankel system with its variables permuted, so any chosen
  coordinate becomes the one the tower eliminates last (`totalDegree_rename_le` keeps the degree);
  `card_coeff_le`, `exists_finset_coeff` — hence **every** jet coefficient of the fibre lies in an
  explicit set of at most `n^(2^(m-1))` values;
  **`nat_card_criticalFibre_le_of_towers`**:

  ```text
  Nat.card (criticalFibre K m n U V) ≤ m + (n^(2^(m-1)))^m
  ```

  for every observation, at **every** pair of depths, given `m` base fibre points whose permuted
  elimination towers do not vanish.  A fibre point is determined by its `m` jet coefficients, so the
  fibre injects into the product of the coordinate sets together with the bases.

  **This is the first proof that the fibre is finite at general `m`.**  Until now finiteness was
  known only at `m = 1` and `m = 2`.  The bound is doubly exponential and the truth is
  `choose(m+n,m)`; the gap is structural, not an artefact of loose estimates, and closing it needs
  the multihomogeneous Bezout number of the bilinear pre-elimination system — the card's open core.

- 2026-08-06 — **Finiteness at both depths two with no genericity at all.**
  `nat_card_criticalFibre_two_two_le_of_critical` in `DepthTwoGeneralPacketBound.lean`,
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  X² | U,  X² | V,  V₂ ≠ 0   ⟹   Nat.card (criticalFibre K 2 2 U V) ≤ 12.
  ```

  The genericity condition `u₂v₃ + u₃v₂ ≠ 0` of the sharp count is dropped entirely.  When it fails
  the first jet coefficient no longer determines the second, but the *first* eliminated equation
  still reads `a₁² = v₂a₀³ + u₂a₀`, so the second coefficient is determined **up to sign**: the fibre
  injects into the pairs `(a₀, a₁)` with `a₀` a root of the sextic (at most six) and `a₁` a root of a
  quadratic (at most two).

  So at both depths two the trichotomy is complete: exactly `choose(4,2) = 6` for a separable sextic
  under the genericity condition, at most `6` under the condition alone, and at most `12` for
  **every** critical observation.  Criticality of the observed reciprocal packet — `v₂ ≠ 0`, which is
  what makes the observation an observation at these depths — is the only hypothesis left.

- 2026-08-06 — **The system really is bilinear: bidegree `(1,1)` proved.**
  `BilinearFibreSystem.lean`, all `[propext, Classical.choice, Quot.sound]`:

  `CoeffDegreeOfLE s P d` — every coefficient of a polynomial has degree at most `d` in a chosen
  variable — with `.add`, `.sub`, `.mono`, `.mul` (degrees add), `degreeOf_neg_le`, and the base
  cases `coeffDegreeOfLE_map_C`, `coeffDegreeOfLE_one`;
  `univB_coeff` (the missing companion of `univA_coeff`), and the four
  `coeffDegreeOfLE_univA/univB_inl/inr` lemmas: the universal jet is linear in the jet unknowns and
  constant in the reciprocal ones, and dually;
  **`degreeOf_bilinSysPoly_inl`** and **`degreeOf_bilinSysPoly_inr`**:

  ```text
  degreeOf (inl i) (bilinSysPoly U V m n k) ≤ 1,   degreeOf (inr j) (bilinSysPoly U V m n k) ≤ 1.
  ```

  This closes the step flagged as outstanding when the bilinear system was first built: the `m + n`
  equations of the observation are, before any elimination, **linear in each group of unknowns
  separately**.  That is precisely the hypothesis a multihomogeneous Bezout count consumes, and it is
  the structural reason the honest answer is `choose(m+n,m)` rather than the product of the
  eliminated system's degrees.  The count itself still needs intersection theory on `P^m x P^n`;
  what is now machine-checked is that the system has the shape that theorem applies to.

- 2026-08-06 — **The observation's scalar equations, at any pair of depths.**
  `BilinearFibreSystem.lean`, `[propext, Classical.choice, Quot.sound]`:

  `criticalLowProduct_sub_one_coeff` — the compatibility defect coefficient by coefficient;
  **`criticalFibre_coeff_eq`** — for a fibre point and every `k` below the horizon,

  ```text
  ∑_{i≤k} a_i b_{k-i}  +  ∑_{i≤k} a_i v_{k-i}  +  ∑_{i≤k} u_i b_{k-i}  =  [k = 0].
  ```

  This is the general form of what was hand-rolled at depth two as `fibre_two_two_coeffs`: the `m+n`
  scalar equations of the observation, each visibly bilinear in the unknown low coefficients of the
  jet and of the reciprocal.  Any future depth-specific elimination starts here instead of being
  re-derived from the divisibility.

  Housekeeping in the same pass: `coeff_mul_range` moved from `DepthTwoGeneralPacketBound.lean` down
  to `TruncatedCompatibilityFibre.lean`, where both the depth-two work and the general bilinear
  layer can reach it, rather than being duplicated or imported sideways.

- 2026-08-06 — **The same bounds at the reciprocal depth.**  `SwappedFibreBounds.lean`, in the
  umbrella, all `[propext, Classical.choice, Quot.sound]`:

  `nat_card_criticalFibre_snd_one_le_of_tail` — at reciprocal depth one, any jet packet, the fibre
  has at most `criticalHorizonMultiplicity m 1` points;
  `nat_card_criticalFibre_snd_depth_two_le` — at reciprocal depth two, any `m`, the fibre is finite
  with the explicit bound;
  **`nat_card_criticalFibre_two_two_le_of_critical_fst`** — at both depths two, a critical observed
  **jet** packet already forces `Nat.card ≤ 12`.

  All three are transported through `criticalFibreSwap`, which exchanges the jet with its reciprocal
  and hence the two depths and the two packets.  The mathematical content is the existing proofs; the
  gain is in coverage and, at both depths two, in the hypothesis: finiteness now follows from
  *either* observed packet being critical, `u₂ ≠ 0` or `v₂ ≠ 0`, where before only the reciprocal
  packet would do.

  Regimes with an unconditional finiteness statement are now: depth one on either side (sharp), both
  depths two (bound `12`, from either packet), reciprocal depth two at any jet depth, jet depth two
  at any reciprocal depth, and — under the tower conditions — every pair of depths.

- 2026-08-06 — **Every critical-degree observation is realised.**  `CriticalFibreNonempty.lean`, in
  the umbrella, `[propext, Classical.choice, Quot.sound]`:

  `exists_monic_divisor_of_natDegree_le` — over an algebraically closed field a polynomial has a
  monic divisor of every degree up to its own: take any sub-multiset of that size of its roots and
  multiply the corresponding linear factors.  No nonvanishing hypothesis is needed — the zero
  polynomial has natural degree zero and the empty product serves;
  **`nonempty_criticalFibre_criticalTails`** — hence every observation whose packets have exactly
  the critical degrees admits at least one compatible source jet.

  This is the existence half of the card's theorem in the critical-degree regime, and unlike the
  count it needs **no separability**: a compatible jet exists whether or not the target `1 + U V` has
  distinct roots.  Previously nonemptiness was only available as a by-product of the exact count,
  which assumes separability, so the degenerate targets had no existence statement at all.

- 2026-08-06 — **The exact count for *every* critical-degree observation.**  Same module,
  `[propext, Classical.choice, Quot.sound]`:

  `exists_monic_divisor_roots_eq` — every sub-multiset of the root multiset is the root multiset of a
  monic divisor of that degree (the product of the corresponding linear factors, using mathlib's
  `roots_multiset_prod_X_sub_C`);
  **`nat_card_criticalFibre_eq_card_powersetCard`**:

  ```text
  Nat.card (criticalFibre K m n U V) = card ((1 + U V).roots.powersetCard m).toFinset
  ```

  with no separability hypothesis at all.  The fibre is in bijection with the monic degree-`m`
  divisors of the target, and those are in bijection with the **distinct** sub-multisets of size `m`
  of its root multiset — injectively because a monic split polynomial is its root multiset, and
  surjectively by the construction above.

  This subsumes the two earlier statements in the critical-degree regime and explains the gap between
  them: for a separable target the sub-multisets are the `choose(m+n,m)` subsets of a set of `m+n`
  distinct roots, giving the exact binomial count; repeated roots merge sub-multisets, and the count
  drops by exactly that merging.  The earlier `≤ choose(m+n,m)` is now the visible corollary that
  distinct sub-multisets are at most all of them.

- 2026-08-06 — **The depth-two count, before separability.**
  `nat_card_criticalFibre_two_two_eq_card_roots` in `DepthTwoGeneralPacketBound.lean`,
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card (criticalFibre K 2 2 U V) = card (criticalSextic u₂ u₃ v₂ v₃).roots.toFinset
  ```

  under `u₂ ≠ 0`, `v₂ ≠ 0` and `u₂v₃ + u₃v₂ ≠ 0`, over **any** field and with **no** separability
  hypothesis.  The exact count `6` is now the specialisation obtained by adding separability and
  algebraic closure, and the closure assumption turns out to be needed only for that last step — the
  bijection itself holds over any field, so the `IsAlgClosed` binder was dropped from it.

  This mirrors, at both depths two with unrestricted packets, exactly what
  `nat_card_criticalFibre_eq_card_powersetCard` does in the critical-degree regime: the fibre count
  is the number of *distinct* solutions of an explicit univariate object, and separability is what
  turns that number into the binomial coefficient.  Both regimes now expose the same structure, and
  in both the loss from repeated roots is visible rather than hidden behind a hypothesis.

- 2026-08-06 — **Depth one, before separability.**  `nat_card_criticalFibre_one_eq_of_tail` in
  `CriticalDegreeTailFibre.lean`, `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card (criticalFibre K 1 n U V) = Nat.card {a // a ≠ 0 ∧ (oneDeepEquation U v_n n).IsRoot a}
  ```

  for an arbitrary observed packet `V` with `X^n | V`, `deg V < 1+n`, `v_n ≠ 0`, over any field and
  with no separability.  The corpus already had this for a *monomial* packet
  (`OneDeepFibreBound.nat_card_criticalFibre_one_eq`); the transfer to arbitrary packets goes through
  `criticalSystemSolutionsCongrOne`, since at depth one the system reads only the packet's
  coefficient at the reciprocal depth.

  All three formalized regimes now have the same shape, stated before any separability hypothesis:

  | regime | the fibre is in bijection with |
  |---|---|
  | critical-degree packets, all depths | distinct sub-multisets of size `m` of the roots of `1 + U V` |
  | depth one, arbitrary packet | distinct nonzero roots of the depth-one equation |
  | both depths two, arbitrary packets | distinct roots of the sextic |

  In each, separability is exactly what turns the distinct-object count into `choose(m+n,m)`, and the
  drop caused by repeated roots is visible in the statement rather than excluded by hypothesis.

- 2026-08-06 — **Depth one with no degree restriction on the packet.**
  `nat_card_criticalFibre_one_eq_of_tail_of_dvd` in `CriticalDegreeTailFibre.lean`,
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card (criticalFibre K 1 n U V) = Nat.card {a // a ≠ 0 ∧ (oneDeepEquation U v_n n).IsRoot a}
  ```

  for `X^n | V` and `v_n ≠ 0`, with **no bound on the degree of `V`**.  The previous statement needed
  `deg V < 1 + n`; truncating the packet at the horizon, `V' = V %ₘ X^(1+n)`, changes neither the
  fibre (by `criticalFibreCongr`, since the difference is divisible by the horizon) nor the
  coefficient the depth-one equation reads, so the restriction was an artefact.

  The depth-one regime is now stated in its natural generality: any observed jet packet, any observed
  reciprocal packet of any degree, over any field, with no separability — and the count is the number
  of distinct nonzero roots of one explicit univariate polynomial.

- 2026-08-06 — **The critical-degree count at any packet length.**
  `nat_card_criticalFibre_eq_card_powersetCard_of_truncation` in `CriticalFibreNonempty.lean`,
  `[propext, Classical.choice, Quot.sound]`: for observations whose packets agree below the horizon
  with critical-degree ones,

  ```text
  Nat.card (criticalFibre K m n U V) = card ((1 + U' V').roots.powersetCard m).toFinset,
  ```

  with no bound on the packets' own degrees and no separability.  This is the separability-free
  strengthening of `nat_card_criticalFibre_of_truncation`, and it completes the pattern of the last
  three entries: every exact count on this card is now stated for packets of arbitrary length, over
  an arbitrary field where the argument allows it, with separability appearing only where it is
  genuinely used — to convert a count of distinct objects into the binomial coefficient.

- 2026-08-06 — **The exactness criterion at both depths two, as an iff.**
  `nat_card_criticalFibre_two_two_eq_iff` in `DepthTwoGeneralPacketBound.lean`,
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card (criticalFibre K 2 2 U V) = choose(4,2)  ↔  (criticalSextic u₂ u₃ v₂ v₃).roots.Nodup
  ```

  under `u₂ ≠ 0`, `v₂ ≠ 0`, `u₂v₃ + u₃v₂ ≠ 0` over an algebraically closed field.  Both directions:
  the fibre counts the *distinct* roots of a sextic all of whose six roots lie in the field, and a
  count of distinct elements reaches the cardinality exactly when there are no repeats.

  This is the first place on the card where the binomial count is characterised rather than merely
  achieved.  Until now separability was a sufficient hypothesis with no statement about necessity;
  here the multiplicity-free condition is proved to be exactly what `(2)` requires, so an observation
  failing it provably has *fewer* than `choose(m+n,m)` compatible jets.  The distinct-object
  formulations of the previous entries are what made the converse direction available at all.

- 2026-08-06 — **The exactness criterion at every pair of depths.**  `PowersetCardNodup.lean` and
  `nat_card_criticalFibre_eq_iff` in `CriticalFibreNonempty.lean`, all
  `[propext, Classical.choice, Quot.sound]`:

  `exists_le_card_eq`, `not_nodup_powersetCard_of_not_nodup`, **`nodup_powersetCard_iff`** — the
  sub-multisets of a fixed size `0 < m < card s` of a multiset are pairwise distinct **iff** the
  multiset has no repeated element.  Mathlib proves only the easy direction
  (`Multiset.Nodup.powersetCard`); the converse is the one a characterisation needs, and it is
  proved by exhibiting the repeat: a doubled element `a` gives `s = a ::ₘ a ::ₘ t`, and a
  sub-multiset `a ::ₘ w` with `w ≤ t` of size `m-1` then appears in **both** summands of
  `powersetCard_cons`;

  **`nat_card_criticalFibre_eq_iff`** — hence, for critical-degree packets at every pair of depths,

  ```text
  Nat.card (criticalFibre K m n U V) = choose(m+n,m)  ↔  (1 + U V).roots.Nodup.
  ```

  The depth-two criterion of the previous entry is now matched in the regime that covers all depths.
  Separability is no longer a hypothesis anywhere in the critical-degree regime: it is a *proved
  equivalent* of the binomial count, so an observation with a repeated target root has provably
  fewer than `choose(m+n,m)` compatible jets, and the card's `(2)` is characterised, not merely
  achieved.

- 2026-08-06 — **Both criteria in the separability phrasing.**
  `nat_card_criticalFibre_eq_iff_separable` and `nat_card_criticalFibre_two_two_eq_iff_separable`,
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card (criticalFibre K m n U V) = choose(m+n,m)  ↔  (1 + U V).Separable          (critical degrees)
  Nat.card (criticalFibre K 2 2 U V) = choose(4,2)    ↔  (criticalSextic ...).Separable (depth two)
  ```

  via mathlib's `nodup_roots_iff_of_splits`, which turns the multiplicity-free condition into
  separability for a split nonzero polynomial.

  The separability hypothesis that every count on this card has carried since the first divisor
  bijection is therefore not an artefact of the proof and not merely sufficient — it is exactly
  equivalent to the binomial answer, in both regimes where an exact count is known.  The card's `(2)`
  is now a characterisation wherever it is proved.

- 2026-08-06 — **The exactness criterion at depth one, completing the trio.**
  `nat_card_criticalFibre_one_eq_iff` in `CriticalDegreeTailFibre.lean`,
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Nat.card (criticalFibre K 1 n U V) = choose(1+n,1)
      ↔  (oneDeepEquation U v_n n).Separable ∧ ¬ (oneDeepEquation U v_n n).IsRoot 0
  ```

  for any observed packets with `X | U`, `X^n | V`, `v_n ≠ 0`, of any degree.  The corpus's
  depth-one count assumes both conditions; they are now proved **necessary** as well.  The argument
  splits on whether the origin is a root: if it is, the nonzero roots number at most `n`, so the
  count cannot reach `1+n` and the right side fails too; if it is not, the count is the number of
  distinct roots and reaching the degree is exactly separability.

  All three regimes with an exact count now have a matching characterisation:

  | regime | count is `choose(m+n,m)` iff |
  |---|---|
  | critical-degree packets, all depths | `1 + U V` is separable |
  | depth one, any packets | the depth-one equation is separable and nonzero at the origin |
  | both depths two, any packets | the sextic is separable |

  Nowhere on this card is separability now merely a convenient hypothesis; wherever `(2)` is proved,
  it is proved as an equivalence.

- 2026-08-06 — **Degenerate observations strictly lose jets.**  Three corollaries, all
  `[propext, Classical.choice, Quot.sound]`:

  `nat_card_criticalFibre_lt_of_not_separable` (critical degrees, all depths),
  `nat_card_criticalFibre_two_two_lt_of_not_separable` (both depths two),
  `nat_card_criticalFibre_one_lt_of_not` (depth one) — when the regime's exactness criterion fails,

  ```text
  Nat.card (criticalFibre K m n U V) < criticalHorizonMultiplicity m n
  ```

  strictly.  Each combines that regime's unconditional ceiling with its characterisation from the
  previous entries: `≤` and `≠` give `<`.

  So the picture in every regime with an exact count is complete in both directions.  A critical
  observation has at most `choose(m+n,m)` compatible jets always; exactly that many when the
  criterion holds; and strictly fewer when it fails.  There is no gap left in these regimes where the
  count is merely bounded — the degenerate case is now a theorem rather than an exclusion.

- 2026-08-06 — **The scaling symmetry of a horizon observation.**  `HorizonScalingSymmetry.lean`, in
  the umbrella, all `[propext, Classical.choice, Quot.sound]`:

  `coeff_comp_C_mul_X` — dilating by `t ↦ c t` multiplies the `i`-th coefficient by `c^i`;
  `comp_C_mul_X_comp`, `degree_comp_C_mul_X`, `X_pow_dvd_comp_C_mul_X_iff` — dilation is invertible,
  preserves degrees, and preserves divisibility by the horizon exactly (for `c ≠ 0`);
  **`criticalFibreScale`** — hence dilation is a *bijection*

  ```text
  criticalFibre K m n U V  ≃  criticalFibre K m n (U ∘ (c t)) (V ∘ (c t)),
  ```

  and `nat_card_criticalFibre_comp_C_mul_X` — the fibre count is an invariant of the scaling orbit of
  the observation, not of the observation itself.

  This is a genuine symmetry of the problem rather than a bookkeeping transport: it acts on the
  observation space by `u_i ↦ c^i u_i`, `v_j ↦ c^j v_j`, so every count on this card is constant
  along those orbits, and the exactness criteria are too — a target `1 + U V` is separable exactly
  when its dilate is.  It also says the genericity conditions cannot be sharpened to anything that
  distinguishes an observation from its dilates.

  (A `private` `coeff_comp_C_mul_X` for `ℂ` exists in `RHTower/CocycleExponentRigidity.lean`; being
  private it is unreachable, and the version here is over an arbitrary field and in the area that
  owns jet geometry.)

- 2026-08-06 — **The unit symmetry of the fibre.**  Same module, all
  `[propext, Classical.choice, Quot.sound]`:

  `criticalLowProduct_unit_scale` — scaling the jet by a constant and the reciprocal by its inverse
  leaves the low product **literally unchanged**, each of its three terms carrying one factor of each;
  **`criticalFibreUnitScale`** — hence

  ```text
  criticalFibre K m n U V  ≃  criticalFibre K m n (c U) (c⁻¹ V),
  ```

  and `nat_card_criticalFibre_unit_scale` for the counts.

  This is the second genuine symmetry of the observation space, and it is orthogonal to the dilation
  of the previous entry: dilation acts by `u_i ↦ c^i u_i` and moves the target, while this one fixes
  the target `1 + U V` exactly.  It is also strictly more general than
  `nat_card_criticalFibre_eq_of_target_eq`, which draws the same conclusion from equal targets but
  only for critical-degree packets — here the packets are arbitrary.

  Together the two symmetries say the fibre count is a function on the quotient of the observation
  space by a two-parameter group, which is a real constraint on what any formula for `(2)` can look
  like.

- 2026-08-06 — **Section 5's nonsingular locus, identified exactly.**
  `injective_transverseDifferential_iff` in `PadeHankelObstruction.lean`,
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Function.Injective (transverseDifferential p m n (m+n))  ↔  (padeHankel p m n).det ≠ 0.
  ```

  When section 5 was formalized I could only exhibit *one* jet with a nonsingular transverse system,
  the unipotent `1 + t^m`, and recorded that the card's claim of nonsingularity "on a nonempty open
  set" needed the locus itself.  This is that locus: the transverse convolution system degenerates
  at `p` exactly when `p` admits a Padé approximant of type `(m-1, n-1)` at the horizon, and those
  jets are cut out by the vanishing of one explicit determinant.  So the nonsingular locus is the
  complement of the Padé–Hankel hypersurface — open, and nonempty because the unipotent jet lies in
  it.  No hypothesis beyond `p` being a polynomial; the depth positivity the first proof carried is
  not needed.

  The two halves of the machinery meet here: the Hankel determinant was built to express the
  obstruction between two fibre points, and it turns out to be the same determinant that governs
  whether a transverse channel lifts uniquely.

- 2026-08-06 — **Section 5 at every nonsingular longitudinal jet.**
  `TransverseChannelGeneral.lean`, in the umbrella, all `[propext, Classical.choice, Quot.sound]`:

  `bijective_transverseDifferential_of_det`, `exists_unique_transverse_of_det`,
  `nat_card_transverseFibre_of_det`, and
  **`nat_card_criticalFibre_prod_transverse_channels_of_det`** — the whole of section 5, now stated
  for **any** longitudinal jets `P i` with `det (padeHankel (P i) m n) ≠ 0` rather than for the one
  unipotent jet the original formalization used.  Different channels may sit over different jets.

  With the locus identified in the previous entry, section 5 now says what the card says: on the
  nonempty open set where the transverse convolution determinant does not vanish, every transverse
  channel has exactly one lift, so projective dimension multiplies the critical count by one.  The
  original `1 + t^m` statements remain as the witness that the locus is inhabited.

- 2026-08-06 — **The Pascal determinant is one.**  Same module,
  `[propext, Classical.choice, Quot.sound]`:

  `padeHankel_one_add_X_pow_apply` — at the unipotent jet the Hankel entry at `(r, j)` is
  `[m + r = j] + [r = j]`;
  **`det_padeHankel_one_add_X_pow`** — hence the matrix is the identity plus a strictly upper
  triangular part (`m + r = j` forces `j > r`), and

  ```text
  det (padeHankel (1 + t^m) m n) = 1;
  ```

  `det_padeHankel_one_add_X_pow_ne_zero` — so the unipotent jet lies in the nonsingular locus, with
  the determinant at its simplest possible value.

  This is the card's own sentence, *"the transverse Pascal determinant is one"*, now a theorem rather
  than a description.  When section 5 was first formalized I flagged that claim as loose — the
  determinant is **not** identically one, and at `p = 1` the system is degenerate — and the honest
  statement was that the nonsingular locus is nonempty.  With the locus now identified as a
  determinantal complement, the card's phrasing is recovered exactly: the value is one at the
  unipotent jet, and that is what inhabits the locus.

- 2026-08-06 — **Section 4 is formalized: the Chow ring of `P^m × P^n` and the intersection
  number.**  New module `formal/GaloisForLFunctions/HTGeometry/BiprojectiveChowRing.lean`, wired into
  the `HTGeometry` umbrella, every declaration `[propext, Classical.choice, Quot.sound]`:

  `chowIdeal m n = (H₁^(m+1), H₂^(n+1))` in `ℤ[H₁,H₂]`, `ChowProd m n` the quotient, with the
  hyperplane classes `chowH₁`, `chowH₂` and the point class `chowTop = H₁^m H₂^n`;

  `coeff_mul_X_pow_eq_zero` — general infrastructure absent from mathlib: a product carrying a factor
  `X i ^ k` has vanishing `d`-coefficient whenever `d i < k`;

  `chowH₁_pow_eq_zero`, `chowH₂_pow_eq_zero` — the two truncation relations;

  `coeff_chowBoxExponent_eq_zero_of_mem` — the coefficient functional at any exponent *inside* the
  box `[0,m] × [0,n]` annihilates the truncation ideal, so it descends to the Chow ring;

  `chow_box_independent` — the box monomials are ℤ-linearly independent, i.e. the Chow ring is free
  abelian on them; `chowTop_ne_zero` and `intCast_mul_chow_box_eq_zero_iff` are the torsion-freeness
  needed to read a degree off a class;

  **`chow_hyperplane_sum_pow`** — the card's `(7)`–`(8)`:

  ```text
  (H₁ + H₂)^(m+n) = choose (m+n) m · H₁^m H₂^n   in ℤ[H₁,H₂]/(H₁^(m+1), H₂^(n+1)),
  ```

  proved by binomial expansion: the term with `H₁`-exponent `k > m` dies by the first truncation,
  the term with `k < m` has `H₂`-exponent `m+n-k > n` and dies by the second, so exactly one term
  survives;

  `chow_degree_unique` — and the integer is unique: any `c` with
  `(H₁+H₂)^(m+n) = c · H₁^m H₂^n` equals `criticalHorizonMultiplicity m n`.

  This replaces the one-variable proxy `criticalHorizonMultiplicity_eq_chowCoefficient`
  (`((X+1)^(m+n)).coeff m`) that had been standing in for section 4.  The proxy was a correct
  binomial identity but said nothing about `P^m × P^n`; the statement now lives in the actual Chow
  ring, with the truncation relations and the freeness that make "the degree is the coefficient of
  `H₁^m H₂^n`" a theorem rather than a convention.

  What section 4 still needs, and what this does not supply, is the *cycle-class map*: that the
  fibre's `m+n` compatibility divisors — already proved to be of bidegree `(1,1)` in
  `BilinearFibreSystem.lean` — have Chow class `H₁ + H₂`, and that a proper intersection of them has
  cardinality equal to the degree of the product class.  That is multihomogeneous Bézout, and it
  remains the single open core of the card for generic `m, n ≥ 2`.  The algebra of section 4 is now
  closed; the geometry that feeds it is not.

- 2026-08-06 — **The bigraded Hilbert identity: the numerical core of bihomogeneous Bézout.**
  New module `formal/GaloisForLFunctions/HTGeometry/BihomogeneousHilbertIdentity.lean`, wired into
  the `HTGeometry` umbrella, every declaration `[propext, Classical.choice, Quot.sound]`:

  `prod_range_add_one_eq_factorial_mul_choose` — the rising product `∏_{i<m}(j+i+1) = m! · C(j+m,m)`;

  `choosePoly m` — the rational polynomial `x ↦ C(x+m, m)`, with `eval_choosePoly` (it computes the
  binomial at every natural argument), `natDegree_choosePoly = m`, `leadingCoeff_choosePoly = 1/m!`;

  `bezoutPoly m n c = choosePoly m · choosePoly n (· + c)`, of degree exactly `m+n` and leading
  coefficient `1/(m! n!)`;

  **`alternating_sum_choose_mul_choose`** — for all `m, n, c, j`:

  ```text
  ∑_(k ≤ m+n) (-1)^(m+n-k) C(m+n,k) · C(j+k+m, m) · C(j+k+c+n, n) = C(m+n, m),
  ```

  with `alternating_sum_choose_mul_choose_int` the integral form.

  This is the Hilbert function, in bidegree `(d, d+c)` for `d = j+m+n`, of the bigraded coordinate
  ring of `P^m × P^n` modulo a regular sequence of `m+n` forms of bidegree `(1,1)`: the Koszul
  numerator `(1-st)^(m+n)` against the denominator `(1-s)^(m+1)(1-t)^(n+1)`.  The theorem says that
  function is *constant*, equal to the bihomogeneous Bézout number `C(m+n,m)` — so a proper such
  intersection has at most `C(m+n,m)` points.

  Mechanism: reversing the summation index turns the sum into the `(m+n)`-th forward difference of
  `bezoutPoly` at `j`, and the `L`-th difference of a degree-`L` polynomial is `L!` times its leading
  coefficient, here `(m+n)!/(m! n!)`.  mathlib supplies the difference calculus
  (`fwdDiff_iter_eq_sum_shift`, `Polynomial.fwdDiff_iter_degree_eq_factorial`); the binomial-as-a-
  polynomial layer and the identity itself were absent and are built here.

  Together with `BiprojectiveChowRing.lean` this closes both *numerical* routes to the card's `(8)` —
  the Chow-ring computation and the Hilbert-series computation now agree, unconditionally, in Lean.
  What is still missing for `(2)` at generic `m, n ≥ 2` is the commutative algebra that connects them
  to the fibre: that the `m+n` bidegree-`(1,1)` compatibility forms are a regular sequence when the
  intersection is finite, Koszul exactness for that sequence, and the surjectivity of evaluation at
  the finitely many points in large bidegree.  That chain is the remaining open core.
