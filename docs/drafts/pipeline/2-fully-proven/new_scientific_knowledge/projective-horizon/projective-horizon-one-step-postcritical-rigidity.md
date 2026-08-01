# One postcritical reciprocal coefficient collapses the entire horizon ambiguity

- **ID:** `projective-horizon-one-step-postcritical-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / SHARP BIRATIONAL PAGE TRANSITION
- **Scientific status:** `[PROVED HERE] [NOVELTY PROVISIONAL] [SIGNIFICANT] [FORMAL CORE COMPLETE]`
- **Parents:** `hypertranscendental-maximal-finite-horizon-galois-law`,
  `projective-horizon-pure-tail-fermionic-fiber`
- **Lane:** source-pure hypertranscendental geometry; finite-resolution reconstruction

## Theorem

Let `f` be hypertranscendental over a characteristic-zero differential field `F`.  Write

```text
x_i=D^i f/i!,
y_i=D^i(f^(-1))/i!,
J_N=F(x_0,...,x_N),
O_(m,n;N)=F(x_m,...,x_N,y_n,...,y_N).                     (1)
```

For `m,n>=1`, put `L=m+n`.  Then the finite ambiguity is confined to exactly one resolution:

```text
[J_(L-1):O_(m,n;L-1)]=choose(L,m),
Gal(normalClosure)=S_(choose(L,m)),                        (2)

O_(m,n;N)=J_N                    for every N>=L.           (3)
```

Equivalently, after adjoining the new raw coordinate `x_L` to the critical fields, the single
postcritical reciprocal coefficient is a primitive generator:

```text
O_(m,n;L-1)(x_L,y_L)=J_(L-1)(x_L)=J_L.                    (4)
```

In particular,

```text
[O_(m,n;L-1)(x_L,y_L):O_(m,n;L-1)(x_L)]=choose(L,m),      (4a)
Gal(normalClosure of minpoly(y_L))=S_(choose(L,m)).        (4b)
```

One scalar postcritical response carries the complete critical extension, including its full
monodromy.

Thus the critical binomial ambiguity does not persist for a second derivative resolution.  The
complete finite-order law is

```text
N<L-1 : positive hidden transcendence dimension,
N=L-1 : finite atomic ambiguity of degree choose(L,m) and group S_D,
N>=L  : birational reconstruction; only compatibility relations remain.     (5)
```

## Proof

### 1. The critical extension is field-primitive

Let

```text
K=F(x_0,...,x_(L-1)),
H=O_(m,n;L-1).                                             (6)
```

The maximal finite-horizon Galois theorem proves `[K:H]=D=choose(L,m)` with normal-closure group
`S_D`.  The field `K` is the fixed field of a point stabilizer `S_(D-1)`, which is maximal in
`S_D`.  Therefore

```text
H subset M subset K  implies  M=H or M=K.                  (7)
```

The next raw jet `u=x_L` is transcendental over `K`.  Base extension preserves `(7)`, so there is
still no field properly between `H(u)` and `K(u)`.

The reciprocal recurrence makes

```text
v=y_L in K(u).                                             (8)
```

It remains only to prove `v notin H(u)`.  Equation `(7)` will then force

```text
H(u,v)=K(u),                                               (9)
```

which is `(4)`.

### 2. The pure fiber proves that `y_L` is not a base function

Use the unramified pure critical value

```text
x_m=y_n=1,
x_(m+1)=...=x_(L-1)=0,
y_(n+1)=...=y_(L-1)=0.                                   (10)
```

Its `D` states are the factor pairs

```text
X_0 Y_0=1+t^L,
deg X_0=m,  deg Y_0=n,                                    (11)
```

labelled by the `m`-subsets of the `L` distinct roots of `1+t^L`.  Add one more raw and reciprocal
coefficient:

```text
X=X_0+u t^L,       Y=Y_0+v t^L.                           (12)
```

Taking the coefficient of `t^L` in `XY=1 mod t^(L+1)` gives the exact equation

```text
1+u Y_0(0)+v X_0(0)=0.                                    (13)
```

At `u=0`, every factor state therefore has

```text
v=-X_0(0)^(-1).                                           (14)
```

This value is not constant on the pure fiber.  Choose an `m`-subset containing one root `alpha`
and not another root `beta`, then exchange them.  The two monic left factors have constant terms
whose ratio is `beta/alpha!=1`, so `(14)` differs.

The pure fiber is reduced and etale because `1+t^L` is separable.  A rational function belonging
to the base field `H(u)` is constant on every etale fiber where its pullback is regular.  But `v` is
regular and takes distinct values on the fiber above `(10),u=0`.  The difference of those two
etale-local branches is nonzero at the pure point, hence remains nonzero on a neighborhood.  That
neighborhood meets the domain of every rational base representative, so possible indeterminacy at
the single pure value cannot hide the nonconstancy.  Hence

```text
v notin H(u).                                              (15)
```

Equations `(7),(9),(15)` prove `(4)`.

### 3. All later resolutions

For `N>L`, the observation field contains the order-`L` field in `(4)` and also the raw coordinates
`x_(L+1),...,x_N`.  Therefore it contains every generator of `J_N`; the reverse inclusion is
tautological because reciprocal jets are rational functions of raw jets.  This proves `(3)`.
Together with the finite Page rank theorem and `(2)`, it proves `(5)`.  `QED`

## Physical meaning

The Page point is a single algebraic diffraction layer, not a persistent hidden sector.  Exactly at
critical resolution there are `D` maximally braided states and no partial state variable.  Extending
the raw source by one new coordinate leaves that atomic ambiguity intact, but its one complementary
reciprocal response separates it completely.  Every later response is redundant compatibility
data.

Equation `(4)` is an exact finite algebraic form of holography: one distinguished boundary
coefficient generates the field of every missing low jet.  Its degree-`D` equation retains all
critical sheets and full `S_D` braiding.  This use of "holography" means primitive field encoding;
there is no gravitational bulk, area law, Hilbert space, or black-hole dynamics.

This is a static observability theorem.  Derivative resolution is not elapsed time, and the
collapse in `(5)` is not measurement dynamics, wave-function collapse, evaporation, or entropy
release.

## Novelty and significance audit

The field-theoretic implication "a nonconstant element generates a primitive extension" is
classical.  Factorization of `1+t^L` and the coefficient equation `(13)` are elementary.  The new
candidate content is their exact conjunction with the full-symmetric critical horizon theorem,
which proves the sharp all-rank degree profile `(5)`: a binomial `S_D` ambiguity at one and only one
resolution, followed immediately by birational reconstruction.

Targeted searches in reciprocal-series, Padé/Hermite--Padé, jet-space, sparse-monodromy, and Page
transition literature found no matching raw/reciprocal field theorem.  Hermite--Padé theory does
contain adjacent block-Toeplitz determinants and isomonodromic structures, for example
Mano--Tsuda ([arXiv:1502.06695](https://arxiv.org/abs/1502.06695)), but not `(2)--(5)`.  Novelty is
provisional pending specialist audit.

The theorem materially strengthens the Page-rank law and the critical monodromy theorem by
classifying the extension at every resolution, rather than only its dimension or its critical
fiber.  It remains below the Fields-Medal completion bar: no external major problem is solved and
expert novelty validation is absent.

## RH impact

For Riemann zeta, the theorem closes the finite raw/reciprocal reconstruction question exactly.
At the critical order, low zeta jets have binomial full-symmetric ambiguity; one further reciprocal
jet reconstructs them rationally, and all later data impose relations rather than new hidden
freedom.

This is useful as a no-waste theorem for finite-jet RH proposals: adding more than one
postcritical order cannot reveal a new universal state variable.  It still does not imply RH.  The
reconstruction is target-translation blind and contains neither Euler orientation nor a mechanism
placing zero-cones on the critical line.

## Lean verification

`ProjectiveHorizonPostcriticalRigidity.lean` formalizes:

- the exact root-subset and complementary-factor construction for the pure critical fiber;
- canonical indexing of all roots of `1+X^L`, with injectivity and nonvanishing;
- recovery of `1+X^L` as the product over that root indexing;
- existence, for every `m,n>0`, of two genuine complementary factor pairs whose left constant
  coefficients differ;
- the first postcritical extensions of the pure critical factor pair;
- the exact top coefficient `(13)` over every commutative ring;
- extraction of `(13)` from divisibility by `t^(L+1)`;
- the explicit specialization `v=-X_0(0)^(-1)` over a field when `u=0`.

The key new endpoint is
`exists_pureCriticalRootFactorPairs_coeff_zero_ne`; its two factor pairs both multiply to
`pureCriticalCyclicPolynomial (m+n)`, and their left constant coefficients are unequal.  Thus the
pure-fiber nonconstancy argument through `(14)` is formalized, rather than merely represented by
the coefficient recurrence.

The global primitive-field step `(7)--(9)` and the etale rational-descent argument converting this
explicit fiber witness into `v notin H(u)` remain paper-level, so the card remains in stage 2.  A
targeted leaf check and axiom audit pass; the new endpoint uses only `propext`, `Classical.choice`,
and `Quot.sound`.  No full or module build was run.

## Log

- 2026-08-01 — **Step 1's field-primitivity `(7)` is formalized.**
  `formal/GaloisForLFunctions/HTGeometry/CoatomFixedField.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `isCoatom_stabilizer_perm` — a point stabilizer in a symmetric group is a maximal subgroup, through
  mathlib's primitivity of the natural action;
  `eq_bot_or_eq_of_isCoatom_fixingSubgroup` — if the fixing subgroup of an intermediate field is
  maximal, then **no field lies strictly between the base and it**: any field below is the base or the
  field itself.  Together these are `(7)`: `K` is the fixed field of a point stabilizer `S_(D-1)`,
  which is maximal in `S_D`, so `H ⊆ M ⊆ K` forces `M = H` or `M = K`.

  The base-extension clause of step 1 — "base extension preserves `(7)`" for the transcendental
  `u = x_L` — is the free-parameter theorem proved for the rank-one card,
  `freeParameterBaseChange` in `FreeParameterBaseChange.lean`: adjoining an independent
  transcendental leaves the Galois group unchanged, hence leaves the lattice of intermediate fields
  unchanged.

  What remains paper-level on this card is `(8)`, `v = y_L ∈ K(u)`, and the etale rational-descent
  step converting the explicit pure-fiber witness into `v ∉ H(u)`.

- 2026-08-01 — **Step `(8)` is formalized: the reciprocal coefficients add no field elements.**
  `formal/GaloisForLFunctions/HTGeometry/ReciprocalCoefficientField.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `constantCoeff_mul_coeff_inverse` — the coefficient equation of an inverse pair,
  `x_0 y_n = -∑_(i=1)^n x_i y_(n-i)`, obtained by reading `X Y = 1` in degree `n`;
  `coeff_inverse_mem_subfield` — hence **every** coefficient of the inverse lies in any subfield
  containing the coefficients of the jet, by strong induction on `n`: the constant term of the
  inverse is the inverse of the constant term, and each later one is that inverse times a
  combination of earlier ones.

  With `v = y_L` and the subfield `K(u) = F(x_0, …, x_L)`, this is `(8)`.

  So of step 1 only the descent `v ∉ H(u)` is left: `(7)` is `CoatomFixedField.lean`, its
  base-extension clause is `freeParameterBaseChange`, and `(8)` is here.

- 2026-08-01 — **The fiber witness now separates the postcritical value.**
  `formal/GaloisForLFunctions/HTGeometry/PostcriticalFiberSeparation.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `exists_pureCriticalRootFactorPairs_neg_inv_ne` — two states of the pure critical fiber factor the
  same `1 + t^L` and receive **different** values of `-(A(0))⁻¹`, which by
  `pureCriticalPost_rightTop_eq_neg_inv` is the first postcritical reciprocal coefficient at
  vanishing new raw coefficient.  The step from the existing witness is that inversion is injective,
  so distinct constant terms give distinct postcritical values.

  This is the witness in the form the descent consumes: over one critical observation the
  postcritical reciprocal coefficient takes two values, so it is not a function of the critical data.
  Turning that into `v ∉ H(u)` still needs the rational-descent argument, which is where the
  observation "same critical data" has to be converted into an equality of specialisations — the one
  paper-level step of this card.

- 2026-08-01 — **The engine of the rational-descent step is formalized.**
  `formal/GaloisForLFunctions/HTGeometry/SpecializationDescent.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `not_mem_adjoin_simple_of_ne` — if two `F`-algebra specialisations of a subalgebra agree at an
  element `g` but take different values at an element `v`, then `v ∉ F⟮g⟯`.  With `F = H` and
  `g = u` this is exactly `v ∉ H(u)`, the step this card has carried as paper-level.

  The content is `eq_of_mem_adjoin_simple`: a specialisation is **determined** on a simply generated
  subfield.  The obstacle is that a fraction's denominator may be killed by the specialisation, and
  the argument that it cannot be is the following.  Write `v = r(g) / s(g)` and cancel the greatest
  common divisor, leaving `r'` and `s'` coprime; the cancelled factor cannot vanish at `g` because
  the denominator does not.  A Bézout identity `u₁ r' + u₂ s' = 1` then evaluates at `g` inside the
  subalgebra, so if the specialised `s'(g)` vanished, the relation `v · s'(g) = r'(g)` — which holds
  in the subalgebra, not merely in the fraction field — would force `r'(g)` to vanish too, and
  Bézout would read `0 = 1`.  So the denominator survives, and `v` is determined by the specialised
  values of `r'(g)` and `s'(g)`, which agree for the two specialisations by
  `eq_aeval_of_eq`.

  What this leaves for the card is the construction of the two specialisations themselves: turning
  the fibre witness `exists_pureCriticalRootFactorPairs_neg_inv_ne` into two `H`-algebra maps on a
  subalgebra containing `u` and `v`, agreeing at `u` and differing at `v`.  The descent itself is no
  longer paper-level — only the passage from the two fibre points to the two algebra maps is.

- 2026-08-01 — **The descent engine now matches the card's situation, and is shown non-vacuous.**
  `formal/GaloisForLFunctions/HTGeometry/SpecializationDescent.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  The first version of the engine required the two specialisations to be `H`-algebra maps, that is,
  to **fix** `H`.  That is wrong for this card: the two fibre points do not fix the critical data,
  they merely give it the same value.  So `eq_aeval_of_eq`, `eq_of_mem_adjoin_simple` and
  `not_mem_adjoin_simple_of_ne` now take plain ring maps together with the hypothesis that they
  **agree** on the base,

  ```text
  ∀ a : H,  π₁ (a) = π₂ (a),     π₁ u = π₂ u,     π₁ v ≠ π₂ v   ⟹   v ∉ H(u),
  ```

  which is exactly "same critical observation, same new raw coefficient, different postcritical
  value".  The polynomial step is now an induction over monomials rather than a use of the algebra
  structure.  `not_mem_adjoin_simple_of_ne_algHom` keeps the algebra-map form as a corollary.

  `X_one_not_mem_adjoin_X_zero` is a worked instance: inside the fraction field of the polynomial
  algebra in two variables, evaluation at `(0,0)` and at `(0,1)` agree at the first variable and
  differ at the second, so the second variable is not a rational function of the first.  The
  hypotheses are therefore satisfiable and the conclusion is not vacuous.

  What is left on this card is the construction of the two specialisations of the jet algebra from
  the two occupation states of `exists_pureCriticalRootFactorPairs_neg_inv_ne`: a ring map on the
  algebra generated by `x_0, …, x_L, y_0, …, y_L` sending each generator to its pure-fibre value for
  that state.  The relations to check are the reciprocal recurrence, which the two factorisations
  satisfy by construction.
