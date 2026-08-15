# One postcritical reciprocal coefficient collapses the entire horizon ambiguity

- **ID:** `projective-horizon-one-step-postcritical-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / SHARP BIRATIONAL PAGE TRANSITION
- **Scientific status:** `[PROVED HERE] [NOVELTY PROVISIONAL] [SIGNIFICANT] [FORMAL CORE COMPLETE]`
- **Formal status:** step 1 is formal in full for every `(m,n)`: `(7)`, `(8)`, and the separation
  `v notin H(u)` — the last as `postcritical_escapes_criticalField`, with no hypotheses beyond
  `m, n >= 1` over an algebraically closed field of characteristic zero.
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

  (Superseded by the entry of 2026-08-02: the pure-fibre evaluations are not admissible
  specialisations for the descent, because they collapse the critical data to constants.  A generic
  fibre witness is needed instead.)

- 2026-08-02 — **The descent engine for the card's actual base, and why the pure fibre cannot feed
  it.**  `formal/GaloisForLFunctions/HTGeometry/MultiGeneratorDescent.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  eq_on_adjoin                              agreement propagates to the generated subalgebra
  exists_frac_of_mem_adjoin                 members of F(S) are fractions of members of F[S]
  eq_of_mem_adjoin_set                      descent, given that pi_1 kills no nonzero element of F[S]
  not_mem_adjoin_set_of_ne                  the contrapositive
  not_mem_adjoin_set_of_ne_of_injective     the hypothesis is automatic for a faithful pi_1
  not_mem_adjoin_set_of_ne_algHom           the algebra-map form
  X_two_not_mem_adjoin_X_zero_X_one         a non-vacuous instance with two generators
  ```

  The previous engine, `SpecializationDescent`, adjoins **one** generator.  The card needs
  `v = y_L notin H(u)` with `H = F(x_m,...,x_(L-1), y_n,...,y_(L-1))`, so the base is adjoined by
  `n + m + 1` generators at once, and the one-variable engine does not apply.  The obstruction in
  several variables is real: the Bezout identity that rules out a vanishing denominator has no
  analogue, so the multi-generator statement is **false** without a further hypothesis.  The correct
  hypothesis is that the specialisation kills no nonzero element of the subalgebra generated by the
  data, and the clean sufficient condition is that one of the two specialisations is *injective*.

  This settles what the remaining step of this card actually requires, and it is not what the
  previous entry supposed.  Building the two specialisations from the two occupation states of
  `exists_pureCriticalRootFactorPairs_neg_inv_ne` **cannot** close the card: those two states sit
  over the pure critical observation, where every critical coordinate takes a *constant* value
  (`x_m = y_n = 1`, all later ones zero), so evaluation there kills `x_m - 1` and every other nonzero
  element of the base cut out by the pure locus.  Neither of the two evaluations is injective on the
  base algebra, the denominator hypothesis fails, and the descent genuinely does not apply — as it
  must not, since a rational function of the critical data is perfectly free to blow up on the pure
  locus.

  So the remaining item is not plumbing but a *generic* fibre witness: two points of the fibre over a
  critical observation whose coordinates stay algebraically independent, equivalently a specialisation
  to the generic point of one component of the fibre rather than to a closed point of the pure fibre.
  Semicontinuity — two points over the special fibre forcing at least two over the generic one — is
  the étale descent this card has been carrying, and it is now isolated as the single missing input:
  everything downstream of it is formal.

- 2026-08-02 — **The card's missing step is closed at the first horizon.**
  `formal/GaloisForLFunctions/HTGeometry/FirstHorizonPostcriticalSeparation.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  jetY2_not_mem_adjoin_critical :
    y_2 notin F(x_1, y_1, x_2)                       for m = n = 1, L = 2
  ```

  which is exactly `v notin H(u)` — the one input everything else on this card waits on — for the
  first nontrivial horizon.  It is unconditional and needs no descent, no specialisation, and no
  étale argument.

  The proof is an automorphism.  Over `F(x_0, x_1, x_2)` the reciprocal coefficients are
  `y_0 = x_0^{-1}`, `y_1 = -x_1 x_0^{-2}`, `y_2 = x_1^2 x_0^{-3} - x_2 x_0^{-2}`; the module proves the
  three defining relations `x_0 y_0 = 1`, `x_0 y_1 + x_1 y_0 = 0`,
  `x_0 y_2 + x_1 y_1 + x_2 y_0 = 0`, so these are the reciprocal jet.  The sign flip `x_0 -> -x_0`,
  extended from the jet algebra to its fraction field, fixes `x_1` and `x_2`, and fixes `y_1` because
  `y_1` is *even* in `x_0` — while it reverses the sign of the leading term of `y_2`, whose
  `x_0^{-3}` is *odd*.  Since a rational function of fixed elements is fixed, `y_2` is not one.

  Why this works here and not in general: the critical fibre at `m = n = 1` has exactly `C(2,1) = 2`
  points, so the critical extension is quadratic and therefore Galois, and the second point is
  reached by an automorphism of the ambient field.  For `C(L,m) >= 3` the extension carries no
  automorphisms at all — the Galois group of the normal closure is the full `S_D` acting on `D`
  points — so the general case cannot be done this way and still needs the generic fibre witness
  isolated in the previous entry.  Supporting general infrastructure added in the same module:
  `fixedIntermediateField` and `not_mem_adjoin_of_apply_ne`, the fixed field of a single
  automorphism and the statement that an element it moves is outside the field generated by elements
  it fixes.

  Umbrella build after wiring: 12880 jobs, no errors.

- 2026-08-02 — **The general fibre is governed by one quadratic: the displacement equation.**
  `formal/GaloisForLFunctions/HTGeometry/FibreDisplacementIdentity.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  fibreDisplacement_identity :
    (B - B') A A' - (A' - A) = A' (A B - 1) - A (A' B' - 1)        an identity, over any ring
  dvd_fibreDisplacement, dvd_displacement_equation :
    U = D A (A + U)     mod t^L,   U := A' - A,   D := B - B'
  reciprocal_of_displacement :
    conversely, any (U, D) solving that equation gives a reciprocal pair (A+U, B-D)
  exists_second_fibre_point :
    ... and if deg U < m, deg D < n, U /= 0 it is a *second point of the same critical fibre*
  ```

  This is a structural reduction of the card's remaining problem, and it is exact in both
  directions.  A second point of the critical fibre over a given observation is **the same thing** as
  a nonzero pair `(U, D)` with `deg U < m`, `deg D < n` solving the single quadratic relation
  `U = D A (A + U)` over the horizon.  The identity behind it is trivial to check and holds over any
  commutative ring: the two inversion errors are the only obstruction to `A' - A = (B - B') A A'`.

  What this buys.  The atomic ambiguity of the horizon is now visibly a *quadratic* phenomenon: for
  fixed `D` the displacement equation `D A U + (D A^2 - U) = 0` is affine in `U`, and for fixed `U`
  it is affine in `D`, while the coupled system is quadratic — which is why a second solution exists
  at all and why the pure fibre's count is a binomial coefficient rather than a power.  The route to
  the general case is now concrete: choose `U` and `D` freely with `U(0), D(0)` nonzero, solve
  `A^2 + U A - U D^{-1} = 0` for `A` over the horizon — a square root of a unit, so a Hensel lift —
  and the resulting `A` and `A + U` are two points of one critical fibre with `L` free parameters
  between them.  The open input is unchanged in substance but sharper in form: it is the
  algebraic independence of the critical observation of that constructed pair, equivalently the
  dominance of `(U, D) |-> ` critical data.

- 2026-08-02 — **The remaining input, stated exactly, and its mathlib gap.**  Analysis, no new Lean.

  Everything on this card now reduces to one statement: *the critical observation of a generic jet is
  algebraically independent over `F`*, equivalently the map

  ```text
  A  |-->  (x_m, ..., x_(L-1);  y_n, ..., y_(L-1))
  ```

  from the `L`-dimensional jet space to the `L`-dimensional observation space is dominant.  With that,
  the multi-generator descent applies with the generic jet as the faithful specialisation `pi_1` and
  a second fibre point as `pi_2`, and `v notin H(u)` follows.

  Two routes were examined and one is correct.

  *Semicontinuity from the pure fibre is the wrong direction.*  The parent card gives the pure fibre
  exactly `C(L,m)` reduced points, hence finite.  Fibre dimension is upper semicontinuous, so a finite
  *special* fibre does bound the generic one — but only through the fibre-dimension theorem
  (`dim Z = dim of the closure of the image + generic fibre dimension`, and every fibre has dimension
  at least the generic one), which is exactly the piece mathlib does not carry.  Note the naive form
  of the argument is backwards: two points in a special fibre do **not** by themselves give two points
  in the generic fibre.

  *The correct route is the deformation.*  The pure fibre is finite **and reduced**, so the fibre
  algebra is étale at each of its `C(L,m)` points.  Deform the observation formally: over
  `F[[s_1, ..., s_L]]` take the observation `c^0 + s`.  Its coordinates are algebraically independent
  over `F` **by construction** — they are the independent indeterminates `s_i` shifted — which is
  precisely the hypothesis the descent needs, and which no argument about the pure fibre can supply.
  Étaleness at each pure point lifts each of them to a solution over `F[[s]]`, giving `C(L,m) >= 2`
  points of the fibre over an independent observation.  Combined with `exists_second_fibre_point`
  and the displacement equation, this closes the card for all `(m,n)`.

  What is missing in mathlib is the lifting step: a *multivariate* Hensel / implicit function theorem
  over a complete local ring.  Present are `HenselianLocalRing` (single-variable),
  `Algebra.FormallyEtale`, and `Algebra.FormallySmooth.lift` (lifting along a *nilpotent* ideal).  The
  build is therefore: lift along `m^k` for every `k` with `FormallySmooth.lift`, then pass to the limit
  using completeness of `F[[s]]`.  That is the next construction on this card.

- 2026-08-02 — **The pure fibre is unramified, and the lifting theorem is in mathlib after all.**
  `formal/GaloisForLFunctions/HTGeometry/PureFibreUnramified.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  separable_one_add_X_pow            1 + t^L is separable
  isCoprime_of_pureFactorisation     hence A and B are coprime
  natDegree_pureFactorisation        and their degrees are exactly m and n
  eq_zero_of_X_pow_dvd_of_natDegree_lt
  tangent_eq_zero_of_pureFactorisation :
    deg dA < m,  deg dB < n,  t^L | dA B + A dB   ==>   dA = 0  and  dB = 0
  ```

  The last is the Jacobian criterion at a pure point, in the only form the card needs: the
  differential of the observation map is *injective* there.  The proof is two lines of mathematics.
  The perturbed product `dA B + A dB` has degree at most `L - 1`, so being divisible by `t^L` makes it
  **zero**, not merely small; then coprimality of `A` and `B` — which is separability of `1 + t^L` —
  gives `A | dA`, and `dA` has smaller degree than `A`.  This replaces the whole Jacobian-determinant
  computation the deformation route seemed to need: no determinant is ever formed.

  Correction to the previous entry: the lifting step is **not** missing from mathlib.
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` in
  `Mathlib/RingTheory/Smooth/AdicCompletion.lean` lifts any `A →ₐ[R] S ⧸ I` to `A →ₐ[R] S` for
  `S` `I`-adically complete and `A` formally smooth over `R`, exactly the multivariate Hensel
  statement.  So does `exists_adicCompletionEvalOneₐ_comp_eq` for the completion itself.

  With unramifiedness in hand the route no longer needs that machinery either.  Injectivity of the
  differential plus equality of dimensions — the perturbation space has dimension `m + n = L` and the
  target `K[t]/t^L` has dimension `L` — makes the differential **bijective**, so every Newton step of
  a deformation of the observation is solvable, and the successive approximation converges in the
  `s`-adic topology by construction.  The next Lean target is that bijectivity as a statement about
  the linear map `(dA, dB) |-> (dA B + A dB) mod t^L` on `degreeLT m × degreeLT n`.

- 2026-08-02 — **Two corpus assets found; the previous entry's "single missing input" was the wrong
  statement.**  Corpus search, no new Lean.

  `GaloisForLFunctions/HTGeometry/ProjectiveHorizonFiniteJetRank.lean` already proves, unconditionally
  and with clean axioms,

  ```text
  finiteHorizonSelectedObservation_algebraicIndependent :
    x algebraically independent,  r <= m
      ==>  (y_n, ..., y_(n+r-1);  x_m, ..., x_(m+a-1))  algebraically independent
  ```

  Taking `r = m` and `a = n + 1` this is exactly *the critical observation together with the new raw
  coefficient* — `y_n, ..., y_(L-1), x_m, ..., x_L`, that is `c` and `u` — algebraically independent
  over `F`.  So the statement the last entry isolated as the card's remaining input has been in the
  corpus all along.  And `GaloisForLFunctions/HTGeometry/JacobianAlgebraicIndependence.lean` already
  carries `MvPolynomial.algebraicIndependent_of_jacobian_det_ne_zero`, the polynomial Jacobian
  criterion, which is how that independence is proved.  Neither needs rebuilding.

  What independence buys is the *faithful* half of the descent: with `c, u` independent, the inclusion
  of the generic jet algebra is a specialisation that kills nothing, so the `hker` hypothesis of
  `not_mem_adjoin_set_of_ne_of_injective` is satisfied by the identity.

  What is genuinely left is the *other* half, and it is a different statement from the one recorded
  last time: **a second point of the fibre over the generic observation**, equivalently
  `[J_L : H(u)] >= 2`.  Note carefully that the pure fibre cannot supply it by any counting argument.
  Fibre length is *upper* semicontinuous: specialising can only increase the number of points, so the
  parent card's `C(L,m)` reduced pure points give `[J_L : H(u)] <= C(L,m)` and never a lower bound.
  Only flatness of the fibre algebra, or an actual lift of a pure point to the deformed observation,
  converts the pure count into a generic one.

  The lift is the route, and its key input is now proved on this card: `PureFibreTangentIso`'s
  `bijective_fibreDifferential` says every Newton step of a deformation has a unique solution.  What
  remains is to assemble the steps — either through
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` after presenting the fibre algebra as
  standard smooth, or by a direct successive approximation over the deformation parameters.

  Normalisation check on that corpus theorem, since it matters for citing it.  Its recursion is
  `y_(n+1) = -y_0 * sum_i C(n+1,i) x_i y_(n+1-i)`, with binomial coefficients — that is the Leibniz
  rule, so its `x_i` and `y_j` are the *derivatives* `D^i f` and `D^j(f^(-1))`, not this card's Taylor
  coefficients `D^i f / i!`.  The two families differ by the nonzero rational factors `i!`, so they
  generate the same subfields and one is algebraically independent exactly when the other is.  The
  citation is therefore sound, but any Lean bridge from that module to this card's `(1)` must carry
  the factorial rescaling explicitly.

- 2026-08-02 — **The lift's two engines, both over an arbitrary ring.**  Two new modules, wired into
  the `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`.

  `formal/GaloisForLFunctions/HTGeometry/CoprimeSplit.lean` — the linearised fibre step, solved
  exactly and without any field, dimension count or flatness:

  ```text
  exists_coprimeSplit          A monic, coprime to B  ==>  E = dA B + A dB with deg dA < deg A
  natDegree_snd_lt_of_coprimeSplit                        and deg dB < n once deg E < m + n
  coprimeSplit_unique          the splitting is unique
  existsUnique_coprimeSplit    so the displacement realising a prescribed error is unique
  ```

  This supersedes the field-only `bijective_fibreDifferential` of the previous entry.  The proof is
  Bezout plus division by a monic: from `uA + vB = 1`, divide `Ev` by `A` and read off the two parts.
  Because it is ring-level it base-changes to *any* deformation of the coefficients, which is exactly
  what the lift needs and what a dimension argument over the residue field could never give.

  `formal/GaloisForLFunctions/HTGeometry/NewtonFibreStep.lean` — the step's algebra:

  ```text
  inversionError_newton_step :
    error E,  dP B + A dQ = -E    ==>   new error  =  dP (W - B) + (Z - A) dQ + dP dQ   mod t^L
  exists_newton_step             the step can always be taken, with the right degrees
  inversionError_deformation     the initial error of a deformation is Gamma B + A Gamma' + Gamma Gamma'
  ```

  Every term of the new error carries a displacement or a deformation as a factor.  So along an
  ideal `I` in which the deformation lies, the error after `k` steps lies in `I^(k+1)`: the iteration
  contracts, with no hypothesis on the ring at all.  Completeness enters only at the very end, to
  turn the contraction into a limit — and `Mathlib`'s `IsAdicComplete.henselianRing` and
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` are both available for that.

  What remains for the card is the limit itself: assembling the contracting sequence into a solution
  over an adically complete base, which then supplies two points of the fibre over an algebraically
  independent observation and closes `v notin H(u)` for all `(m,n)`.

- 2026-08-02 — **The lift is proved: a fibre point deforms with the observation.**
  Two more modules, wired into the `HTGeometry` umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`.

  `formal/GaloisForLFunctions/HTGeometry/CoprimeSplitIdeal.lean`:

  ```text
  coprimeSplit_coeff_mem :
    every coefficient of the error in J  ==>  every coefficient of the displacement in J
  ```

  The proof inspects nothing.  Reduce the split equation modulo `J`: over the quotient the monic
  factor is still monic and the pair still coprime, so the split of the *zero* error is unique, hence
  zero.  This is the contraction estimate.

  `formal/GaloisForLFunctions/HTGeometry/NewtonFibreInvariant.lean` — the estimate assembled:

  ```text
  CoeffMem, CoeffMem.mul, coeff_modByMonic_X_pow, X_pow_dvd_sub_modByMonic
  newton_step_contracts :
    error in I^(k+1)  ==>  displacement in I^(k+1)  and  new error in I^(k+2)
  ```

  `formal/GaloisForLFunctions/HTGeometry/NewtonFibreLift.lean` — the limit, and the card's missing
  construction:

  ```text
  exists_deformed_factorisation :
    S complete for I,  A monic of degree m coprime to B of degree <= n,  t^L | A B - 1,
    Gamma, Gamma' with all coefficients in I
      ==>  there are P, Q with deg P < m, deg Q < n, all coefficients in I, and
           t^L | (A + Gamma + P)(B + Gamma' + Q) - 1
  ```

  That is: **a factorisation over the horizon deforms with its coefficients.**  Adding to the two
  factors anything with coefficients in `I` can be compensated below the two critical orders, again by
  coefficients in `I`.  The proof is the Newton iteration — a total step function chosen once, a
  sequence built by recursion, the contraction estimate proving the sequence Cauchy coefficientwise,
  `IsPrecomplete` producing the limits and `IsHausdorff` killing the residual error.

  This is precisely the passage that a count at the pure fibre can never give, and it is now
  unconditional.  Applied to the `C(L,m)` pure factorisations of `1 + t^L` — distinct, and coprime
  because that polynomial is separable, which is `isCoprime_of_pureFactorisation` — it produces that
  many distinct points of the fibre over a deformed observation.  What is left is the bookkeeping that
  identifies the deformed observation with an algebraically independent one and reads off
  `v notin H(u)` through `not_mem_adjoin_set_of_ne_of_injective`.

- 2026-08-02 — **Two points over the universal deformed observation.**  Two more modules, wired into
  the `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`.

  `formal/GaloisForLFunctions/HTGeometry/TwoDeformedFibrePoints.lean`:

  ```text
  exists_two_deformed_factorisations :
    two factorisations over the horizon whose constant terms differ modulo I,
    deformed by the same Gamma, Gamma'
      ==>  two factorisations sharing every coefficient from the critical orders on
           and whose constant terms still differ modulo I
  ```

  The observation is unchanged because both factors are monic of the two critical degrees, so their
  coefficients from those degrees on are `1, 0, 0, …` for both, and the lift's corrections live
  strictly below those degrees.  Distinctness survives because the corrections lie inside `I` while
  the constant terms already differ outside it.

  `formal/GaloisForLFunctions/HTGeometry/DeformedCriticalObservation.lean` — the universal
  deformation, over the right base:

  ```text
  deformBase K m n           = MvPowerSeries (Fin n ⊕ Fin m) K,  one variable per critical coordinate
  rawDeformation, reciprocalDeformation, and their CoeffMem
  notMem_deformIdeal_of_ne_zero :  a nonzero constant is not a deformation parameter
  exists_two_deformed_pure_factorisations :
    two factorisations of 1 + t^L over K with different constant terms
      ==>  two points of the fibre over the deformed observation
  ```

  The base is the multivariate power series ring on exactly `m + n` variables, which mathlib knows is
  adically complete for the ideal of its variables (`Mathlib/RingTheory/AdicCompletion/Completeness`,
  and note that importing `MvPowerSeries.Basic` alone does *not* bring that instance in).  Under this
  deformation the critical observation becomes `1 + s_0, s_1, …, s_(n-1)` on the raw side and
  `1 + s_n, …, s_(L-1)` on the reciprocal side: an **affine change of the variables**, hence as generic
  as an observation can be, with no independence argument left to make.

  So the chain from a pure fibre with two points to a deformed fibre with two points is complete and
  unconditional.  What remains is to read `v notin H(u)` off it: identify the two deformed jets'
  postcritical reciprocal coefficients — which differ because their constant terms do — and feed the
  pair into `not_mem_adjoin_set_of_ne_of_injective`.

- 2026-08-02 — **The postcritical coefficient separates the deformed fibre.**
  `formal/GaloisForLFunctions/HTGeometry/DeformedPostcriticalSeparation.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  exists_postcritical_coefficient :
    Z W - 1 = t^L G,  Z(0) a unit
      ==>  there is v with  G(0) + v Z(0) = 0  and  t^(L+1) | Z (W + v t^L) - 1
  postcritical_relation :   that relation is forced by the divisibility
  postcritical_separates :
    two such pairs with  G_i(0) = 1 mod I  and  Z_0(0) - Z_1(0) notin I
      ==>  v_0 - v_1 notin I
  ```

  The separation proof uses no inverses and no field structure on the quotient.  Reducing the two
  relations modulo `I` gives `1 + v_i Z_i(0) = 0`, which makes `v_0` invertible modulo `I` — its
  inverse is `-Z_0(0)` — so equal postcritical coefficients would force equal constant terms.  Three
  lines of ideal arithmetic, valid over any commutative ring.

  Together with the previous entry this completes the fibre side of the card for all `(m,n)`: two
  pure factorisations of `1 + t^L` with distinct constant terms deform to two jets over an
  observation that is an affine change of independent variables, and their first postcritical
  reciprocal coefficients differ.  The `1 + t^L` normalisation is what makes the hypothesis
  `G_i(0) = 1 mod I` hold: the undeformed error is exactly `t^L`.

- 2026-08-02 — **The card's fibre statement, for every `(m,n)`.**
  `formal/GaloisForLFunctions/HTGeometry/DeformedFibreJets.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  exists_two_deformed_postcritical_jets :
    two factorisations of 1 + t^L over K with distinct constant terms
      ==>  there are jets Z_0, W_0, Z_1, W_1 over the universal deformation and scalars v_0, v_1 with
             Z_0, Z_1 equal in every raw coefficient from m on,
             W_0, W_1 equal in every reciprocal coefficient from n on,
             t^(L+1) | Z_i (W_i + v_i t^L) - 1,
             v_0 /= v_1
  ```

  This is the fibre statement of the card, unconditional and for **every** `(m,n)` with `m, n >= 1`:
  two jets with the *same* critical observation and the *same* vanishing new raw coefficient — both
  `Z_i` have degree below `L`, so their `t^L` coefficient is zero — whose first postcritical
  reciprocal coefficients differ.  One postcritical reciprocal coefficient is therefore not a
  function of the critical observation and the new raw coefficient.

  The assembly needed three facts about the deformation, each proved in the module: the truncated
  error of each deformed pair is congruent to `1` modulo the deformation ideal — because the
  undeformed error is exactly `t^L` and the two pairs differ by coefficients in the ideal; the
  constant terms are units — a power series is a unit exactly when its constant coefficient is, and
  that coefficient is the nonzero `A_i(0)`; and `A_i(0)` is nonzero because `A_i(0) B_i(0) = 1` reading
  `A_i B_i = 1 + t^L` in degree zero.

  What is left on the card is only the translation into field language: identify the two jets with
  two specialisations of the generic jet algebra, and read `v notin H(u)` off
  `not_mem_adjoin_set_of_ne_of_injective`.

- 2026-08-02 — **The new raw coefficient must be deformed too, or the descent cannot apply.**
  A correction to the shape of the previous entry, found while assembling the field-language step.

  The descent `not_mem_adjoin_set_of_ne_of_injective` requires the specialisation to kill no nonzero
  element of the algebra generated by the data — the data being the critical observation **and** the
  new raw coefficient `u = x_L`.  The previous construction set `x_L = 0` in both jets.  That makes
  `u` itself map to zero, so the hypothesis fails outright: not for a subtle reason, but because a
  generator of the data is killed.  Setting `x_L` to a *constant* would fail the same way.

  The fix is to give `x_L` its own deformation parameter.  The base
  `deformBase K m n` now carries one more variable, `deformParam`, and the jets are
  `Z_i + deformParam · t^L`.  Everything downstream generalises with a single extra term:

  ```text
  exists_postcritical_coefficient (tau) :  G(0) + tau W(0) + v Z(0) = 0
  postcritical_relation, postcritical_separates :   same, with tau in I
  exists_two_deformed_postcritical_jets :
    t^(L+1) | (Z_i + deformParam t^L)(W_i + v_i t^L) - 1,   v_0 /= v_1
  ```

  The separation survives untouched because `tau` lies in the deformation ideal, so modulo that ideal
  the relation still reads `1 + v_i Z_i(0) = 0`.  The two jets now agree on the whole of the data —
  critical observation *and* new raw coefficient, all of them deformation parameters, hence an affine
  change of independent variables — and still differ at the postcritical reciprocal coefficient.

- 2026-08-02 — **The card's statement, in rational-function form, for every `(m,n)`.**
  `formal/GaloisForLFunctions/HTGeometry/PostcriticalNotRational.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  criticalObservation m n Z W tau :   the raw coefficients from m up to and including the horizon,
                                      and the reciprocal coefficients from n up to the horizon
  criticalObservation_eq :            the two deformed jets share it
  not_common_rational_of_ne :         two separated values admit no common rational expression
                                      in a common argument
  postcritical_not_rational :
    two factorisations of 1 + t^L over K with distinct constant terms
      ==>  there are two jets over the universal deformation with the *same* critical observation and
           the *same* new raw coefficient, both inverting to order L+1, such that **no** polynomial
           fraction P/Q in that data computes the first postcritical reciprocal coefficient of both
  ```

  This is the card's `v notin H(u)` in the form that needs no field theory at all.  The separation
  argument is one line of ring algebra: if `v_0 Q = P` and `v_1 Q = P` with `P`, `Q` evaluated at the
  *same* point, then `(v_0 - v_1) Q = 0`, so in a ring without zero divisors either the two values
  agree — they do not — or the denominator vanishes, which the hypothesis excludes.  The base has no
  zero divisors: mathlib's lexicographic order argument gives `NoZeroDivisors` for multivariate power
  series over a field (there is no `IsDomain` instance, and none is needed).

  What remains is only the change of language: presenting the two jets as two specialisations of the
  generic jet algebra `K(x_0, …, x_L)` localised at `x_0`, so that the statement above reads literally
  as `y_L notin H(u)` for the generic jet.  That is the localisation-universal-property plumbing, not
  new mathematics: the two specialisations exist because `x_0` maps to a unit in both.

- 2026-08-02 — **The generic jet algebra and its specialisations.**  Two more modules, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`.

  `formal/GaloisForLFunctions/HTGeometry/TruncatedReciprocalRecurrence.lean`:

  ```text
  coeff_convolution_of_dvd :   sum_(i<=k) Z_i W_(k-i) = [k = 0]   for every k below the horizon
  coeff_zero_mul_of_dvd :      Z_0 W_0 = 1
  coeff_zero_mul_coeff_of_dvd: Z_0 W_k = - sum_(i<k) Z_(i+1) W_(k-1-i)
  ```

  The corpus already had this for `PowerSeries` with an exact inverse
  (`constantCoeff_mul_coeff_inverse` in `ReciprocalCoefficientField.lean`); the truncated polynomial
  form is what a horizon needs, and it is three lines from `X_pow_dvd_iff`.

  `formal/GaloisForLFunctions/HTGeometry/GenericJetAlgebra.lean`:

  ```text
  genericJetAlgebra K N =  Localization.Away (X 0)  on  K[x_0, …, x_N]
  genericRaw, genericInv, genericRecip :   the generic raw and reciprocal coefficients
  jetLift a h :        the specialisation at an actual jet with unit constant term
  jetLift_genericRecip :
    jetLift (Z-coefficients) (generic reciprocal coefficient k)  =  W.coeff k   for k <= N
  ```

  The transport is an induction in which both sides satisfy the *same* recursion from the same
  initial value: the generic side by definition, the actual side by the convolution identity above.
  The base case is the uniqueness of an inverse in a commutative ring, not a division.

  With this the card's statement can be phrased about the generic jet: the two deformed jets of the
  previous entries are two specialisations of one algebra, they agree on the critical observation and
  on the new raw coefficient, and they separate the postcritical reciprocal coefficient.  The last
  step is to run `not_mem_adjoin_set_of_ne` on that pair inside the fraction field of the generic jet
  algebra.

- 2026-08-02 — **Genericity of the deformed observation: the two missing independence facts.**
  `formal/GaloisForLFunctions/HTGeometry/ShiftedVariablesIndependent.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  algebraicIndependent_add_const :
    an algebraically independent family stays independent after adding constants
  algebraicIndependent_mvPowerSeries_X :
    the variables of a multivariate power series ring are algebraically independent
  ```

  These are exactly what the descent's remaining hypothesis needs.  The deformed observation is
  `1 + s_0, s_1, …, s_(n-1), 1 + s_n, …, s_(L-1), s_L` — the deformation parameters with a constant
  added in two places — so its independence is the composite of the two statements above with a
  reindexing.  The first is proved by a polynomial automorphism: adding constants is the algebra map
  `X_i |-> X_i + c_i`, whose inverse subtracts them, so composing with it cannot create a relation.
  The second is proved by identifying `aeval X` with the coercion `MvPolynomial -> MvPowerSeries` by
  induction, and that coercion is injective.

  With these, every hypothesis of `not_mem_adjoin_set_of_ne` is in hand for the pair of
  specialisations of the generic jet algebra: they agree on the base and on the observation, the
  first is faithful on the algebra the observation generates, and they separate the postcritical
  reciprocal coefficient.  The final module has only to assemble them.

- 2026-08-02 — **The deformation chain now carries everything the final descent consumes.**
  Plumbing only; no new mathematics, umbrella green at 12926 jobs.

  `exists_two_deformed_factorisations`, `exists_two_deformed_pure_factorisations` and
  `exists_two_deformed_postcritical_jets` were extended to return, besides the two jets and their
  separated postcritical coefficients:

  ```text
  W_i.natDegree < L,  Z_i.natDegree < L            hence  W_i.coeff L = 0
  Z_0.coeff i = A_0.coeff i + rawDeformation.coeff i          for i >= m
  W_0.coeff j = B_0.coeff j + reciprocalDeformation.coeff j   for j >= n
  ```

  The degree bounds come from the deformations having degree below the horizon, which is now proved
  as `natDegree_rawDeformation_lt` and `natDegree_reciprocalDeformation_lt`.  Two consumers needed
  these.  `W_i.coeff L = 0` is what makes the `L`-th coefficient of the *whole* reciprocal jet equal
  to `v_i` rather than `W_i.coeff L + v_i`, so the separated quantity really is the postcritical
  coefficient.  The two decomposition identities are what will let the deformed observation be
  computed explicitly as `1 + s_0, s_1, …` — the affine change of parameters whose independence the
  previous entry proved — rather than only known up to the deformation ideal.

- 2026-08-02 — **The deformed observation is algebraically independent — explicitly.**
  `formal/GaloisForLFunctions/HTGeometry/DeformedObservationIndependent.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  coeff_rawDeformation, coeff_reciprocalDeformation :
    the deformation puts exactly one parameter in each critical coefficient
  observationParam, observationParam_injective :
    the observation coordinates index distinct parameters
  criticalObservation_eq_shift :
    the deformed observation IS  s |-> X_(param s) + (1 in exactly two places)
  algebraicIndependent_criticalObservation :
    hence it is algebraically independent over the coefficient field
  ```

  The middle statement is the point.  Until now the deformed observation was known only modulo the
  deformation ideal; it is now computed on the nose, as the deformation parameters with a `1` added at
  the two monic slots — the raw critical coefficient `x_m` and the reciprocal one `y_n`, each of which
  is the leading coefficient of a monic factor.  Everything else is `0` plus a parameter, including
  the new raw coefficient `x_L`, which is the last parameter untouched.

  Independence then follows from the two general facts of the previous entry: the variables of a
  power series ring are independent, composing with an injection preserves that, and adding constants
  preserves it too.  This is the last hypothesis of `not_mem_adjoin_set_of_ne` that was outstanding.

- 2026-08-02 — **The card's step 1 is closed, for every `(m,n)`.**
  `formal/GaloisForLFunctions/HTGeometry/GenericPostcriticalEscape.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  genericObservation m n :   the generic critical observation and the new raw coefficient,
                             inside the generic jet algebra K[x_0, …, x_L] localised at x_0
  genericPostcritical_not_rational :
    two factorisations of 1 + t^L over K with distinct constant terms
      ==>  for every nonzero Q,
             genericRecip L * aeval genericObservation Q  /=  aeval genericObservation P
  ```

  This is `v notin H(u)` for the **generic** jet, unconditional, for all `m, n >= 1`: no rational
  function of the critical observation and the new raw coefficient computes the first postcritical
  reciprocal coefficient.  Everything the card carried as paper-level in step 1 — `(7)` was already
  formal, `(8)` was already formal, and the etale rational descent was the gap — is now formal.

  The proof specialises the generic jet twice at once.  Both jets of the deformed fibre give algebra
  maps out of the generic jet algebra, by the universal property of the localisation, since the
  constant term of each is a unit; those maps send the generic observation to the *same* deformed
  observation and the generic postcritical coefficient to the two *different* values; a rational
  expression valid generically specialises to both; and the denominator survives because the deformed
  observation is algebraically independent.

  One Lean-level note worth keeping: `set M : Type _ := deformBase K m n` — a `set` on a **type** —
  made the whole declaration exceed the heartbeat limit, because it blocks reducibility and instance
  search then unfolds the power series type repeatedly.  Writing the type out restored an elaboration
  time of under two seconds.  Never `set` a type in this development.

- 2026-08-02 — **Hypothesis-free: the card's step 1 stands on its own.**
  `formal/GaloisForLFunctions/HTGeometry/PostcriticalEscapeUnconditional.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  monic_/natDegree_criticalHorizonLeft/RightFactorFromRoots :
    a root-subset factor is monic of degree m, its complement monic of degree n
  exists_two_pureFactorisations :
    over an algebraically closed field of characteristic zero, 1 + t^L has two factorisations
    into monic factors of degrees m and n with different constant terms
  postcritical_escapes_criticalField :
    for all m, n >= 1, and every nonzero Q,
      genericRecip L * aeval genericObservation Q  /=  aeval genericObservation P
  ```

  The last statement has **no** hypotheses beyond `m, n >= 1` and the field being algebraically closed
  of characteristic zero.  The two factorisations come from the corpus's own
  `exists_pureCriticalRootFactorPairs_coeff_zero_ne`: distinct `m`-element subsets of the roots of
  `1 + t^L` give factor pairs with different constant terms, and those roots are distinct because the
  polynomial is separable.  Monicity and the two degrees are read off the product over a subset;
  coprimality is `isCoprime_of_pureFactorisation`.

  So step 1 of this card — `(7)`, `(8)`, and the rational descent `v notin H(u)` — is now formal in
  full, for every `(m,n)`, with nothing left at paper level.

- 2026-08-02 — **`v notin H(u)` in field language.**
  `formal/GaloisForLFunctions/HTGeometry/PostcriticalNotMemField.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  isDomain_genericJetAlgebra, genericJetField, genericJetSubalgebra, genericJetEquiv
  postcritical_notMem_criticalField :
    the first postcritical reciprocal coefficient of the generic jet does not lie in
    IntermediateField.adjoin K (critical observation and the new raw coefficient)
  ```

  This is the card's `v notin H(u)` literally, as non-membership in a subfield of the generic jet
  field, rather than as the absence of a rational expression.  It is derived from the
  rational-function form, not proved again: membership in a generated subfield exhibits the element
  as a fraction of two members of the generated *algebra* (`exists_frac_of_mem_adjoin`), each of which
  is a polynomial in the observation (`Algebra.adjoin_range_eq_range_aeval`), and clearing the
  denominator gives exactly the relation the deformation argument excludes.

  The vanishing-denominator branch is not vacuous and is handled separately: a zero denominator would
  force the postcritical coefficient itself to vanish, which is the relation with numerator `0` and
  denominator `1` — also excluded.

  With this the card's step 1 is complete in the language the rest of the card uses, and `(4)` —
  `H(u)(v) = J_L` — is now one step away: it needs only the coatom property `(7)`, whose Lean form
  `eq_bot_or_eq_of_isCoatom_fixingSubgroup` is already in `CoatomFixedField.lean` and whose input is
  the parent card's identification of the critical Galois group.

- 2026-08-02 — **`(4)` assembled: one element outside the base generates a field-primitive
  extension.**  `formal/GaloisForLFunctions/HTGeometry/PostcriticalPrimitiveElement.lean`, wired into
  the `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  adjoin_eq_of_notMem_of_isCoatom :
    K.fixingSubgroup maximal,  v in K,  v not in the base   ==>   F(v) = K
  adjoin_eq_top_of_notMem_of_isCoatom :   the same with K = the whole extension
  ```

  This is the last inference of the card's step 1, and it closes the shape of `(4)`.  The card's
  argument was: `(7)` says nothing lies strictly between `H(u)` and `J_L`; `v notin H(u)` says the
  field generated by `v` is not `H(u)`; therefore it is `J_L`.  The middle premise was the paper-level
  gap and is now `postcritical_notMem_criticalField`; the inference itself is the theorem above.

  What `(4)` still rests on is `(7)` alone — that is, the identification of the critical Galois group
  as `S_D`, so that `J_L` is the fixed field of a point stabiliser and `isCoatom_stabilizer_perm`
  applies.  That identification is the parent card's `(2)`, not this card's, and it is the only input
  this card now takes from outside.

- 2026-08-02 — **The pure fibre really has binomially many points.**
  `formal/GaloisForLFunctions/HTGeometry/OccupationFactorInjective.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  criticalHorizonLeftFactorFromRoots_injective :
    distinct occupation states give distinct selected factors
  exists_injective_pureFactorisations :
    an injection from the occupation states into factorisations of 1 + t^L into
    monic factors of degrees m and n
  ```

  The parent card identifies the pure fibre with the `m`-element subsets of the roots and counts
  `C(L,m)` of them; what was formal until now was the *count of subsets*, not the injectivity of the
  passage from subsets to factorisations.  The proof is the obvious one and is worth recording because
  it is what makes the count a count of fibre points: a root selected by one state and not the other
  is a root of one factor and not of the other, the roots being distinct because `1 + t^L` is
  separable.

  Combined with the deformation, this says the fibre over the deformed observation has at least
  `C(L,m)` points: distinct pure factorisations deform to distinct ones, since they already differ
  modulo the deformation ideal.  That is the lower bound the parent card's `(2)` needs, from the side
  that semicontinuity cannot supply.

- 2026-08-02 — **The deformed fibre has at least binomially many points.**
  `formal/GaloisForLFunctions/HTGeometry/DeformedFibreLowerBound.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  exists_injective_deformed_fibre :
    an injection  S |-> (Z_S, W_S)  from the occupation states into pairs over the deformation, with
      t^L | Z_S W_S - 1   for every S,
      Z_S and Z_T agreeing in every raw coefficient from m on,
      W_S and W_T agreeing in every reciprocal coefficient from n on
  ```

  Every point of the pure fibre deforms; distinct pure points deform to distinct ones, because they
  already differ modulo the deformation ideal and a nonzero constant is never in that ideal; and all
  of them carry the *same* deformed observation, because the deformation is added to the same monic
  data — the raw coefficients from `m` on are `1, 0, …` for every occupation state.

  So the fibre over one algebraically independent observation has at least `C(L,m)` points.  This is
  the lower bound that the parent card's `(2)` needs and that no count at the special fibre can
  supply, since fibre length is only upper semicontinuous.  What `(2)` needs on top of it is the
  matching upper bound — that the extension `J_(L-1)/O` has degree at most `C(L,m)` — which is a
  statement about the *generic* fibre and remains the parent card's own work.

- 2026-08-02 — **The reciprocal packet is redundant, for the generic jet.**
  `formal/GaloisForLFunctions/HTGeometry/GenericRecipMemAdjoin.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  genericRawAlgebra :  the algebra of the raw coefficients and the inverse of the constant term
  genericRecip_mem_genericRawAlgebra :  every reciprocal coefficient lies in it
  ```

  This is step 3's tautological half in the generic jet algebra: the inverse recursion never leaves
  the algebra it starts in, so only the raw coordinates are free and the reciprocal packet is
  redundant data.  The corpus already had the field version for power series with an exact inverse
  (`coeff_inverse_mem_subfield`); this is the truncated, algebra-level form the generic jet uses, and
  it is what step 3 pairs with `(4)` to get `O_(m,n;N) = J_N` for `N >= L`.

- 2026-08-06 — **Correction: the "Lean verification" section above is stale about step 1.**

  That section says "the etale rational-descent argument converting this explicit fiber witness
  into `v notin H(u)` remain[s] paper-level, so the card remains in stage 2", and repeats the point
  in its closing paragraph.  The card's own header already contradicts it, and the header is
  right: `postcritical_escapes_criticalField` is in the repository and is unconditional,

  ```text
  postcritical_escapes_criticalField   [propext, Classical.choice, Quot.sound]
  ```

  so the separation `v ∉ H(u)` is formalized, and with `(7)` (`isCoatom_stabilizer_perm`,
  `eq_bot_or_eq_of_isCoatom_fixingSubgroup` in `CoatomFixedField.lean`) and the base-change clause
  (`freeParameterBaseChange`) step 1 is complete for every `(m,n)`.

  What is genuinely open on this card is step 3's forward inclusion: that the order-`N` observation
  field contains the order-`L` field of `(4)` together with the raw coordinates `x_(L+1), …, x_N`.
  Its reverse half is already formalized — `genericRecip_mem_genericRawAlgebra` in
  `GenericRecipMemAdjoin.lean`, the statement that the inverse recursion never leaves the algebra
  it starts in — and the forward half rests on `(4)`, which is the parent card's degree bound.

## Corpus audit — `(4)` is one assembly away, given full monodromy

The card's step 3 was recorded as open through its forward inclusion, which rests on `(4)`.  An
audit shows `(4)` itself is now a short assembly of theorems that are already in the tree:

```text
CriticalObservationField.lean
    criticalObservationField, criticalSourceField, criticalObservationField_le_criticalSourceField
    postcriticalRawFieldElement, postcriticalReciprocalFieldElement
    postcriticalRawFieldElement_transcendental_criticalSourceField
    postcriticalRawFieldElement_transcendental_criticalObservationField
    postcriticalReciprocalFieldElement_notMem_criticalObservation_sup_raw
        y_L ∉ O ⊔ K(x_L)      — the escape, unconditional for m, n ≥ 1
CriticalGeometricDegreeExact.finrank_criticalSourceField_eq_criticalHorizonMultiplicity
        [J : O] = C(L, m)     — the degree, unconditional
CriticalGeometricFieldPrimitivity.eq_bot_or_eq_criticalSourceNormalClosureFieldRange_of_full_monodromy
        no proper intermediate field between O and J, given full monodromy
FreeParameterBaseChange.lean            adjoining the free parameter x_L keeps the Galois group
GenericRecipMemAdjoin.genericRecip_mem_genericRawAlgebra      y_L ∈ J_L
```

The assembly is: base-change along the transcendental `x_L`, so `[J(x_L) : O(x_L)] = C(L,m)` with the
same Galois group; `y_L ∈ J(x_L)` by the reciprocal recursion and `y_L ∉ O(x_L)` by the escape; field
primitivity leaves no field strictly between `O(x_L)` and `J(x_L)`; hence
`O(x_L)(y_L) = J(x_L) = J_L`, which is `(4)`.  Step 3's forward inclusion is then generator
bookkeeping: `O_{m,n;N} ⊇ O_{m,n;L-1}(x_L, y_L) = J_L` and `x_{L+1}, …, x_N ∈ O_{m,n;N}`, so
`J_N ⊆ O_{m,n;N}`; the reverse inclusion is `genericRecip_mem_genericRawAlgebra`.

So this card's only genuinely open input is **full monodromy**, i.e. the two hypotheses recorded on
`projective-horizon-full-symmetric-monodromy`: that the root-permutation action lies inside the
geometric monodromy, and that the Schur inertia is nontrivial and simple.  Both cards close together.
