# Prime-valuation profile differential-field classification law

- **ID:** `prime-valuation-profile-hypertranscendence`
- **Stage:** 3-formalized
- **Type:** `[GENERAL HT THEOREM] [DIFFERENTIAL-FIELD CLASSIFICATION]`
- **Scientific status:** `[UNCONDITIONALLY FORMALIZED] [NOVELTY PROVISIONAL]`
- **Parent methods:** Shapiro--Sparer arithmetic-function Jacobians; Pong's logarithmic
  derivation method; prime-power coefficient separation

## Main theorem

Let `g_1,...,g_d` be arithmetic functions supported on positive prime powers.  Suppose that for
each source there is a valuation profile `u_j : N -> C` such that

```text
g_j(p^(n+1)) = u_j(n)
```

for every prime `p` and every `n >= 0`.  Equip the arithmetic-function fraction field with the
rotated logarithmic derivation.

Then

```text
{g_1,...,g_d} is differentially algebraically independent over C
    iff
{u_1,...,u_d} is linearly independent over C.
```

Consequently the finite differential matroid of prime-radial positive-prime-power sources is
exactly the ordinary linear matroid of their valuation profiles.  Differential rank, circuits,
closure, and bases are determined by profile linear algebra.

## Complete relation theorem

Choose linearly independent pivot profiles `u_b`.  Let every remaining profile have an exact
constant linear presentation

```text
v_r(n) = sum_b A(r,b) u_b(n).
```

For the corresponding prime-radial sources, the complete differential relation ideal is generated
by the prolonged linear relations

```text
D^k y_r - sum_b A(r,b) D^k x_b = 0,
```

for all dependent labels `r` and all jet orders `k`.  There are no additional nonlinear
differential relations.  The full family and the pivot family generate the same differential
field.

## Field membership and field-lattice theorem

Let `u_1,...,u_d` be linearly independent pivot profiles with corresponding sources
`g_1,...,g_d`, and let `y` be any further prime-radial source with profile `v`.  Then the converse
to pivot generation is exact:

```text
y belongs to the embedded differential field C<g_1,...,g_d>
    iff
v belongs to span_C{u_1,...,u_d}.
```

The complementary statement is stronger than non-membership:

```text
y is differentially algebraically independent over C<g_1,...,g_d>
    iff
v does not belong to span_C{u_1,...,u_d}.
```

Thus every new profile direction contributes a genuinely relative hypertranscendental generator,
not merely a new element of the ambient field.

Consequently, for any finite source family `x` and any linearly independent pivot family `y`,

```text
C<x> is contained in C<y>
    iff
span(profile(x)) is contained in span(profile(y)).
```

In particular, two finite linearly independent prime-radial presentations generate the same
embedded differential field exactly when their profile subspaces are equal.  The profile span is
therefore a complete invariant of both membership and generated-field equality on minimal finite
presentations.  This resolves the simultaneous-family question left open by independence-only
results: distinct presentations may generate the same field, but only through ordinary linear
change of profile coordinates.

## Stronger arbitrary-tail certificate

The proof establishes a theorem beyond the prime-radial class.  Let `g_1,...,g_d` be arbitrary
sources supported on positive prime powers, with no restriction on unselected valuation layers.
If there are pairwise-distinct exponents `e_1,...,e_d` for which the profile minor

```text
P(i,j) = g_j(p^(e_i+1))
```

is independent of `p` and nonsingular, then the sources are differentially independent.  Thus
uncontrolled infinite prime-power tails cannot cancel a nonsingular finite valuation minor.

## Proof geometry

For a finite jet rectangle, linear independence of the profiles supplies a nonsingular evaluation
minor at pairwise-distinct valuation coordinates.  Distinct packets of primes supply independent
logarithmic clocks inside every selected valuation row.  Applying prime derivations to the jets
produces an arithmetic-function Jacobian whose rows may have arbitrary infinite tails along their
own prime rays.

Unique factorization isolates one coefficient of the full convolution determinant:

```text
coefficient at product_i q_i^(e_i)
    = determinant of the rowwise scalar coefficient matrix.
```

The scalar determinant is a block product of the valuation-profile minor and logarithmic-clock
Vandermonde factors, hence is nonzero.  The domain-valued Jacobian criterion gives algebraic
independence of every finite jet rectangle.  Finite character gives differential independence.

The converse is exact: a linear relation among profiles lifts coefficientwise to the same relation
among the complete arithmetic sources, so differential independence is impossible.  Pivot
elimination then computes the whole relation ideal.

## Literature boundary and provisional novelty verdict

The following are parents, not contributions:

1. H. N. Shapiro and G. H. Sparer, *On algebraic independence of Dirichlet series*, Comm. Pure
   Appl. Math. 39 (1986), 695--745: arithmetic-function derivations and the Jacobian criterion.
2. W. Y. Pong, *Applications of differential algebra to algebraic independence of arithmetic
   functions*, Acta Arith. 172 (2016), 149--173: Ax-based strengthening, logarithmic-derivation
   transcendence criteria, hypertranscendence of zeta, and finite-order lower bounds.
3. T. Komatsu, V. Laohakosol, and P. Ruengsinsub, *Independence measures of arithmetic
   functions*, J. Number Theory 131 (2011), 1--17, and *Independence measures of arithmetic
   functions II*, Acta Arith. 153 (2012), 199--216: quantitative Jacobian tests.
4. D. Rearick, *Operators on algebras of arithmetic functions*, Duke Math. J. 35 (1968),
   761--766: exponential and logarithmic operators on arithmetic functions.

Pong proves that a single infinite-prime-support arithmetic source has an algebraically independent
logarithmic-jet orbit under suitable hypotheses, proves zeta hypertranscendence, and explains that
the Shapiro--Sparer Jacobian criterion underlies the known arithmetic-function independence tests.
Those are not novelty claims here.  The present theorem surface instead classifies simultaneous
finite families with common all-prime support: it gives an exact rank law, the entire differential
relation ideal, a relative hypertranscendence dichotomy, and an order/equality classification of
their embedded differential fields by valuation-profile subspaces.  The inspected Shapiro--Sparer, Pong,
Komatsu--Laohakosol--Ruengsinsub, and Rearick sources do not state this profile-subspace
differential-field classification.

This is a provisional novelty verdict, not a priority claim.  The theorem uses classical
ingredients in a new configuration, so specialist review could still identify it as an unstated
corollary of the arithmetic-function Jacobian literature.

## Anti-theatre verdict

- The separated-prime determinant identity alone is infrastructure, not new science.
- The finite evaluation-minor lemma is ordinary linear algebra, not new science.
- Hypertranscendence of a single source, including zeta, is classical.
- The candidate new content is only the exact simultaneous-family rank and relation
  classification, arbitrary-tail finite-minor certificate, and the field-membership/order law.
- The strongest non-theatrical statement is the closure law: a source is relatively
  hypertranscendental over the generated field exactly outside the profile span, while
  differential-field containment is equivalent to profile-span containment.  Removing project
  vocabulary leaves a genuine classification theorem, not merely the classical Jacobian
  criterion.

## Downstream zeta and RH boundary

The unit profile `u(n)=1/(n+1)` represents the formal Euler logarithm, while delta profiles
represent individual prime-zeta dilation layers.  The rank law reduces every finite joint
independence question for these sources to sequence linear algebra.  A separate formal
instantiation is still required before asserting relative hypertranscendence of `log zeta` over a
specified finite prime-zeta-dilate differential field.

For RH this gives only a positive architecture constraint: a prime-side mechanism using this
radial class is completely visible in valuation-profile linear algebra.  Any genuinely new
nonlinear constraint capable of addressing RH must therefore leave the prime-radial differential
matroid or use a completion operation not represented by a finite profile span.  This is not an RH
implication.

More sharply, no finite prime-radial enlargement can hide new differential-field information: it
changes the generated field exactly when it enlarges the profile span.  Therefore an RH route whose
prime-side data remain inside a fixed finite valuation-profile subspace has already exhausted its
embedded differential field; a successful route must produce a new profile direction, a genuinely
non-radial prime dependence, or an infinite completion effect.

## Formal declaration ledger

| Claim | Declaration |
|---|---|
| separated-prime coefficient law | `primeRayMatrix_det_apply` |
| arbitrary distinct-exponent packet | `cofinitePrimePowerPacket_of_injective_layerExponents` |
| arbitrary-tail leading-echelon law | `primeValuationLeadingEchelon_differentialIndependent` |
| nonsingular profile-minor law | `primeValuationProfileMinor_differentialIndependent` |
| finite evaluation-minor extraction | `exists_injective_evaluation_minor_of_linearIndependent_profiles` |
| exact profile rank law | `primeValuationProfile_differentialIndependent_iff` |
| complete relation ideal | `primeValuationProfile_complete_relationIdeal` |
| exact differential field generated by pivots | `primeValuationProfile_differentialAdjoin_eq_pivots` |
| source membership iff profile-span membership | `primeValuationProfile_mem_differentialAdjoin_iff_mem_span` |
| relative differential independence iff outside the profile span | `primeValuationProfile_relative_differentialIndependent_iff_not_mem_span` |
| field containment iff profile-span containment | `primeValuationProfile_differentialAdjoin_le_iff_span_le` |
| field equality iff profile-subspace equality | `primeValuationProfile_differentialAdjoin_eq_iff_span_eq` |

The declarations are in:

- `formal/GaloisForLFunctions/HTGeometry/PrimeSeparatedDeterminantCoefficient.lean`;
- `formal/GaloisForLFunctions/HTGeometry/PrimeValuationLeadingEchelon.lean`;
- `formal/GaloisForLFunctions/HTGeometry/PrimeValuationProfileRankLaw.lean`;
- `formal/GaloisForLFunctions/HTGeometry/PrimeValuationProfileFieldClassification.lean`.

## Verification

The theorem modules pass direct leaf checks.  Exact cached module builds were run only when the
corresponding `.olean` was missing; no full build was run.  The main rank, relation-ideal,
differential-adjoin, relative-independence, field-membership, field-order, field-equality, and
arbitrary-tail declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.  No
`sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration occurs in the theorem modules.

## Gates

- [x] exact finite-family rank classification proved
- [x] arbitrary-tail nonsingular-minor theorem proved
- [x] complete relation ideal proved
- [x] differential-adjoin equality proved
- [x] differential-field membership iff profile-span membership proved
- [x] relative differential independence iff outside the profile span proved
- [x] differential-field containment iff profile-span containment proved
- [x] generated-field equality iff profile-subspace equality proved
- [x] direct checks and exact cached module builds passed
- [x] standard-axiom audit passed
- [ ] specialist priority audit completed
- [ ] analytic zeta/prime-zeta instantiation formalized
- [ ] standalone publication-ready paper written
