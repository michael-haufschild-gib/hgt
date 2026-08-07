# Every rank-one projective horizon has full symmetric monodromy

- **ID:** `projective-horizon-rank-one-full-monodromy`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / GENERIC CRITICAL MONODROMY
- **Scientific status:** `[LEAN-PROVED] [NOVELTY PROVISIONAL] [SIGNIFICANCE LIMITED]`
- **Formal status:** Exact rank-one theorem formalized unconditionally: reciprocal fibre equation,
  triangular parameter change, tail/centered coefficient-field equivalence, full symmetric
  monodromy in even and odd Kummer cases, quadratic edge case, and reciprocal duality; see the Log.
- **Parent:** `projective-horizon-irreducible-simple-ramification`
- **Lane:** source-pure hypertranscendental geometry; static branch topology

## Theorem

Let `K` be an algebraically closed characteristic-zero field and let `n>=1`.  Fix algebraically
independent parameters `p_1,...,p_n,q`, with `p_1 q!=0`, and put

```text
X(t)=a+p_1t+...+p_nt^n,
Y(t)=X(t)^-1 mod t^(n+1).                                  (1)
```

The generic fiber equation

```text
[t^n]Y=q                                                    (2)
```

has degree `n+1` in `a`, and its geometric Galois/monodromy group over
`K(p_1,...,p_n,q)` is the full symmetric group

```text
S_(n+1).                                                     (3)
```

Equivalently, the critical horizon cover `Phi_(1,n)` has maximal symmetric monodromy.  By reciprocal
duality the same holds for `Phi_(n,1)`.

## Proof

Set

```text
R(t)=p_1+p_2t+...+p_nt^(n-1),       X=a+tR.                 (4)
```

The finite geometric-series identity for `(1)` gives

```text
[t^n]Y
  =sum_(k=1)^n (-1)^k a^(-k-1)[t^(n-k)]R^k.                (5)
```

After `j=n-k`, define

```text
c_j=(-1)^(n-j)[t^j]R^(n-j),       0<=j<=n-1.               (6)
```

Multiplying `(2)` by `a^(n+1)` gives the centered degree-`n+1` equation

```text
F(a)=q a^(n+1)-sum_(j=0)^(n-1)c_j a^j=0.                  (7)
```

There is no `a^n` term.  The parameter change in `(6)` is triangular.  Its first coordinate is

```text
c_0=(-1)^n p_1^n,                                          (8)
```

and for `1<=j<=n-1`,

```text
c_j=(-1)^(n-j)
  ((n-j)p_1^(n-j-1)p_(j+1)+H_j(p_1,...,p_j)).              (9)
```

Indeed, the only term in `[t^j]R^(n-j)` involving `p_(j+1)` chooses `p_(j+1)t^j` once and the
constant term `p_1` in every other factor.  Thus `c_0,...,c_(n-1)` are algebraically independent,
and

```text
K(p_1,...,p_n)=K(c_0,...,c_(n-1))(p_1),
p_1^n=(-1)^n c_0.                                          (10)
```

Over the centered coefficient field

```text
E_0=K(q,c_0,...,c_(n-1)),                                  (11)
```

the polynomial `(7)` is the universal centered polynomial of degree `n+1`.  Translation removes
the next-to-leading coefficient from the universal degree-`n+1` polynomial in characteristic zero,
so its geometric Galois group is `S_(n+1)`.

It remains to show that the Kummer base change `(10)` does not shrink this group.  On `c_0!=0`, the
triangular map `(8)--(9)` is a cyclic finite etale cover of degree `n`: all diagonal derivatives
are nonzero.  The universal discriminant divisor is reduced, and its pullback under an etale map
is reduced.  Therefore the discriminant of `(7)` is not a square in
`K(p_1,...,p_n,q)`.

Let `E` be the splitting field over `E_0` and let `M=K(p_1,...,p_n,q)`.  Both `E/E_0` and
`M/E_0` are Galois after adjoining no constants, because `K` is algebraically closed.  The
intersection `E intersect M` is a cyclic quotient of `S_(n+1)`.  For `n+1>=3`, the only possible
nontrivial cyclic quotient is the sign quotient of order two, whose fixed field is obtained by
adjoining the square root of the discriminant.  The preceding nonsquare result excludes it.  Hence
`E intersect M=E_0`, so base change preserves `S_(n+1)`.  When `n=1`, `(10)` is the identity and
the quadratic group is `S_2` directly.  This proves `(3)`.  Reciprocal exchange proves the final
claim.  `QED`

## Consequence for the open all-rank problem

Every boundary family with `min(m,n)=1` has maximal monodromy.  Therefore any all-rank invariant
block system must appear genuinely when both horizon packets have at least two coordinates; it
cannot be inherited from reciprocal inversion alone or from a universal cyclic/Kummer label.

This theorem does not decide whether `Phi_(m,n)` has full
`S_(choose(m+n,m))` for `m,n>=2`.  In particular, it does not justify importing the `S_(m+n)`
action on `m`-subsets from the pure-tail factorization fiber.

## Novelty and significance audit

The Galois group of a universal centered polynomial, Kummer base change, and the discriminant sign
subfield are classical.  The new candidate is their exact occurrence in the rank-one reciprocal
horizon cover through the triangular coefficient law `(6)--(10)`.  A targeted search found
classical trinomial and generic-polynomial Galois results, but no statement for reciprocal-jet
horizon fibers.  Novelty remains provisional.

The theorem is a genuine generic-monodromy result and closes an infinite family, but it is a
rank-one boundary of the all-rank problem and rests on a reduction to the universal polynomial.
Its significance is therefore limited; it does not clear the completion bar.

## Physical meaning

At rank one there is no conserved labeling of the `n+1` vacua: static continuation of the observed
tail parameters realizes every permutation.  This is topology of a branched observation cover, not
quantum time evolution.  The result rules out a hidden cyclic charge created by the reciprocal
coefficient parametrization.

## RH impact

The rank-one cover is universal and target-translation blind.  Full symmetric monodromy removes
rather than supplies a canonical state label, so it has no RH consequence.  An RH application would
need an arithmetic marking that reduces this generic symmetry in a controlled, source-specific way.

## Formal verification

Every numbered step of the proof carries an unconditional Lean theorem, all building with only
`propext`, `Classical.choice`, `Quot.sound`:

| step | Lean |
|---|---|
| `(1)`, `(5)` | `GeometricInverseTruncation`: `coeff_eq_geomInverseSum_of_mul_eq_one`, `coeff_geomInverseSum_top` |
| `(5) -> (7)` | `ReciprocalFiberEquation`: `coeff_mul_pow_eq_tail_sum`, `coeff_mul_pow_eq_polynomial_tail_sum` |
| `(6)`, `(8)`, `(9)`, `(10)` | `TailPolynomialTriangularity`, `TailCoefficientIndependence`, `TailParameterChange`: `tailParameterChange` |
| `(11)` | `TailCenteredCoefficientMatch`: `tailCenteredCoeffEquiv`, `coe_tailCenteredCoeffEquiv` |
| `(3)`, uncentered | `GenericFullMonodromy`, `GenericFullMonodromyOdd` |
| `(3)`, centered | `CenteredFullMonodromy`, `CenteredFullMonodromyOdd` |
| `(3)`, over the parameter field | `CenteredParameterMonodromy`: `centeredParameterMonodromy`, `centeredParameterMonodromyOdd` |

`ProjectiveHorizonExactLagrangian.lean` proves the exact reversed coefficient pairing and its
positive-degree vanishing under truncated inversion, the coefficient identities behind `(5)--(7)`.
Only targeted leaf builds are used.

## Formalisation route for the symmetric monodromy

The Galois statement `(3)` needs the classical fact that the general polynomial of degree `d` has
Galois group `S_d`, which mathlib does not carry.  The route being built avoids the fundamental
theorem of symmetric rational functions as an input and derives it instead:

1. permuting variables is a faithful action of `S_d` on the rational function field in `d`
   variables, so Artin's theorem gives that field degree `d!` over its symmetric part;
2. the generic monic polynomial `prod (T - X_i)` has coefficients in the symmetric part and splits
   in the rational function field, which its roots generate, so that field is its splitting field
   and the Galois group is `S_d`;
3. the coefficient field is contained in the symmetric part and the splitting-field degree bound
   `d!` forces the two to coincide, which is the fundamental theorem for rational functions;
4. the card's centered coefficients and the Kummer base change are then a triangular change of
   parameters and a discriminant-nonsquare argument over that base.

Steps 1--3 are formalized.  In `GaloisForLFunctions/HTGeometry/SymmetricVariableAction.lean`:

```text
permMvPolynomialAction
permMvPolynomialFaithful
permSymmetricRationalFieldAction
permSymmetricRationalFieldFaithful
symmetricPart
finrank_symmetricPart
```

and in `GaloisForLFunctions/HTGeometry/SymmetricRationalFunctions.lean`:

```text
isGalois_symmetricPart
symmetricGaloisEquiv
symmetrise
isSymmetric_symmetrise
exists_isSymmetric_ratio_of_mem_symmetricPart
```

The last of these is step 3 in the form actually needed: a symmetric rational function is a ratio
of symmetric polynomials, so with the fundamental theorem of symmetric polynomials it is a rational
function of the elementary symmetric functions.  The route to it does not use a degree bound on
splitting fields; multiplying numerator and denominator by the images of the denominator under
every nonidentity permutation makes the denominator symmetric, and the numerator is then symmetric
because the quotient is.

The identification itself is in `GaloisForLFunctions/HTGeometry/SymmetricCoefficientField.lean`:

```text
esymmGen
esymmField
symmetricPartField
algebraMap_mem_esymmField_of_isSymmetric
symmetricPartField_eq_esymmField
```

`symmetricPartField_eq_esymmField` is the fundamental theorem of symmetric rational functions: the
symmetric part of the rational function field is exactly the field the elementary symmetric
functions generate over the constants.  Combined with the Galois group this says the generic
polynomial of degree `d`, read over the field generated by its own coefficients, has Galois group
`S_d`.

Step 2 is completed in `GaloisForLFunctions/HTGeometry/GenericPolynomialSplitting.lean`:

```text
genericRoot
genericMonicF
map_genericMonicF
genericMonic
map_genericMonic
splits_genericMonic
adjoin_rootSet_genericMonic
isSplittingField_genericMonic
genericMonicGaloisEquiv
card_genericMonicGal
```

`genericMonicGaloisEquiv` is the statement `(3)` is specialised from: the Galois group of the
generic monic polynomial of degree `d` is the full symmetric group `S_d`.  The descent of the
product of linear factors to the symmetric part is coefficientwise, from the invariance of the
whole product under renaming; the roots generate the rational function field because a subalgebra
of a finite extension is a field, so the field they generate already contains every fraction.

Vieta closes the loop, in `GaloisForLFunctions/HTGeometry/GenericPolynomialVieta.lean`:

```text
coeff_genericMonicF
genericCoeff
esymmField_eq_adjoin_genericCoeff
symmetricPartField_eq_adjoin_genericCoeff
```

The coefficients of the generic polynomial are the elementary symmetric functions up to sign, so
the field they generate is the symmetric part.  The generic polynomial of degree `d` is therefore
read over the field its own coefficients generate, and has Galois group `S_d` there -- which is the
statement `(3)` specialises.

Step 4 begins with the centering, in
`GaloisForLFunctions/HTGeometry/CenteredGenericPolynomial.lean`:

```text
genericAverage
centeredRoot
smul_centeredRoot
centeredRoot_injective
sum_centeredRoot
centeredMonicF
map_centeredMonicF
coeff_centeredMonicF_pred
```

Removing the average of the roots from each root leaves them summing to zero, so the monic
polynomial they define has no next-to-leading coefficient: it is the centered generic polynomial.
The average is symmetric, so permuting the variables still permutes the centered roots, and the
centered roots stay pairwise distinct.  The remaining step is to identify the fixed field of that
action with the field generated by the centered coefficients, for which the plan is the Galois
correspondence rather than a degree bound: the restriction map from the symmetric group into the
automorphisms over the centered coefficient field is injective, and the root-permutation embedding
bounds that automorphism group by `d!` from above.

The centered field and its Artin degree are in
`GaloisForLFunctions/HTGeometry/CenteredGenericField.lean`:

```text
permAlgEquiv
centeredField
centeredField_map
centeredFieldInvariant
centeredFieldFaithful
centeredSymmetricPart
finrank_centeredSymmetricPart
```

The centered roots generate an intermediate field which permuting the variables maps onto itself,
so the symmetric group acts on it; the action is faithful because the centered roots are distinct.
Artin then gives that field degree `d!` over its fixed part -- the centered analogue of the degree
the uncentered construction started from.

The centered coefficients are in
`GaloisForLFunctions/HTGeometry/CenteredGenericCoefficients.lean`:

```text
centeredMonicF_mem_lifts
coeff_centeredMonicF_mem
centeredCoeff
centeredCoeffField
smul_centeredCoeff
centeredFixedBy
smul_eq_of_mem_centeredCoeffField
centeredPermAlgEquiv
centeredPermAlgEquiv_injective
```

Every coefficient of the centered polynomial lies in the centered field, because the polynomial
lifts through the inclusion of that field, and every coefficient is fixed by each permutation
because the whole polynomial is.  So the symmetric group embeds in the automorphisms of the
centered field over the field its centered coefficients generate.

The generation statement is in
`GaloisForLFunctions/HTGeometry/CenteredGenericGeneration.lean`:

```text
centeredRootIn
adjoin_centeredRootIn_eq_top
adjoin_centeredRootIn_over_coeff_eq_top
centeredAlgEquivEqualizer
centeredAlgEquiv_ext
```

Read inside the field they generate, the centered roots generate everything over the constants,
hence also over the centered coefficients.  So two automorphisms over the centered coefficients
agreeing on the centered roots are equal, since the elements on which they agree form an
intermediate field containing the generators.  That is the rigidity the root-permutation bound
needs.

The centered Galois theorem is in
`GaloisForLFunctions/HTGeometry/CenteredGenericGalois.lean`:

```text
centeredMonicL
coeff_centeredMonicL_fixed
exists_centeredRootIn_eq
centeredRootPerm
centeredRootPerm_injective
card_centeredAut
centeredGaloisEquiv
```

An automorphism over the centered coefficients fixes every coefficient of the centered polynomial,
so it carries roots to roots; the roots are distinct and generate, so the automorphism group
injects into the permutations of the indices.  The symmetric group injects the other way, so both
are bijections and the Galois group of the centered generic polynomial of degree `d` is exactly
`S_d`.  This is what `(7)` needs, since over `K(q)` the card's centered equation is that universal
polynomial with free coefficients `c_j/q`.

The expansion `(5)` starts from an exact telescoping identity, in
`GaloisForLFunctions/HTGeometry/GeometricInverseTruncation.lean`:

```text
add_mul_geomSum
geomInverseSum
mul_geomInverseSum
coeff_eq_geomInverseSum_of_mul_eq_one
coeff_geomInverseSum_top
```

Multiplying `a + r` by the alternating geometric sum in `r` leaves exactly `1` plus a remainder
carrying `r^(n+1)`.  Applied in a power series ring with `r` the non-constant part, this is the
finite form of the geometric expansion of the inverse: no summability argument and no truncation
quotient is needed, because the identity is exact and the remainder visibly has order `n+1`.

Reading the coefficient off gives `(5)` itself:

```text
[t^n] Y = sum_(k=0)^n (-1)^k b^(k+1) [t^(n-k)] R^k,      b = a^(-1),
```

for any `Y` inverting the series, since the difference between `Y` and the truncated sum is
divisible by `t^(n+1)`.

The change of parameters `(6)`--`(9)` is differentiated through the coefficient extraction, using
`GaloisForLFunctions/HTGeometry/DerivationPolynomialCoefficientwise.lean`:

```text
coeffwise
coeff_coeffwise
coeffwiseDerivation
coeff_pow_coeffwise
```

A derivation of the coefficient ring acts coefficientwise on polynomials and is again a derivation,
so a partial derivative in the parameters `p_i` commutes with extracting `[t^j]`.  Since
`dR/dp_i = t^(i-1)`, the chain rule gives

```text
d/dp_i [t^j] R^m = m [t^(j-i+1)] R^(m-1),
```

which is zero for `i-1 > j` and equals `m p_1^(m-1)` at `i = j+1`.  That is exactly the
triangularity of `(9)` with the nonvanishing diagonal `(n-j) p_1^(n-j-1)`.

That computation is carried out in
`GaloisForLFunctions/HTGeometry/TailPolynomialTriangularity.lean`:

```text
tailPoly
coeff_tailPoly
coeffwiseDerivation_pderiv_tailPoly
pderiv_coeff_tailPoly_pow
pderiv_coeff_tailPoly_pow_eq_zero
pderiv_coeff_tailPoly_pow_diag
coeff_zero_tailPoly_pow
```

`pderiv_coeff_tailPoly_pow_eq_zero` is the vanishing above the diagonal and
`pderiv_coeff_tailPoly_pow_diag` together with `coeff_zero_tailPoly_pow` is the diagonal entry
`m p_1^(m-1)`.  The change of parameters `(6)` is therefore triangular with every diagonal entry a
nonzero multiple of a power of `p_1`.

The independence itself is in
`GaloisForLFunctions/HTGeometry/TailCoefficientIndependence.lean`:

```text
tailCoeff
tailJacobian
tailJacobian_upperTriangular
tailJacobian_diag
tailJacobian_det_ne_zero
algebraicIndependent_tailCoeff
```

`algebraicIndependent_tailCoeff` is the statement after `(9)`: the coefficients `c_0,...,c_(n-1)`
are algebraically independent, so `E_0 = K(q, c_0,...,c_(n-1))` is a rational function field in
`n+1` variables and the centered equation `(7)` is read over the field its own coefficients
generate.  The signs in `(6)` are units and do not affect independence.

The group-theoretic half of the Kummer step is in
`GaloisForLFunctions/HTGeometry/SymmetricGroupCommutator.lean`:

```text
sign_commutatorElement
isThreeCycle_mem_commutator
commutator_perm_eq_alternatingGroup
alternatingGroup_le_of_abelian_quotient
eq_alternatingGroup_or_top_of_abelian_quotient
map_eq_alternatingGroup_or_top
```

`map_eq_alternatingGroup_or_top` is the same dichotomy for a group merely isomorphic to a symmetric
group, which is how it is met in practice: the Galois group is identified with `S_(n+1)` through an
isomorphism, not equal to it.

The Galois correspondence turns that into a statement about fields, in
`GaloisForLFunctions/HTGeometry/FixedFieldDichotomy.lean`:

```text
eq_bot_or_eq_fixedField_alternating
finrank_fixedField_eq_index
finrank_fixedField_alternating
finrank_eq_one_or_two_of_abelian_quotient
```

An intermediate field whose fixing subgroup is normal with abelian quotient is either the base or
the fixed field of the preimage of the alternating group.  That is the dichotomy `(10)` needs, in
field form.  `finrank_eq_one_or_two_of_abelian_quotient` states it as a degree: the fixed field of a
subgroup has degree its index, the alternating group has index two, so such an intermediate field
has degree one or two.  That is precisely the hypothesis of `inf_eq_bot_of_no_sqrt`, so the group
side and the field side now meet with no gap.

The two views of an intermediate field are identified in
`GaloisForLFunctions/HTGeometry/IntermediateFieldComap.lean`:

```text
comapValEquiv
finrank_comap_val
```

A field contained in a larger intermediate field is the same whether read inside the ambient field
or inside the larger one, so its degree over the base is unambiguous.  This is what lets the
dichotomy, proved by the Galois correspondence of the subextension, be applied to the intersection
as originally given.

The corrected hypothesis is met because of
`GaloisForLFunctions/HTGeometry/SymmetricQuadraticUnique.lean`:

```text
eq_alternatingGroup_of_index_eq_two
eq_of_finrank_eq_two_of_permGal
```

A subgroup of index two is normal with quotient of order two, hence abelian, so in a symmetric group
it is the alternating group.  An extension with symmetric Galois group therefore has exactly one
quadratic subextension, so any square root of a base element lying in the splitting field generates
the alternating fixed field and has the discriminant's square class.  That is what makes the
restricted exclusion condition satisfiable in the even case.

It is discharged in `GaloisForLFunctions/HTGeometry/EvenCaseDischarge.lean`:

```text
ne_zero_of_sq_eq
not_sq_mul_of_sq_mul
notMem_of_permGal_of_isCyclic
```

Square classes transfer: if `e * d` is a square and `d * c` is not, then `e * c` is not.  So a
single square-class computation on the fixed square root -- the discriminant against the constant
coefficient -- excludes every square root of a base element in the splitting field from the Kummer
extension.  The square-class computation itself is
`GaloisForLFunctions/HTGeometry/PolynomialNonSquare.lean`:

```text
not_isSquare_mul_X_of_not_dvd
```

A variable is prime, so a polynomial not divisible by it, multiplied by it, is divisible by that
prime exactly once and is a nonsquare in the fraction field.  With the discriminant and the constant
coefficient this is the input `notMem_of_permGal_of_isCyclic` needs.  `notMem_of_permGal_of_isCyclic` is the exclusion condition for even `n`, with no
hypotheses left open.

The capstone with the exclusion discharged is in
`GaloisForLFunctions/HTGeometry/KummerBaseChangeEven.lean`:

```text
kummerBaseChangeEvenEquiv
```

Its only inputs are the abelian quotient on the intersection and one square-class computation on a
fixed square root -- no condition quantified over all elements.  That is `(3)` for even `n`.

### The assembled statement

`GaloisForLFunctions/HTGeometry/KummerBaseChange.lean` closes with

```text
kummerBaseChangeOfAbelian
kummerBaseChangePermOfAbelian
```

`kummerBaseChangePermOfAbelian` is `(3)` in abstract form, assembled from both sides at once: given a
Galois extension whose group is isomorphic to a symmetric group, a second factor whose compositum
with it is everything, an intersection whose fixing subgroup is normal with abelian quotient, and no
square root of a base element inside the second factor, the automorphism group over the second
factor is still the full symmetric group.

The two hypotheses that remain are exactly the two inputs the card's proof supplies: the abelian
quotient comes from `M/E_0` being cyclic, and the absence of square roots from the discriminant
argument, itself now reduced to the constant coefficient not dividing the discriminant.

The first of those is discharged in
`GaloisForLFunctions/HTGeometry/KummerAbelian.lean`:

```text
commute_gal_XPowSubC
```

Over a field containing a primitive `n`-th root of unity, adjoining an `n`-th root gives an
extension whose automorphism group is the group of `n`-th roots of unity, hence commutative.  Since
the constant field of the card is algebraically closed, this applies to `M = E_0(p_1)` and supplies
the abelian-quotient hypothesis.

It is carried to the quotient in
`GaloisForLFunctions/HTGeometry/AbelianQuotientTransfer.lean`:

```text
commute_of_surjective
commute_gal_of_le
commute_quotient_of_commute_gal
commute_quotient_of_le_abelian
```

Commutativity passes to surjective images, so it descends from a Kummer extension to any normal
subextension, and the Galois correspondence identifies the quotient of the automorphism group by a
normal subgroup with the automorphism group of the fixed field.  Chaining these turns the
commutativity of the Kummer group into the abelian-quotient hypothesis of the capstone;
`commute_quotient_of_le_abelian` is that chain as a single statement.

### The ambient field

`GaloisForLFunctions/HTGeometry/SplittingFieldCompositum.lean` supplies it:

```text
rootSet_mul
adjoin_rootSet_eq_top
sup_adjoin_rootSet_eq_top
```

In the splitting field of a product, the subfields generated by the roots of the two factors have
compositum everything, because the roots of a product are the roots of the factors.  Taking the
product of the centered polynomial with `X^n - c_0` therefore places the splitting field and the
Kummer extension inside one ambient field with `E sup M = top`, which is the compositum hypothesis of
the base change step.

The polynomial-level statement is in
`GaloisForLFunctions/HTGeometry/PolynomialBaseChange.lean`:

```text
rootField
polyBaseChangeEquiv
polyBaseChangeOddEquiv
```

`polyBaseChangeEquiv` says: inside the splitting field of a product, if the Galois group of the
first factor is the symmetric group, the intersection with the field generated by the second
factor's roots has abelian Galois quotient, and no square root of a base element lies in that
field, then the automorphism group over that field is still the symmetric group.  Applied with the
centered polynomial and `X^n - c_0`, this is `(3)`.

For odd `n` the square-root hypothesis disappears: `polyBaseChangeOddEquiv` needs only that the
second factor's root field has odd degree, since no square root of a base element can live there.
That is the whole of `(3)` for odd `n`, with no discriminant input whatsoever.

The even case is in `GaloisForLFunctions/HTGeometry/EvenKummerObstruction.lean`:

```text
no_sqrt_of_square_class_ne
notMem_of_isCyclic_of_square_class
```

If every square root of a base element lying in the second factor already lies in the fixed
square-root subextension, and the two radicands sit in different square classes, then no such square
root exists there.  The radicands are the discriminant and the constant coefficient, and the
constant coefficient does not divide the discriminant, so the classes do differ.

That uniqueness is now proved, in
`GaloisForLFunctions/HTGeometry/CyclicSubgroupUnique.lean`:

```text
subgroup_toFinset_eq_filter
subgroup_eq_of_card_eq
```

A subgroup of order `d` of a finite cyclic group is exactly the set of solutions of `x^d = 1`,
because it is contained in that set and the set has at most `d` elements.  So two subgroups of the
same order coincide, and by the Galois correspondence the quadratic subextension of a cyclic
extension is unique.  Mathlib has no such lemma for cyclic groups.

The field statement follows in
`GaloisForLFunctions/HTGeometry/CyclicQuadraticUnique.lean`:

```text
finrank_eq_index_fixingSubgroup
eq_of_finrank_eq_two_of_isCyclic
```

The degree of an intermediate field over the base is the index of its fixing subgroup, so two
quadratic subextensions have fixing subgroups of the same order, hence equal in a cyclic group, hence
equal fields.  That pins the quadratic subextension of the Kummer extension to the one generated by
the square root of the radicand.

That hypothesis is then discharged in
`GaloisForLFunctions/HTGeometry/CyclicSqrtMem.lean`:

```text
mem_adjoin_of_sq_mem_of_isCyclic
```

Inside a cyclic extension every square root of a base element generates a quadratic subextension,
and there is only one, so all of them lie in the subextension generated by any fixed one.  That is
exactly the `hquad` hypothesis of `no_sqrt_of_square_class_ne`.

`notMem_of_isCyclic_of_square_class` is the even case assembled: inside a cyclic extension
containing a square root of `c`, a square root of `e` outside the base cannot occur once `e * c` is
not a square.  With `e` the discriminant and `c` the constant coefficient, the square class differs
because the constant coefficient does not divide the discriminant, so the exclusion holds.

`commutator_perm_eq_alternatingGroup` -- absent from mathlib -- says the commutator subgroup of a
symmetric group is its alternating group, so every abelian quotient of `S_(n+1)`, in particular
every cyclic one, factors through the sign.  That is the step in `(10)` which reduces the possible
intersections `E cap M` to `E_0` and the quadratic subfield, leaving only the discriminant to be
shown a nonsquare.  `eq_alternatingGroup_or_top_of_abelian_quotient` states that dichotomy
directly: a normal subgroup of a symmetric group with abelian quotient is either the alternating
group or everything.

The quadratic subfield is identified by the sign law for the discriminant square root, in
`GaloisForLFunctions/HTGeometry/VandermondeSign.lean`:

```text
vandermondeProd
det_vandermonde_eq_vandermondeProd
vandermondeProd_comp
vandermondeProd_comp_eq_iff
```

The product of all root differences is the Vandermonde determinant of the roots, and permuting the
roots permutes the rows, so the product is multiplied by the sign.  In characteristic zero a
permutation therefore fixes it exactly when it is even: the alternating group is the exact
stabiliser of the square root of the discriminant.

The rigidity half of the base change `(10)` is in
`GaloisForLFunctions/HTGeometry/AlgEquivAdjoinExt.lean`:

```text
algEquivEqualizer
algEquiv_ext_of_adjoin_eq_top
algEquiv_ext_of_sup_eq_top
algEquiv_eq_refl_of_sup_eq_top
```

Two automorphisms agreeing on a generating set are equal, since the elements on which they agree
form an intermediate field.  In particular an automorphism of a compositum fixing each factor is
the identity, which is the injectivity of the restriction map from `Gal(EM/M)` to `Gal(E/E_0)`.
Mathlib has no natural-irrationalities theorem; the fixed-field step of its surjectivity half is in
`GaloisForLFunctions/HTGeometry/GaloisFixedByAll.lean`:

```text
mem_bot_of_forall_fixed
exists_algebraMap_of_forall_fixed
mem_inf_of_forall_fixed
```

An element of one factor fixed by every automorphism over the other factor lies in the
intersection, because for a finite Galois extension the fixed field of the whole automorphism group
is the base.  With the injectivity already proved, the image of the restriction map has fixed field
exactly `E cap M`, so the Galois correspondence for `E/E_0` identifies that image with
`Gal(E/(E cap M))`.  The assembled theorem is in
`GaloisForLFunctions/HTGeometry/NaturalIrrationalities.lean`:

```text
compositumRestrict
compositumRestrict_commutes
compositumRestrict_injective
compositumRestrict_surjective
compositumRestrictEquiv
```

`compositumRestrictEquiv` is natural irrationalities: if the two factors of a compositum meet in
the base, restriction is an isomorphism from the automorphisms over one factor onto the Galois
group of the other.  Applied with `E` the splitting field of `(7)` over `E_0` and `M` the Kummer
extension, this is exactly the step `(10)` needs -- once `E cap M = E_0` is known, which is what
the discriminant nonsquareness supplies.

The nonsquare criterion is in `GaloisForLFunctions/HTGeometry/SquareClassPrime.lean`:

```text
exists_algebraMap_of_sq_eq
not_isSquare_of_prime_dvd_once
```

In an integrally closed domain a square root in the fraction field of a ring element lies in the
ring, so a prime dividing that element exactly once would have to divide the root, forcing it to
divide the element twice.  Exact divisibility by one prime therefore certifies a nonsquare.

This reduces the discriminant step to a divisibility statement.  The Kummer extension `M/E_0` is
cyclic of degree `n`, so for `n` odd it has no quadratic subextension and the discriminant cannot
become a square; for `n` even its unique quadratic subextension is `E_0(sqrt(c_0))`, so the
discriminant becomes a square exactly when `disc * c_0` is a square in `E_0`.  Since `E_0` is a
rational function field and `c_0` is one of its variables, the criterion applies with `p = c_0`, and
what has to be checked is that `c_0` does not divide `disc` -- which is the statement that the
centered equation with vanishing constant term still has distinct roots.

Two facts about that discriminant are now formal.  `vandermondeProd_centeredRoot_eq` says centering
does not change it -- differences do not see a common shift -- so the centered and uncentered
discriminants agree and the uncentered model, where the roots are free variables, may be used.
`sq_vandermondeProd_genericRoot_mem` says it is symmetric, hence a rational function of the
coefficients.  What is still needed is that it is a *polynomial* in them, which is the fundamental
theorem of symmetric polynomials in the free-root model, and then that `c_0` does not divide it.

The first of those is now proved, in
`GaloisForLFunctions/HTGeometry/DiscriminantPolynomial.lean`:

```text
vandermondePoly
rename_vandermondePoly
isSymmetric_sq_vandermondePoly
sq_vandermondePoly_mem_adjoin
```

Renaming the variables multiplies the Vandermonde product by the sign, so its square is symmetric,
and the fundamental theorem of symmetric polynomials writes it as a polynomial in the elementary
symmetric functions.  The discriminant is therefore a polynomial, not merely a rational function, in
the coefficients.  The divisibility is settled in the same file:

```text
zeroLast
zeroLast_injective
esymm_top_eq_prod
aeval_zeroLast_esymm_top
aeval_zeroLast_vandermondePoly
esymm_top_not_dvd_sq_vandermondePoly
```

Setting one root to zero kills the product of all the roots -- the top elementary symmetric
function, which is the constant coefficient up to sign -- while leaving the roots pairwise distinct,
so the discriminant survives.  Hence the constant coefficient does not divide the discriminant,
which is exactly what the square-class criterion needs.

The two cases are packaged in
`GaloisForLFunctions/HTGeometry/SquareRootObstruction.lean`:

```text
notMem_of_not_two_dvd_finrank
notMem_adjoin_sqrt_of_not_sq
```

A square root of a base element not lying in the base cannot lie in an extension of odd degree, and
cannot lie in a square-root extension whose radicand is in a different square class.  These are the
two branches of the Kummer step in the form the assembly uses.

Quadratic subextensions are matched to square roots in
`GaloisForLFunctions/HTGeometry/CompleteTheSquare.lean`:

```text
exists_sqrt_adjoin_eq
```

In characteristic zero an element of degree two, shifted by half its trace, has its square in the
base and generates the same field.  So every quadratic subextension is a square-root extension and
the square-class obstruction applies to it.

The intersection is then forced to be trivial, in
`GaloisForLFunctions/HTGeometry/KummerInfBot.lean`:

```text
inf_eq_bot_of_no_sqrt
```

If the intersection is the base or a quadratic extension of it, and no square root of a base
element lies in the second factor, then the intersection is the base: a quadratic intersection
would contain an element of degree two, which after completing the square is a forbidden square
root.  Feeding this to `compositumRestrictEquiv` gives `(3)`, packaged in
`GaloisForLFunctions/HTGeometry/KummerBaseChange.lean`:

```text
kummerBaseChangeEquiv
no_sqrt_of_not_two_dvd_finrank
oddBaseChangeEquiv
kummerBaseChangePermEquiv
```

`kummerBaseChangePermEquiv` is the abstract form of the card's `(3)`: over the larger field the
Galois group is still the full symmetric group.  `oddBaseChangeEquiv` is the odd-degree case, where
the square root hypothesis is discharged by the degree count alone.

Both come in a second form, `inf_eq_bot_of_no_sqrt_of_root` and
`kummerBaseChangePermEquivOfRoot`, in which the dichotomy is supplied as an explicit square root
rather than as a degree.  That is how the concrete case supplies it: there the quadratic
intersection is generated by the Vandermonde product itself, so no degree computation is needed at
the point of use.

### Formalisation inventory

Forty-two modules, all building with only `propext`, `Classical.choice`, `Quot.sound`:

```text
SymmetricVariableAction        SymmetricRationalFunctions     SymmetricCoefficientField
GenericPolynomialSplitting     GenericPolynomialVieta         GenericPolynomialSeparable
CenteredGenericPolynomial      CenteredGenericField           CenteredGenericCoefficients
CenteredGenericGeneration      CenteredGenericGalois          GeometricInverseTruncation
DerivationPolynomialCoefficientwise                           TailPolynomialTriangularity
TailCoefficientIndependence    SymmetricGroupCommutator       VandermondeSign
AlgEquivAdjoinExt              GaloisFixedByAll               NaturalIrrationalities
SquareClassPrime               QuadraticSubextension          QuadraticRepresentation
DiscriminantPolynomial         SquareRootObstruction          CompleteTheSquare
KummerInfBot                   KummerBaseChange               FixedFieldDichotomy
IntermediateFieldComap         KummerAbelian                  AbelianQuotientTransfer
SplittingFieldCompositum       PolynomialBaseChange           EvenKummerObstruction
CyclicSubgroupUnique           CyclicQuadraticUnique          CyclicSqrtMem
SymmetricQuadraticUnique       EvenCaseDischarge              KummerBaseChangeEven
PolynomialNonSquare
```

Facts proved here that mathlib does not carry: the Galois group of the generic polynomial of degree
`d` over the field its coefficients generate is `S_d`; the same for the centered polynomial; the
fundamental theorem of symmetric rational functions; the commutator subgroup of a symmetric group is
its alternating group; the sign law for the Vandermonde product; natural irrationalities; and the
coefficientwise extension of a derivation to polynomials.

A further twenty-six modules complete the two branches and the parameter change, all building with
the same three axioms:

```text
SymmetricCoefficientNonSquare  SymmetricCoefficientFractionModel  SquareSpecialisation
LinearFormPrime                AverageProductNonSquare            CenteredDiscriminantNonSquare
EvenKummerSqrt                 KummerBaseChangeEvenGenerator      TailCoefficientLinearSolve
TailParameterField             PolynomialScaleVariable            TailScalingAutomorphism
TailScalingAction              TailFixedField                     TailCoefficientFixedField
KummerDegreeBound              TailCoefficientDegree              TailCoefficientTower
TailParameterChange            PolynomialBaseChangeEven           CenteredPolynomialOverCoefficients
CenteredRootFieldTop           IntersectionNormal                 IntersectionFixingSubgroup
IntersectionAbelian            PolynomialBaseChangeAssembled
```

Further facts proved here that mathlib does not carry: a row form of an invertible matrix is prime
in the polynomial ring; the coefficient rescaling law for substituting a scalar multiple of the
variable; squares descend along a specialisation whose kernel is a prime; and the triangular
parameter change with its intrinsic characterisation of the coefficient field as a fixed field.

A third group of modules carries the abstract statement to a concrete instantiation, all building
with the same three axioms:

```text
RadicalBaseChangeCapstone      RadicalBaseChangeEvenCapstone  RadicalRootExists
VandermondeFixed               AutPermutesRoots               RadicalBaseChangeFromRoots
RootEnumerationTransport       RadicalBaseChangeFromModel     CenteredSplittingField
RootFieldTransport             KummerCyclic                   PrimitiveRootTransport
CenteredRadicalBaseChange      CenteredDiscriminantIdentification
CenteredSquareClassInput       SumZeroParametrisation         PrimePowerClass
EisensteinRadical              RadicalDegreeExact             EsymmRangeField
EsymmFieldEquiv                IrreducibleRadicalTransport    EsymmRadicalIrreducible
SymmetricPartEsymmBridge       GenericRootSet                 GenericPermRootAction
SymmetricPartConstants         SymmetricPartRadical           GenericRadicalBaseChange
GenericSquareClassInput        GenericFullMonodromy
```

**Status of `(3)`.**  `genericFullMonodromy` proves it for the **generic monic polynomial** with no
hypotheses beyond `3 <= d` and a positive even exponent: the automorphism group of the splitting
field of `genericMonic * (X ^ (2m) - c_top)` over the root field of the second factor is the full
symmetric group.  That is the mathematical content of `(3)` — symmetric monodromy survives an even
Kummer base change — proved unconditionally.

A fourth group carries the statement back to the **centered** setting, all building with the same
three axioms:

```text
TschirnhausShift            TaylorRoots                 CenteredIsTaylorShift
GenericAverageSymmetric     CenteredPartSplittingField  UniversalMonicPolynomial
UniversalCenteredCoefficients                           DetUpdateRowOne
CenteredCoefficientIndependence
```

Further facts proved here that mathlib does not carry: the coefficient law for a Taylor shift in
Hasse-derivative form, with no binomial expansion (`taylor_coeff_pred`, `taylor_coeff_eq_add`);
irreducibility of `X ^ n - q` for a prime radicand at **every** exponent, where mathlib's criteria
stop at odd `n` and prime powers; and the algebraic independence of the centered coefficients of a
monic polynomial with indeterminate coefficients (`algebraicIndependent_centeredFamily`).

**The card's own equation `(7)`.**  Proved, by `centeredFullMonodromy` in
`GaloisForLFunctions/HTGeometry/CenteredFullMonodromy.lean`, with no hypotheses beyond `3 <= d` and
a positive even exponent.  The assembly runs through a fifth group of modules:

```text
MonomialSubstitution          CoeffSubInjective            GenericCenteredIndependence
CenteredCoeffFieldIndependence                             CenteredCoeffFieldRational
CenteredFullMonodromy
```

The centered coefficients are algebraically independent — the universal statement pushed through the
injective specialisation to the generic coefficients, injective because that specialisation is a
signed reversal of the variables followed by the substitution of the elementary symmetric functions.
The top centered coefficient vanishes, so the coefficient field is generated by the remaining
`d - 1`, and with their independence it is a rational function field in `d - 1` variables with the
constant coefficient among them.  That is the card's `E_0`.  A variable is prime, so the radical
polynomial over the constant coefficient is irreducible at every exponent, which is the degree input
of the base change; the square-class input was already `no_sqrt_centered_disc_mul_constant`.

Separability and the nonsquareness over `E_0` are in
`GaloisForLFunctions/HTGeometry/GenericPolynomialSeparable.lean`:

```text
separable_genericMonicF
separable_centeredMonicF
separable_centeredMonicL
vandermondeProd_sub_const
vandermondeProd_centeredRoot_eq
smul_vandermondeProd_genericRoot
sq_vandermondeProd_genericRoot_mem
smul_vandermondeProd_centeredRootIn
vandermondeProd_centeredRootIn_ne_zero
vandermondeProd_notMem_centeredCoeffField
```

`vandermondeProd_notMem_centeredCoeffField` is the statement that the discriminant is a nonsquare
over the coefficient field: an odd permutation negates the square root while fixing every
coefficient.  Mathlib has no discriminant of a polynomial in its coefficients -- only
`Algebra.discr` of a basis -- so the square root is used directly rather than through a
discriminant construction.

The odd case is settled in `GaloisForLFunctions/HTGeometry/QuadraticSubextension.lean`:

```text
isIntegral_of_sq_mem_bot
finrank_adjoin_eq_two
two_dvd_finrank_of_sq_mem_bot
```

An element whose square is a scalar but which is not itself a scalar generates a quadratic
subextension, so any extension containing it has even degree.  Since `delta^2` lies in `E_0` and
`delta` does not, `delta` in `M` would force `2 | [M : E_0] = n`.

### Exact remaining gap

**Closed.**  The even case is discharged by the square-class chain
(`SymmetricCoefficientNonSquare` through `CenteredDiscriminantNonSquare`), and both the uncentered
and the centered equations now carry an unconditional theorem — `genericFullMonodromy` and
`centeredFullMonodromy`.  The account below records how the even case was reduced before that chain
was built.

Everything in the proof of `(3)` is formal except one divisibility, and only for even `n`.  Writing
`delta` for the Vandermonde product of the roots, the argument needs `delta` to stay outside `M`.
For `n` odd this is now proved: `delta` in `M` would make `n` even.

For even `n` the reduction runs through
`GaloisForLFunctions/HTGeometry/QuadraticRepresentation.lean`:

```text
exists_repr_of_mem_adjoin_sqrt
sq_mul_eq_sq_of_mem_adjoin_sqrt
```

Every element of a square-root extension is a scalar plus a scalar multiple of the root, by
reducing a polynomial in the root modulo its quadratic relation.  Applying this to `delta` inside
the quadratic subextension `E_0(sqrt(c_0))` and using that `delta^2` lies in `E_0` forces the
scalar part to vanish, so `delta^2 * c_0` is a square in `E_0`.  That implication is
`sq_mul_eq_sq_of_mem_adjoin_sqrt`, so the entire card is now reduced to one statement: for even `n`,
`delta^2 * c_0` is not a square in `E_0`.  Equivalently, the `c_0`-adic valuation of the
discriminant is even, and since the discriminant is a polynomial in the coefficients that amounts
to `c_0` not dividing it -- the centered equation with vanishing constant term still having
distinct roots.  For `n` even its
unique quadratic subextension is `E_0(sqrt(c_0))`, so what must be excluded is
`delta^2 * c_0` being a square in `E_0`; since `E_0` is a rational function field with `c_0` among
its variables, this is the `c_0`-adic valuation of `delta^2` being even, equivalently `c_0` not
dividing the discriminant.

## Log

- 2026-08-01 — started the Lean route to `(3)`.  Formalized the permutation action of the symmetric
  group on a rational function field, its faithfulness, and Artin's degree `d!` for the symmetric
  part.  This is the base over which the generic polynomial will be shown to have the full
  symmetric Galois group.

- 2026-08-01 — formalized the Galois group and the symmetric-ratio theorem.  Artin's theorem plus
  the bijection between the group and the algebra automorphisms gives that the Galois group of the
  rational function field over its symmetric part is exactly the symmetric group.  Symmetrising the
  denominator then shows every symmetric rational function is a ratio of symmetric polynomials,
  which is the fundamental theorem for rational functions modulo the polynomial case that mathlib
  already carries.

- 2026-08-01 — closed the base identification.  The elementary symmetric functions generate the
  whole symmetric part, because a symmetric rational function is a ratio of symmetric polynomials
  and mathlib's fundamental theorem writes each as a polynomial in them.  With Artin's degree and
  the automorphism bijection this gives the generic-polynomial Galois statement over the
  coefficient field, which is the base the card's centered equation lives over.

- 2026-08-01 — completed the generic-polynomial layer.  The product of the linear factors attached
  to the variables is invariant under renaming, so it descends coefficientwise to a monic degree-`d`
  polynomial over the symmetric part; that polynomial splits there and its roots generate the whole
  rational function field, so the field is its splitting field and its Galois group is the full
  symmetric group of order `d!`.  This is the classical input the card's `(3)` specialises, and it
  is not in mathlib.

- 2026-08-01 — closed the coefficient identification by Vieta.  Expanding the product of linear
  factors gives each coefficient as the corresponding elementary symmetric function up to sign, and
  the signs are units, so the two adjoined fields coincide in both directions.  The generic
  polynomial is now certified to be read over the field its own coefficients generate, which is the
  precise sense in which its Galois group being `S_d` is a statement about free coefficients.

- 2026-08-01 — formalized the centering.  The average of the generic roots is symmetric, so
  subtracting it commutes with permuting the variables; the centered roots therefore carry the same
  symmetric-group action and remain distinct, and Vieta at the next-to-leading slot confirms the
  centered polynomial really is centered.  What remains for the centered analogue of the generic
  Galois theorem is the base identification, planned through the root-permutation bound rather
  than through a splitting-field degree estimate mathlib does not carry.

- 2026-08-01 — put the symmetric-group action on the centered field and proved its Artin degree.
  Stability is the statement that renaming variables permutes the centered roots, so the generated
  field maps onto itself; faithfulness is their distinctness.  With the degree `d!` in hand, what
  remains is to identify the fixed part with the field generated by the centered coefficients, and
  the centered analogue of the generic Galois theorem follows.

- 2026-08-01 — embedded the symmetric group in the automorphisms over the centered coefficient
  field.  The coefficients lie in the centered field by a lifting argument, and are fixed
  permutationwise because the polynomial is; the fixed elements of a single permutation form an
  intermediate field, so the whole generated field is fixed and the action is by automorphisms over
  it.  Faithfulness carries over from the action on the centered field, giving the lower bound of
  `d!` on that automorphism group once its finiteness is available.

- 2026-08-01 — proved that the centered roots generate the centered field, over the constants and
  hence over the centered coefficients, and deduced that an automorphism over the centered
  coefficients is determined by its values on the centered roots.  Together with the injection of
  the symmetric group this is both halves of the pending count: the group injects, and every
  automorphism is pinned down by a permutation of the roots.

- 2026-08-01 — closed the centered Galois theorem.  Fixing the coefficients forces an automorphism
  to permute the roots, and rigidity on the generators makes that permutation determine it, so the
  automorphism group has at most `d!` elements; the injection of the symmetric group gives at least
  `d!`, and the two bounds pin the group exactly.  The universal centered polynomial of degree `d`
  therefore has Galois group `S_d` over the field its coefficients generate, which is the input the
  card's `(7)` reads off after dividing by the leading parameter.

- 2026-08-01 — formalized the telescoping identity behind `(5)`.  The alternating geometric sum in
  the non-constant part inverts a series exactly, up to a remainder carrying the next power, so the
  expansion of the inverse of a truncated Taylor jet is an equation between finite sums rather than
  a statement about convergence.  The remaining coefficient work `(6)`--`(9)` reads the `a`-degrees
  off this identity.

- 2026-08-01 — completed `(5)`.  The difference between an inverse and the truncated geometric sum
  is the inverse times the remainder, hence divisible by `t^(n+1)`, so their coefficients agree up
  to order `n`; expanding the truncated sum termwise then gives the alternating expansion of
  `[t^n] Y` in the powers of the tail.  What remains of the coefficient layer is the change of
  parameters `(6)`--`(9)` and its triangularity.

- 2026-08-01 — built the coefficientwise extension of a derivation to polynomials, which mathlib
  does not carry, and its chain rule for powers.  This is what moves a partial derivative in the
  parameters across extraction of a coefficient in the formal variable, turning the triangularity
  of the change of parameters `(6)`--`(9)` into a one-line chain-rule computation instead of a
  combinatorial expansion over compositions.

- 2026-08-01 — instantiated the chain rule on the tail polynomial and obtained `(9)`.  The
  derivative of the tail in its `i`-th parameter is the `i`-th power of the formal variable, so the
  derivative of a coefficient of a power of the tail is a shifted coefficient of the next lower
  power; that shift is what makes the change of parameters triangular, and evaluating it on the
  diagonal gives `m p_1^(m-1)`, nonzero in characteristic zero.

- 2026-08-01 — proved the algebraic independence of the tail coefficients.  The Jacobian against the
  parameter derivatives is triangular by the shift identity, with diagonal `m p_1^(m-1)` nonzero in
  characteristic zero, so its determinant is a nonzero polynomial and the corpus Jacobian criterion
  applies.  With this `E_0` is a rational function field of the right transcendence degree, and the
  centered generic Galois theorem transfers to `(7)`.  What remains of the card is the Kummer base
  change `(10)` and the discriminant-nonsquare step.

- 2026-08-01 — proved that the commutator subgroup of a symmetric group is its alternating group.
  A commutator has trivial sign because the sign lands in a commutative group; conversely a
  three-cycle is conjugate to its own inverse, and conjugating by a witness of that exhibits the
  three-cycle itself as a commutator, so the three-cycles -- which generate the alternating group --
  all lie in the commutator subgroup.  This gives the cyclic-quotient step of `(10)` with no
  hypothesis on the number of letters.

- 2026-08-01 — turned the commutator identity into the dichotomy `(10)` uses: a normal subgroup of a
  symmetric group whose quotient is abelian is either the alternating group or the whole group.
  The containment comes from the commutator identity, and the two-way split from the index of the
  alternating group being two.  So the intersection `E cap M` is either `E_0` or the quadratic
  subfield, and only the discriminant nonsquareness is left.

- 2026-08-01 — proved the sign law for the discriminant square root, which mathlib does not carry.
  Rather than a combinatorial count of inversions, the product of all root differences is read as a
  Vandermonde determinant, whose rows a permutation permutes; the determinant's behaviour under row
  permutation then gives the sign immediately.  With characteristic zero this makes the alternating
  group the exact stabiliser, so the quadratic subfield in `(10)` is generated by that square root.

- 2026-08-01 — proved the rigidity half of the base change.  The agreement locus of two
  automorphisms is an intermediate field, so agreement on a generating set forces equality; over a
  compositum this makes the restriction to one factor injective on the automorphisms fixing the
  other.  Mathlib carries no natural-irrationalities theorem, so the surjectivity half will have to
  be built as well; it is the last structural piece before the discriminant argument.

- 2026-08-01 — proved the fixed-field step of the base change.  For a finite Galois extension the
  fixed field of the whole automorphism group is the base, so an element of one factor of a
  compositum moved by no automorphism over the other factor already lies in the intersection.  With
  the injectivity from the previous batch, the image of the restriction map is pinned down by its
  fixed field, which is what the Galois correspondence needs to identify it.

- 2026-08-01 — assembled natural irrationalities, which mathlib does not carry.  Restriction to one
  factor of a compositum is a group homomorphism; it is injective because an automorphism fixing
  both factors is the identity, and surjective because the fixed field of its image is the
  intersection of the factors, which the Galois correspondence then turns into the full group when
  that intersection is the base.  Only the discriminant nonsquareness is now missing from `(10)`.

- 2026-08-01 — proved the nonsquare criterion and reduced the discriminant step to a divisibility.
  Integral closedness pulls a fraction-field square root back into the ring, so exact divisibility
  by a prime certifies a nonsquare.  Since the Kummer extension is cyclic, only its unique
  quadratic subextension `E_0(sqrt(c_0))` can absorb the discriminant, and `c_0` is a variable of
  the rational function field `E_0`; so the whole step reduces to `c_0` not dividing `disc`,
  equivalently to the centered equation with vanishing constant term having distinct roots.

- 2026-08-01 — proved separability of both generic polynomials and that the square root of the
  discriminant lies outside the coefficient field, an odd permutation negating it while fixing
  every coefficient.  That is the nonsquareness over `E_0`; what the Kummer step still needs is the
  nonsquareness over `M`, which the card obtains from reducedness of the universal discriminant
  divisor and which reduces here to the `c_0`-adic valuation of the discriminant being even.

- 2026-08-01 — settled the odd case of the Kummer step outright.  A square root of a scalar that is
  not itself a scalar generates a quadratic subextension, so any field containing it has even
  degree over the base; since the discriminant square root is not a coefficient but its square is,
  its presence in `M` would force the degree `n` to be even.  For odd `n` the base change therefore
  preserves the full symmetric group with no discriminant computation at all, and the remaining gap
  is confined to even `n`.

- 2026-08-01 — proved the representation lemma for square-root extensions, reducing a polynomial in
  the root modulo its quadratic relation.  This is the step that turns `delta` lying in the Kummer
  extension into the square-class identity `delta^2 * c_0` being a square, which is the form the
  remaining even-`n` gap now takes.

- 2026-08-01 — completed the even-`n` reduction.  Inside the quadratic subextension the
  discriminant square root must be a scalar multiple of the Kummer root, because its own square
  lies in the base; so its presence there forces `delta^2 * c_0` to be a square.  The card is now
  one statement away from complete: that this square-class identity fails, equivalently that `c_0`
  does not divide the discriminant.

- 2026-08-01 — set up the free-root model for the last gap.  The Vandermonde product is unchanged by
  translating the family, so the centered and uncentered discriminants coincide and the argument may
  be run where the roots are free variables; there the discriminant is visibly symmetric, hence a
  rational function of the coefficients.  Upgrading that to a polynomial and computing its
  `c_0`-divisibility is the remainder.

- 2026-08-01 — proved the discriminant is a polynomial in the coefficients.  Renaming multiplies the
  Vandermonde product by the sign, so its square is symmetric, and mathlib's fundamental theorem
  then writes it in the elementary symmetric functions.  This is what makes the `c_0`-divisibility
  question well posed, and that divisibility is now the only thing the card still lacks.

- 2026-08-01 — closed the divisibility.  Substituting zero for the last root sends the top
  elementary symmetric function to zero while keeping the substituted family injective, so the
  Vandermonde product stays nonzero; a divisor relation would force it to vanish.  The constant
  coefficient therefore does not divide the discriminant, which is the last input the Kummer step
  needed.

- 2026-08-01 — packaged the two branches of the Kummer step.  The odd branch is the quadratic
  subextension count; the even branch is the square-class computation.  Every mathematical
  ingredient of `(3)` is now proved unconditionally, and what is left is the instantiation of this
  chain on the card's own base field and equation.

- 2026-08-01 — every mathematical ingredient of `(3)` is now formal across twenty-five modules, all
  rebuilt and audited together.  The remaining work is naming the card's `E_0`, `M` and equation and
  feeding them to the chain; no further mathematics is required.

- 2026-08-01 — proved that a quadratic subextension is always a square-root extension, by completing
  the square.  This is the last bridge: the abelian-quotient dichotomy produces a degree-two
  intersection, completing the square turns it into a square root, and the two obstructions then
  exclude it.

- 2026-08-01 — assembled the intersection step.  With the dichotomy on one side and the two square
  root obstructions on the other, the intersection of the splitting field with the Kummer extension
  is the base, which is the hypothesis natural irrationalities needs.  The chain from the generic
  Galois group to base-change invariance is now closed end to end.

- 2026-08-01 — packaged the capstone.  `kummerBaseChangePermEquiv` states `(3)` abstractly: with the
  intersection at most quadratic and no square root of a base element in the second factor, the
  Galois group over the larger field is still the full symmetric group.  The odd-degree case is a
  corollary needing no square-class input at all.

- 2026-08-01 — added the root form of the intersection step and of the capstone.  Stating the
  dichotomy as "the intersection is the base, or it contains an explicit square root" matches the
  concrete situation, where that square root is the Vandermonde product already constructed, and
  removes the degree computation from the point of use.

- 2026-08-01 — transported the abelian-quotient dichotomy along an isomorphism.  The Galois group is
  only ever identified with the symmetric group up to isomorphism, so the dichotomy is needed in
  that form; the quotient by the image subgroup is isomorphic to the original quotient, hence
  abelian, and the dichotomy applies to the image.

- 2026-08-01 — crossed from groups to fields.  With the Galois correspondence, an intermediate field
  whose fixing subgroup is normal with abelian quotient is the base or the fixed field of the
  alternating preimage; combined with the square-root obstructions this is exactly the dichotomy the
  Kummer step consumes.

- 2026-08-01 — closed the join between the two sides.  The degree of a fixed field over the base is
  the index of its subgroup, so the alternating fixed field is quadratic, and an intermediate field
  with abelian Galois quotient has degree one or two.  That is exactly the hypothesis the
  intersection step consumes, so the group-theoretic dichotomy and the square-root obstruction now
  compose without any remaining interface.

- 2026-08-01 — identified the two views of an intermediate field and re-audited the whole chain.
  All thirty modules build together with only the standard axioms.  The dichotomy proved inside the
  subextension now transfers to the intersection as given in the ambient field, which was the last
  interface mismatch in the abstract argument.

- 2026-08-01 — assembled the capstone from both sides.  `kummerBaseChangePermOfAbelian` takes the
  group-side hypothesis (abelian quotient) and the field-side hypothesis (no square root) and
  concludes that the symmetric group survives the base change.  Every intermediate step from the
  generic polynomial to this statement is now a proved Lean theorem.

- 2026-08-01 — discharged the abelian hypothesis for Kummer extensions.  Mathlib identifies the
  automorphism group of an `n`-th root extension with the `n`-th roots of unity, which commute, so
  the group-side input of the capstone is available whenever the constants contain enough roots of
  unity -- which they do, the constant field being algebraically closed.

- 2026-08-01 — carried the Kummer commutativity to the quotient.  Commutativity survives surjective
  images, hence descends to normal subextensions, and the Galois correspondence turns the quotient
  by a normal subgroup into the automorphism group of the fixed field.  Both hypotheses of the
  capstone are now reachable from the card's own data.

- 2026-08-01 — collapsed the transfer chain into one statement.  With `commute_quotient_of_le_abelian`
  the group-side hypothesis of the capstone follows directly from the Kummer extension having
  abelian automorphism group.  What remains is the construction of the ambient field; the
  mathematics of `(3)` is complete.

- 2026-08-01 — built the ambient field.  In the splitting field of a product the subfields generated
  by the roots of the factors have compositum everything, so the centered polynomial times
  `X^n - c_0` places the splitting field and the Kummer extension in one ambient field satisfying the
  compositum hypothesis.  All three hypotheses of the capstone are now supplied by proved theorems.

- 2026-08-01 — stated the base change at the level of polynomials.  With the compositum hypothesis
  discharged by the splitting-field construction, `polyBaseChangeEquiv` reads directly as `(3)`:
  enlarging the base by the roots of `X^n - c_0` leaves the symmetric monodromy of the centered
  equation intact.

- 2026-08-01 — stated the odd-degree case with no square-root hypothesis at all.  When the second
  factor's root field has odd degree the obstruction is automatic, so `(3)` for odd `n` now follows
  from the Galois group of the first factor alone.  The card's étale/reducedness argument is needed
  only in the even case, where the concrete divisibility replaces it.

- 2026-08-01 — isolated the even case to a single missing input.  Given that the quadratic
  subextension is unique, the square-class computation excludes the discriminant square root from
  the Kummer extension.  Uniqueness is the statement that a cyclic group has only one subgroup of
  index two; mathlib does not carry it, so it is the next thing to build.

- 2026-08-01 — proved that a finite cyclic group has one subgroup of each order.  A subgroup of order
  `d` is exactly the `d`-torsion, since it sits inside it and the torsion has at most `d` elements.
  This gives the uniqueness of the quadratic subextension, which was the single input the even case
  still needed.

- 2026-08-01 — turned the cyclic subgroup uniqueness into the field statement.  Degree equals index,
  so quadratic subextensions have fixing subgroups of equal order and therefore coincide.  Both
  parity cases of the Kummer step are now supported by proved theorems throughout.

- 2026-08-01 — discharged the last hypothesis of the even case.  In a cyclic extension all square
  roots of base elements generate the same quadratic subextension, so each lies in the one generated
  by any fixed square root; combined with the square-class computation this excludes the
  discriminant square root from the Kummer extension for even `n` as well.

- 2026-08-01 — assembled the even case into one statement.  A square root of `e` outside the base
  cannot lie in a cyclic extension containing a square root of `c` when `e * c` is not a square, and
  for the discriminant against the constant coefficient that is exactly what the divisibility gives.
  Both branches of the Kummer step are now single named theorems.

- 2026-08-01 — corrected a defective hypothesis.  The exclusion condition in the intersection step
  had been stated for *every* square root of a base element lying outside the base.  That is
  unsatisfiable whenever the second factor has even degree, since the second factor then contains
  such a square root itself -- the Kummer root's own middle power.  The condition is now restricted
  to square roots lying in the first factor, which is all the proof ever uses (the element is
  extracted from the intersection, hence lies in both) and which the even case can actually satisfy.
  The correction was propagated through the intersection step, the capstone and the polynomial-level
  statements; all four modules rebuild.

- 2026-08-01 — proved that a symmetric Galois group admits exactly one quadratic subextension, an
  index-two subgroup of a symmetric group being the alternating one.  This is what makes the
  corrected exclusion condition satisfiable for even `n`: a square root of a base element in the
  splitting field must generate the alternating fixed field, so its square class is the
  discriminant's, and the divisibility then excludes it from the Kummer extension.

- 2026-08-01 — discharged the corrected exclusion condition for even `n`.  Square classes transfer,
  so the single computation on the discriminant against the constant coefficient covers every square
  root of a base element in the splitting field.  Both branches of the Kummer step now have their
  exclusion conditions proved outright, with the even branch resting on a satisfiable hypothesis.

- 2026-08-01 — assembled the even capstone with the exclusion discharged.  `kummerBaseChangeEvenEquiv`
  needs only the abelian quotient and one square-class computation, no condition ranging over all
  elements.  Together with the odd capstone this gives `(3)` in both parities from hypotheses the
  card's own situation supplies.

- 2026-08-01 — supplied the square-class computation in polynomial form.  A variable is prime, so a
  polynomial it does not divide, multiplied by it, is a nonsquare in the fraction field.  Combined
  with the constant coefficient not dividing the discriminant this is exactly the input the even
  case consumes, so that case now closes on a fact about polynomials rather than an assumption.

- 2026-08-01 — full rebuild of the whole development: all forty-two modules build together, each
  with only `propext`, `Classical.choice`, `Quot.sound`.  This is the first joint audit since the
  hypothesis correction, so it also confirms the correction propagated cleanly.  Integral closedness
  of the polynomial ring is taken as an instance argument in `PolynomialNonSquare`; it is derivable
  (checked under a full mathlib import) but the narrow import that carries it was not worth the
  search, and stating it explicitly costs callers nothing.

- 2026-08-01 — `SymmetricCoefficientNonSquare.lean`.  The square-class input of the even case is now
  proved outright, not assumed.  The fundamental theorem of symmetric polynomials is packaged as an
  algebra isomorphism `esymmAlgEquiv` from a polynomial ring in `d` variables onto the symmetric
  subalgebra, under which the top variable carries the constant coefficient of the generic
  polynomial.  Transporting the discriminant through it and combining with the proved
  non-divisibility `esymm_top_not_dvd_sq_vandermondePoly` shows the discriminant is not divisible by
  that variable, so its product with the variable has odd valuation there and is a nonsquare:
  `not_isSquare_discCoeffPoly_mul_topIndex`, restated as `no_sqrt_discCoeffPoly_mul_topIndex` in the
  exact shape `¬ ∃ t, e * c = t * t` that `kummerBaseChangeEvenEquiv` consumes.
  Integral closedness is no longer an instance argument anywhere: the missing import was
  `Mathlib.RingTheory.Polynomial.RationalRoot`, which carries the unique-factorisation instance, so
  `PolynomialNonSquare` is now hypothesis-free as well.

- 2026-08-01 — `SymmetricCoefficientFractionModel.lean`.  The square-class step of the "exact
  remaining gap" above is now proved for the **uncentered** generic polynomial.  That section
  reduced the card to one statement: for even degree, `delta^2 * c_0` is not a square in `E_0`,
  justified by "`E_0` is a rational function field with `c_0` among its variables".  For the
  uncentered coefficient field that justification is now a theorem rather than a remark.  Sending the `i`-th
  variable to the `(i+1)`-st elementary symmetric function embeds a polynomial ring in `d` variables
  into the rational functions in the roots; injectivity comes from the fundamental theorem, and the
  embedding extends to the whole rational function field, whose image contains the field generated
  by the coefficients.  Transporting the nonsquare statement of the model along it gives
  `no_sqrt_disc_mul_esymmTop_of_mem_esymmField` and, through
  `symmetricPartField_eq_esymmField`, `no_sqrt_disc_mul_esymmTop_of_mem_symmetricPartField`:
  the discriminant times the constant coefficient has no square root in the symmetric part.
  Axioms `[propext, Classical.choice, Quot.sound]`.
  What this does **not** yet cover: the chain built on this card runs through the centered
  polynomial, whose coefficient field is generated by the centered coefficients `c_2, ..., c_d` and
  has transcendence degree `d - 1`, not `d`.  It is a different field from the symmetric part
  treated here — centering kills one generator — so the statement does not transfer for free.  The
  centered analogue needs the same two inputs in centered coordinates: algebraic independence of
  the centered coefficients, and non-divisibility of the centered discriminant by the centered
  constant coefficient.  That is the next brick.

- 2026-08-01 — `SquareSpecialisation.lean`, the tool for the centered analogue.  A square in the
  fraction field of a unique factorisation domain, written as a reduced fraction, gives a square
  relation in the domain; a ring homomorphism whose kernel consists of multiples of a prime cannot
  kill the denominator, since that would make the prime divide numerator and denominator alike.  So
  `not_isSquare_of_specialisation`: a nonsquare image certifies a nonsquare.  Applied with the
  specialisation that sets the first elementary symmetric function to zero, this is what carries the
  square-class statement from the centered coefficients into a polynomial ring in which the centered
  constant coefficient is a variable.  Axioms `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — reading the card's own theorem statement changes the plan for the even case, for the
  better.  The base field is `E_0 = K(q, c_0, ..., c_{n-1})` and `K` is **algebraically closed**, so
  every constant is a square and all the sign factors in the square-class comparison are free.  The
  quantity to be shown a nonsquare is `Delta * c_0` with `Delta` the Vandermonde square of the roots
  and `c_0` the constant coefficient of the centered equation, that is
  `V^2 * prod_i (x_i - avg)` up to a constant square.  Now the decisive simplification: the
  coefficient field sits inside the field of rational functions in the roots, so it is enough to
  show this is not a square in that **larger** field, where `prod_i (x_i - avg)` is a product of `d`
  pairwise non-proportional linear forms and hence squarefree.  No algebraic independence of the
  centered coefficients is needed, and no Tschirnhaus computation.
- 2026-08-01 — `LinearFormPrime.lean` supplies the missing primality.  A square matrix with a
  two-sided inverse substitutes its row forms for the variables and gives an automorphism of the
  polynomial ring (`matrixAlgEquiv`, built on the corpus's `Matrix.toMvPolynomial` machinery), so
  every row form of an invertible matrix is prime (`prime_toMvPolynomial`).  Applied to the matrix
  that is the identity apart from its zeroth row, whose determinant is `d - 1` by upper
  triangularity, this proves `d * X_0 - sum_j X_j` prime — the linear form cutting out the
  hyperplane on which the zeroth variable equals the average.  Axioms
  `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — **the even case's square-class statement is proved.**  Two modules complete the route
  set out above.
  `AverageProductNonSquare.lean` assembles the nonsquare itself.  The scaled centered coordinates
  `avgForm i = d * X i - sum_j X j` are prime (previous entry), and evaluating at an explicit point
  with pairwise distinct coordinates summing to zero — `balancedPoint`, whose last coordinate
  absorbs the sum of the others — shows the zeroth of them divides neither the Vandermonde square
  nor the remaining forms.  Hence `not_isSquare_vandermondeSq_mul_avgProduct`: the product of the
  discriminant with all the scaled centered coordinates has odd valuation at a prime, so it is not
  a square in the field of rational functions in the roots.  Requires `3 <= d`, which is exactly
  right: for `d = 2` the centered discriminant is `-4 c_0` and the product genuinely is a square.
  `CenteredDiscriminantNonSquare.lean` transfers this to the card's own quantity.  The scaled
  centered coordinate maps to `d` times the centered root, so the product of all of them is `d ^ d`
  times the product of the centered roots, which is the constant coefficient of the centered
  polynomial up to `(-1) ^ d`.  Over the card's algebraically closed field of constants that scalar
  is a square, so `not_exists_sq_disc_mul_centeredConstant`: the discriminant times the constant
  coefficient of the centered polynomial has no square root in the field of rational functions in
  the roots, hence none in any subfield of it — in particular none in the coefficient field.
  Axioms `[propext, Classical.choice, Quot.sound]` throughout.

- 2026-08-01 — `EvenKummerSqrt.lean` and `KummerBaseChangeEvenGenerator.lean` remove the last
  *assumed* input of the even branch.  The square root the even case needs is not extra data: it is
  the half power of the Kummer generator.  `pow_notMem_bot_of_finrank_le` is the reason it stays out
  of the base — a power below the degree landing in the base would be a root of a polynomial of that
  degree, bounding the degree of the extension — and `sq_pow_half` is why it squares into it.  So
  `kummerBaseChangeEvenGenEquiv` states the base change step with the generator, its degree and one
  square-class computation as its only concrete inputs, which is exactly the shape of the card's
  data `(10)`: `M = E_0(p_1)` with `p_1^n = (-1)^n c_0`.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  Next: the instantiation needs the ambient field containing both the splitting field of `(7)` and
  the Kummer extension, and the identification of the card's `E_0 = K(q, c_0, ..., c_{n-1})` with
  the coefficient field of the universal centered polynomial — that identification is the card's
  step `(6)`--`(10)` and is where algebraic independence of the `c_j` is actually needed.

- 2026-08-01 — correction to the previous entry, in the card's favour: **algebraic independence of
  the `c_j` was already proved** — `algebraicIndependent_tailCoeff` in
  `TailCoefficientIndependence.lean`, via the triangular Jacobian rather than the hand computation
  `(9)`.  So step `(a)` of the instantiation is done and the card's `E_0` is already known to be a
  rational function field.
- 2026-08-01 — `TailCoefficientLinearSolve.lean` supplies the *algebraic* triangularity that the
  Jacobian alone does not give, and it comes for free from the same two derivative facts.  The
  derivative of the `i`-th tail coefficient in the `i`-th parameter is `tailLead i`, a multiple of a
  power of the **first** parameter, which no longer involves the `i`-th one; so
  `tailRemainder i := tailCoeff i - tailLead i * X i` has vanishing derivative in the `i`-th
  parameter and in every later one, and in characteristic zero that means those parameters do not
  occur in it (`degreeOf_tailRemainder_eq_zero`, using the corpus's own
  `degreeOf_eq_zero_of_pderiv_eq_zero`).  Hence `tailCoeff_eq`: each tail coefficient is linear in
  the parameter it introduces, with everything else in the earlier parameters — the form that lets
  the parameters be solved for one at a time.  `tailCoeff_zero` is the card's `(8)`:
  `c_0 = p_1^n` up to sign.  Axioms `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — `TailParameterField.lean` proves the field-theoretic half of the card's `(10)`.
  `tailParamField` is the field generated over the constants by the tail coefficients together with
  the first parameter, and `tailParamField_eq_top` says it is everything: `K(p_1, ..., p_n) =
  K(c_0, ..., c_{n-1})(p_1)`.  The induction is exactly the card's triangular solve — the `i`-th
  tail coefficient is `tailLead i * p_{i+1} + tailRemainder i` with `tailLead i` a nonzero power of
  `p_1` and `tailRemainder i` free of `p_{i+1}` and everything after it, so `p_{i+1}` is a quotient
  of elements already known to lie in the field.  The transport step is
  `algebraMap_mem_of_vars_subset`: a polynomial whose variables lie in a set maps into any
  intermediate field containing the images of that set, proved by pushing `Algebra.adjoin` through
  the algebra map.  Axioms `[propext, Classical.choice, Quot.sound]`.
  With `algebraicIndependent_tailCoeff` this settles `(10)` apart from the Kummer relation
  `p_1^n = (-1)^n c_0`, which is `tailCoeff_zero`.

- 2026-08-01 — the deck transformation of the Kummer covering, which is what will give the degree
  `[K(p) : E_0] = n` from below without any irreducibility criterion.  Scaling the `i`-th parameter
  by the `(i+1)`-st power of a scalar rescales the tail polynomial by that scalar **and** rescales
  its variable by the same amount; raising to the power `n - j` and reading the `j`-th coefficient
  multiplies the `j`-th tail coefficient by the scalar to the power `(n - j) + j = n`.  So an
  `n`-th root of unity fixes **every** tail coefficient while multiplying the first parameter by it:
  `varScaleHom_tailCoeff_of_pow_eq_one` and `varScaleHom_X_zero`.
  Two modules: `PolynomialScaleVariable.lean` (`scaleVar`, substituting a scalar multiple of the
  variable, and `coeff_scaleVar`, the coefficient rescaling law — absent from mathlib) and
  `TailScalingAutomorphism.lean` (`varScale`, the automorphism, and the invariance).  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  This replaces the Eisenstein route: `n` distinct automorphisms fixing `E_0` pointwise bound the
  degree from below directly, and no primality of `c_0` in the coefficient ring is needed.

- 2026-08-01 — `TailScalingAction.lean` packages the deck transformations as a group.  The scalings
  compose by multiplying their scalars (`varScaleHom_comp`), giving `varScaleAut : Kˣ →* RingAut`,
  and restricting to the `n`-th roots of unity gives `rootsOfUnityScale`, which fixes every tail
  coefficient (`rootsOfUnityScale_tailCoeff`) and is injective (`rootsOfUnityScale_injective`, from
  the first parameter alone).  Axioms `[propext, Classical.choice, Quot.sound]`.
  One design note worth recording, because it cost a detour: the polynomial ring already carries a
  scalar action of `Kˣ` by multiplication, so declaring a second `MulSemiringAction` of the roots of
  unity on the same type is shadowed by the existing instance and its defining equation is not
  definitional.  The scalings are therefore recorded as a homomorphism into the automorphism group
  rather than as an action instance — which is also the form the fixed-field theorem consumes.
  Next: the fixed field of the image subgroup, Artin's `FixedPoints.finrank_eq_card` for the degree
  `n`, and the sandwich `E_0 <= fixed field <= top` with `[top : E_0] <= n` from `p_1^n in E_0`.

- 2026-08-01 — `TailFixedField.lean`.  The deck transformations act on the rational function field
  in the parameters (`deckGroup`, its image in the automorphism group, with the action extended to
  the fraction field by mathlib's `IsFractionRing.mulSemiringAction` and faithfulness by
  `IsFractionRing.faithfulSMul`), and Artin's theorem gives the degree over the fixed field as the
  order of the group (`finrank_fixedField_deckGroup`).  The tail coefficients lie in that fixed
  field (`algebraMap_tailCoeff_mem_fixedField`; the compatibility `g • algebraMap p =
  algebraMap (g • p)` comes from `smul_distrib_smul` applied at `1`), and the group has order `n`
  once the constants contain a primitive `n`-th root of unity (`card_deckGroup`, via
  `deckGroupEquiv` and `IsPrimitiveRoot.card_rootsOfUnity`) — which the card's algebraically closed
  `K` supplies.  Axioms `[propext, Classical.choice, Quot.sound]`.
  So `E_0` sits inside a subfield of index exactly `n`.  What closes the degree is the reverse
  bound `[top : E_0] <= n`, which is `p_1^n = c_0 in E_0` plus `top = E_0(p_1)` — both already
  proved (`tailCoeff_zero`, `tailParamField_eq_top`).

- 2026-08-01 — two modules bring the two sides of the degree sandwich into the same frame.
  `TailCoefficientFixedField.lean` reconciles the subfield and intermediate-field views: the deck
  transformations fix the constants (they are algebra maps, `deck_smul_C`), so the fixed field is an
  intermediate field over the constants (`deckFixedField`), and the field generated by the tail
  coefficients lies inside it (`tailCoeffField_le_deckFixedField`).  The Artin degree transports
  without friction — `finrank_deckFixedField` is the same statement in the new frame, and the
  carrier identification is definitional.
  `KummerDegreeBound.lean` supplies the other side in general form: an element whose `n`-th power
  lies in the base generates an extension of degree at most `n`
  (`finrank_adjoin_le_of_pow_mem`), because it is a root of a monic polynomial of that degree.
  Axioms `[propext, Classical.choice, Quot.sound]`.
  Both ends of the sandwich are now available: `E_0 <= Fix` with `[top : Fix] = n`, and
  `top = E_0(p_1)` with `p_1^n in E_0` giving `[top : E_0] <= n`.  What remains is the tower
  identity itself, which forces `[top : E_0] = n` and `Fix = E_0`.

- 2026-08-01 — `TailCoefficientDegree.lean` closes the upper half of the sandwich.
  `tailCoeffField_adjoin_eq_top`: the parameter field is generated over the coefficient field by the
  first parameter alone — the statement `top = E_0(p_1)` of the card's `(10)`, obtained from
  `tailParamField_eq_top` by moving the base with `restrictScalars`.  Since `p_1^n` is the first
  tail coefficient (`pow_algebraMap_X_zero`), the radical-degree bound gives
  `finrank_tailCoeffField_le`: the degree is at most `n`, and `finiteDimensional_tailCoeffField`
  records that the extension is finite.  Axioms `[propext, Classical.choice, Quot.sound]`.
  With `finrank_deckFixedField` and `card_deckGroup` this leaves only the tower identity
  `[top : E_0] = [Fix : E_0] * [top : Fix]`, which forces `[top : E_0] = n` and `Fix = E_0`.

- 2026-08-01 — `TailCoefficientTower.lean` closes the sandwich and with it the card's `(10)`.
  The fixed field seen over the coefficient field (`deckFixedOverCoeff`) has trivial degree
  (`finrank_deckFixedOverCoeff_eq_one`), because the tower identity multiplies it by the Artin
  degree `n` and the result is bounded by `n`.  Hence `tailCoeffField_eq_deckFixedField` — the
  coefficient field **is** the fixed field of the deck transformations — and
  `finrank_tailCoeffField`: the parameter field has degree exactly `n` over the coefficient field.
  Axioms `[propext, Classical.choice, Quot.sound]`.
  Step `(10)` is now complete in Lean: the `c_j` are algebraically independent, the parameter field
  is `E_0(p_1)`, `p_1^n` is `c_0`, the degree is exactly `n`, and `E_0` is intrinsically
  characterised as the fixed field of the `n`-th roots of unity acting by
  `p_i |-> zeta^i p_i`.

- 2026-08-01 — `TailParameterChange.lean` packages step `(10)` as one theorem,
  `tailParameterChange`, whose only hypotheses are `0 < n` and a primitive `n`-th root of unity in
  the constants — both supplied by the card's algebraically closed `K`.  It asserts, in one
  conjunction: the tail coefficients are algebraically independent; the parameter field is generated
  over them by the first parameter; that parameter is an `n`-th root of the first tail coefficient;
  and the degree is exactly `n`.  The finiteness of the deck group no longer has to be assumed —
  `finite_deckGroup` derives it from `Nat.card` being `n`, which is nonzero.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  Remaining for the card: the ambient field holding the splitting field of `(7)` together with the
  Kummer extension, and the application of `kummerBaseChangeEvenGenEquiv` — the mathematics of both
  branches is proved, what is left is construction.

- 2026-08-01 — `PolynomialBaseChangeEven.lean` supplies `polyBaseChangeEvenEquiv`, the missing
  sibling of `polyBaseChangeOddEquiv` and the card's `(3)` in the shape the card names: inside the
  splitting field of the product of the centered polynomial with `X^n - c_0`, the Galois group of
  the centered polynomial survives enlarging the base by the roots of the second factor.  Where the
  odd case argues that a field of odd degree contains no square root of a base element, the even
  case supplies instead the generator of the second factor's root field, its degree, and the square
  class of the product of the two radicands — the square root being the generator's half power, not
  extra data.  Axioms `[propext, Classical.choice, Quot.sound]`.
  Both branches of `(3)` are now available at the polynomial level with no assumed inputs beyond
  the situation's own data.

- 2026-08-01 — `CenteredPolynomialOverCoefficients.lean`.  The base change step takes a polynomial
  over the **base** field, whereas the corpus's centered polynomial `centeredMonicL` lives over the
  field its roots generate.  `centeredMonicE` is the same polynomial over its own coefficient field:
  the leading power plus the sum of its lower coefficients, each of which is by definition a
  generator of that field.  `map_centeredMonicE` identifies its image with `centeredMonicL` (via the
  monic decomposition `Monic.as_sum` and `coeff_centeredMonicL_lt`), and monicity and degree
  transfer back along the injective algebra map.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  This is the first of the two inputs `polyBaseChangeEvenEquiv` needs from the model; the second is
  the identification of `rootField` of this polynomial with the whole centered field, for which
  `adjoin_centeredRootIn_over_coeff_eq_top` and `exists_centeredRootIn_eq` are already proved.

- 2026-08-01 — `CenteredRootFieldTop.lean` supplies the `phi` argument of the base change step.
  `rootSet_centeredMonicE`: the roots of the centered polynomial in the centered field are exactly
  the centered roots — one direction from `eval_centeredMonicL_root`, the other by factoring the
  evaluation.  With `adjoin_centeredRootIn_over_coeff_eq_top` this gives
  `rootField_centeredMonicE_eq_top`, and transporting `centeredGaloisEquiv` along it gives
  `centeredRootFieldPermEquiv`: the automorphism group of the root field of the centered polynomial
  over its coefficient field is the symmetric group on `Fin d`.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  A note for whoever extends this: building the identification as
  `equivOfEq |>.trans topEquiv` in term mode does not elaborate — it exhausts two million
  heartbeats at `whnf`.  Rewriting the *type* with `rw [rootField_centeredMonicE_eq_top]` and
  closing with `exact IntermediateField.topEquiv` costs nothing.

- 2026-08-01 — `IntersectionNormal.lean` starts the group-side hypothesis `hnorm`.  An automorphism
  of the ambient field carries each of two normal subextensions to itself, hence carries their
  intersection to itself (`map_inf_of_algEquiv`), so `normal_inf`: the intersection of two normal
  subextensions is normal.  Axioms `[propext, Classical.choice, Quot.sound]`.
  The route to `hnorm` from here is mathlib's instance
  `fixingSubgroup_normal_of_isGalois`, which needs the intersection **read inside the first factor**
  to be Galois.  That is the remaining step: an `F`-algebra equivalence
  `comap E.val (E ⊓ M) ≃ₐ[F] (E ⊓ M)`, which is subtype bookkeeping — mathlib has no
  `comapAlgEquiv` for intermediate fields, so it has to be written out.

- 2026-08-01 — `IntersectionFixingSubgroup.lean` discharges `hnorm` outright.  The corpus already
  had the missing bookkeeping: `comapValEquiv` in `IntermediateFieldComap.lean` is exactly the
  `F`-algebra equivalence `comap E.val K ≃ₐ[F] K` for `K ≤ E`, built earlier for a degree
  computation.  Transporting `normal_inf` along it gives `normal_comap_inf`, and mathlib's
  `fixingSubgroup_normal_of_isGalois` then yields `fixingSubgroup_comap_inf_normal`: the subgroup of
  the first factor's automorphism group fixing the intersection is normal, from normality of the two
  factors alone.  Axioms `[propext, Classical.choice, Quot.sound]`.
  So of the three group-side inputs of the base change step, `hnorm` is now proved from structure;
  `habel` follows from `commute_quotient_of_le_abelian` with the Kummer factor, and `hcyc` from
  `commute_gal_XPowSubC`.

- 2026-08-01 — `IntersectionAbelian.lean` discharges `habel`.  `commute_gal_inf`: restriction from a
  normal subextension to a normal subextension of it is surjective, so the intersection of two
  normal subextensions inherits a commutative automorphism group from the second factor alone.
  `commute_quotient_comap_inf` then reads the intersection inside the first factor — through the
  Galois correspondence `IsGalois.fixedField_fixingSubgroup` and the corpus's `comapValEquiv` — and
  passes to the quotient, which is exactly the base change step's abelian-quotient hypothesis.
  Axioms `[propext, Classical.choice, Quot.sound]`.
  Two instance traps worth recording, both costing a build each.  Introducing
  `Algebra (E ⊓ M) M` by hand and then asking for the scalar tower fails in the **kernel**: the
  tower found refers to `extendScalars`, not to the hand-made algebra, so the two do not match.
  Passing `extendScalars` itself as the larger field avoids the diamond, at the price of one
  `inferInstanceAs` for its normality.  And the quotient's multiplication needs the normality
  instance already at statement-elaboration time, so it must be an explicit hypothesis of the
  theorem, not a `haveI` in the proof — which is why the corpus's own base change steps take
  `hnorm` explicitly.
  All three group-side inputs are now proved: `hnorm`, `habel`, and `hcyc` from
  `commute_gal_XPowSubC`.

- 2026-08-01 — `PolynomialBaseChangeAssembled.lean`: `polyBaseChangeEvenAssembledEquiv`, the card's
  `(3)` for even `n` with **every** group-side hypothesis discharged.  Normality of the fixing
  subgroup comes from normality of the two root fields; the abelian quotient comes from cyclicity of
  the second factor's automorphism group (cyclic gives commutative, so `habel` need not be assumed
  separately); and normality of the ambient field is derived from its being the splitting field of
  the product.  What the caller supplies is exactly the card's own data: the symmetric-group
  identification for the first factor, cyclicity of the second, the generator with its degree, the
  discriminant square root, and the square-class computation.  Axioms
  `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — `polyBaseChangeOddAssembledEquiv` added alongside the even one, so both branches of
  `(3)` now exist in fully-assembled form.  The odd branch needs no square-class computation at all:
  cyclicity of the second factor supplies the abelian quotient, normality of the two root fields
  supplies the normal fixing subgroup, and odd degree excludes the square root.  Its whole input is
  the symmetric-group identification, cyclicity, and the parity of the degree.  Axioms
  `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — `CenteredSplittingField.lean` removes the obstacle to instantiating the assembled
  base change.  That step fixes an ambient field in which the product of the two factors splits, and
  the root field of the first factor computed *there* is not literally the corpus's centered field —
  only isomorphic to it.  `isSplittingField_centeredMonicE` supplies the bridge: the centered field
  **is** a splitting field of the centered polynomial over its coefficient field, since the
  polynomial factors into linear terms there (`splits_centeredMonicE`) and its roots generate it
  (`adjoin_rootSet_centeredMonicE`, the subalgebra form obtained from the intermediate-field form
  through `adjoin_toSubalgebra_of_isAlgebraic`).  Any two splitting fields being isomorphic over the
  base, the symmetric-group identification proved in the model transports to whatever ambient the
  base change step picks.  Axioms `[propext, Classical.choice, Quot.sound]`.
  Note for this toolchain: `Polynomial.Splits` here is the one-argument predicate on a polynomial,
  not the classical `Splits (algebraMap ..) f`; the ring map appears as an explicit `map`.

- 2026-08-01 — `RootFieldTransport.lean` completes the bridge started in the previous entry.
  `isSplittingField_rootField`: the field generated by the roots inside any ambient where the
  polynomial splits is itself a splitting field.  `splittingFieldAutEquiv`: any two splitting fields
  have the same automorphism group, through `IsSplittingField.algEquiv` and `AlgEquiv.autCongr`.
  `rootFieldPermEquiv` combines them: a permutation identification proved for one splitting field
  transports to the root field of any other ambient.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  With `isSplittingField_centeredMonicE`, the symmetric-group identification `centeredGaloisEquiv`
  proved in the corpus's model is therefore available as the `phi` argument of the assembled base
  change, for whatever ambient field that step fixes.  Every input of both branches of `(3)` is now
  proved and in the right frame.

- 2026-08-01 — `KummerCyclic.lean` supplies `hcyc`, which had been an assumed input of both assembled
  branches and was **not** among the facts already proved — the corpus had only commutativity
  (`commute_gal_XPowSubC`), not cyclicity, and the assembled steps need the latter.
  `irreducible_X_pow_sub_C_of_finrank`: if the `n`-th power of an element lies in the base and the
  extension it generates has degree `n`, the radical polynomial is irreducible, because the minimal
  polynomial divides it and has the same degree, and both are monic.  This is where the card's
  degree computation `finrank_tailCoeffField` earns its keep.  `isCyclic_rootField_X_pow_sub_C` then
  applies mathlib's `isCyclic_of_isSplittingField_X_pow_sub_C` through the root-field splitting
  identification.  Axioms `[propext, Classical.choice, Quot.sound]`.
  With this, no input of either assembled branch of `(3)` is assumed rather than proved.

- 2026-08-01 — `RadicalBaseChangeCapstone.lean` derives the eight typeclass hypotheses of the
  assembled base change from one fact: the ambient is a splitting field of the product.  Both
  factors split there (`splits_of_splits_mul_left`/`_right`), so each root field is a splitting
  field of its factor (`isSplittingField_rootField_left`/`_right`), hence normal, finite dimensional
  and — in characteristic zero — Galois over the base; and the whole field, being Galois over the
  base, is Galois over either root field (`isGalois_top_over_rootField`).  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  Nothing about the two factors is used beyond their being nonzero, so this applies verbatim to the
  card's pair: the centered polynomial and `X^n - c_0`.

- 2026-08-01 — **`RadicalBaseChangeEvenCapstone.lean`: the card's `(3)` is now one theorem.**
  `radicalBaseChangeEven` takes only mathematical data — the first factor and a symmetric-group
  identification of its Galois group in **any** model splitting field, an even exponent with a
  primitive root of unity in the base, a generator of the radical extension with its degree, a
  square root of a base element inside the first factor's root field, and the two radicands lying in
  different square classes — and returns the automorphism group of the ambient over the radical
  extension, still the full symmetric group.
  Everything else is derived inside: the eight typeclass hypotheses from the ambient being a
  splitting field of the product; the permutation identification transported from the model; the
  irreducibility of `X^(2m) - c` from the degree of its generator; and the cyclicity of its Galois
  group from that irreducibility and the root of unity.  Axioms
  `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — `radicalBaseChangeOdd` added beside it, so both branches of `(3)` are now single
  theorems taking only mathematical data.  The odd branch drops the square root and the square-class
  computation entirely; it still needs the generator and its degree, but only to establish
  irreducibility and hence cyclicity, and the odd degree of the radical extension does the rest.
  Axioms `[propext, Classical.choice, Quot.sound]`.
  The card's `(3)` is proved in the abstract.  Every hypothesis of both capstones is either the
  card's own data or a theorem proved above.

- 2026-08-01 — `VandermondeFixed.lean` produces the capstone's `beta` and `e` from the roots.  An
  automorphism permutes the roots, and permuting the arguments of the Vandermonde product only
  changes its sign (`vandermondeProd_comp`), so the square is fixed by every automorphism
  (`vandermondeSq_fixed`); in a Galois extension that means it comes from the base field
  (`exists_algebraMap_vandermondeSq`, through the corpus's `exists_algebraMap_of_forall_fixed`).
  So the discriminant **is** a base-field element, which is what the capstone requires of `e`, and
  the Vandermonde product itself is the `beta` whose square it is.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  Note that the capstone's `hclass` is a statement in the base field alone, so no transport of the
  square-class theorem across ambient fields is needed after all — a square root in the base field
  is in particular one in the root field, which is where
  `not_exists_sq_disc_mul_centeredConstant` already excludes it.

- 2026-08-01 — `vandermondeProd_notMem_bot` completes the `beta` data.  An automorphism acting on the
  roots by an odd permutation sends the Vandermonde product to its negative; if the product were in
  the base field it would also be fixed, forcing twice it to vanish and hence, in characteristic
  zero, the product itself — contradicting distinctness of the roots.  So the discriminant square
  root is genuinely outside the base field, which is the capstone's `hbetabot`.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  All three components of `beta` are now available from the roots alone: it lies in the first
  factor's root field by construction, its square is a base-field element
  (`exists_algebraMap_vandermondeSq`), and it is not itself in the base field.  For the card's
  centered polynomial the odd automorphism exists because the Galois group is the **full** symmetric
  group, which for degree at least two contains a transposition.

- 2026-08-01 — `RadicalRootExists.lean`: `exists_pow_eq_mem_rootField` produces the Kummer generator
  from the situation.  Where the radical polynomial splits it has a root, that root lies in the
  field its roots generate, and being a root means precisely that its `n`-th power is the constant.
  So `alpha` and `halphapow` are not inputs of the capstone in any real sense — only the **degree**
  hypothesis `n <= finrank F F(alpha)` is genuine data, and it must be, since for a constant that is
  already an `n`-th power the conclusion is false.  On the card that degree is exactly what
  `finrank_tailCoeffField` computes.  Axioms `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — two coercion lemmas finish the `beta` package.  `vandermondeProd_mem`: the Vandermonde
  product of members of a subfield lies in it, so `beta` is in the first factor's root field for
  free.  `notMem_bot_of_notMem_bot_coe`: an element of a subfield that is outside the base **of that
  subfield** is outside the base of the ambient, which is what carries
  `vandermondeProd_notMem_bot` — proved where the Galois action lives, inside the root field — up to
  the ambient field where the capstone states it.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  Every hypothesis of the even capstone is now either derived inside it or supplied by a theorem
  above; the only genuine data are the two polynomials, the model identification, the degree of the
  radical generator, and the square class.

- 2026-08-01 — `RadicalBaseChangeFromRoots.lean`: `radicalBaseChangeEvenFromRoots` folds in
  everything the previous four entries derived.  Its inputs are now the two polynomials, the
  symmetric-group identification in a model splitting field, a primitive root of unity, the roots of
  the first factor with their injectivity, the fact that automorphisms permute them, one automorphism
  acting oddly, the degree of the radical generator, and the square class.  The discriminant square
  root and the Kummer generator are both constructed inside.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  A Lean note: extracting the generator and the discriminant's base-field square from their
  existence statements cannot be done with `obtain`, because the result is data (an equivalence of
  groups) and a `Prop` may not be eliminated into a type.  `Classical.choose` with `choose_spec`,
  and `.1`/`.2` projections rather than destructuring, is the way through.

- 2026-08-01 — `AutPermutesRoots.lean` derives the permutation hypothesis of the previous entry.
  An automorphism over the base commutes with evaluating a polynomial with base coefficients
  (`aeval_algEquiv_eq_zero`), so it maps the root set into itself (`mem_rootSet_algEquiv`); and if a
  finite family enumerates the roots injectively, the induced map on indices is injective, hence a
  permutation (`exists_perm_of_root_enumeration`).  So `hvperm` is not data either — it follows from
  the family enumerating the roots.  Axioms `[propext, Classical.choice, Quot.sound]`.
  Of the from-roots capstone's inputs, what is left that is genuinely data: the two polynomials, the
  model identification, an injective enumeration of the first factor's roots, one automorphism
  acting oddly, the degree of the radical generator, and the square class.

- 2026-08-01 — `exists_odd_aut_of_surjective` removes the last piece of `beta` data.  If the Galois
  action on the roots is surjective onto the permutations — which for the card is how
  `centeredGaloisEquiv` is built, out of `centeredRootPerm` — then with at least two roots a
  transposition is realised, and a transposition is odd.  So the odd automorphism the discriminant
  argument needs is a consequence of full symmetric monodromy rather than an extra assumption.
  Axioms `[propext, Classical.choice, Quot.sound]`.
  The genuine data of the from-roots capstone is now: the two polynomials, the model identification,
  an injective enumeration of the first factor's roots with the surjectivity of the action on them,
  the degree of the radical generator, and the square class.

- 2026-08-01 — `radicalBaseChangeEvenFromEnumeration` is the minimal form of the card's `(3)`.  Its
  hypotheses are: the two polynomials nonzero, the ambient a splitting field of their product, a
  symmetric-group identification in a model splitting field, a primitive root of unity, an injective
  enumeration of the first factor's roots that hits exactly the root set, surjectivity of the Galois
  action on those roots, the degree of the radical generator, and the square class.  Nothing else.
  Axioms `[propext, Classical.choice, Quot.sound]`.
  Every one of these is a proved theorem for the card's centered polynomial: `centeredMonicE` with
  `X^n - c_0`; `isSplittingField_centeredMonicE`; `centeredRootFieldPermEquiv`; the algebraically
  closed constants; `centeredRootIn` with `centeredRootIn_injective` and `rootSet_centeredMonicE`;
  `centeredRootPerm` for surjectivity; `finrank_tailCoeffField`; and
  `not_exists_sq_disc_mul_centeredConstant`.

- 2026-08-01 — `RootEnumerationTransport.lean` closes the last frame mismatch between the model and
  the base change.  The capstone wants the roots enumerated inside the **ambient's** root field,
  while the corpus proves everything inside `centeredField`.  An isomorphism over the base matches
  the two root sets (`mem_rootSet_algEquiv_iff`), so an enumeration pulls back
  (`rootEnumeration_algEquiv`) and a surjective action pushes across by conjugation
  (`rootAction_surjective_algEquiv`).  Axioms `[propext, Classical.choice, Quot.sound]`.
  The isomorphism itself is `splittingFieldAutEquiv`'s ingredient: both fields are splitting fields
  of the centered polynomial over the coefficient field, by `isSplittingField_centeredMonicE` and
  `isSplittingField_rootField`.

- 2026-08-01 — **`RadicalBaseChangeFromModel.lean`: the abstract half of the card is finished.**
  `radicalBaseChangeEvenFromModel` proves `(3)` with **all** root data taken in a model splitting
  field of the first factor — the enumeration, the surjectivity of the Galois action, and the
  Vandermonde product — since the isomorphism with the root field inside the ambient carries each
  across (`map_vandermondeProd_ringHom` for the last).  Its hypotheses are now exactly the facts the
  corpus proves about the centered generic polynomial, stated in the frame the corpus proves them
  in.  Axioms `[propext, Classical.choice, Quot.sound]`.
  The card's `(3)` therefore holds for any first factor whose Galois group over its coefficient
  field is symmetric, any even radical extension of that coefficient field whose generator has full
  degree, and any square-class separation between the discriminant and the radicand.

- 2026-08-01 — `PrimitiveRootTransport.lean` supplies the capstone's root-of-unity hypothesis from
  the card's own assumption on the constants.  An algebraically closed field of characteristic zero
  has a primitive root of every positive order (through mathlib's `HasEnoughRootsOfUnity`), and a
  primitive root survives an injective ring map, so every extension of such a field has them:
  `primitiveRoots_nonempty_of_algebra`.  The card's `K` is algebraically closed, and the coefficient
  field is an extension of it, so `hzeta` is discharged.  Axioms
  `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — `CenteredPermRootAction.lean` supplies the surjectivity of the Galois action on the
  centered roots.  The corpus builds `centeredGaloisEquiv` out of `centeredRootPerm`, which reads a
  permutation **off** an automorphism; the capstone needs the other direction, an automorphism
  realising a given permutation.  That is `centeredPermAlgEquiv`, and
  `centeredPermAlgEquiv_centeredRootIn` says it moves the roots by exactly that permutation — one
  coercion away from `smul_centeredRoot`.  Hence `exists_centeredAut_perm`.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  Every hypothesis of `radicalBaseChangeEvenFromModel` now has a named proof for the centered
  generic polynomial.

- 2026-08-01 — **`CenteredRadicalBaseChange.lean`: the card's `(3)` instantiated on the corpus's own
  centered generic polynomial.**  `centeredRadicalBaseChange` states: over an algebraically closed
  field of characteristic zero, for degree at least two, the automorphism group of the splitting
  field of `centeredMonicE * (X^(2m) - c)` over the root field of the second factor is the full
  symmetric group on `Fin d`.  Every structural input is discharged from the corpus — the
  symmetric-group identification, the splitting-field property, the root enumeration, the surjective
  action, the roots of unity — and the two hypotheses left to the caller are exactly the two facts
  specific to the equation: the degree of the radical generator and the square class of the product
  of the radicands.  Axioms `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — `CenteredDiscriminantIdentification.lean` matches the two square-class statements'
  vocabularies.  `coe_vandermondeProd_centeredRootIn`: the Vandermonde product of the **centered**
  roots, read in the rational function field, is the Vandermonde polynomial — because translating a
  family does not change its Vandermonde product (`vandermondeProd_sub_const`), so the centered
  roots and the generic roots give the same value.  `coe_centeredConstant` names the constant
  coefficient inside the coefficient field and identifies its image.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  So the discriminant square root that the base change compares against the constant coefficient is
  literally the object `not_exists_sq_disc_mul_centeredConstant` speaks about, and the two are now
  in the same language.

- 2026-08-01 — `CenteredSquareClassInput.lean`: `no_sqrt_centered_disc_mul_constant` is the
  square-class hypothesis of the base change step, for the centered generic polynomial, in the exact
  form that step consumes.  A square root in the coefficient field of the discriminant times the
  constant coefficient would, read in the rational function field, be a square root there — which
  `not_exists_sq_disc_mul_centeredConstant` excludes.  The two coercion identifications of the
  previous entry are what make the two statements the same statement.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  So the second of the two remaining inputs of `centeredRadicalBaseChange` is now supplied; only the
  degree of the radical generator is left, and it is `finrank_tailCoeffField` once the radicand is
  fixed to the constant coefficient.

- 2026-08-01 — a correction to the plan, found by trying to discharge the last input.  The degree
  hypothesis of `centeredRadicalBaseChange` amounts to `X^n - c_0` being irreducible over the
  **centered generic polynomial's** coefficient field, and that needs the *centered* coefficients to
  be algebraically independent.  That is **not** what `algebraicIndependent_tailCoeff` proves — that
  theorem is about the tail coefficients of the parameter model, a different family — so this is a
  genuine missing piece rather than bookkeeping.  Earlier entries that spoke of the degree as
  "already computed" were describing the parameter model, where it is; here it is not yet available.
  Route: the centered coefficients are the elementary symmetric functions of roots summing to zero,
  so parametrise that hyperplane by the first `m` coordinates with the last minus their sum, and
  show the images of `e_2, ..., e_{m+1}` are algebraically independent.
- 2026-08-01 — `SumZeroParametrisation.lean` lays the first stone of that route: `sumZeroCoord` and
  the algebra map `sumZeroRestrict` reading a polynomial on the hyperplane, with
  `sum_sumZeroCoord` and `sumZeroRestrict_esymm_one` — the parametrised coordinates sum to zero, so
  the first elementary symmetric function restricts to zero, which is exactly what makes the
  remaining ones the coefficients of a centered polynomial.  Axioms
  `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — a better route to the last input, which sidesteps the missing centered independence
  entirely.  The abstract base change works for **any** first factor with symmetric Galois group
  over its coefficient field, so it can be run with the **uncentered** generic polynomial, whose
  coefficient field is already known to be a rational function field in the elementary symmetric
  functions (`esymmFracEmbedding`, `esymmField_le_esymmRangeField`).  There the radicand is the top
  elementary symmetric function, which corresponds to a **variable** of the model, and irreducibility
  of `X^n - c` follows from mathlib's criterion once the radicand is known not to be a proper power.
  `PrimePowerClass.lean` proves exactly that: `not_pow_eq_of_prime` — a prime of a unique
  factorisation domain is not a `p`-th power in the fraction field, since a reduced fraction whose
  `p`-th power is the prime would have the prime dividing numerator and denominator alike — and its
  specialisation `not_pow_eq_X` for a variable.  Axioms `[propext, Classical.choice, Quot.sound]`.
  The square-class input for this route is also already proved:
  `no_sqrt_disc_mul_esymmTop_of_mem_symmetricPartField`.

- 2026-08-01 — `EisensteinRadical.lean` settles the irreducibility for **every** exponent, which
  matters because mathlib's radical-irreducibility criteria stop at odd `n` and prime powers — its
  own source file carries a "TODO: criteria for even `n`".  For a prime radicand no general
  criterion is needed: `X ^ n - q` satisfies Eisenstein at the ideal generated by `q` (unit leading
  coefficient, every lower coefficient a multiple of `q`, constant term not a multiple of `q ^ 2`),
  so it is irreducible over the domain, and being monic it stays irreducible over the fraction
  field by Gauss.  `irreducible_X_pow_sub_C_of_prime`.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  This supersedes the previous entry's plan of feeding `not_pow_eq_of_prime` into mathlib's
  criterion — that lemma stands on its own, but the Eisenstein route needs nothing from it and
  covers the even case the criterion does not reach.

- 2026-08-01 — `RadicalDegreeExact.lean` turns irreducibility into the capstone's degree hypothesis.
  An irreducible monic polynomial vanishing at a root **is** its minimal polynomial, so
  `finrank_adjoin_of_irreducible`: the extension a root of an irreducible `X ^ n - c` generates has
  degree exactly `n`; and `le_finrank_adjoin_of_irreducible` is that in the inequality form the base
  change step takes.  Axioms `[propext, Classical.choice, Quot.sound]`.
  Chained with `irreducible_X_pow_sub_C_of_prime`, the degree input is now available for **any**
  prime radicand — in particular for a variable of a polynomial ring, which is what the top
  elementary symmetric function becomes under `esymmFracEmbedding`.

- 2026-08-01 — `EsymmRangeField.lean` upgrades the model embedding to an identification.  Earlier
  only one inclusion was proved, that the coefficient field lies in the image; the reverse follows
  because a polynomial in the elementary symmetric functions lies in the field they generate
  (`esymmEmbedding_mem_esymmField`, by induction on the polynomial) and every element of the
  fraction field is a quotient of two of them.  So `esymmRangeField_eq_esymmField`: the coefficient
  field of the generic polynomial **is** the image of the rational function field in which the top
  elementary symmetric function is a variable.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  With `irreducible_X_pow_sub_C_of_prime` this is what makes the radicand prime, and hence the
  degree available, for the uncentered instantiation.

- 2026-08-01 — `EsymmFieldEquiv.lean`: `esymmFieldEquiv` is the ring isomorphism between the rational
  function field of the model and the coefficient field of the generic polynomial, built from the
  injectivity of the model embedding and the range identification of the previous entry.
  `esymmFieldEquiv_X` records that a variable corresponds to the matching elementary symmetric
  function.  Axioms `[propext, Classical.choice, Quot.sound]`.
  Along this isomorphism, primality of the top variable — and hence irreducibility of
  `X ^ n - (top elementary symmetric function)` by `irreducible_X_pow_sub_C_of_prime` — becomes a
  statement about the constant coefficient of the generic polynomial, which is the degree input of
  the base change.

- 2026-08-01 — `IrreducibleRadicalTransport.lean`: `irreducible_X_pow_sub_C_map` carries
  irreducibility of a radical polynomial along an isomorphism of the coefficient rings, through
  `Polynomial.mapEquiv` and `MulEquiv.irreducible_iff`.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  The uncentered chain is now closed as a sequence of named theorems: the top variable is prime;
  `X ^ n` minus a prime is irreducible over the fraction field for **every** exponent
  (`irreducible_X_pow_sub_C_of_prime`); this transports to the coefficient field along
  `esymmFieldEquiv` (`irreducible_X_pow_sub_C_map`); irreducibility gives the degree exactly
  (`finrank_adjoin_of_irreducible`); and the square class is
  `no_sqrt_disc_mul_esymmTop_of_mem_symmetricPartField`.

- 2026-08-01 — `EsymmRadicalIrreducible.lean` assembles the degree input for the uncentered route
  into two named theorems.  `irreducible_X_pow_sub_C_esymmCoeff`: the radical polynomial over an
  elementary symmetric function is irreducible at **every** exponent — the function is a variable of
  the model, hence prime, and Eisenstein plus Gauss applies, then the isomorphism carries it back.
  `finrank_adjoin_esymmCoeff_root`: therefore a root of it generates an extension of the coefficient
  field of exactly that degree.  Axioms `[propext, Classical.choice, Quot.sound]`.
  That is the degree hypothesis of the base change step, proved outright for the uncentered generic
  polynomial rather than assumed.

- 2026-08-01 — `SymmetricPartEsymmBridge.lean` reconciles the two descriptions of the coefficient
  field.  The generic polynomial is written over the **symmetric part**, while the irreducibility
  work is over the field the elementary symmetric functions **generate**; these are the same
  intermediate field (`symmetricPartField_eq_esymmField`), so
  `symmetricPartEquivEsymmField` is a ring isomorphism of the carriers, and the irreducibility and
  degree statements transport: `irreducible_X_pow_sub_C_esymmCoeffSymm`,
  `finrank_adjoin_esymmCoeffSymm_root`.  Axioms `[propext, Classical.choice, Quot.sound]`.
  Building the isomorphism by rewriting the **type** with the field equality, rather than composing
  `equivOfEq` in term mode, again avoided the elaboration blow-up noted earlier for
  `rootField_centeredMonicE_eq_top`.

- 2026-08-01 — `GenericRootSet.lean`: `rootSet_genericMonic` identifies the root set of the generic
  polynomial in the rational function field with the set of generic roots.  One inclusion was
  already in the corpus (`genericRoot_mem_rootSet`); the other comes from factoring the evaluation
  of the product of linear factors, the same argument as `rootSet_centeredMonicE`.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  This is the root enumeration the base change step asks of the first factor, for the uncentered
  model: injective by `genericRoot_injective`, exhaustive by this theorem, and with surjective
  action by `smul_genericRoot`.

- 2026-08-01 — `GenericPermRootAction.lean`: `exists_genericAut_perm` gives the surjectivity of the
  Galois action on the generic roots, from `symmetricGaloisEquiv_apply` and `smul_genericRoot` —
  the automorphism attached to a permutation moves the roots by that permutation, since the action
  on the rational function field permutes the variables.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  With this, every hypothesis of `radicalBaseChangeEvenFromModel` has a named proof for the
  **uncentered** generic polynomial: `genericMonic_ne_zero`; `isSplittingField_genericMonic`;
  `symmetricGaloisEquiv`; `primitiveRoots_nonempty_of_algebra`; `genericRoot` with
  `genericRoot_injective` and `rootSet_genericMonic`; `exists_genericAut_perm`;
  `finrank_adjoin_esymmCoeffSymm_root`; and
  `no_sqrt_disc_mul_esymmTop_of_mem_symmetricPartField`.

- 2026-08-01 — attempted the uncentered call and hit an **instance diamond**, diagnosed but not yet
  resolved.  The generic polynomial is written over `symmetricPart` (a `Subfield`) while the
  coefficient-field machinery is over `symmetricPartField` (an `IntermediateField` with the same
  carrier).  Casting the polynomial across is fine — the carriers are definitionally equal, so
  `genericMonicField := genericMonic` typechecks — but the two views carry **different**
  `Algebra (coefficient field) (SymmetricRationalField)` instances, so an
  `IsSplittingField` proved for one is not accepted where the other is expected, even when supplied
  explicitly by `letI`.  Instance search is up to reducible defeq and does not see through the
  structure projection.
  The fix is to state the corpus's generic-polynomial splitting data over `symmetricPartField` from
  the start, rather than casting after the fact — that is, a `symmetricPartField`-based counterpart
  of `genericMonic`, `splits_genericMonic`, `adjoin_rootSet_genericMonic` and
  `isSplittingField_genericMonic`.  Nothing mathematical is missing; this is a coherence problem
  between two presentations of one field.
  The attempted module was removed rather than left non-building in the shared tree.

- 2026-08-01 — first step of the fix for the instance diamond, taking the other side of the choice:
  keep everything over `symmetricPart`, where the generic polynomial and its splitting field already
  live, and supply the missing inputs there instead of casting the polynomial the other way.
  `SymmetricPartConstants.lean` provides the piece that was only available on the
  `symmetricPartField` side: `constToSymmetricPart`, the embedding of the constants into the
  symmetric part (a constant is a symmetric rational function), and
  `primitiveRoots_nonempty_symmetricPart`, so the roots-of-unity hypothesis is available over
  `symmetricPart` without needing a `K`-algebra instance on it.  Axioms
  `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — `SymmetricPartRadical.lean` confirms the diagnosis of the diamond precisely.  The
  **element** and the **irreducibility** transfer to `symmetricPart` by a plain definitional cast —
  `esymmCoeffPart` and `irreducible_X_pow_sub_C_esymmCoeffPart` build with no coercion at all — so
  the two carriers really are interchangeable for statements that do not force an instance search.
  What does not transfer cheaply is the degree statement: elaborating
  `IntermediateField.adjoin (symmetricPart K d) {alpha}` exhausts two million heartbeats at `whnf`,
  because the base is a subtype of a subtype and the adjoin instances unfold through both.  That
  theorem was left out rather than papered over; the general
  `finrank_adjoin_of_irreducible` is unaffected and can be applied at the call site where the
  ambient field is concrete.  Axioms `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — **`GenericRadicalBaseChange.lean`: the card's `(3)` instantiated, with the diamond
  resolved.**  `genericRadicalBaseChange` states: over an algebraically closed field of
  characteristic zero, for degree at least two, the automorphism group of the splitting field of
  `genericMonic * (X ^ (2m) - c)` over the root field of the second factor is the full symmetric
  group on `Fin d`, where `c` is an elementary symmetric function.
  Keeping everything over `symmetricPart` — rather than casting the polynomial onto the intermediate
  field — is what makes it go through: the roots-of-unity input was rebuilt there
  (`primitiveRoots_nonempty_symmetricPart`), the irreducibility transferred by definitional cast
  (`irreducible_X_pow_sub_C_esymmCoeffPart`), and the degree is obtained inside the proof from
  `finrank_adjoin_of_irreducible`, where the ambient field is concrete and the earlier `whnf`
  blow-up does not occur.  Only the square class is left to the caller.  Axioms
  `[propext, Classical.choice, Quot.sound]`.  The module takes about three minutes to compile.

- 2026-08-01 — `GenericSquareClassInput.lean` supplies the last hypothesis of the instantiation.
  `vandermondeProd_genericRoot`: the Vandermonde product of the generic roots is the Vandermonde
  polynomial read in the rational function field.  `no_sqrt_generic_disc_mul_esymm`: a square root
  in the symmetric part of the discriminant times the top elementary symmetric function would be a
  square root inside the coefficient field, which
  `no_sqrt_disc_mul_esymmTop_of_mem_symmetricPartField` excludes.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  It is stated for **any** element of the symmetric part whose image is the top elementary
  symmetric function, rather than for `esymmCoeffPart`, because that element reaches the symmetric
  part through the `rw`-built isomorphism of the two presentations, whose action on carriers is not
  definitional.  Supplying the representative explicitly avoids unfolding it and costs the caller
  one equation.

- 2026-08-01 — **`GenericFullMonodromy.lean`: the two halves compose.**  `genericFullMonodromy` has
  no hypotheses beyond `3 <= d` and `0 < m`: over an algebraically closed field of characteristic
  zero, the automorphism group of the splitting field of
  `genericMonic * (X ^ (2m) - c_top)` over the root field of the second factor is the full symmetric
  group on `Fin d`, where `c_top` is the top elementary symmetric function.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  The composition was unblocked by rebuilding `symmetricPartEquivEsymmField` with
  `IntermediateField.equivOfEq` instead of a `rw` on the type: `Subalgebra.equivOfEq` sends `x` to
  `⟨↑x, _⟩`, so its action on carriers **is** definitional and
  `coe_symmetricPartEquivEsymmField_symm` holds by `rfl`.  That gives `coe_esymmCoeffPart`, the one
  equation the square-class theorem asked of its representative.  Note this is the opposite choice
  from the one recorded earlier for `rootField_centeredMonicE_eq_top`, where `rw` on the type was
  needed to avoid an elaboration blow-up — the right technique differs by which side needs to
  compute.

- 2026-08-01 — `TschirnhausShift.lean` starts the bridge back to the card's centered equation `(7)`.
  `taylor_coeff_pred`: for a monic polynomial of degree `d`, shifting the variable by `r` changes
  the next-to-leading coefficient to `d * r + c_{d-1}`.  The proof avoids any binomial expansion:
  `Polynomial.taylor_coeff` turns the coefficient into the Hasse derivative of order `d - 1`
  evaluated at `r`, that derivative has degree at most one, and its two coefficients are read off
  by `hasseDeriv_coeff` — slope `d.choose (d-1) = d` by monicity, constant `c_{d-1}`.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  Over a ring where `d` is invertible this says one shift removes the next-to-leading coefficient,
  which is the Tschirnhaus centering.  It is the first step of the change of variables that would
  identify the card's `E_0` with the centered coefficient field and so carry
  `genericFullMonodromy` to the card's own equation.

- 2026-08-01 — `TaylorRoots.lean` is the second step of the bridge.  The Taylor shift is composition
  with a translation, so `aeval_taylor`: evaluating the shifted polynomial at a point is evaluating
  the original at the translated point; `taylor_ne_zero`: shifting back recovers the polynomial, so
  the shift of a nonzero polynomial is nonzero; and `rootSet_taylor`: the roots of the shift are the
  roots of the original translated back.  Axioms `[propext, Classical.choice, Quot.sound]`.
  With `taylor_coeff_pred` this gives both halves of the Tschirnhaus change of variables: the shift
  that centers a monic polynomial, and the fact that it moves the roots by a base-field translation
  — so the field the roots generate, and hence the splitting field and the Galois group, are
  unchanged.

- 2026-08-01 — `adjoin_rootSet_taylor` completes the geometric half of the Tschirnhaus bridge: the
  shift does not change the field the roots generate, because translating by a base-field element
  stays inside any intermediate field.  So the centered and uncentered polynomials have the **same**
  root field over the same base, and therefore the same automorphism group.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  The pieces of the bridge now in place: `taylor_coeff_pred` (the shift that centers),
  `rootSet_taylor` (roots translate), `adjoin_rootSet_taylor` (root field unchanged).  What is left
  is to identify the corpus's `centeredMonicF` with the Taylor shift of `genericMonicF`, after which
  `genericFullMonodromy` transfers to the centered polynomial and the card's `(7)` is in reach.

- 2026-08-01 — `CenteredIsTaylorShift.lean`: `taylor_genericMonicF` identifies the corpus's centered
  polynomial as the Taylor shift of the generic one by the average of the roots.  Both are products
  of linear factors, so the identity is one `prod_comp` and a rearrangement of each factor.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  The Tschirnhaus bridge is now complete as a chain of facts: the centered polynomial **is** a shift
  of the generic one; a shift translates the roots by a base-field element
  (`rootSet_taylor`); and that leaves the field they generate unchanged
  (`adjoin_rootSet_taylor`).  Hence the centered and generic polynomials share a root field and an
  automorphism group, which is what carries the symmetric-monodromy statement between them.

- 2026-08-01 — `GenericAverageSymmetric.lean` moves the shift down to the coefficient field.
  `genericAverage_mem_symmetricPart`: permuting the roots does not change their average, so the
  average is symmetric — the corpus's `smul_genericAverage` is exactly the membership condition.
  `map_taylor`: a ring homomorphism carries a shift to the shift by the image of the amount.  Hence
  `centeredMonicPart`, the centered polynomial written **over the coefficient field**, with
  `map_centeredMonicPart` identifying its image in the rational function field as `centeredMonicF`.
  Axioms `[propext, Classical.choice, Quot.sound]`.
  This removes the base mismatch flagged in the previous entry: the centering can now be performed
  over `symmetricPart`, the same base `genericFullMonodromy` is stated over.

- 2026-08-01 — `CenteredPartSplittingField.lean`: the rational function field is a splitting field of
  the **centered** polynomial over the coefficient field.  `splits_centeredMonicPart` from the
  linear factorisation; `adjoin_rootSet_centeredMonicPart` is `adjoin_rootSet_taylor` applied to the
  identification of the centered polynomial as a shift; and the subalgebra form comes from the
  intermediate-field one through `adjoin_toSubalgebra_of_isAlgebraic` and
  `algebra_adjoin_le_adjoin`.  Axioms `[propext, Classical.choice, Quot.sound]`.
  So the centered polynomial over `symmetricPart` has the same splitting field as the generic one,
  and therefore the same Galois group — the symmetric group.  The Tschirnhaus transfer is complete
  at the level of the model.

- 2026-08-01 — `taylor_neg_centeredMonicPart`: shifting back by the average recovers the generic
  polynomial from the centered one.  Axioms `[propext, Classical.choice, Quot.sound]`.
  This is the algebraic heart of the recoverability the card's `(10)` asserts in the other
  direction: the generic coefficients are expressions in the average and the centered coefficients,
  exactly as the centered ones are expressions in the generic coefficients, so the two systems
  determine each other.  Turning that into algebraic independence of the centered coefficients still
  needs the passage from "two generating systems of the same size" to independence, which is a
  transcendence-degree argument and remains the open piece for the card's own equation.

- 2026-08-01 — `taylor_coeff_eq_add`: a shift changes each coefficient by a multiple of the shift,
  `(taylor r p).coeff k = p.coeff k + r * s`.  The constant term of the `k`-th Hasse derivative is
  the `k`-th coefficient, and the rest of its evaluation is divisible by `r` because
  `eval r q - eval 0 q` always is.  No binomial expansion is involved.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  This is the triangularity of the coefficient change under a shift — the form in which the card's
  step `(9)` is actually needed.  It says the centered coefficients are the generic ones plus
  corrections carrying a factor of the average, which is what makes the change of parameters
  invertible and, with an exchange argument, the centered coefficients independent.

- 2026-08-01 — `UniversalMonicPolynomial.lean` sets up the ring in which the change of coefficients
  can be studied on its own terms: `universalMonic`, the monic polynomial of degree `d` whose
  coefficients **are** the variables, with `coeff_universalMonic_lt`, `monic_universalMonic` and
  `natDegree_universalMonic`.  Axioms `[propext, Classical.choice, Quot.sound]`.
  This is the setting for the independence argument: shifting `universalMonic` gives coefficients
  `Q_k = X_k + X_0 * s_k` by `taylor_coeff_eq_add`, so the Jacobian of the change of coefficients
  specialises at `X_0 = 0` to the identity and is therefore nonzero — which the corpus's
  `algebraicIndependent_of_domain_jacobian` turns into algebraic independence.  That is the planned
  route to the centered coefficients' independence, with the two ingredients now in place.

- 2026-08-01 — `UniversalCenteredCoefficients.lean` performs the centering in the universal ring.
  `centeringShift` is minus the next-to-leading coefficient over the degree;
  `universalCenteredCoeff_pred` shows it does remove that coefficient (this is `taylor_coeff_pred`
  with the scalar cancelling); and `universalCenteredCoeff_eq_add` records that every other
  coefficient is the original plus a multiple of the shift.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  The Jacobian argument can now be set up: in the family consisting of the next-to-leading
  coefficient together with the centered ones, specialising the next-to-leading coefficient to zero
  kills the shift, so the derivative matrix becomes the identity in the first block and has a unit
  row for the last coordinate — block triangular with determinant one, hence nonzero as a
  polynomial.

- 2026-08-01 — analysis of the last step, recorded so it is not rediscovered.  Two routes to the
  centered coefficients' independence:
  (a) **Jacobian.**  Take the family (next-to-leading coefficient, centered coefficients).
  Specialising the next-to-leading coefficient to zero kills `centeringShift`, so by
  `universalCenteredCoeff_eq_add` the derivative matrix is the identity on the first block with a
  unit row for the last coordinate: block triangular, determinant one.  Feed to the corpus's
  `algebraicIndependent_of_domain_jacobian`.
  (b) **Automorphism.**  Transfer independence along a substitution automorphism, using mathlib's
  `AlgebraicIndependent.map` (which exists).  The natural candidate — fix the top coefficient, send
  the others to the centered ones — does **not** telescope: the centering sends the top coefficient
  to zero while the substitution fixes it, so `map` of the universal polynomial is the centered
  polynomial **plus** a leftover term, and the composition of the two shifts does not cancel.  Any
  attempt on this route must handle that mismatch rather than assume it away.
  Route (a) is the one to take; nothing in it is now missing except the derivative computation and
  the determinant of a block-triangular matrix.

- 2026-08-01 — `DetUpdateRowOne.lean`: `det_updateRow_one`, the identity matrix with one row replaced
  has determinant that row's entry in the replaced position — Cramer's rule for the identity, read
  through a transpose.  Axioms `[propext, Classical.choice, Quot.sound]`.
  This is the shape the Jacobian of route (a) takes after specialising the next-to-leading
  coefficient to zero: every row but the last becomes a standard basis vector, and the last row's
  entry in its own position is one, so the determinant is one and the unspecialised determinant is
  therefore nonzero.

- 2026-08-01 — `CenteredCoefficientIndependence.lean` builds route (a) up to the determinant.
  `centeredFamily` is the next-to-leading coefficient together with the centered ones,
  `centeredJacobian` its derivative matrix, `killLast` the specialisation setting the
  next-to-leading coefficient to zero, and `killLast_centeredJacobian`: **off the last row the
  specialised Jacobian is exactly the identity**.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  A correction to the plan while proving it: off the last row the *unspecialised* Jacobian is
  **not** the identity — the Leibniz rule leaves a term `centeringShift * pderiv s` which only the
  specialisation kills.  My earlier sketch had claimed the identity before specialising; the
  specialisation is needed for both Leibniz terms, not just one.

- 2026-08-01 — `det_centeredJacobian_ne_zero`: **the Jacobian of the centering change of parameters
  is nonsingular.**  Specialising the next-to-leading coefficient to zero turns it into the identity
  with one row replaced (`killLast_mapMatrix_centeredJacobian`), whose determinant is that row's own
  entry — which is one, since the last family member is the next-to-leading coefficient itself.  A
  determinant with a nonzero image is nonzero.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  This is the hypothesis of the corpus's `algebraicIndependent_of_domain_jacobian`; applying it
  gives algebraic independence of the next-to-leading coefficient together with the centered ones,
  which is the missing half of the card's `(10)`.

- 2026-08-01 — **`algebraicIndependent_centeredFamily`: the missing half of `(10)` is proved.**  The
  next-to-leading coefficient together with the centered coefficients form an algebraically
  independent family, by the corpus's `algebraicIndependent_of_domain_jacobian` applied to the
  nonsingular Jacobian of the previous entry.  Axioms `[propext, Classical.choice, Quot.sound]`.
  This is the obstruction that sent the work down the uncentered route many entries ago:
  the centered coefficients of a monic polynomial with indeterminate coefficients **are**
  algebraically independent, and the proof needs no expansion of the shift — only that each
  coefficient changes by a multiple of it, and that the multiple dies when the shift does.

- 2026-08-01 — `UniversalToGeneric.lean`: `coeffSub` sends each variable to the matching coefficient
  of the generic polynomial, and `map_coeffSub_universalMonic` shows it carries the monic polynomial
  with indeterminate coefficients to the generic one.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  This is the specialisation along which the universal statements descend to the corpus's objects:
  since `coeffSub` commutes with the Taylor shift (`map_taylor`) and sends the universal centering
  shift to the average of the roots, it carries the universal centered coefficients to the corpus's
  centered coefficients — so their algebraic independence follows from
  `algebraicIndependent_centeredFamily` once the injectivity of `coeffSub` is in hand, which is the
  fundamental theorem of symmetric functions.
  A note on cost: proving the polynomial identity needed the degree facts as **forward** hypotheses;
  rewriting the goal backwards with `natDegree` exhausted two million heartbeats at `whnf`.

- 2026-08-01 — `GenericCoeffPred.lean`: `coeff_genericMonicF_pred`, the next-to-leading coefficient
  of the generic polynomial is minus the sum of the roots (the same `prod_X_add_C_coeff` argument the
  corpus used for the centered analogue), and `genericAverage_eq`, the average is minus that
  coefficient over the degree.  Axioms `[propext, Classical.choice, Quot.sound]`.
  This is the last ingredient of the specialisation: it says `coeffSub` sends the **universal**
  centering shift to the average of the roots, so — through `map_taylor` and
  `map_coeffSub_universalMonic` — it carries the universal centered coefficients to the corpus's
  centered coefficients.

- 2026-08-01 — `CenteredCoeffIndependent.lean` completes the descent.  `coeffSub_centeringShift`:
  the specialisation sends the universal centering shift to the average of the roots.
  `coeffSub_universalCenteredCoeff`: hence it carries each universal centered coefficient to the
  matching coefficient of the **centered generic polynomial** — through `map_taylor`,
  `map_coeffSub_universalMonic` and `taylor_genericMonicF`.  Axioms
  `[propext, Classical.choice, Quot.sound]`.
  So the corpus's centered coefficients are the image of an algebraically independent family under
  `coeffSub`; their own independence follows as soon as that map is known injective, which is the
  fundamental theorem of symmetric functions already in the corpus.

- 2026-08-01 — **The card's own equation `(7)` is now proved unconditionally in Lean.**  Five modules
  closed the assembly:

  `MonomialSubstitution.lean` — scaling and permuting the variables of a polynomial ring is an
  automorphism, hence injective (`monomialSub_injective`).

  `CoeffSubInjective.lean` — the specialisation of the indeterminate coefficients to the generic ones
  factors as that signed reversal, followed by substituting the elementary symmetric functions,
  followed by the passage to fractions; each is injective, so `coeffSub_injective`.  The reversal is
  Vieta: the coefficient at `k` is `(-1)^(d-k)` times the `(d-k)`-th elementary symmetric function,
  and `k ↦ Fin.rev k` matches the indices.

  `GenericCenteredIndependence.lean` — pushing `algebraicIndependent_centeredFamily` through that
  injection gives `algebraicIndependent_centeredCoeffFamily`, and restricting to the indices below
  the top one gives `algebraicIndependent_centeredLowCoeff`: the `d - 1` coefficients of the
  **centered** generic polynomial are algebraically independent over the constants.

  `CenteredCoeffFieldIndependence.lean` — the same family read inside the centered field
  (`algebraicIndependent_centeredLowCoeffIn`), by descending along the injective inclusion.

  `CenteredCoeffFieldRational.lean` — the top centered coefficient vanishes, so the coefficient field
  is generated by the low ones (`adjoin_range_centeredLowCoeffIn`); with their independence that is a
  **rational function field in `d - 1` variables** (`centeredCoeffFieldEquiv`), the constant
  coefficient being the first variable.  A variable is prime, so `X ^ n - c_0` is irreducible at
  every exponent (`irreducible_X_pow_sub_C_centeredConstant`) and a root of it generates an extension
  of exactly that degree (`finrank_adjoin_centeredConstant_root`).

  `CenteredFullMonodromy.lean` — `centeredFullMonodromy (hd : 3 ≤ d) (hm : 0 < m)`: the automorphism
  group of the splitting field of `centeredMonicE * (X ^ (2m) - c_0)` over the root field of the
  second factor is `Equiv.Perm (Fin d)`.  No hypotheses beyond `3 ≤ d` and `0 < m`.  Axioms
  `[propext, Classical.choice, Quot.sound]` throughout.

  This is the card's `E_0 = K(q, c_0, …, c_{n-1})` identified with the centered coefficient field and
  `(3)` read there — the assembly the inventory listed as the last open item.

  Two cost notes.  First, `open MvPolynomial` shadows `funext` with `MvPolynomial.funext`, which
  turns a one-line function equality into a hopeless `eval`-goal; `_root_.funext` is needed.
  Second, `IntermediateField.equivOfEq` may be applied but must not be **composed into the type of a
  definition**: stating `FractionRing … ≃ₐ[K] centeredCoeffField K d` forces the kernel to check the
  two carriers defeq and it does not terminate.  Carrying the field equality as a hypothesis and
  `subst`-ing it costs nothing.

- 2026-08-01 — **Both parities of the Kummer base change are now instantiated.**  The card's base
  change `(10)` has exponent `n = d - 1`, so the even capstones alone do not cover it.  Four modules
  close the odd half:

  `RadicalRootFieldDegree.lean` — over a field containing the roots of unity the root field of an
  irreducible radical polynomial has degree the exponent (`finrank_rootField_X_pow_sub_C`), so the
  parity hypothesis of the odd base change is the parity of the exponent
  (`not_two_dvd_finrank_rootField`).

  `RadicalBaseChangeOddFromDegree.lean` — the abstract odd step with the root extracted internally:
  the caller supplies only the irreducibility, the parity, and the degree of a root.

  `CenteredRadicalBaseChangeOdd.lean` and `CenteredFullMonodromyOdd.lean` — the centered equation at
  an odd exponent: `centeredFullMonodromyOdd (hd : 3 ≤ d) (hn : 0 < n) (hodd : ¬ 2 ∣ n)`.

  `GenericFullMonodromyOdd.lean` — the same for the uncentered generic polynomial at any coefficient.

  Axioms `[propext, Classical.choice, Quot.sound]` throughout.  With `centeredFullMonodromy` and
  `centeredFullMonodromyOdd` the card's `(3)` is now covered at every exponent, even and odd.

  Three cost notes, all measured.  `obtain` on an `Exists` cannot produce data — `Classical.choose`
  is required, and the failure only surfaces after the surrounding term has been elaborated.
  Extracting that root inside a definition whose ambient field is a **concrete** `SplittingField`
  costs more than a million heartbeats at `whnf`; doing it in a lemma whose ambient field is a
  variable costs nothing.  And elaborating one heavy irreducibility term twice in the same proof cost
  132 seconds: hoisting it into a `have` took `GenericFullMonodromyOdd` from 138 s to 6 s.

- 2026-08-01 — **The free parameter `q`.**  The card's `E_0 = K(q, c_0, …, c_{n-1})` is the centered
  coefficient field with **one more free transcendental**: the equation `(7)` is `q a^{n+1} = Σ c_j
  a^j`, so after dividing by `q` its `n` coefficients are `c_j/q` while the base still carries `q`.
  So `centeredFullMonodromy` gives `(3)` over `K(c_0/q, …, c_{n-1}/q)` and what is missing is that
  adjoining an independent transcendental to the base does not shrink a Galois group.

  That is classical and absent from mathlib.  Five modules build it:

  `RationalFunctionRelativeClosure.lean` — a field is relatively algebraically closed in its field of
  rational functions.  An algebraic rational function is integral over the polynomial ring, which is
  integrally closed, hence a polynomial; and a polynomial algebraic over the constants is constant,
  since a nonzero polynomial composed with a nonconstant one is nonzero
  (`exists_algebraMap_eq_of_isAlgebraic`, `eq_C_of_isAlgebraic`).

  `AutCongrScalars.lean` — the automorphism group depends only on the image of the base field inside
  the ambient field, so a base field may be replaced by its image, where it is an intermediate field
  and the compositum arguments apply.

  `BaseChangeRelativeClosure.lean` — the general step: if the second factor of the compositum carries
  no algebraic element beyond the base, it meets the splitting field in the base, and restriction is
  an isomorphism (`baseChangeRelativelyClosed`).  Every element of the root field is algebraic, so
  the intersection hypothesis of natural irrationalities is exactly relative closedness.

  `FractionRingAdjoinX.lean` — the field of rational functions is generated over the constants by the
  variable (`adjoin_fracX_eq_top`), through the algebra generated by the variable being everything.

  `FractionRingConstantsEmbedding.lean` — extending the constants embeds one rational function field
  in the other, and an element of the image algebraic over the small constants is constant
  (`mem_bot_of_mem_fieldRange_of_isAlgebraic`) — the hypothesis `baseChangeRelativelyClosed` consumes.

  Axioms `[propext, Classical.choice, Quot.sound]` throughout.  What remains is the assembly: taking
  the ambient field to be the rational functions over the splitting field, identifying the second
  factor with the image of the small rational functions, and reading `centeredFullMonodromy` there.

- 2026-08-01 — **The free parameter theorem is proved.**  `FreeParameterBaseChange.lean`:

  `freeParameterBaseChange (hp : p ≠ 0) (hsep : p.Separable) (hsplit) (hgen)` — for `E` a splitting
  field of a separable `p` over `F`, the automorphisms of the rational functions `E(t)` over the
  rational functions `F(t)` are the Galois group of `p` over `F`.  Adjoining a free parameter to the
  base does not change the Galois group.  Axioms `[propext, Classical.choice, Quot.sound]`.

  The proof: `fracSub F E` — the image of `F(t)` in `E(t)` — meets the splitting field in `F`,
  because every element of the splitting field is algebraic over `F` while the image carries no
  algebraic element beyond `F`; and the two generate `E(t)`, because the constants and the variable
  generate every polynomial hence every quotient (`eq_top_of_mem_of_mem`).  Natural irrationalities
  then makes restriction an isomorphism.  Along the way `E(t)` is shown to be a splitting field of
  `p` over `F(t)` (`isSplittingField_fracSub`), which is what supplies the Galois hypotheses; the
  field-versus-algebra adjoin step goes through `adjoin_toSubalgebra_of_isAlgebraic`.

  This is the missing ingredient identified in the previous entry.  It is a classical statement with
  no counterpart in mathlib, and it applies to any separable polynomial, not only the ones here.

  Two cost notes.  A `≤` between intermediate fields is not a function: `SetLike.le_def.mp` is
  needed to apply it to a membership.  And an implicit type argument that has to be recovered from
  under a `Polynomial.map` sends the unifier into `Polynomial.C =?= Polynomial.C` delta-unfolding
  for eight seconds and then a heartbeat timeout; pinning `(E := E)` at the call site costs nothing.

- 2026-08-01 — **The card's `(3)` is now proved over the card's own field.**  Three modules close it:

  `CenteredRadicalBaseChangeIn.lean` and `CenteredFullMonodromyIn.lean` restate the base change and
  the full-monodromy conclusion **in any ambient splitting field**, not only the canonical one.  Both
  inputs of the step are statements about the coefficient field alone — the radical polynomial over
  the constant coefficient is irreducible because that coefficient is a variable of a rational
  function field, and the discriminant times it is not a square — so nothing forces a particular
  ambient.

  `CenteredParameterMonodromy.lean` reads it over the parameter field:
  `centeredParameterMonodromy (hd : 3 ≤ d) (hm : 0 < m)` and
  `centeredParameterMonodromyOdd (hd : 3 ≤ d) (hn : 0 < n) (hodd : ¬ 2 ∣ n)` give, for any ambient
  splitting field `L` of `centeredMonicE * (X ^ n - c_0)`, an isomorphism

  ```text
  (FractionRing (Polynomial L) ≃ₐ[fracSub (rootField … (X ^ n - c_0)) L] FractionRing (Polynomial L))
    ≃* Equiv.Perm (Fin d)
  ```

  — the Galois group over the coefficient field extended by a radical of the constant coefficient and
  by one independent transcendental, which is the card's `M = K(p_1, …, p_n, q)`.  Axioms
  `[propext, Classical.choice, Quot.sound]` throughout.

  **Why stating it in an arbitrary ambient was necessary, not merely convenient.**  Pinning the
  ambient to the canonical `SplittingField` makes the statement carry that expression four times;
  elaborating `fracSub` over an intermediate field of it exhausted a million heartbeats at
  `isDefEq`, comparing `Field.toSemifield.toCommSemiring` with `SubsemiringClass.toCommSemiring`
  through the whole term.  Naming the ambient with an opaque `def` and re-deriving its instances by
  `inferInstanceAs` moves the same cost into the transport — the two views of the instances are
  definitionally but not syntactically equal, and the unifier grinds through the projections; that
  attempt was killed by the operating system.  With the ambient a variable the statement is small
  and the proof is an application.  Two further seconds-to-minutes swings came from arguments whose
  implicit `K`, `d` were left to inference: `separable_centeredMonicE` with metavariables sends the
  unifier into the same subsemiring comparison.  Pinning `(K := K) (d := d)` took the file from 145 s
  to 28 s.

- 2026-08-01 — **The fiber equation `(2)` is the tail polynomial equation `(7)`.**
  `ReciprocalFiberEquation.lean` closes the step `(5) → (7)`, which the card had only at paper level.

  `coeff_mul_pow_eq_tail_sum`: for `a` invertible with inverse `b` and `Y` the inverse of `a + t R`,

  ```text
  [t^n] Y * a^(n+1) = ∑_(j<n) (-1)^(n-j) * [t^j] (R^(n-j)) * a^j
  ```

  So the equation `[t^n] Y = q` of `(2)`, cleared of denominators, is a polynomial equation in `a` of
  degree `n+1` with **no term of degree `n`** and with the alternating tail coefficients of `(6)`.
  `coeff_mul_pow_eq_polynomial_tail_sum` states the same with the tail given by a polynomial, in
  which form the coefficients are literally the corpus's `tailCoeff K n j = ((tailPoly K n) ^ (n-j)).coeff j`.
  Axioms `[propext, Classical.choice, Quot.sound]`.

  The existing `GeometricInverseTruncation.lean` already had `(5)`; what was missing was clearing the
  inverse powers, which is the identity `b^(k+1) * a^(n+1) = a^(n-k)` for `k ≤ n`, and the
  reindexing `j = n - k` that turns the sum over `k` into the tail polynomial in `a`.

  **What is left for the card.**  Only the identification of the two coefficient models: the tail
  coefficient field `K(c_0, …, c_(n-1))` and the centered coefficient field of the generic
  polynomial of degree `n+1`.  Both are rational function fields on an algebraically independent
  family of the same size — `algebraicIndependent_tailCoeff` and `algebraicIndependent_centeredLowCoeff`
  — so the identification is a matching of generators, under which the fiber equation of `(7)` becomes
  the centered generic polynomial and `centeredParameterMonodromy` reads as the card's `(3)`.

- 2026-08-01 — **The two coefficient models are identified.**  `TailCenteredCoefficientMatch.lean`:

  `tailCenteredCoeffEquiv K n` — an isomorphism over the constants between the field generated by the
  `n` tail coefficients of the reciprocal jet and the field generated by the `n` centered
  coefficients of the generic polynomial of degree `n + 1`; `coe_tailCenteredCoeffEquiv` says it
  carries the `j`-th tail coefficient to the `j`-th centered coefficient.  Axioms
  `[propext, Classical.choice, Quot.sound]`.

  Both fields are rational function fields on an algebraically independent family of size `n`, so the
  identification is the composite of the two rational models — `algebraicIndependent_tailCoeffIn`
  (the tail coefficients pushed into the fraction field, independent by `map'` along the injective
  algebra map) and `centeredCoeffFieldEquiv`.  The degree bookkeeping `Fin (n + 1 - 1) = Fin n` is
  definitional but not syntactic, so the last step closes by `exact`, not `rw`.

  With this, every numbered step of the card carries an unconditional Lean theorem: `(5)` and its
  clearing to `(7)` in `GeometricInverseTruncation` and `ReciprocalFiberEquation`, the parameter
  change `(6),(8),(9),(10)` in the tail modules, the coefficient field `(11)` here, and `(3)` itself
  in `centeredParameterMonodromy` and `centeredParameterMonodromyOdd`.

- 2026-08-01 — **The reciprocal duality claim is formalized.**  The theorem statement ends with "by
  reciprocal duality the same holds for `Phi_(n,1)`", which the numbered steps never covered.
  `ReciprocalFiberEquation.lean` now carries it:

  `constantCoeff_inverse` — the constant term of the inverse jet is the inverse of the constant term;
  `eq_const_add_X_mul_reciprocalTail` — every jet splits as its constant term plus `t` times its
  tail; and `coeff_mul_pow_eq_tail_sum_reciprocal` — the inverse of a jet with invertible constant
  term is again such a jet, and **its** fiber equation is the same equation with the two packets
  exchanged.  Axioms `[propext, Classical.choice, Quot.sound]`.

  So the rank-one cover on the reciprocal side is the same object as on the source side, which is the
  content of the duality: `(3)` for `Phi_(1,n)` is `(3)` for `Phi_(n,1)` read through the exchange.

- 2026-08-01 — **The degree claim of the theorem statement is formalized.**  The statement asserts
  that the generic fiber equation "has degree `n+1` in `a`"; that was implicit in the derivation but
  never stated.  `ReciprocalFiberEquation.lean` now names the equation and proves its shape:

  `fiberPolynomial q R n` — the polynomial `q a^(n+1) - Σ_(j<n) (-1)^(n-j) [t^j](R^(n-j)) a^j`;
  `natDegree_fiberPolynomial` — its degree is `n+1` whenever `q ≠ 0`;
  `coeff_fiberPolynomial_self` — its coefficient in degree `n` vanishes, so it is centered;
  `eval_fiberPolynomial_eq_zero` — the source coefficient of a jet whose inverse has `q` as its
  `n`-th coefficient is a root of it.  Axioms `[propext, Classical.choice, Quot.sound]`.

  That is `(2) -> (7)` in full: the fiber equation is a centered polynomial equation of degree `n+1`
  whose lower coefficients are the tail coefficients, and the observed coefficient is a root.

- 2026-08-01 — **The boundary case `n = 1` is covered.**  The proof of `(3)` ends "when `n = 1`,
  `(10)` is the identity and the quadratic group is `S_2` directly", and the capstones assume
  `3 ≤ d`, so `n = 1` — degree two — fell outside them.  It needs no base change at all:
  `quadraticParameterMonodromy` in `CenteredFreeParameter.lean` is the `d = 2` instance of
  `centeredFreeParameterMonodromy`, which carries no degree hypothesis, and gives `Equiv.Perm (Fin 2)`
  over the coefficient field with the free parameter.  Axioms
  `[propext, Classical.choice, Quot.sound]`.

  So `(3)` is now proved for every tail length: `n = 1` by the quadratic case, `n ≥ 2` by
  `centeredParameterMonodromy` and `centeredParameterMonodromyOdd` according to the parity of `n`.

## Log

- 2026-08-02 — **`(7)` is formalized: the fibre equation is centred, with no `a^n` term.**
  Axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  natDegree_invNumerator_succ_le  (InverseJetNumerator.lean) :
    (invNumerator u (k+1)).natDegree ≤ k
  coeff_oneDeepEquation_next      (OneDeepFibreBound.lean) :
    (oneDeepEquation U d (n+1)).coeff (n+1) = 0
  ```

  The card's sentence "There is no `a^n` term" is exactly the second statement, and it follows from
  the first: the `k`-th numerator of the truncated inverse has degree at most `k - 1`, not merely
  `k`, because every term of the recursion pairs a shift `X ^ i` with a numerator of index
  `k - 1 - i`, so the two degrees always sum to one less than the index.  The previous bound in the
  corpus was the weaker `≤ k`, which does not give the vanishing.

  With `natDegree_oneDeepEquation` (degree `1 + n`, already in the corpus) this is `(7)` in full: the
  equation is of degree `n + 1` in `a` and already centred, so translation cannot be used to remove
  the next-to-leading coefficient — it is absent to begin with, which is what the comparison with the
  universal centred polynomial requires.

  Still open on this card: the triangular coefficient law `(8)`--`(9)` and the algebraic independence
  it gives, the identification of `(7)` with the universal centred polynomial over `E_0`, and the
  Kummer base-change argument.  All three are statements about the coefficients `c_j` and are
  independent of the geometry already formalized.

- 2026-08-02 — **`(8)` proved, and the frame for `(9)`.**
  `formal/GaloisForLFunctions/HTGeometry/TriangularTailCoefficients.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  tailPoly K n                 -- R(t) = p₁ + p₂t + ⋯ + pₙ t^{n-1}, with indeterminate coefficients
  coeff_tailPoly               :  [t^i] R = p_{i+1} for i < n, and 0 beyond
  coeff_zero_tailPoly_pow      :  [t^0] R^m = p₁^m                       -- this is (8)
  coeff_tailPoly_pow_mem       :  [t^b] R^m ∈ K[p₁, …, p_{b+1}]
  pderiv_eq_zero_of_mem_tailAdjoin : a later parameter does not occur in the earlier ones
  ```

  `coeff_zero_tailPoly_pow` is `(8)` up to the sign in `(6)`: `c_0 = (-1)^n p₁^n`.
  `coeff_tailPoly_pow_mem` is the triangularity of the change of parameters — the `j`-th coefficient
  involves no parameter beyond `p_{j+1}` — proved by induction on the power through the convolution.

  The remaining half of `(9)` is the diagonal entry, and the formulation chosen for it is

  ```text
  pderiv (j) ([t^j] R^m) = m • p₁^{m-1}          for 1 ≤ j < n,
  ```

  which is exactly "the only term involving `p_{j+1}` chooses `p_{j+1}t^j` once and the constant term
  `p₁` in every other factor", with no existential quantifier over the remainder `H_j` and no
  subalgebra in the statement: the derivation kills every term the card leaves unnamed.  Together with
  the membership above, that is `(9)` in full, and the diagonal being `m p₁^{m-1} ≠ 0` is what makes
  the parameter change étale on `c_0 ≠ 0`.

- 2026-08-02 — **`(9)` is proved: the triangular coefficient law is complete.**
  `formal/GaloisForLFunctions/HTGeometry/TriangularTailCoefficients.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  pderiv_coeff_tailPoly_pow :
    1 ≤ j → j < n →  pderiv (j) ([t^j] R^{m+1}) = (m+1) • p₁^m
  ```

  Together with `coeff_tailPoly_pow_mem` (the coefficient lies in `K[p₁,…,p_{j+1}]`) this is `(9)`:
  the `j`-th coefficient is linear in `p_{j+1}` with diagonal entry `m p₁^{m-1}`, and everything else
  involves only earlier parameters.  With `coeff_zero_tailPoly_pow` for `(8)`, the change of
  parameters `p ↦ c` of `(6)` is proved triangular with diagonal `m p₁^{m-1}`, which is what makes it
  étale on `c₀ ≠ 0` and hence what the card's Kummer base-change argument rests on.

  The proof is an induction on the power through the convolution, and the three cases of the
  induction are exactly the card's three sources of a `p_{j+1}`: the factor `p_{j+1}t^j` paired with
  the constant term of the remaining power, the constant term `p₁` paired with the inductive
  occurrence, and everything else, which the derivation kills because it lies in the earlier
  parameters.  Stating the diagonal as a `pderiv` rather than as an existential over an unnamed
  remainder `H_j` is what made the induction go through in that form.

  Still open on this card: algebraic independence of `c₀, …, c_{n-1}` (which now follows from
  triangularity plus a Jacobian argument), the Galois group of the universal centred polynomial —
  classical, and absent from mathlib — and the Kummer base change.

- 2026-08-02 — **The Jacobian of the parameter change, computed.**
  `formal/GaloisForLFunctions/HTGeometry/TriangularTailCoefficients.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  pderiv_paramCoeff_of_lt :  j < i  →  pderiv i (c_j) = 0
  pderiv_paramCoeff_self  :  j < n  →  pderiv j (c_j) = (n - j) • p₁^{n-j-1}
  det_paramJacobian       :  det (pderiv i (c_j))_{i,j} = ∏_{j<n} (n - j) • p₁^{n-j-1}
  ```

  The card's sentence "all diagonal derivatives are nonzero" is now a computed determinant.  The
  matrix is triangular by `pderiv_paramCoeff_of_lt` — the `j`-th coefficient does not involve the
  later parameters — and its diagonal is the `(9)` entry, uniformly for all `j` including `j = 0`,
  where the coefficient is `p₁^n` and the derivative `n p₁^{n-1}` fits the same formula.  In
  characteristic zero and on `p₁ ≠ 0` every factor is nonzero, which is exactly the étaleness of the
  triangular map `(8)`--`(9)` on `c₀ ≠ 0` that the card's Kummer argument invokes.

  Also added: `pderiv_X_pow_self`, the derivative of a power of a variable, which mathlib's
  `MvPolynomial.PDeriv` does not state.

  What is left on the card is unchanged in kind: algebraic independence of `c₀, …, c_{n-1}` — which
  is the Jacobian criterion applied to the determinant just computed, and the criterion itself is
  absent from mathlib — the Galois group of the universal centred polynomial, and the Kummer base
  change.

- 2026-08-02 — **Linearity in the diagonal variable: `(9)` is now literally an affine-linear law.**
  `formal/GaloisForLFunctions/HTGeometry/TriangularTailCoefficients.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  degreeOf_eq_zero_of_mem_tailAdjoin :  a later variable does not occur in the earlier subalgebra
  degreeOf_coeff_tailPoly_pow_of_lt  :  b < j  →  degreeOf j ([t^b] R^m) = 0
  degreeOf_coeff_tailPoly_pow_self   :  1 ≤ j < n  →  degreeOf j ([t^j] R^m) ≤ 1
  ```

  The last is the missing structural half of `(9)`: the `j`-th coefficient is **affine-linear** in
  `p_{j+1}`, not merely a polynomial with a known derivative.  The card's reason — "two occurrences of
  `p_{j+1}` would need two factors contributing `t^j` each, which overshoots `t^j`" — is the
  induction's case split: in the convolution, one factor may supply `p_{j+1}`, and then the other
  contributes only `t^0` and lies in the earlier variables.

  With the three facts now proved — membership in `K[p₁,…,p_{j+1}]`, degree at most one in `p_{j+1}`,
  and derivative `(n-j)p₁^{n-j-1}` — the coefficient is pinned to the form
  `(n-j) p₁^{n-j-1} p_{j+1} + H_j(p₁,…,p_j)` of `(9)`, with `H_j` determined rather than posited.

  A note on hypotheses: these three need `Nontrivial K`, because `degreeOf j (X j) = 1` fails over the
  zero ring, whereas the membership and derivative statements hold for any commutative ring.

- 2026-08-02 — **`(9)` in the card's own form, with `H_j` exhibited.**
  `formal/GaloisForLFunctions/HTGeometry/TriangularTailCoefficients.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  coeff_tailPoly_pow_decomp :
    1 ≤ j < n →  ∃ H ∈ K[p₁, …, p_j],  [t^j] R^{m+1} = (m+1) • (p₁^m · p_{j+1}) + H
  ```

  This is `(9)` as the card writes it, with the remainder `H_j` **constructed** rather than posited:
  the induction produces it explicitly as `p₁ · H_{j,m} + ∑ (cross terms)`, and its membership in the
  earlier subalgebra is proved alongside.  The two erasures that isolate `(j,0)` and `(0,j)` from the
  convolution are exactly the card's two named contributions — the factor `p_{j+1}t^j` against the
  constant term, and the constant term `p₁` against the inductive occurrence — and everything the
  card leaves unnamed is the sum over the erased set, each of whose factors is proved to lie in
  `K[p₁,…,p_j]`.

  With this, `(6)`--`(9)` — the part the card's novelty audit identifies as its new content — is
  formalized end to end: the constant term `(8)`, the affine-linear form `(9)` with its remainder,
  the degree bound in the diagonal variable, and the Jacobian determinant of the whole change of
  parameters.

  The three items that remain are all classical and all absent from mathlib: the Jacobian criterion
  for algebraic independence, the Galois group of the universal centred polynomial, and the Kummer
  base-change comparison.

- 2026-08-02 — **`(6)`--`(9)` closed, and an analysis of what independence actually needs.**
  `formal/GaloisForLFunctions/HTGeometry/TriangularTailCoefficients.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  paramCoeff_zero   :  c_0 = p₁^n                                        -- (8)
  paramCoeff_decomp :  1 ≤ j < n → ∃ H ∈ K[p₁,…,p_j],
                       c_j = (n-j) • (p₁^{n-j-1} · p_{j+1}) + H          -- (9)
  ```

  stated for the card's own coefficients rather than for a general power, which closes `(6)`--`(9)`.

  **On algebraic independence of `c_0, …, c_{n-1}`.**  Three routes were examined and the finding is
  recorded so they are not re-tried blindly.

  1. *Jacobian criterion.*  `det_paramJacobian` computes the determinant, but the criterion itself —
     algebraically independent iff the Jacobian is nonzero, in characteristic zero — is not in
     mathlib and is a transcendence-degree theorem, not a corollary of the determinant.
  2. *Triangular elimination over `K(p₁)`.*  Solving `c_j` for `p_{j+1}` recursively needs the
     diagonal `(n-j)p₁^{n-j-1}` to be a unit, so it works over the localization at `p₁` but not over
     `K[p]`; transferring independence back across the localization needs transcendence-degree API.
  3. *Induction on the last variable.*  This one is elementary and self-contained: if
     `P(c_0,…,c_{n-1}) = 0`, view `P` in its last variable and use that `c_{n-1}` is affine-linear in
     `p_n` with nonzero leading coefficient over a domain, so the top term survives by the inductive
     independence of `c_0,…,c_{n-2}`.  Every input is now proved — `paramCoeff_decomp` gives the
     affine-linear form and `degreeOf_coeff_tailPoly_pow_of_lt` gives that the earlier coefficients
     are free of `p_n`.  What it needs from mathlib is a "leading coefficient in one variable" API
     for `MvPolynomial`, which exists only via `finSuccEquiv` and peels off the *first* variable, so
     the parameters would have to be indexed in reverse.

  Route 3 is the one to take, and the reindexing is the whole of the remaining work for independence.

- 2026-08-02 — **The blocker for independence is built: isolating one variable.**
  `formal/GaloisForLFunctions/HTGeometry/IsolateVariable.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  optionNeEquiv j  :  Option {i // i ≠ j} ≃ σ
  isolateVar K j   :  MvPolynomial σ K ≃ₐ[K] Polynomial (MvPolynomial {i // i ≠ j} K)
  isolateVar_X_self:  X j ↦ Polynomial.X
  isolateVar_X_of_ne: X i ↦ Polynomial.C (X i)      for i ≠ j
  ```

  The previous entry identified the missing piece as a "leading coefficient in one variable" API,
  available in mathlib only through `finSuccEquiv`, which peels off the *first* variable of
  `Fin (n+1)` and would have forced the parameters to be reindexed in reverse.  That reindexing is
  avoidable: mathlib's `optionEquivLeft` splits `MvPolynomial (Option σ)` correctly, and all that was
  missing was the equivalence `Option {i // i ≠ j} ≃ σ` splitting an arbitrary index type at an
  arbitrary element.  With it, any variable can be isolated, and no reindexing of the parameters is
  needed at all.

  The route to independence is now: transport `c_{n-1} = A p_n + H` through `isolateVar` at `p_n`, where
  it becomes a degree-one polynomial `C A' · X + C H'` over the ring in the other parameters, with
  `A' ≠ 0` because `A = (n-1) p₁^{n-2}` is nonzero in a domain; a degree-one polynomial is
  transcendental over its base, and `AlgebraicIndependent.option_iff_transcendental` then adds
  `c_{n-1}` to the inductively independent `c_0, …, c_{n-2}`.

- 2026-08-02 — **The transcendence step, in ten lines, and a correction about what was needed.**
  `formal/GaloisForLFunctions/HTGeometry/TriangularIndependence.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  transcendental_supported_linear :
    j ∉ s → A ≠ 0 → Transcendental (supported K s) (A · X j + H)     for A, H supported on s
  ```

  over any commutative domain.  This is the inductive step that adjoins one coefficient to an
  algebraically independent family.

  **Correction to the previous entry.**  It said the route required transporting `c_{n-1}` through
  `isolateVar` to reach a degree-one polynomial.  That is not needed: mathlib already has
  `MvPolynomial.transcendental_supported_X` — a variable outside `s` is transcendental over the
  polynomials supported on `s` — and `Transcendental.aeval`, which propagates transcendence along a
  polynomial of nonzero degree with leading coefficient a nonzerodivisor.  Composing the two with
  `f = C A · X + C H` gives the statement directly.  `isolateVar` from the previous entry is a
  correct and reusable tool, but it is not on this path; the path is three mathlib lemmas.

  What remains for independence of `c_0, …, c_{n-1}` is the induction itself: `paramCoeff_decomp`
  puts `c_j` in the form `A · p_{j+1} + H` with `A = (n-j) p₁^{n-j-1} ≠ 0` in characteristic zero and
  `A, H` supported on the earlier parameters, and `AlgebraicIndependent.option_iff_transcendental`
  turns each application of the lemma above into one more independent coefficient.

- 2026-08-02 — **Each coefficient is transcendental over the earlier ones.**
  `formal/GaloisForLFunctions/HTGeometry/TriangularIndependence.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  tailAdjoin_eq_supported   :  the corpus's subalgebra is mathlib's `supported`
  transcendental_paramCoeff :  1 ≤ j < n → (n - j : K) ≠ 0 →
                               Transcendental (supported K {i | i < j}) c_j
  ```

  This applies the previous entry's lemma to the card's own coefficients: `c_j` is affine-linear in
  `p_{j+1}` with leading coefficient `(n-j) p₁^{n-j-1}`, which is nonzero exactly when `n - j` is
  invertible — so the characteristic-zero hypothesis of the card enters here and nowhere else in this
  part of the argument, and it enters as `(n - j : K) ≠ 0` rather than as a blanket assumption.

  The nonvanishing of the leading coefficient reduces, over a domain, to two independent facts: the
  integer `n - j` is nonzero in `K`, and `p₁^{n-j-1} ≠ 0`; the first is the characteristic condition
  and the second is `MvPolynomial.X_ne_zero`.

  What is left for `AlgebraicIndependent K (c_0, …, c_{n-1})` is the bookkeeping of the induction:
  the subalgebra generated by `c_0, …, c_{j-1}` is contained in `supported K {i | i < j}`, so
  transcendence over the latter restricts to transcendence over the former, and
  `AlgebraicIndependent.option_iff_transcendental` then extends the family by one element at each
  step.

- 2026-08-02 — **`(10)` proved: the coefficients `c_0, …, c_{n-1}` are algebraically independent.**
  `formal/GaloisForLFunctions/HTGeometry/TriangularIndependence.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  transcendental_paramCoeff_zero :  0 < n → Transcendental (supported F ∅) c_0
  algebraicIndependent_paramCoeff :
    0 < n → (∀ 0 < j < n, (n - j : F) ≠ 0) →
    ∀ m ≤ n, AlgebraicIndependent F (fun j : Fin m => c_j)
  ```

  At `m = n` this is the card's assertion that `c_0, …, c_{n-1}` are algebraically independent, which
  `(10)` uses to identify `E_0 = K(q, c_0, …, c_{n-1})` as a rational function field of the right
  transcendence degree.

  The induction adds one coefficient at a time: the subalgebra generated by `c_0, …, c_{m-1}` sits
  inside the polynomials supported on the first `m` parameters, so `Transcendental.of_tower_top_of_
  subalgebra_le` restricts the transcendence of `c_m` proved in the previous entry, and
  `AlgebraicIndependent.option_iff_transcendental` extends the family; the index type is moved from
  `Option (Fin m)` to `Fin (m+1)` along `finSuccEquivLast`, which sends the last index to the new
  element.  The base case `c_0 = p₁^n` is transcendental over the constants because `X^n` is
  transcendental over `F` and a variable is transcendental over the empty support.

  Hypotheses: a field is needed only for the empty-family base case of mathlib's
  `algebraicIndependent_empty_type`; everything else runs over a commutative domain.  The
  characteristic enters solely as `(n - j : F) ≠ 0`.

  This closes `(6)`--`(10)`.  What remains on the card is the Galois group of the universal centred
  polynomial and the Kummer base change, both classical and both absent from mathlib.

- 2026-08-02 — **First step toward the universal polynomial's Galois group: the permutation action.**
  `formal/GaloisForLFunctions/HTGeometry/PermutationAction.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  permMulSemiringAction :  MulSemiringAction (Equiv.Perm σ) (MvPolynomial σ R)
  permFaithfulSMul      :  the action is faithful when R is nontrivial
  mem_symmetricSubalgebra_iff_smul_eq : symmetric ↔ fixed by the action
  ```

  Mathlib defines a symmetric polynomial as one invariant under `rename` by every permutation and
  builds `symmetricSubalgebra` from that, but never records that this is a **group action** — so the
  symmetric polynomials are not available as the fixed points of anything.  They are now, and the
  action is faithful, which is the hypothesis that Artin's theorem needs.

  Why this is the right first step for `(11)`: mathlib has `IsGalois (FixedPoints.subfield G E) E`
  for a faithful finite group action on a field, and it has the fundamental theorem of symmetric
  polynomials.  Composing them gives the Galois group of the universal polynomial as `S_{n+1}` — the
  card's `(11)` — but neither is usable until the permutation action exists as an instance.  What
  remains for that composition is to extend the action from the polynomial ring to its fraction
  field and to identify the fixed field with the rational functions in the elementary symmetric
  polynomials.

- 2026-08-02 — **The universal polynomial's Galois setting, formalized.**
  `formal/GaloisForLFunctions/HTGeometry/PermutationAction.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  permFractionAction        :  S_m acts on the field of rational functions in m variables
  permFractionFaithful      :  faithfully
  isGalois_symmetricFixedField :
    IsGalois (FixedPoints.subfield (Perm (Fin m)) (FractionRing (MvPolynomial (Fin m) K)))
             (FractionRing (MvPolynomial (Fin m) K))
  ```

  The field of rational functions in `m` variables is Galois over its symmetric part, with `S_m`
  acting.  This is the Galois setting of `(11)`: the generic polynomial of degree `m` splits there,
  and its group is the full symmetric group.

  Once the action existed as an instance (previous entry), the extension to the fraction field was
  mathlib's `IsFractionRing.mulSemiringAction` and the Galois conclusion was `inferInstance` —
  Artin's theorem, already present, applies the moment the action is faithful.  The only friction was
  that mathlib states the compatibility `SMulDistribClass` under a `letI` of the very action being
  defined, so it has to be re-registered as a local instance before faithfulness can be transported
  from the polynomial ring to its fraction field.

  What remains between this and `(11)` as the card states it: identifying the fixed field with the
  rational functions in the elementary symmetric polynomials — mathlib's fundamental theorem of
  symmetric polynomials, extended from polynomials to fractions — and then matching the card's
  centred polynomial `(7)` with the universal one by the translation that removes the
  next-to-leading coefficient, which `coeff_oneDeepEquation_next` has already shown to be absent.

- 2026-08-02 — **The Galois group of the generic degree-`m` extension is `S_m`, with degree `m!`.**
  `formal/GaloisForLFunctions/HTGeometry/PermutationAction.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  finrank_over_symmetricFixedField :
    finrank (fixed field of S_m) (rational functions in m variables) = m !
  symmetricGaloisEquiv :
    Equiv.Perm (Fin m) ≃ (L →ₐ[L^{S_m}] L)
  ```

  So the extension has degree `m!` and its automorphism group is the symmetric group itself, not
  merely a group of that order — the content of the card's `(11)` for the universal polynomial,
  modulo naming the base field as the rational functions in the elementary symmetric polynomials.

  Both follow from mathlib's `FixedPoints.finrank_eq_card` and `FixedPoints.toAlgHomEquiv` once the
  action is faithful, which the previous two entries supplied; the degree computation is then
  `Fintype.card_perm` and `Fintype.card_fin`.

  Remaining for `(11)` as the card phrases it: the fixed field is `K(e_1, …, e_m)`, which is the
  fundamental theorem of symmetric polynomials transported to fractions — mathlib has the polynomial
  form in `RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean`, and what is missing is only
  the passage to the fraction field.

- 2026-08-02 — **Fixed fractions are fractions of invariants.**
  `formal/GaloisForLFunctions/HTGeometry/InvariantFractions.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  smul_algebraMap_eq    :  g • algebraMap r = algebraMap (g • r)
  prod_smul_invariant   :  ∏_{g ∈ G} g • q is invariant
  prod_smul_ne_zero     :  and nonzero when q is
  exists_invariant_ratio:  x fixed by G  →  x = a / b with a, b invariant in the base
  ```

  For a finite group acting by ring automorphisms on a domain, every element of the fraction field
  fixed by the group is a ratio of **invariant** elements of the base.  This is the missing step
  between the fixed field and the invariant subring, and mathlib does not have it.

  The proof is the classical one: multiply numerator and denominator by the other translates of the
  denominator.  The denominator becomes `∏_{g ∈ G} g • q`, invariant by reindexing the product along
  left translation, and nonzero because the base is a domain; the numerator is then forced to be
  invariant, not by a combinatorial argument but because it equals `x · b` in the fraction field,
  where both factors are fixed, and the embedding of the base is injective and equivariant.

  Applied to the symmetric group acting on rational functions, this says the fixed field is the
  fraction field of the symmetric polynomials, which mathlib's fundamental theorem identifies with a
  polynomial ring in the elementary symmetric polynomials — the last step in naming the base field of
  `(11)`.

- 2026-08-02 — **The fixed field is the field of symmetric rational functions.**
  `formal/GaloisForLFunctions/HTGeometry/PermutationAction.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  smul_eq_self_iff_ratio_isSymmetric :
    (∀ g : S_m, g • x = x)  ↔  ∃ a b symmetric, b ≠ 0 ∧ x = a / b
  ```

  Both directions.  Forward is the previous entry's `exists_invariant_ratio` together with the
  identification of invariance under the action with `MvPolynomial.IsSymmetric`, which is `rfl`;
  backward is that a ratio of symmetric polynomials is fixed, via `map_div₀` for the ring
  automorphism the action supplies.

  So the base field of `(11)` is named: the Galois extension
  `L / L^{S_m}` of degree `m!` recorded two entries ago has for its base exactly the symmetric
  rational functions in `m` variables.  Together with mathlib's fundamental theorem of symmetric
  polynomials — `symmetricSubalgebra` is a polynomial ring in `e_1, …, e_m` — this is the classical
  statement the card cites: the generic polynomial of degree `m` has Galois group `S_m` over the field
  generated by its coefficients.

  What is left of the card is `(12)`, the Kummer base change: that adjoining `p₁` with `p₁^n = ±c_0`
  does not shrink the group, which the card reduces to the discriminant not being a square.

- 2026-08-02 — **The group-theoretic core of `(12)`: abelian quotients of `S_k` factor through the
  sign.**  `formal/GaloisForLFunctions/HTGeometry/AbelianQuotientOfPerm.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  eq_one_of_isThreeCycle  :  φ : S_α →* H abelian  →  φ kills every three-cycle
  alternatingGroup_le_ker :  alternatingGroup α ≤ φ.ker
  ```

  So every homomorphism from a symmetric group to an abelian group factors through `S_α / A_α`, which
  has order two.  This is the card's sentence "the only possible nontrivial cyclic quotient is the
  sign quotient of order two", proved rather than asserted, and it is what forces the intersection
  `E ∩ M` of `(12)` to be either `E_0` or the quadratic subfield cut out by the discriminant.

  The proof avoids any decomposition of a three-cycle into transpositions.  A three-cycle is
  conjugate to its inverse — same cycle type — so in an abelian quotient its image equals its own
  inverse and therefore squares to one; its order also divides three; and an element whose order
  divides both two and three is trivial.  Mathlib's `closure_three_cycles_eq_alternating` then
  upgrades this from three-cycles to the whole alternating group.

  Remaining on the card: that the discriminant of `(7)` is not a square in `K(p₁,…,p_n,q)`, which is
  the other half of `(12)` and is a statement about the reducedness of the universal discriminant
  divisor pulled back along the étale map whose Jacobian was computed earlier.

- 2026-08-02 — **The alternating fixed field, and its degree.**
  `formal/GaloisForLFunctions/HTGeometry/AlternatingFixedField.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  card_alternatingGroup_mul_two            :  2 ≤ m → |A_m| * 2 = m !
  finrank_over_alternatingFixedField_mul_two :
    2 ≤ m → finrank (L^{A_m}) L * 2 = m !
  ```

  With `finrank_over_symmetricFixedField` (`= m !`) this says the alternating fixed field sits
  halfway: `[L : L^{A_m}] = m !/2` against `[L : L^{S_m}] = m !`.  That halfway field is the one
  generated by a square root of the discriminant, and the previous entry's
  `alternatingGroup_le_ker` says it is the *only* proper subfield a cyclic base change could meet —
  which is what `(12)` has to exclude.

  A Lean note worth recording.  The obstruction for most of this turn was self-inflicted: I declared
  a `MulSemiringAction` for the alternating group by restricting the symmetric one along the subgroup
  inclusion.  Mathlib already derives that action, and its faithfulness, canonically; the custom
  instance shadowed the canonical path, so `FaithfulSMul` was provable in isolation by `inferInstance`
  yet unavailable to `FixedPoints.finrank_eq_card`, which had resolved the action differently.
  Deleting the instance made the whole file compile unchanged.  **Do not re-declare a subgroup's
  action when the group already acts.**

- 2026-08-02 — **The discriminant subfield is quadratic.**
  `formal/GaloisForLFunctions/HTGeometry/AlternatingFixedField.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  finrank_alternating_over_symmetric :  2 ≤ m →  [L^{A_m} : L^{S_m}] = 2
  ```

  The alternating fixed field is a **quadratic** extension of the symmetric one — the subfield
  generated by a square root of the discriminant.  It follows from the two degree computations of the
  previous entry through the tower `L^{S_m} ⊆ L^{A_m} ⊆ L`: the outer degree is `m !`, the inner
  `m !/2`, so the middle is `2`.

  The statement takes the algebra structure on the inclusion of fixed fields as an instance
  hypothesis rather than fixing one, which keeps it unconditional and avoids adding a redundant
  instance — the mistake diagnosed in the previous entry.

  With this, `(12)`'s two halves are formal in the following sense: any cyclic base change meets the
  splitting field in a subfield whose group is an abelian quotient of `S_{n+1}`
  (`alternatingGroup_le_ker`), hence in `E_0` or in this unique quadratic subfield; so the base change
  preserves the full symmetric group exactly when the discriminant is not a square.  What is still
  missing is that last nonsquareness for the card's specific discriminant, which the card derives
  from reducedness of the universal discriminant divisor under an étale pullback.

- 2026-08-02 — **`(12)` for odd `n`, unconditionally — no discriminant needed.**
  `formal/GaloisForLFunctions/HTGeometry/AbelianQuotientOfPerm.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  alternatingGroup_le_of_isCyclic_quotient   :  N ⊴ S_α, S_α/N cyclic  →  A_α ≤ N
  index_dvd_two_of_isCyclic_quotient         :  … →  N.index ∣ 2
  eq_top_of_isCyclic_quotient_of_odd_index   :  … and N.index odd  →  N = ⊤
  ```

  The last is `(12)` for odd `n`: the Kummer base change `(10)` is cyclic of degree `n`, so the
  subgroup it cuts out has cyclic quotient and index dividing `n`; if `n` is odd the index also
  divides `2`, hence is `1`, and the symmetric group survives **without any discriminant argument at
  all**.

  So the card's appeal to reducedness of the universal discriminant divisor under an étale pullback
  is needed only for even `n`.  For odd `n` — which includes `n = 1`, the case the card treats
  separately, and every other odd rank — `(3)` now follows from what is formalized here plus `(11)`.

  For even `n` the remaining gap is exactly one statement: that the discriminant of `(7)` is not a
  square in `K(p₁, …, p_n, q)`.  Everything else in `(12)` is proved: the intersection is a cyclic
  quotient of `S_{n+1}`, hence trivial or the unique quadratic subfield
  (`finrank_alternating_over_symmetric`), and the discriminant is what distinguishes the two.

- 2026-08-02 — **The arithmetic step of `(12)` for even `n`, and an elementary replacement for the
  étale argument.**  `formal/GaloisForLFunctions/HTGeometry/PrimeNonSquare.lean`, axioms
  `[propext]` for the first, `[propext, Classical.choice, Quot.sound]` for the second:

  ```text
  not_isSquare_of_prime_of_not_dvd :  p prime, p ∤ a  →  ¬ IsSquare (p * a)
  not_X_dvd_of_aeval_ne_zero       :  setting X i to 0 does not kill f  →  X i ∤ f
  ```

  The first is axiom-light — it needs only `propext` — and is the whole arithmetic content of the
  even-`n` case: over `E_0 = K(q, c_0, …, c_{n-1})` the discriminant `Δ` is a square in the Kummer
  extension `M` exactly when `Δ · c_0` is a square in `E_0`, and `c_0` is prime there, so this fails
  as soon as `c_0 ∤ Δ`.

  This replaces the card's appeal to reducedness of the universal discriminant divisor under an étale
  pullback by something elementary and checkable: by `not_X_dvd_of_aeval_ne_zero`, `c_0 ∤ Δ` follows
  from `Δ` not vanishing identically when `c_0 = 0` — and at `c_0 = 0` the polynomial `(7)` becomes
  `a · (q a^n - c_{n-1} a^{n-1} - ⋯ - c_1)`, whose second factor has nonzero constant term `-c_1`, so
  `0` is a simple root and the discriminant does not vanish.

  What is left is exactly that one evaluation: `Δ|_{c_0 = 0} ≠ 0`.  It is a statement about mathlib's
  `Polynomial.discriminant` of an explicit polynomial, with no geometry in it — the étale and
  reducedness language of the card is not needed on this route.

- 2026-08-02 — **The nonvanishing witness for `(12)`.**
  `formal/GaloisForLFunctions/HTGeometry/PrimeNonSquare.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  separable_X_pow_succ_sub_X :  n ≠ 0, (n : K) ≠ 0  →  Separable (X^{n+1} - X)
  ```

  Setting the first coefficient to zero and specialising the rest to `q = 1`, `c_1 = 1`, the others
  zero, the fibre equation `(7)` becomes `X^{n+1} - X`.  It is separable: it factors as
  `X · (X^n - 1)`, the first factor is separable, the second is separable because `n` is invertible,
  and the two are coprime because `X^m · X - (X^{m+1} - 1) = 1`.  So the origin, which acquires a root
  when `c_0 = 0`, is a **simple** root, and the discriminant survives the specialisation.

  That is the last mathematical input of `(12)`: the discriminant does not vanish identically at
  `c_0 = 0`, hence `c_0` does not divide it, hence `Δ · c_0` is not a square
  (`not_isSquare_of_prime_of_not_dvd`), hence the Kummer base change does not meet the quadratic
  subfield and the symmetric group survives.

  Every step of the card's `(6)`--`(12)` is now formal except the plumbing that connects mathlib's
  `Polynomial.discriminant` of the explicit family to these facts — the specialisation homomorphism on
  the coefficient ring.  No mathematical content of the card remains unproved on this route, and the
  étale-pullback argument the card gives has been replaced throughout by elementary algebra.

- 2026-08-02 — **Separable implies nonzero discriminant, closing the chain of `(12)`.**
  `formal/GaloisForLFunctions/HTGeometry/PrimeNonSquare.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  discr_ne_zero_of_separable :  0 < deg f, f separable  →  discr f ≠ 0
  ```

  over a field of characteristic zero.  Mathlib defines `Polynomial.discr` and gives closed formulas
  in degrees at most three, but does not state the separability criterion; it follows from
  `resultant_deriv`, which expresses the resultant of `f` and `f'` as a signed multiple of
  `leadingCoeff · discr`, together with `resultant_eq_zero_iff`.  The degree bookkeeping is where
  characteristic zero enters: `natDegree f' = natDegree f - 1` is needed for the two resultants to be
  the same one.

  Combined with the previous entry this gives the specialised nonvanishing outright: `X^{n+1} - X` is
  separable, hence its discriminant is nonzero, hence the discriminant of `(7)` does not vanish
  identically at `c_0 = 0`.

  The chain of `(12)` is now complete as a chain of proved statements:

  ```text
  X^{n+1} - X separable  →  discr ≠ 0 at the specialisation  →  c_0 ∤ Δ
    →  Δ · c_0 not a square  →  the Kummer base change misses the quadratic subfield
    →  the symmetric group survives.
  ```

  What is not formalized is only the identification of the card's family with the specialisation —
  that the discriminant of `(7)`, evaluated at `c_0 = 0, q = 1, c_1 = 1, c_2 = ⋯ = 0`, is the
  discriminant of `X^{n+1} - X`.  That is a computation in the coefficient ring, not a further
  mathematical input.

- 2026-08-02 — **The specialisation step: the discriminant commutes with degree-preserving
  specialisation.**  `formal/GaloisForLFunctions/HTGeometry/PrimeNonSquare.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  discr_map :  0 < deg f, (f.map φ).natDegree = f.natDegree, φ (leadingCoeff f) ≠ 0
               →  discr (f.map φ) = φ (discr f)
  ```

  Mathlib has `sylvester_map_map` and `resultant_map_map` but no discriminant version; proving it
  through the matrix would require transporting along an equality of index types, since
  `sylvesterDeriv` is indexed by the degree.  Going through `resultant_deriv` avoids that entirely:
  both sides are read off the same resultant, and the factor `(-1)^e · φ(leadingCoeff)` cancels
  because the target is a domain and the leading coefficient survives.

  This is the last piece of `(12)`.  The chain is now:

  ```text
  discr_map                    -- specialising the family commutes with the discriminant
  separable_X_pow_succ_sub_X   -- the specialised polynomial is separable
  discr_ne_zero_of_separable   -- so its discriminant is nonzero
  not_X_dvd_of_aeval_ne_zero   -- so c_0 does not divide Δ
  not_isSquare_of_prime_of_not_dvd  -- so Δ · c_0 is not a square
  alternatingGroup_le_of_isCyclic_quotient, finrank_alternating_over_symmetric
                               -- so the cyclic base change misses the only candidate subfield
  ```

  every link of which is proved.  What is left is bookkeeping with no mathematical content: writing
  the card's family `(7)` as a polynomial over `K[q, c]`, checking that the specialisation
  `c_0 ↦ 0, q ↦ 1, c_1 ↦ 1, c_j ↦ 0` sends it to `X^{n+1} - X` and preserves the degree, and chaining
  the six lemmas above.

- 2026-08-02 — **The family `(7)` itself, and its specialisation.**
  `formal/GaloisForLFunctions/HTGeometry/FibreFamilyDiscriminant.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  fibreFamily K n        :  q a^{n+1} - ∑_{j<n} c_j a^j,  with indeterminate coefficients
  natDegree_fibreFamily  :  its degree is n + 1
  leadingCoeff_fibreFamily : its leading coefficient is q
  map_fibreFamily        :  2 ≤ n →  its specialisation at q = 1, c_1 = 1, rest 0  is  X^{n+1} - X
  ```

  The card's equation `(7)` is now a Lean object rather than a description, with the two facts the
  discriminant argument needs about it — degree and leading coefficient — and the specialisation
  identified explicitly.  `2 ≤ n` is what keeps the index `1` distinct from the index `n` carrying the
  leading coefficient; the excluded case `n = 1` is the one the card treats separately, and it is
  also covered by the parity argument, since `1` is odd.

  With `discr_map`, `separable_X_pow_succ_sub_X` and `discr_ne_zero_of_separable` from the previous
  entries, the specialised discriminant is nonzero and the specialisation preserves degree and
  leading coefficient — so `c_0` does not divide the discriminant of `(7)`.  Assembling those three
  into that single statement, and then into the non-squareness of `Δ · c_0`, is what remains.

- 2026-08-02 — **`(12)` assembled: the discriminant of `(7)` is not a square after the Kummer base
  change.**  `formal/GaloisForLFunctions/HTGeometry/FibreFamilyDiscriminant.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  not_X_zero_dvd_discr_fibreFamily :  2 ≤ n  →  c_0 ∤ discr (fibreFamily F n)
  not_isSquare_X_zero_mul_discr    :  2 ≤ n  →  ¬ IsSquare (c_0 · discr (fibreFamily F n))
  ```

  over a field of characteristic zero.  The chain runs exactly as designed: the specialisation sends
  `(7)` to `X^{n+1} - X` and preserves degree and leading coefficient, that polynomial is separable,
  so its discriminant is nonzero, so `discr_map` makes the specialised discriminant of `(7)` nonzero,
  so the specialisation — which kills `c_0` — witnesses that `c_0` does not divide it, and `c_0` is
  prime, so `c_0 · Δ` is not a square.

  This is the statement the card derives from reducedness of the universal discriminant divisor under
  an étale pullback.  It is now proved by elementary algebra, with the étale language nowhere in the
  argument.

  **Status of the card.**  `(6)`--`(12)` are formalized:  the triangular coefficient law and its
  Jacobian, the algebraic independence of the coefficients, the Galois group of the universal
  polynomial as the symmetric group over the symmetric rational functions, the fact that abelian
  quotients of a symmetric group factor through the sign, the quadratic discriminant subfield, and
  now the non-squareness that excludes it.  What is not formalized is the passage between the card's
  field-theoretic phrasing of `(12)` — intersections of splitting fields inside a Kummer extension —
  and the group- and ring-theoretic statements above; the mathematics of every step is proved.

- 2026-08-02 — **The discriminant of the generic polynomial, and its symmetry.**
  `formal/GaloisForLFunctions/HTGeometry/PermutationAction.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  discrProd K m           :  ∏_{i ≠ j} (x_i - x_j),  the discriminant of the generic polynomial
  isSymmetric_discrProd   :  it is a symmetric polynomial
  ```

  The discriminant of the polynomial whose roots are the variables is symmetric, hence lies in the
  base field of the Galois extension `L / L^{S_m}` — which is where the card's `(12)` needs it, since
  the question is whether it is a *square* there.

  The proof is a reindexing: a permutation carries the set of ordered pairs of distinct indices
  bijectively to itself, and the factor attached to a pair is carried to the factor attached to its
  image.  Mathlib has neither this polynomial nor its symmetry — the symmetric-function files stop at
  the elementary symmetric polynomials and Newton's identities, and the Galois-group file does not
  mention discriminants at all.

  This is the object that identifies the quadratic subfield `L^{A_m}` concretely: its square root is
  the alternating product, fixed by even permutations and negated by odd ones.  Proving that sign law
  is the remaining dictionary entry between the group-theoretic side of `(12)`, which is complete,
  and the ring-theoretic non-squareness, which is also complete.

- 2026-08-02 — **The generic polynomial is separable.**
  `formal/GaloisForLFunctions/HTGeometry/PermutationAction.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  discrProd_ne_zero :  the discriminant of the generic polynomial is nonzero
  ```

  over any domain: it is a product of differences of distinct variables, each nonzero because `X` is
  injective.  This is the separability the Galois setting of `(11)` presupposes — the generic
  polynomial has distinct roots because its roots are independent variables.

  **The one remaining dictionary entry, scoped honestly.**  What is left between the two completed
  halves of `(12)` is the sign law: that the alternating product `∏_{i<j}(x_j - x_i)`, whose square is
  the discriminant, is fixed by even permutations and negated by odd ones.  That is what identifies
  the quadratic subfield `L^{A_m}` — whose existence and degree are already proved — as the one
  generated by a square root of the discriminant, and it is what lets the ring-theoretic
  non-squareness proved earlier be read as a statement about that subfield.

  It is not a short step.  The transposition case requires partitioning the ordered pairs into those
  disjoint from the transposed indices, those meeting them in one index — which contribute sign
  changes in cancelling pairs — and the transposed pair itself, which contributes the single sign.
  Mathlib has no Vandermonde or alternating polynomial to build on.  Recording the estimate so the
  next attempt starts with the right expectation rather than the wrong one.

- 2026-08-02 — **The sign is the inversion count, and the Vandermonde product is defined.**
  `formal/GaloisForLFunctions/HTGeometry/PermutationAction.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  sign_eq_signAux :  sign σ = signAux σ,  for σ a permutation of Fin n
  vandermonde K n :  ∏_{j < i} (x_i - x_j)
  ```

  Mathlib defines `signAux σ` as the product over pairs `j < i` of `-1` when `σ` inverts the pair,
  and defines `sign` by a different route through lists and multisets; the two are never stated to
  agree.  They do, and the proof is four lines by induction on transpositions, using that both are
  multiplicative and both send a transposition to `-1`.

  This reshapes the remaining step.  The sign law for the Vandermonde product no longer needs an
  induction on transpositions with its partition of pairs into cancelling families: it is a **single
  reindexing**, uniform in `σ`.  Renaming permutes the pairs, each factor picks up `-1` exactly when
  its pair is inverted, and the accumulated sign is `signAux σ` by definition — hence `sign σ` by the
  lemma above.  The previous entry's estimate of that step was pessimistic; with `signAux` as the
  target the combinatorics is already done inside mathlib.

- 2026-08-02 — **The reindexing bijection for the sign law.**
  `formal/GaloisForLFunctions/HTGeometry/PermutationAction.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  orderPair σ x         :  the pair (σ x.1, σ x.2), put back in decreasing order
  orderPair_mem         :  it maps the pairs of `finPairsLT` into themselves
  orderPair_orderPair   :  reordering by σ then by σ⁻¹ is the identity
  ```

  This is the bijection the sign law reindexes along, with the involution property that makes it
  bijective.  Both proofs are case splits on whether `σ` inverts the pair; the inverse case needs only
  that `<` is asymmetric, since a permutation cannot identify the two entries of a pair with distinct
  entries.

  What remains for the sign law is the per-factor computation — `X (σ x.1) - X (σ x.2)` equals
  `±(X (orderPair σ x).1 - X (orderPair σ x).2)` with the sign that `signAux` attaches to the pair —
  and then `Finset.prod_mul_distrib` with `Finset.prod_nbij'` along `orderPair`.  No further
  combinatorics: the inversion count is `signAux` by definition, and `signAux` is `sign` by the
  previous entry.

- 2026-08-02 — **The sign law is proved.**
  `formal/GaloisForLFunctions/HTGeometry/PermutationAction.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  prod_sign_cast     :  ∏ over pairs of the inversion signs = sign σ, in any commutative ring
  rename_vandermonde :  rename σ (vandermonde K n) = (sign σ) · vandermonde K n
  ```

  The Vandermonde product is fixed by the even permutations and negated by the odd ones.  This is the
  last dictionary entry of `(12)`: it identifies the quadratic subfield `L^{A_m}` — whose existence
  and degree were proved earlier — as the one generated by a square root of the discriminant, since
  the Vandermonde product is exactly that square root and `A_m` is exactly its stabiliser.

  The proof is one reindexing, as the reshaped plan predicted: each factor picks up `-1` exactly when
  its pair is inverted, `Finset.prod_mul_distrib` separates the signs from the reordered factors,
  `Finset.prod_nbij'` along `orderPair` restores the product, and the accumulated sign is `signAux σ`
  by definition, hence `sign σ`.  Two turns ago this looked like 150 lines of new combinatorics; it is
  twenty, because mathlib's `signAux` had already done the counting and only needed to be connected
  to `sign`.

  **`(6)`--`(12)` are now formalized end to end.**  Coefficient law, Jacobian, algebraic independence,
  the symmetric Galois group of the universal polynomial and its base field, abelian quotients
  factoring through the sign, the quadratic discriminant subfield with its degree and its generator,
  and the non-squareness that excludes it in the Kummer base change.

- 2026-08-02 — **The discriminant subfield, generated.**
  `formal/GaloisForLFunctions/HTGeometry/PermutationAction.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  vandermonde_ne_zero                    :  the Vandermonde product is nonzero over a domain
  rename_vandermonde_of_mem_alternating  :  it is fixed by every even permutation
  isSymmetric_vandermonde_sq             :  its square is symmetric
  not_isSymmetric_vandermonde            :  2 ≤ n, char ≠ 2  →  it is not itself symmetric
  ```

  Together these say the Vandermonde product lies in the alternating fixed field and not in the
  symmetric one, while its square lies in the symmetric one — so it generates the quadratic extension
  `L^{A_m} / L^{S_m}` and is a square root of the discriminant.  With
  `finrank_alternating_over_symmetric` giving that degree as exactly two, the discriminant subfield is
  now both located and generated.

  The non-symmetry is where the characteristic matters and it enters cleanly: a transposition negates
  the product, so if it were symmetric then twice it would vanish, and over a domain of characteristic
  other than two that forces the product itself to vanish, which it does not.

  This completes the identification the card's `(12)` needs.  Every statement of `(6)`--`(12)` is now
  proved in Lean, over the hypotheses the card assumes and no others.

- 2026-08-02 — **The convolution recursion, and a rename in the shared tree.**
  `formal/GaloisForLFunctions/HTGeometry/TriangularTailCoefficients.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  coeff_triangularTailPoly_pow_succ :
    [t^j] R^{m+1} = ∑_{i + i' = j} p_{i+1} · [t^{i'}] R^m
  ```

  the convolution recursion for the coefficients of the powers of the tail.  It is the engine of every
  induction on the power, and it is what the remaining bridge `(5)` needs: the recursion defining the
  numerators of the truncated inverse has the same shape, so the two can be matched term by term.

  Noted while doing it: `tailPoly` and `coeff_tailPoly` in this module have been renamed to
  `triangularTailPoly` and `coeff_triangularTailPoly` by another agent working in the same tree.  All
  dependent modules — `TriangularIndependence`, `FibreFamilyDiscriminant` — still build, so the rename
  was carried through; this entry uses the current names.  Card entries above that quote the old names
  refer to the same objects.

- 2026-08-02 — **`(5)` is closed: the reciprocal jet *is* the triangular parameter change.**
  Two new results, both unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

  First, in `formal/GaloisForLFunctions/HTGeometry/InverseJetNumerator.lean`, the closed form of the
  numerators for a jet read off a single polynomial `T`:

  ```text
  coeff_invNumerator :
    [a^m] N_k = (-1)^(k-m) · [t^m] T^(k-m)          for all k, m
  ```

  This is the polynomial shadow of the geometric series `1/(1+T) = ∑ (-T)^e`, and it is stated with
  no side condition at all: for `m > k` both sides vanish, because truncated subtraction sends the
  exponent to zero and `[t^m] T^0 = 0`.  The proof is a strong induction on `k`; the step turns the
  defining convolution into the coefficient of one higher power of `T`, which is exactly what
  `coeff_triangularTailPoly_pow_succ` was built for.

  Second, in the new module `formal/GaloisForLFunctions/HTGeometry/ReciprocalParameterBridge.lean`
  (wired into the `HTGeometry` umbrella), the specialisation to the free parameters:

  ```text
  jetParam K n (i+1)              = p_{i+1}                     the free parameters
  coeff_invNumerator_jetParam :
    [a^j] N_n                     = (-1)^(n-j) · c_j            (5)
  paramCoeff_self :                 c_n = 0
  eval_invNumerator_jetParam :
    N_n(a)                        = ∑_{j<n} (-1)^(n-j) c_j a^j
  pow_mul_eq_paramCoeff_sum :
    a^{n+1} · g_n                 = ∑_{j<n} (-1)^(n-j) c_j a^j  (5) ∘ (6)
  ```

  The last one is the card's fibre equation with its coefficients named: the observed quantity
  `a^{n+1} g_n` is the value at the unknown constant term of a polynomial of degree `n` whose
  coefficients are exactly the `c_j` of `(9)`--`(10)`, which are triangular in and algebraically
  independent of the free jet parameters.  The bridge that the previous entry listed as the one
  remaining formal item is therefore closed, and the chain `(5)`--`(12)` is now continuous in Lean:
  the fibre equation, its coefficients, their independence, their triangular Jacobian, and the
  non-squareness of the discriminant that excludes the quadratic subfield.

- 2026-08-02 — **Umbrella collision cleared.**  Wiring `ReciprocalParameterBridge` into
  `GaloisForLFunctions.HTGeometry` exposed two duplicate top-level names between
  `PermutationAction` and the modules of the monodromy route: `perm_smul_X`
  (also in `SymmetricVariableAction`) and `symmetricGaloisEquiv` (also in
  `SymmetricRationalFunctions`).  A full duplicate-name scan over the whole `GaloisForLFunctions`
  tree found exactly those two.  Since the monodromy modules are the ones the theorem table above
  cites, the two declarations in `PermutationAction` were renamed to `perm_smul_X_mv` and
  `symmetricFixedFieldGaloisEquiv`; both were used only inside their own module.  The umbrella now
  builds clean: 12867 jobs, no errors.

- 2026-08-06 — **Verification pass, and a correction to this card's own text.**

  The capstones this card cites were re-checked against the repository, all unconditional:

  ```text
  centeredParameterMonodromy      [propext, Classical.choice, Quot.sound]
  centeredParameterMonodromyOdd   [propext, Classical.choice, Quot.sound]
  tailCenteredCoeffEquiv          [propext, Classical.choice, Quot.sound]
  tailParameterChange             [propext, Classical.choice, Quot.sound]
  ```

  **The "Formalisation route for the symmetric monodromy" section above is stale where it says
  "The remaining step is to identify the fixed field of that action with the field generated by
  the centered coefficients."**  That step is done: `CenteredRootFieldTop.lean` has
  `rootField_centeredMonicE_eq_top`, `centeredRootFieldEquiv` and `centeredRootFieldPermEquiv` —
  the Galois group of the centered polynomial is the symmetric group on its roots — with
  `CenteredGenericGalois.lean`, `CenteredCoeffFieldRational.lean` and
  `CenteredPartSplittingField.lean` completing the chain.  Anyone continuing should read the
  modules, not this section.

  The section's remaining purpose is the *sibling* card `projective-horizon-full-symmetric-
  monodromy`, whose open input is the classification of finite etale covers of
  `(G_m)^2 x A^(L-2)` as torus Kummer covers — not a field-theoretic step at all.

- 2026-08-07 — **Stage-3 audit complete.**  The exact theorem is represented without route
  assumptions by the following continuous Lean chain:

  - `pow_mul_eq_paramCoeff_sum` identifies the rank-one reciprocal fibre equation with the
    triangular coefficient polynomial;
  - `tailParameterChange`, `tailCenteredCoeffEquiv`, and `coe_tailCenteredCoeffEquiv` identify its
    algebraically independent parameter field with the universal centered coefficient field and
    its Kummer extension;
  - `centeredParameterMonodromy` and `centeredParameterMonodromyOdd` give the full symmetric group
    in the even and odd exponent cases, while `quadraticParameterMonodromy` closes `n = 1`;
  - `coeff_mul_pow_eq_tail_sum_reciprocal` and `criticalFibreSwap` formalize reciprocal duality.

  Foreground checks passed with `lake env lean` on every owning leaf.  Final batched module audit:

  ```text
  lake build GaloisForLFunctions.HTGeometry.ReciprocalParameterBridge \
    GaloisForLFunctions.HTGeometry.TailParameterChange \
    GaloisForLFunctions.HTGeometry.TailCenteredCoefficientMatch \
    GaloisForLFunctions.HTGeometry.CenteredParameterMonodromy \
    GaloisForLFunctions.HTGeometry.ReciprocalFiberEquation
  ```

  passed (`8800` jobs).  Scratch `#print axioms` for all capstones reports only `propext`,
  `Classical.choice`, and `Quot.sound`.  No `sorry`, `admit`, project axiom, `opaque`, or `unsafe`
  declaration is used.  Card promoted to Stage 3.
