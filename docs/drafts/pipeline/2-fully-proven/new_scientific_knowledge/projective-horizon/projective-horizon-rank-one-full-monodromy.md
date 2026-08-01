# Every rank-one projective horizon has full symmetric monodromy

- **ID:** `projective-horizon-rank-one-full-monodromy`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / GENERIC CRITICAL MONODROMY
- **Scientific status:** `[PROVED ON PAPER] [NOVELTY PROVISIONAL] [SIGNIFICANCE LIMITED]`
- **Formal status:** reciprocal coefficient and exact cotangent cores formalized
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

`ProjectiveHorizonExactLagrangian.lean` proves the exact reversed coefficient pairing and its
positive-degree vanishing under truncated inversion; these are the coefficient identities from
which `(5)--(7)` arise.  The triangular finite-cover and splitting-field argument are paper-level.
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

What remains is instantiation of this chain on the card's own base field and equation:
`polyBaseChangeEvenAssembledEquiv` and `polyBaseChangeOddAssembledEquiv` take exactly the card's own
data, and every one of their inputs is proved somewhere above.

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
