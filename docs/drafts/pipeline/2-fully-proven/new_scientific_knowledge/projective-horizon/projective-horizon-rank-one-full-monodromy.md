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

Thirty-three modules, all building with only `propext`, `Classical.choice`, `Quot.sound`:

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
SplittingFieldCompositum
```

Facts proved here that mathlib does not carry: the Galois group of the generic polynomial of degree
`d` over the field its coefficients generate is `S_d`; the same for the centered polynomial; the
fundamental theorem of symmetric rational functions; the commutator subgroup of a symmetric group is
its alternating group; the sign law for the Vandermonde product; natural irrationalities; and the
coefficientwise extension of a derivation to polynomials.

What remains is instantiation of this chain on the card's own base field and equation.

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
