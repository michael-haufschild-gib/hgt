# Projective-horizon ramification has one generically simple component

- **ID:** `projective-horizon-irreducible-simple-ramification`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / RAMIFICATION GEOMETRY
- **Scientific status:** `[PROVED ON PAPER] [BRIDGE]`
- **Parents:** `projective-horizon-rectangular-schur-caustic`,
  `hypertranscendental-horizon-q-system`
- **Lane:** source-pure hypertranscendental geometry; monodromy support

## Theorem

Let `m,n>=1`, `L=m+n`, and let `Phi_(m,n)` be the critical raw/reciprocal horizon map on the unit
jet chart over an algebraically closed characteristic-zero field.  Its ramification divisor is
geometrically irreducible and reduced.  At its generic point the differential has corank exactly
one and the Jacobian determinant vanishes to order one.

Equivalently, the critical cover has one ramification component and generic ramification index two.
This does not assert that only one ramification point lies over a generic branch value.

## Proof

Write `Y=y_0 Z`, with `Z(0)=1`, and `h_k=[t^k]Z^2`.  The prior caustic theorem identifies the
Jacobian determinant, up to the unit `(-1)^m y_0^(2m)`, with

```text
tau_(m,n)=s_((n^m))[h]
  =det(h_(n-i+j))_(1<=i,j<=m).                              (1)
```

The variables `h_1,...,h_(L-1)` are algebraically independent coordinates: if
`Z=1+sum_(k>0)z_k t^k`, then

```text
h_k=2z_k+polynomial(z_1,...,z_(k-1)),                       (2)
```

so characteristic zero makes `(2)` a triangular polynomial automorphism.

The Schur function in `(1)` is irreducible in the polynomial ring on the complete-homogeneous
generators used here.  One way to see this from the standard Schur irreducibility theorem is to
specialize the independent `h_k` to complete homogeneous functions in `N` variables, where
`N>=max(L-1,m+2)`.  Then `h_1,...,h_(L-1)` remain algebraically independent, while the rectangle
partition `(n^m,0,...,0)` has the Dvornicich--Zannier common-divisor invariant equal to one because
its padded exponent sequence contains consecutive tail integers, including `1` and `0`.  Their
theorem makes the resulting Schur polynomial irreducible.  Injectivity of the specialization on
`K[h_1,...,h_(L-1)]` proves irreducibility of `(1)`.

The triangular automorphism `(2)`, the reciprocal-jet birational involution, and localization at
`y_0` preserve irreducibility.  Therefore the ramification divisor in the unit source chart is
irreducible.  In characteristic zero an irreducible polynomial is square-free, so the divisor is
reduced and generically smooth.

If the critical Jacobian had corank at least two at its generic ramification point, every
`(m-1) x (m-1)` cofactor would vanish there.  Every first derivative of its determinant would then
vanish, contradicting generic smoothness of `(1)`.  Thus the generic corank is one.  Reducedness
means the Jacobian determinant has valuation one along the divisor, which is generic simple
ramification.  `QED`

## Monodromy consequence and remaining obstruction

A meridian about the branch image acts as a product of disjoint transpositions, and all generic
ramification points belong to one irreducible family.  Full symmetric monodromy would follow if the
ramification divisor mapped generically one-to-one to its branch image, or from a separate
primitivity/two-transitivity theorem.

That degree is not proved here.  If several points of the irreducible ramification divisor lie over
one generic branch value, the meridian is a product of several transpositions and can preserve a
block system.  The exact remaining core is therefore the degree of

```text
Ram(Phi_(m,n)) -> Branch(Phi_(m,n)).                         (3)
```

## Novelty audit

Jacobi--Trudi and irreducibility results for Schur polynomials are classical; in particular,
Dvornicich and Zannier study irreducibility of Schur polynomials in
*Newton functions generating symmetric fields and irreducibility of Schur polynomials*, Advances
in Mathematics 222 (2009).  Generic smoothness and the cofactor criterion are also classical.

The application closes two concrete geometric steps for this horizon cover, but it is a
parent-theory bridge and is not classified as new scientific knowledge.  The potentially new
result remains the monodromy or the discovery of its invariant correspondence.

## RH impact

The single ramification component gives no Euler orientation and remains target-translation blind.
It has no RH consequence.  An arithmetic use would require the zeta source to distinguish a real
or signed cycle inside this otherwise generic irreducible divisor.

## Formal status

The exact determinant and its Q-system engine are formalized in the adjacent Lean modules.  The
general Schur irreducibility theorem is not present in this mathlib snapshot and is used at paper
level.  No new Lean claim is attached to this bridge card.

