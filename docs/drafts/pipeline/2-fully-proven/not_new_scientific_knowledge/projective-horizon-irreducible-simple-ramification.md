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


## Log

- 2026-08-01 — **Step `(2)` is formalized: the coefficients of the squared jet are free coordinates.**
  `formal/GaloisForLFunctions/HTGeometry/SquaredJetCoefficientIndependence.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `jetZero_pderiv_sqJetCoeff` — at the origin the derivative of `h_m = [t^m](Z^2)` in the `j`-th jet
  coefficient is `2` when `m = j+1` and `0` otherwise, which is `h_k = 2 z_k + polynomial(z_1,…,z_(k-1))`
  in the form the Jacobian criterion consumes;
  `det_sqJetJacobian_ne_zero` — the Jacobian specialises at the origin to `2` times the identity, so
  its determinant is `2^N`, nonzero in characteristic zero;
  `algebraicIndependent_sqJetFamily` — hence `h_1, …, h_N` are algebraically independent over the
  constants, so the passage from the jet coefficients to the coefficients of the square is a
  triangular polynomial automorphism.

  This is the input the Schur irreducibility argument needs before specialising the `h_k` to complete
  homogeneous functions.  What stays paper-level on this card is the Dvornicich--Zannier
  irreducibility theorem for Schur polynomials itself, which has no mathlib counterpart.

  One cost note: the corpus Jacobian criterion reads its matrix as `D i (g j) = M i j` — derivative
  in direction `i` of the `j`-th family member.  Supplying the transpose makes the final application
  spin at `whnf` until the heartbeat limit rather than fail; with the indices in the criterion's
  order the file checks in seven seconds.

- 2026-08-01 — **First step toward the Schur irreducibility: the top variable occurs once.**
  `formal/GaloisForLFunctions/HTGeometry/RectangularSchurTopEntry.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `rectangularSchurToeplitz_corner` — the bottom-left entry of the rectangular Jacobi--Trudi matrix
  is `h_(n+m-1)`; `rectangularSchurToeplitz_index_eq_top` and
  `rectangularSchurToeplitz_index_lt_top` — that index is attained **only** there, every other entry
  carrying a strictly smaller one.

  Consequence, and the reason to record it: `tau_(m,n)` is of degree one in `h_(n+m-1)`, with the
  complementary minor as its leading coefficient.  So irreducibility reduces to that minor being
  coprime to the remainder, which is the shape any proof must take — including the one through the
  Dvornicich--Zannier theorem the card currently cites, which has no mathlib counterpart.

  Together with `algebraicIndependent_sqJetFamily` this leaves the card's irreducibility step with a
  precise formal target rather than an external citation: the coprimality of the corner minor with
  the rest of the expansion.

- 2026-08-01 — **The degree-one bound is proved in general.**
  `formal/GaloisForLFunctions/HTGeometry/DeterminantDegreeOne.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `degreeOf_det_le_one_of_unique_entry` — if a variable occurs to degree at most one in a single
  entry of a matrix over a polynomial ring and not at all in the others, the determinant has degree
  at most one in it.  The proof is the permutation expansion: each term takes one entry from each
  column, so at most one factor of each term can carry the variable.

  With `rectangularSchurToeplitz_index_lt_top` — the corner is the only entry carrying `h_(n+m-1)` —
  this makes `tau_(m,n)` a polynomial of degree at most one in that variable, over any coefficient
  ring.  Combined with `algebraicIndependent_sqJetFamily`, the irreducibility statement of this card
  is now reduced to a single self-contained algebraic target: that the coefficient of `h_(n+m-1)`,
  the complementary minor, is coprime to the remaining term.

- 2026-08-01 — **The corner expansion is proved: `det = ± X_s · minor + B` with `B` free of `X_s`.**
  `formal/GaloisForLFunctions/HTGeometry/DeterminantDegreeOne.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `degreeOf_det_eq_zero` — a determinant whose entries are free of a variable is free of it;
  `det_eq_corner_mul_minor_add` — if a variable occupies the entry `(r_0, 0)` and no other, then
  expanding along the first column gives

  ```text
  det M = (-1)^r_0 * X_s * det (minor at r_0) + B,     B free of X_s.
  ```

  The minors are free of the variable because they omit column zero, which is where it sits; the
  other first-column entries are free of it by hypothesis.

  Applied to the rectangular Jacobi--Trudi matrix through `rectangularSchurToeplitz_corner`, this is
  the exact statement `tau_(m,n) = ± h_(n+m-1) * tau_(m-1,n) + B`.  Irreducibility of `tau_(m,n)` is
  therefore equivalent to `tau_(m-1,n)` and `B` having no common factor — a statement about two
  explicit determinants in free variables, with no external citation left in it.

- 2026-08-01 — **The irreducibility criterion is proved.**
  `formal/GaloisForLFunctions/HTGeometry/LinearIrreducibleCriterion.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `isPrimitive_linear_of_isCoprime` — a linear polynomial whose two coefficients are coprime is
  primitive: a constant dividing it divides both coefficients, read off in degrees one and zero;
  `irreducible_linear_of_isCoprime` — over a unique factorisation domain such a polynomial with
  nonzero leading coefficient is **irreducible**, through Gauss's lemma
  (`IsPrimitive.irreducible_iff_irreducible_map_fraction_map`) and the fact that degree one already
  gives irreducibility over the fraction field.

  With `det_eq_corner_mul_minor_add`, the irreducibility of `tau_(m,n)` now follows from exactly one
  input: `tau_(m-1,n)` and the remainder `B` are coprime.  Everything else in the argument — the
  freeness of the coordinates, the location of the top variable, the degree bound, the expansion, and
  the passage from coprimality to irreducibility — is proved.

  The remaining coprimality is where the Dvornicich--Zannier theorem was doing its work; stated this
  way it is a question about two explicit determinants in independent variables, and it is the single
  open target of this card.

- 2026-08-01 — **The Jacobi--Trudi determinant does not vanish identically.**
  `rectangularSchurToeplitz_unit_tail` in
  `formal/GaloisForLFunctions/HTGeometry/RectangularSchurTopEntry.lean`, axioms `[propext, Quot.sound]`:
  setting the `n`-th complete homogeneous coefficient to one and all others to zero turns the
  rectangular Toeplitz section into the **identity matrix**, since `n + r - i = n` holds exactly when
  `i = r` in the admissible range.

  So `tau_(m,n)` takes the value one at that point and is therefore a nonzero polynomial in the free
  coordinates — which is the `A ≠ 0` hypothesis of `irreducible_linear_of_isCoprime`, and equally the
  nonvanishing of every corner cofactor, since those are again rectangular sections.

  The irreducibility of `tau_(m,n)` is now reduced to the coprimality of the corner cofactor with the
  remainder, with every other hypothesis of the criterion discharged.
