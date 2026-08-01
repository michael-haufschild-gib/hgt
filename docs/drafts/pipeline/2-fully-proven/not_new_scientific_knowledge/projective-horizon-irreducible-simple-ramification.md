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

- 2026-08-01 — **Correction of scope, and the divisibility criterion.**
  `formal/GaloisForLFunctions/HTGeometry/LinearIrreducibleCriterion.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  The first form of the criterion asked for `IsCoprime A B` — the Bezout condition `u A + v B = 1`.
  Over a polynomial ring in several variables that almost never holds, so as stated it could not have
  been applied to the Schur expansion.  `irreducible_linear_of_isUnit_gcd` replaces it by the correct
  hypothesis for a unique factorisation domain, `IsUnit (gcd A B)` — the two coefficients have no
  common factor — through `dvd_gcd` and `isUnit_of_dvd_unit`.  The `IsCoprime` version is kept, since
  it is the right one over a Bezout domain.

  `not_dvd_of_map_eq_zero_of_map_ne_zero` — a specialisation that kills the cofactor but not the
  remainder proves the cofactor does not divide the remainder.

  That fixes the shape of the remaining work: since the corner cofactor of the `(m,n)` rectangle is
  the `(m-1,n-1)` rectangle, an induction gives its irreducibility, and then `gcd` is a unit exactly
  when the cofactor does not divide the remainder — for which one explicit specialisation suffices.
  So the open target is now a single point of evaluation, not a general gcd computation.

- 2026-08-01 — **The criterion is transported to several variables.**
  `formal/GaloisForLFunctions/HTGeometry/MvLinearIrreducible.lean` and the gcd-free form in
  `LinearIrreducibleCriterion.lean`, axioms `[propext, Classical.choice, Quot.sound]`:

  `irreducible_linear_of_forall_isUnit` — the criterion with the only hypothesis a polynomial ring in
  several variables can supply: every common divisor of the two coefficients is a unit.  A chosen
  `gcd` is not available there, so the `GCDMonoid` structure is introduced inside the proof from
  unique factorisation;
  `finSuccEquiv_rename_succ` — peeling off the first variable sends a polynomial in the remaining
  ones to a constant, proved by induction on the polynomial;
  `irreducible_linear_in_X_zero` — hence `X_0 * A + B` with `A`, `B` in the remaining variables is
  **irreducible** as soon as `A ≠ 0` and the two have only unit common divisors.

  This is the criterion in the form the Schur expansion needs, since `tau_(m,n)` is exactly of that
  shape once the top variable is taken as the first one.  With the nonvanishing already proved, the
  card's irreducibility step is now one statement away: the corner cofactor and the remainder share
  no non-unit factor.

- 2026-08-01 — **The separating specialisation is found, and it closes the argument on paper.**
  `det_rectangularSchurToeplitz_shift_unit_tail` in `RectangularSchurTopEntry.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`: at the unit tail — the `n`-th coefficient one, all
  others zero — the section of shift `n-1` has a **vanishing first row**, because its indices never
  reach `n`, so its determinant is zero.

  Together with `rectangularSchurToeplitz_unit_tail`, which gives `tau_(m,n) = 1` at that same point,
  this is the separating specialisation the coprimality needs:

  ```text
  at the unit tail:   tau_(m,n) = 1,   corner cofactor tau_(m-1,n-1) = 0,   hence  B = 1.
  ```

  So the cofactor does not divide the remainder (`not_dvd_of_map_eq_zero_of_map_ne_zero`), and if the
  cofactor is irreducible then every common divisor of the two is a unit — which is exactly the
  hypothesis of `irreducible_linear_in_X_zero`.  Induction on `m` with base `tau_(1,n) = h_n`, a
  variable and so prime, then gives the irreducibility of every rectangular section.

  Every step of that chain is now a proved Lean theorem except the assembly itself: writing `tau` as
  a multivariate polynomial with the top variable first, identifying the corner cofactor with the
  `(m-1,n-1)` section, and running the induction.  The Dvornicich--Zannier citation is no longer load
  bearing.

- 2026-08-01 — **The induction step is proved as a single theorem.**
  `irreducible_linear_of_irreducible_cofactor` in
  `formal/GaloisForLFunctions/HTGeometry/MvLinearIrreducible.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  cofactor irreducible  +  a specialisation killing the cofactor but not the remainder
    ==>  X_0 * cofactor + remainder  is irreducible.
  ```

  The proof: a common divisor of the two either is a unit or is an associate of the cofactor, and in
  the second case the cofactor would divide the remainder, which the specialisation forbids; then the
  multivariate linear criterion applies.

  This is the whole induction step of the Schur argument in one reusable statement, with the
  separating point supplied abstractly as a ring map.  For the rectangular sections that map is
  evaluation at the unit tail, where the two values are `0` and `1` by
  `det_rectangularSchurToeplitz_shift_unit_tail` and `rectangularSchurToeplitz_unit_tail`.

  What is left is bookkeeping rather than mathematics: presenting `tau_(m,n)` as a polynomial with
  the top variable first and identifying its corner cofactor with the `(m-1,n-1)` section, after
  which this theorem and the base case `tau_(1,n) = h_n` give the induction.

- 2026-08-01 — **The last two presentational gaps are closed.**
  `formal/GaloisForLFunctions/HTGeometry/MvLinearIrreducible.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `exists_rename_succ_of_degreeOf_zero` — a polynomial of degree zero in the first variable **is** a
  polynomial in the remaining variables, through `natDegree_finSuccEquiv` and
  `Polynomial.natDegree_eq_zero`.  This is what converts the "free of the top variable" conclusions of
  the corner expansion into the renamed form the criterion consumes;
  `irreducible_of_corner_expansion` — the criterion with the expansion's sign absorbed as a unit, so
  it applies directly to `(-1)^r * det`.

  The chain for the irreducibility of a rectangular Jacobi--Trudi determinant is now complete as
  Lean theorems: free coordinates, the corner is the only occurrence of the top variable, degree one
  there, the explicit expansion, the cofactor and remainder values at the unit tail (`0` and `1`), the
  passage from a separating point to unit-only common divisors, and the linear criterion over a unique
  factorisation domain.  What is not yet written is the single definition presenting `tau_(m,n)` with
  the top variable indexed first, which is what would let these be chained mechanically into
  `Irreducible tau_(m,n)`.

- 2026-08-01 — **The criterion is now stated at the level of the matrix.**
  `irreducible_det_of_corner_X_zero` in
  `formal/GaloisForLFunctions/HTGeometry/MvLinearIrreducible.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  first variable in one entry of the first column and nowhere else,
  complementary minor = image of an irreducible A,
  a specialisation of the ambient ring killing A but not the determinant
    ==>  the determinant is irreducible.
  ```

  The determinant's decomposition is now derived inside the proof from `det_eq_corner_mul_minor_add`
  rather than assumed, and the remainder's nonvanishing at the point is deduced from the
  determinant's: at the specialisation the corner term dies with `A`, so what survives of the
  determinant is exactly the remainder.

  For the rectangular sections the specialisation is evaluation at the unit tail, where
  `rectangularSchurToeplitz_unit_tail` gives determinant `1` and
  `det_rectangularSchurToeplitz_shift_unit_tail` gives cofactor `0`.  So the only thing still missing
  for `Irreducible tau_(m,n)` is the presentation of the section over a polynomial ring with the top
  variable indexed first, together with the identification of its corner minor.

- 2026-08-01 — **The reversed presentation of the coefficients.**
  `formal/GaloisForLFunctions/HTGeometry/SchurVariablePresentation.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `schurVar K L k` presents the complete homogeneous coefficients as variables indexed in reverse —
  the largest index `L = n + m - 1` becoming the **first** variable — with the convention that the
  zeroth coefficient is one.  `schurVar_top` — the top coefficient is the first variable;
  `degreeOf_zero_schurVar` — every coefficient of index `k ≤ L` with `k ≠ L` is free of that variable.

  Those are exactly the first two hypotheses of `irreducible_det_of_corner_X_zero`, now available for
  the rectangular section in this presentation.  What remains is the third: identifying the corner
  minor with the `(m-1, n-1)` section in its own reversed presentation, which is an index shift
  between the two variable numberings.

  One correction found while proving it: the freeness statement needs `k ≤ L`.  Without it the
  natural-number truncation makes `L - k = 0` for `k > L`, so the coefficient would be read as the
  first variable again — vacuous in the application, where indices never exceed `L`, but false as
  stated.

- 2026-08-01 — **Adding a variable preserves irreducibility.**
  `irreducible_rename_succ` in `formal/GaloisForLFunctions/HTGeometry/MvLinearIrreducible.lean`,
  axioms `[propext, Classical.choice, Quot.sound]`: an irreducible polynomial stays irreducible when
  read in one more variable.  The proof passes to primality, where the added variable makes it a
  constant and `Polynomial.prime_C_iff` applies.

  This is needed by the induction independently of the indexing, and it settles a point the index
  bookkeeping raised: the corner minor of the `(m,n)` section uses only the coefficients of index at
  most `n+m-3`, so in the reversed presentation it is free of the **first two** variables, not just
  the first.  It is therefore the `(m-1,n-1)` section read in extra variables, and the lemma above
  says its irreducibility is unaffected — so the induction can carry the smaller section's
  irreducibility across the shift without a bespoke transport.

- 2026-08-01 — **The presentation shift is proved, closing the identification at entry level.**
  `schurVar_shift` in `formal/GaloisForLFunctions/HTGeometry/SchurVariablePresentation.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  schurVar K (L' + 2) k  =  rename (fun j => j.succ.succ) (schurVar K L' k)     for k ≤ L'.
  ```

  Since the corner expansion drops the top two coefficient indices, `L = L' + 2` exactly, and a
  coefficient surviving into the minor is the same variable read two places later.  So the minor of
  the `(m,n)` section is the `(m-1,n-1)` section renamed by two successive shifts, and
  `irreducible_rename_succ` applied twice carries its irreducibility across.

  With this the criterion's third hypothesis is available in the same form as the first two: the minor
  is `rename Fin.succ A` for `A` the once-shifted smaller section, and `A` is irreducible whenever the
  smaller section is.  The induction on `m` — base `tau_(1,n) = h_n`, step
  `irreducible_det_of_corner_X_zero` with the unit-tail specialisation — is now assembled from proved
  parts only.

- 2026-08-01 — **A boundary case of the induction, found by working it out.**
  `det_rectangularSchurToeplitz_zero_shift` in `SchurVariablePresentation.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`: at shift zero the section is lower triangular with unit
  diagonal, so its determinant is **one**.

  This matters for the shape of the induction.  The corner expansion of the `(m,n)` rectangle has the
  `(m-1,n-1)` rectangle as cofactor, so the recursion in `n` bottoms out at shift zero — and there the
  cofactor is a **unit**, not an irreducible.  The step `irreducible_det_of_corner_X_zero`, which
  assumes an irreducible cofactor, therefore cannot be used at `n = 1`; that case needs its own
  argument, as does `m = 1`, where `tau_(1,n) = h_n` is a variable.

  So the induction is on both parameters with two boundary families, not the single chain the paper
  sketch suggests.  Both boundaries are now computed: `tau_(1,n) = h_n` and `tau_(m,1)` has unit
  cofactor with `det = 1` at shift zero.

- 2026-08-01 — **The base rectangle is proved irreducible.**
  `SchurVariablePresentation.lean`, axioms `[propext, Classical.choice, Quot.sound]`:
  `det_rectangularSchurToeplitz_one` — a rectangle of height one has determinant the single
  coefficient `h_n`, which in the reversed presentation is the first variable;
  `irreducible_det_rectangularSchurToeplitz_one` — hence it is irreducible, a variable being prime.

  That is the `m = 1` boundary of the induction.  With the `n = 1` boundary computed in the previous
  entry (`det = 1` at shift zero) and the step available as
  `irreducible_det_of_corner_X_zero`, the two-parameter induction has all three of its cases
  supplied.

- 2026-08-01 — **The corner minor is identified.**  `SchurVariablePresentation.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `submatrix_rectangularSchurToeplitz` — deleting the last row and the first column of the
  `(m'+1, n'+1)` section leaves the `(m', n')` section read two variables later, entry by entry
  through `schurVar_shift`;
  `det_submatrix_rectangularSchurToeplitz` and `det_submatrix_eq_rename_succ` — hence its determinant
  is the smaller determinant renamed twice, which is the form `irreducible_det_of_corner_X_zero`
  consumes for its minor hypothesis.

  All four hypotheses of the step are now available for the rectangular sections: the corner is the
  first variable (`schurVar_top`), the other entries are free of it (`degreeOf_zero_schurVar`), the
  minor is a renamed smaller determinant (here), and the unit tail separates
  (`rectangularSchurToeplitz_unit_tail`, `det_rectangularSchurToeplitz_shift_unit_tail`).  With the
  two boundary cases proved, what is left is to write the induction itself.

- 2026-08-01 — **A scope condition on the separating point, found while wiring the induction.**
  `SchurVariablePresentation.lean`, axioms `[propext, Classical.choice, Quot.sound]`:
  `unitTailEval` is the unit tail as a specialisation of the reversed presentation;
  `unitTailEval_schurVar` — a coefficient of index `1 ≤ k ≤ L` evaluates to `1` if `k = n` and `0`
  otherwise; `unitTailEval_schurVar_zero` — the **zeroth** coefficient evaluates to `1`.

  The last of these is the point.  The convention `h_0 = 1` is not a variable, so no specialisation
  can send it to zero.  The unit tail therefore realises the identity matrix — the computation
  behind `rectangularSchurToeplitz_unit_tail` — only when the index zero never occurs in the section,
  that is when `n + r - i = 0` is impossible for `r, i < m`, which means **`n ≥ m`**.

  For `n < m` the same point gives a matrix with extra ones below the diagonal and the separating
  argument needs a different specialisation.  Since the corner recursion decreases `m` and `n`
  together, the ratio `n/m` is preserved along it, so this is a genuine restriction on the induction
  rather than something that disappears at the next step: the argument as sketched proves the
  irreducibility of `tau_(m,n)` for `n ≥ m`, and the complementary range needs its own separating
  point.

- 2026-08-01 — **The separating value is proved in the valid regime.**
  `SchurVariablePresentation.lean`, axioms `[propext, Classical.choice, Quot.sound]`:
  `map_unitTailEval_rectangularSchurToeplitz` — when the shift is at least the height, no entry has
  index zero, so evaluating at the unit tail turns the section into the constant unit-tail section;
  `unitTailEval_det_rectangularSchurToeplitz` — hence the determinant evaluates to **one** there.

  That is the `ψ M.det ≠ 0` hypothesis of `irreducible_det_of_corner_X_zero`, for `m ≤ n`.  The
  companion `φ A = 0` is the same evaluation applied to the corner minor, where
  `det_rectangularSchurToeplitz_shift_unit_tail` gives zero.

  So in the range `m ≤ n` every hypothesis of the induction step is now a proved theorem about the
  presentation itself, not about an abstract matrix: corner, freeness, minor, and both separating
  values.

- 2026-08-01 — **The last connector: the unit tail commutes with adding a variable.**
  `unitTailEval_rename_succ` in `SchurVariablePresentation.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`: reading a polynomial one variable later and evaluating
  at the unit tail is the unit-tail evaluation of the smaller presentation.

  This is the `hcomp` hypothesis of `irreducible_det_of_corner_X_zero`, which relates the
  specialisation of the ambient ring to the one of the coefficient ring.  With it, all six inputs of
  the step are proved for the rectangular presentation in the range `m ≤ n`:

  ```text
  corner = X 0                    schurVar_top
  other entries free of X 0       degreeOf_zero_schurVar + rectangularSchurToeplitz_index_lt_top
  minor = rename succ of smaller  det_submatrix_eq_rename_succ
  smaller irreducible             induction hypothesis + irreducible_rename_succ
  specialisations agree           unitTailEval_rename_succ
  values 0 and 1                  det_..._shift_unit_tail, unitTailEval_det_...
  ```

  Writing the induction is now a matter of instantiating the step with these; no further lemma is
  needed for `m ≤ n`.

- 2026-08-01 — **Reindexing transport, the last obstacle to writing the induction.**
  `irreducible_rename_finCongr` in `MvLinearIrreducible.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`: irreducibility is unaffected by a reindexing of the
  variables along an equality of their number.

  This is needed for a reason particular to the formalisation rather than the mathematics.  The
  number of variables is a **type index**, and the induction meets the same ambient ring written in
  two arithmetically equal but syntactically different ways — `n' + m' - 1 + 2` from the minor lemma
  against `n' + m' + 1` in the natural statement of the step.  No phrasing of the induction avoids
  this: it is inherent in the corner recursion decreasing both parameters.  Transporting along
  `finCongr` resolves it.

  With this the induction for `m ≤ n` can be written from proved parts only.

- 2026-08-01 — **The presentation transports along an equality of variable counts.**
  `SchurVariablePresentation.lean`, axioms `[propext, Classical.choice, Quot.sound]`:
  `rename_finCongr_schurVar` — reindexing the variables carries each coefficient to the
  corresponding one; `map_rename_finCongr_rectangularSchurToeplitz` and
  `rename_finCongr_det_rectangularSchurToeplitz` — hence a section and its determinant transport too.

  Combined with `irreducible_rename_finCongr`, this removes the last friction in the induction: the
  ambient ring appearing as `n' + m' - 1 + 2` on one side and `n' + m' + 1` on the other can now be
  matched, since both the statement and the object transport along the arithmetic identity.

  Every ingredient of the `m ≤ n` induction is proved.  What is left is to write it.

- 2026-08-01 — **The cofactor's vanishing at the point, in the form the step needs.**
  `SchurVariablePresentation.lean`, axioms `[propext, Classical.choice, Quot.sound]`:
  `map_unitTailEval_succ_rectangularSchurToeplitz` — the section of shift `n`, seen at the unit tail
  belonging to `n+1`, becomes the constant section of that tail;
  `unitTailEval_succ_det_rectangularSchurToeplitz` — hence its determinant is **zero**, its first row
  being zero.

  The distinction matters: in the step the ambient specialisation belongs to the **larger** rectangle,
  whose shift is one more than the cofactor's.  So the cofactor is evaluated at the unit tail of the
  next index, not of its own, and the earlier lemma — which evaluates a section at its own tail and
  gives `1` — is the wrong one for it.  Both are now available, and they are what make the two
  separating values `1` and `0` come from the same specialisation.

- 2026-08-01 — **Ambient-generalised forms of the two separating values.**
  `unitTailEval_det_rectangularSchurToeplitz'` and `unitTailEval_succ_det_rectangularSchurToeplitz'`
  in `SchurVariablePresentation.lean`, axioms `[propext, Classical.choice, Quot.sound]`: the values
  `1` and `0` with the number of variables given as a parameter together with the equation defining
  it, so an application can supply the arithmetic in whatever form it arises and discharge it by
  `subst`.

  A note on what can and cannot be generalised this way.  Both sides of these statements are scalars,
  so the ambient appears only inside the argument and the equation hypothesis is harmless.  The
  minor identity `det_submatrix_eq_rename_succ` cannot be generalised so: its two sides live in
  polynomial rings whose variable counts differ by two, so with the ambient a free parameter the
  statement does not even typecheck.  There the arithmetic has to be met in its own form, which is
  why the step will be written with the ambient exactly as the minor lemma produces it.

- 2026-08-01 — **The induction step is proved for the rectangular section itself.**
  `irreducible_det_schur_step` in
  `formal/GaloisForLFunctions/HTGeometry/SchurSectionIrreducible.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  0 < n', 0 < m', m' ≤ n',  section (n', m') irreducible
    ==>  section (n'+1, m'+1) irreducible.
  ```

  Every hypothesis of `irreducible_det_of_corner_X_zero` is discharged from the presentation lemmas:
  the corner is the first variable, the other entries are free of it, the minor is the smaller
  determinant renamed twice, that renaming preserves irreducibility, the two specialisations agree,
  and the unit tail gives `0` on the minor and `1` on the determinant.

  Two mechanical points that cost iterations and are worth remembering.  The criterion's
  specialisations are **ring** homomorphisms while `unitTailEval` is an algebra homomorphism, so they
  must be passed as `.toRingHom` and the resulting goals restated with `show` before the algebra-map
  lemmas apply.  And the compatibility argument must be supplied with its indices pinned, since
  unifying a metavariable ring hom against a coerced algebra hom is beyond what Lean will do on its
  own.

  With the step proved, the two boundary cases already in hand, and the reindexing transport, the
  induction for `m ≤ n` is a recursion over these.

- 2026-08-01 — **The rectangular Schur determinant is proved irreducible, unconditionally in Lean.**
  `irreducible_det_schur` and `irreducible_det_schur_of_le` in
  `formal/GaloisForLFunctions/HTGeometry/SchurSectionIrreducible.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  0 < m,  m ≤ n   ==>   Irreducible (det (rectangularSchurToeplitz (schurVar K (n+m-1)) n m))
  ```

  The induction is on the height with the difference of the parameters fixed, since the corner
  expansion lowers both by one: the height-one section is a single variable, and the step is
  `irreducible_det_schur_step`.

  **This is the statement the card cited Dvornicich--Zannier for.**  It is now a proved theorem of the
  corpus in the range `m ≤ n`, resting on nothing external: the coordinates are free
  (`algebraicIndependent_sqJetFamily`), the corner carries the top variable alone, the determinant is
  linear in it, the cofactor is the smaller section, the unit tail separates the two, and a linear
  polynomial with no common factor in its coefficients is irreducible over a unique factorisation
  domain.

  The complementary range `n < m` remains open for the reason recorded earlier: the convention
  `h_0 = 1` is not a variable, so the unit tail is not a separating point there and a different
  specialisation is needed.  For the ramification divisor of this card the relevant rectangle is
  `(n^m)` with `n = L - m`, so the proved range covers the horizons with `m ≤ L/2`, and by the
  symmetry of the two depths that is every case up to exchanging them.

- 2026-08-01 — **Half of the range restriction is removed.**
  `det_unitTail_rectangularSchurToeplitz` in `SchurVariablePresentation.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`: at the unit tail, with the convention `h_0 = 1` in
  force, the section is **unitriangular** — below the diagonal the index exceeds `n` so the entry
  vanishes, on the diagonal it is one — hence its determinant is one **for every height**, with no
  constraint between the parameters.

  This corrects the reasoning behind the earlier restriction.  The point was never that the matrix
  had to be the identity; the extra ones forced by `h_0 = 1` sit strictly above the diagonal and do
  not disturb the determinant.  So the hypothesis `psi (det) ≠ 0` of the step holds in general.

  What still needs `m ≤ n` is the other half: the cofactor's vanishing.  Its first row acquires a one
  at column `n-1` exactly when `n ≤ m-1`, so for `n < m` the unit tail no longer kills it.  The
  restriction on the proved theorem is therefore located precisely: it comes from the cofactor, not
  from the determinant.

- 2026-08-01 — **The unit-cofactor case, which is what the complementary range needs.**
  `irreducible_linear_of_isUnit_leading` and `irreducible_linear_in_X_zero_of_isUnit`, axioms
  `[propext, Classical.choice, Quot.sound]`: when the cofactor is a **unit**, `X_0 * A + B` is
  irreducible with no separating point at all — every common divisor of the coefficients divides a
  unit.

  This is the missing case for `n < m`.  There the corner recursion reaches shift zero, where the
  section is unitriangular with determinant one — a unit, not an irreducible — so the step that
  assumes an irreducible cofactor does not apply and the one above does.  The smallest instance is
  the `(2,1)` rectangle, whose determinant `h_1^2 - h_2` is linear in `h_2` with unit leading
  coefficient.

  So the two ranges need different final moves: `m ≤ n` bottoms out at a variable and uses the
  separating point throughout; `n < m` bottoms out at a unit and uses the unit-cofactor criterion at
  that end.  Both criteria are now proved; what remains is the recursion for the second range, whose
  cofactor identification is the same lemma already used for the first.

- 2026-08-01 — **The matrix criterion with a unit minor.**
  `irreducible_det_of_corner_X_zero_of_isUnit` in `MvLinearIrreducible.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`: if the first variable occupies one entry of the first
  column and no other, and the complementary minor is a **unit**, the determinant is irreducible —
  with no separating point and no hypothesis relating the parameters.

  This is the form the shift-one rectangles need: their corner minor is the shift-zero section, whose
  determinant is one.  It applies at any height, so `tau_(m,1)` is irreducible for every `m`, a family
  entirely outside the range `m ≤ n` covered by the main theorem.

  The two matrix criteria now available differ exactly in what they ask of the minor — irreducible
  with a separating point, or a unit with nothing further — and between them they cover both ends of
  the corner recursion.

- 2026-08-01 — **The shift-one rectangles are irreducible at every height.**
  `irreducible_det_schur_shift_one` in `SchurSectionIrreducible.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`: `tau_(m,1)` is irreducible for every `m ≥ 1`, through
  the unit-minor criterion — its corner minor is the shift-zero section, whose determinant is one.

  This is the first family proved entirely **outside** the range `m ≤ n` of the main theorem, and it
  is the far end of the corner recursion for every rectangle with `n < m`.

  Two hypotheses were also removed as unnecessary while doing this: the minor identity
  `submatrix_rectangularSchurToeplitz` and its determinant forms never needed the shift to be
  positive, only a row to exist, so they now apply at shift zero — which is exactly what the
  shift-one case requires of them.

- 2026-08-01 — **Analysis of the remaining strip `2 ≤ n < m`, and the route to close it.**
  No new theorem this entry; the work was to determine what the strip actually needs.

  *Why the corner recursion alone does not reach it.*  Expanding along the first column isolates the
  top coefficient `h_(n+m-1)` and produces the `(m-1,n-1)` cofactor, decreasing both parameters, so
  the ratio `n/m` never improves.  Expanding along the **last** column would decrease only `m` — which
  is what the strip needs — but the largest index in that column is `n`, so the expansion is not
  linear in a variable absent from the minor and neither corner criterion applies.  The recursion
  cannot be redirected.

  *What a separating point must do.*  At each step one needs a specialisation with
  `phi(tau_(m-1,n-1)) = 0` and `psi(tau_(m,n)) ≠ 0`.  Under the convention `h_0 = 1` a point of the
  form `h_k = [k = j]` makes the section a sum of two band matrices, with nonzero entries where
  `i - r ∈ {n - j, n}`; its determinant is a signed count of permutations tiled by those two steps.
  Choosing `j` to make that count vanish for `(m-1,n-1)` but not for `(m,n)` is a lattice condition on
  `(m, n, j)` and is a genuine combinatorial question, not bookkeeping.

  *The route that avoids it.*  The dual Jacobi--Trudi identity gives
  `det(h_(n-i+j))_(m×m) = det(e_(m-i+j))_(n×n)`, and the passage from the `h` generators to the `e`
  generators is the triangular substitution determined by `sum_(i+j=k) (-1)^i e_i h_j = 0`, hence an
  automorphism of the polynomial ring.  Composing the two exchanges the roles of `m` and `n` without
  changing irreducibility, so the proved range `m ≤ n` would cover everything.  Three pieces are
  needed: the recursive definition of the `e` family, that a triangular substitution is an
  automorphism, and the dual identity itself.

  Coverage as it stands: `m ≤ n` by `irreducible_det_schur_of_le`, and `n = 1` at every height by
  `irreducible_det_schur_shift_one`.

- 2026-08-01 — **First piece of the dual route: the `e` family and its triangularity.**
  `formal/GaloisForLFunctions/HTGeometry/DualSchurVariables.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `dualVar` defines the elementary coefficients from the complete homogeneous ones by the alternating
  convolution `e_(k+1) = sum_(i≤k) (-1)^i h_(i+1) e_(k-i)`, by well-founded recursion;
  `degreeOf_dualVar` — **each dual coefficient involves only the coefficients of index at most its
  own**, by strong induction: in the defining sum every factor is either a coefficient of index at
  most `k+1` or an earlier dual coefficient.

  That is the triangularity the substitution `h ↦ e` needs to be an automorphism, which is the second
  of the three pieces of the route recorded in the previous entry.  The third is the dual
  Jacobi--Trudi identity itself.

- 2026-08-01 — **The convolution identity relating the two families.**
  `DualSchurVariables.lean`, axioms `[propext, Classical.choice, Quot.sound]`:
  `dualVar_succ_reflect` — the defining recursion read in the reversed order of summation;
  `sum_dualVar_schurVar` — hence the alternating convolution vanishes above degree zero,

  ```text
  sum_(i ≤ k+1) (-1)^i e_i h_(k+1-i) = 0.
  ```

  This is the symmetric form of the relation between the two families: it determines `e` from `h` and
  equally `h` from `e`, which is what makes the substitution an involution rather than merely
  triangular.  With `degreeOf_dualVar` from the previous entry, the second piece of the dual route —
  that `h ↦ e` is an automorphism — now has both of its inputs.

- 2026-08-01 — **The relation is symmetric in the two families.**
  `schurVar_succ_eq_sum` in `DualSchurVariables.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`: solving the convolution for the complete homogeneous
  coefficient gives

  ```text
  h_(k+1) = sum_(i ≤ k) (-1)^i e_(i+1) h_(k-i),
  ```

  which is the **same shape** as the definition of the dual family with the two exchanged.  So the
  substitution sending each coefficient to the corresponding dual one carries the defining recursion
  to itself, and its square fixes every generator — the involutivity that makes it an automorphism,
  by strong induction on the index.

  That is the last identity needed for the second piece of the dual route; what remains of that piece
  is to package the substitution as an algebra map and run the induction.

- 2026-08-01 — **The exchange of the two families is an automorphism.**
  `DualSchurVariables.lean`, axioms `[propext, Classical.choice, Quot.sound]`:

  `dualSub` — the substitution sending each coefficient to the corresponding dual one;
  `dualSub_schurVar` — it sends `h_k` to `e_k` for `k ≤ L`;
  `dualSub_dualVar` — and sends `e_k` back to `h_k`, by strong induction on the two recursions, which
  are the same with the families exchanged;
  `dualSub_comp_dualSub` — hence it squares to the identity; `dualEquiv` — so it is an algebra
  **automorphism**; `irreducible_dualSub_iff` — and irreducibility is preserved by it.

  That completes the second of the three pieces of the dual route.  Only the dual Jacobi--Trudi
  identity

  ```text
  det(h_(n-i+j))_(m×m) = det(e_(m-i+j))_(n×n)
  ```

  now stands between the proved range `m ≤ n` and the full statement: with it, the automorphism above
  carries the `(m,n)` section to the `(n,m)` section without changing irreducibility, and the two
  ranges collapse into one.

- 2026-08-01 — **The two families as triangular matrices.**
  `formal/GaloisForLFunctions/HTGeometry/DualTriangularInverse.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `schurTri` and `dualTri` arrange the complete homogeneous coefficients and the signed dual ones in
  lower triangular matrices; `schurTri_diag`, `dualTri_diag` — both have unit diagonal;
  `det_schurTri`, `det_dualTri` — hence both have determinant one, so both are invertible over the
  coefficient ring; `schurTri_mul_dualTri_above` and `schurTri_mul_dualTri_diag` — their product is
  unitriangular.

  The remaining step to `schurTri * dualTri = 1` is the off-diagonal entry below the diagonal, which
  is the convolution identity after reindexing the sum over the interval between the two indices —
  the identity is proved (`sum_dualVar_schurVar`), the reindexing is what is left.

  That product identity is the linear-algebraic input to the dual Jacobi--Trudi duality: with the two
  matrices inverse, Jacobi's complementary-minor formula exchanges an `m × m` minor of one for an
  `n × n` minor of the other, which is the identity the route needs.

- 2026-08-01 — **The two triangular matrices are inverse.**
  `schurTri_mul_dualTri` in `DualTriangularInverse.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  schurTri * dualTri = 1.
  ```

  The below-diagonal entries are the alternating convolution reindexed over the interval between the
  two indices — `Fin.sum_univ_eq_sum_range` to leave `Fin`, `Finset.sum_subset` to restrict to that
  interval, and `Finset.sum_Ico_eq_sum_range` to shift it to a range — after which
  `sum_dualVar_schurVar` closes it.  The diagonal and above-diagonal entries were already proved.

  This is the linear-algebraic form of the relation between the two families and the input to
  Jacobi's complementary-minor formula, which is what would exchange an `m × m` minor of one matrix
  for an `n × n` minor of the other and so give the dual Jacobi--Trudi identity.  That formula is
  absent from mathlib and is the one remaining piece of the route.

- 2026-08-01 — **Complementary blocks of inverse matrices.**
  `formal/GaloisForLFunctions/HTGeometry/BlockComplementaryMinor.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  Jacobi's complementary-minor formula is absent from mathlib.  What the dual route needs is its
  block form, and that admits a short self-contained proof.  For `H` of row type `α ⊕ β` and column
  type `β ⊕ α`, and `E` of the opposite shape, with `H * E = 1`,

  ```text
  det(H_21) = det(H with its two column blocks exchanged) * det(E_21).
  ```

  `det_toBlocks₂₁_eq`.  The mechanism is one auxiliary matrix `G = fromBlocks 1 A' 0 C'`, built from
  `E` by replacing its first column block by the identity.  Its determinant is `det(E_21)` because it
  is block triangular.  Multiplying `H` by it kills the two blocks that the inverse relation
  annihilates, leaving `fromBlocks A 1 C 0`, whose determinant after exchanging the column blocks is
  `det(H_21)`.  `submatrix_mul_equiv` splits the determinant of the product; the two block triangular
  determinants are `det_fromBlocks_zero₂₁`.

  `irreducible_det_toBlocks₂₁_iff` — when the exchanged matrix has unit determinant, irreducibility
  passes between the two complementary blocks; `isUnit_det_submatrix_of_det_eq_one` — a matrix of
  determinant one reindexed by two bijections has unit determinant, the factor being the sign of the
  permutation comparing the two reindexings, so that hypothesis is automatic here.

- 2026-08-01 — **The two parameters of a rectangular section can be exchanged, and the restriction
  `m ≤ n` disappears.**  `formal/GaloisForLFunctions/HTGeometry/DualRectangularSection.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  Irreducible (det (rectangularSchurToeplitz (schurVar K (n+m-1)) n m))   for all n,m ≥ 1.
  ```

  `irreducible_det_rectangularSchurToeplitz`.  This is `(1)` of the theorem above — the rectangular
  Schur determinant `tau_(m,n) = s_((n^m))[h]` in the algebraically independent coefficients
  `h_1,...,h_(m+n-1)` — and it is now proved in the corpus at **every** pair of parameters.  The
  appeal to Dvornicich--Zannier is no longer a citation: the whole chain from the corner expansion to
  the full statement is Lean.

  The construction.  Cut the ambient index of the `(n+m)`-square triangular matrix at the shift in
  the rows (`schurRowSplit`) and at the height in the columns (`schurColSplit`).  Then
  `toBlocks₂₁_schurBlock`: the lower left block of `schurTri` is exactly the section
  `rectangularSchurToeplitz (schurVar K L) n m`.  Cutting the inverse matrix the opposite way,
  `dualBlock_toBlocks₂₁_apply`: its lower left block is the section of the **dual** family with the
  two parameters exchanged, `rectangularSchurToeplitz (dualVar K L) m n`, up to one sign per row and
  one per column.  Those signs are units, so `irreducible_det_toBlocks₂₁_dualBlock_iff` discards them
  (`det_mul_row`, `det_mul_column`, and `Finset.prod_pow_eq_pow_sum` to see the two products as a
  single power of `-1`).  `schurBlock_mul_dualBlock` is `schurTri_mul_dualTri` reindexed, and
  `isUnit_det_schurBlock_swap` is the reindexing lemma applied to `det_schurTri = 1`.  The block
  relation then gives

  ```text
  Irreducible (det (rect (schurVar K L) n m)) ↔ Irreducible (det (rect (dualVar K L) m n))
  ```

  (`irreducible_det_rect_swap_iff`), and `dualSub_det_rect` — the exchange of the two families
  applied entrywise, through `AlgHom.map_det` — identifies the right-hand determinant with the image
  of `det (rect (schurVar K L) m n)` under the automorphism `dualSub`, which by
  `irreducible_dualSub_iff` does not change irreducibility.

  So for `m ≤ n` the statement is `irreducible_det_schur_of_le` directly, and for `n < m` it is that
  same theorem with the parameters exchanged, transported across the complementary block relation and
  the exchange of the two coefficient families.  This closes the dual route and the last gap in the
  Schur irreducibility chain of this card.
