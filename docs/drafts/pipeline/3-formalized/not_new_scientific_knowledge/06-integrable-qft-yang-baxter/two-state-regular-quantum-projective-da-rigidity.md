# The regular two-state strict-difference quantum Yang--Baxter class is projectively DA

- **ID:** `two-state-regular-quantum-projective-da-rigidity`
- **Stage:** 3-formalized / not_new_scientific_knowledge
- **Type:** CLASSIFICATION COROLLARY / ROUTE KILL
- **Scientific status:** `[PROVED FROM COMPLETE PUBLISHED CLASSIFICATION]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Scope:** general two-state regular strict-difference quantum Yang--Baxter families; no RH and
  no distinguished special-function input
- **Parents:**
  - `../needs-audit/projective-wigner-smith-nonabelian-ht-separation.md`
  - `../../5-failed/two-state-projective-hypertranscendence-no-go.md`
- **Statement:** After quotienting a common scalar and constant one-particle gauge, every analytic
  regular strict-difference `4 x 4` quantum Yang--Baxter family has differentially algebraic entry
  ratios.  Hence this exact quantum classification stratum cannot carry projective HT.

## Exact theorem

Let

```text
R(theta) in GL(C^2 tensor C^2)
```

be analytic near zero, satisfy the additive difference-form quantum Yang--Baxter equation, and
obey

```text
R(0)=-P.                                                     (1)
```

Modulo a nonvanishing common scalar, constant one-particle basis change, discrete
transpose/parity operations, and affine spectral rescaling, every ratio of nonzero entries of
`R` is differentially algebraic over `C(theta)`.  Consequently the differential transcendence
degree of its `PGL_4` projective field is zero.

## Proof from the complete classification

Put

```text
R_hat=-R,             R_hat(0)=P.                           (2)
```

This is exactly the regular quantum convention classified by de Leeuw--Pribytok--Ryan: analytic
strict difference form, the quantum Yang--Baxter equation, and the permutation anchor.  Their
classification is complete up to scalar normalization and the stated constant equivalences.
Corcoran--de Leeuw's completed regular classification organizes the strict-difference solutions
into the following functional alphabet:

```text
rational functions,
exponentials and trigonometric/hyperbolic functions,
Jacobi elliptic functions,                                  (3)
```

together with degenerations and rational combinations of these entries.  The later
de Leeuw--Posch classification closes the nonregular analytic cases; those do not enlarge the
regular anchor `(2)`.

Every function in `(3)` is DA.  The elliptic endpoint is explicit, for example

```text
(sn'(z))^2=(1-sn(z)^2)(1-k^2 sn(z)^2).                     (4)
```

The other Jacobi functions satisfy analogous algebraic differential equations.  DA functions
are closed under the rational operations occurring in the classified matrices, affine spectral
rescaling, and constant conjugation.  Quotienting the arbitrary common scalar therefore leaves
only DA entry ratios.  This proves the theorem.

## Positive-metric cut

Suppose in addition that `R_hat(theta)` is unitary for real rapidity.  Define the regular
Hamiltonian density

```text
H=P R_hat'(0).                                               (5)
```

Differentiating `R_hat(theta)^* R_hat(theta)=I` at zero gives

```text
R_hat'(0)^* P + P R_hat'(0)=0,
H^*=-H.                                                      (6)
```

Thus `H` is normal and diagonalizable.  The exceptional non-diagonalizable strict-difference
classes survive `(6)` only at parameter values where their nilpotent deformation vanishes and
they collapse to lower-vertex/XXX cases.  The positive-unitary candidates are therefore contained
in the six/eight-vertex families and their degenerations, still inside the DA alphabet `(3)`.
Hermitian analyticity, crossing, and strip regularity further restrict constants and the common
scalar; they cannot introduce a projective function absent from the classification.

## Convention boundary

This theorem must not be restated as a no-go for every physical two-species scattering
convention.  If

```text
B(theta)=R(theta)P,
```

then `(1)` gives `B(0)=-I`, and right multiplication by `P` merely permutes columns, so `R` and
`B` have the same projective differential field.  But the already constructed diagonal
two-species local QFT is naturally presented in an adjacent-braid class whose quantum conversion
has a scalar-identity, nonregular anchor.  It lies outside `(1)` and physically realizes commuting
projective HT.  This is exactly why the earlier broad two-state physical no-go failed.

The proved conclusion is only:

```text
regular strict-difference quantum 4 x 4 class -> projectively DA.   (7)
```

It closes one intrinsically mixing search lane, not the nonregular scalar-identity lane and not
the already proved diagonal/commuting local-QFT construction.

## Anti-theatre and novelty gate

The classification and the special-function differential equations are published parent
mathematics.  The Kolchin-language corollary `(7)` is immediate once those lists are inspected.
It is retained as a route selector, not promoted as new knowledge.

The physically free common scalar remains important.  Its unitarity and crossing equations admit
minimal and CDD factors, including HT functions.  Therefore this route kill says that any HT in
the regular two-state quantum stratum is scalar; it does not make scalar HT physically trivial.

## Primary literature

- M. de Leeuw, A. Pribytok, and P. Ryan, *Classifying integrable spin-1/2 chains with nearest
  neighbour interactions*, <https://arxiv.org/abs/1904.12005>.
- L. Corcoran and M. de Leeuw, *All regular `4 x 4` solutions of the Yang--Baxter equation*,
  <https://arxiv.org/abs/2306.10423>.
- M. de Leeuw and V. Posch, *All `4 x 4` solutions of the quantum Yang--Baxter equation*,
  <https://arxiv.org/abs/2411.18685>.
- NIST Digital Library of Mathematical Functions, Section 22.13, *Jacobian elliptic functions:
  derivatives and differential equations*, <https://dlmf.nist.gov/22.13>.

## Classification-free proof, in every state dimension

The published classification is not needed, and the restriction to two states is not needed either.

Write the family in braid form, `check R(a) = P R(a)`, so regularity is `check R(0) = 1`, and put
`H = check R'(0)`.  Differentiating the difference-form braid Yang--Baxter equation

```text
check R_12(a) check R_23(a+b) check R_12(b)
  = check R_23(b) check R_12(a+b) check R_23(a)                    (8)
```

in `b` at `b = 0` gives the **Sutherland identity**

```text
check R_12 check R'_23 - check R'_12 check R_23
  = H_23 check R_12 check R_23 - check R_12 check R_23 H_12.       (9)
```

Its left side is linear in `check R'`.  At `check R = 1` that linear map is `Z |-> Z_23 - Z_12`,
whose kernel is exactly the scalars: comparing entries at `(a,b,c),(a',b',c')` forces `Z` to vanish
off the diagonal in each label separately and then forces the diagonal to be constant.  The scalar
direction is precisely the freedom of a common scalar factor, so normalizing one entry to `1`
removes it and `(9)` determines `check R'` as an explicit rational function of `check R` with
constant coefficients.

Hence the field generated over `C(a)` by the normalized entries is closed under differentiation and
has finite transcendence degree, so **every entry ratio is differentially algebraic**.  This proves
`(7)` for arbitrary state dimension with no classification input:

```text
regular difference-form braid family, arbitrary state dimension
  -> projectively DA.                                              (7')
```

The two-state statement `(7)` of the theorem above is the case `dim V = 2`.  Nothing here is
asserted to be new: the Sutherland linearisation is the standard tool of the classification
programme, and the differential-algebraic reading is immediate once its kernel is computed.  What
changes is that the classification is no longer load-bearing for this card.

## Lean formalization

Formalized unconditionally in
`formal/GaloisForLFunctions/HTGeometry/ThreeParticleLegsRing.lean`,
`SutherlandLinearisation.lean`, `MatrixEntriesInSubfield.lean`,
`SutherlandProjectiveAlgebraicity.lean`, `MatrixHasDerivAt.lean`,
`BraidYangBaxterSutherland.lean`, `AnalyticMatrixGerm.lean`,
`RegularBraidProjectiveDA.lean` and `RegularQuantumAnchorCut.lean`.

- `legLeft` / `legRight` are the two tensor embeddings over an arbitrary commutative ring, and
  `eq_smul_one_of_legRight_eq_legLeft` proves that the kernel of the identity Sutherland map is
  exactly the scalars.
- `sutherlandSolve` is an **explicit** linear left inverse of that map, anchored at a base label:
  `sutherlandSolve_legRight_sub_legLeft` proves
  `sutherlandSolve (Z_23 - Z_12) = Z - Z_anchor * 1`.  No basis, rank argument or choice is used.
  `sutherlandOp` is the resulting endomorphism, `sutherlandOp_one` proves it is the identity at
  `check R = 1`, and `sutherlandMatrix_one` proves its matrix is `1` there.
- `sutherland_of_braid` proves `(9)` from `(8)` by differentiating at the anchor, using only the
  matrix product rule and the two leg rules (`MatrixHasDerivAt`).
- `entrywiseDeriv_mem_adjoin_of_sutherland` proves that the Sutherland identity plus the anchor
  normalization plus invertibility of that one finite system puts every entry of `check R'` in the
  field generated by the entries of `check R`;
  `differentialAlgebraicOver_entry_of_sutherland` and
  `differentialAlgebraicOver_normalized_entry_of_sutherland` turn that into differential
  algebraicity of every entry ratio, for **every state dimension**.
- `exists_jetRelation_normalized_of_regular_braid` is the analytic capstone `(7')`: for an analytic
  difference-form braid family with `check R(0) = 1` on a nonempty connected open chart containing
  the anchor, on which the anchor entry does not vanish, every entry ratio satisfies an algebraic
  differential equation with complex polynomial coefficients on that chart.  The germ transfer runs
  through `analyticMatrixElement` and the corpus's meromorphic jet bridge
  `differentialAlgebraicOver_analyticMeroElement_iff`; invertibility of the Sutherland system comes
  from evaluating its determinant at the anchor, where it is `det 1 = 1`.
- `conjTranspose_anchorHamiltonian` proves the positive-metric cut `(6)`: differentiating unitarity
  at a self-adjoint anchor makes `H = P R'(0)` anti-Hermitian, hence normal.
- `range_entries_mul_pairFlip` and `neg_pairFlip_mul_pairFlip` prove the convention boundary: right
  multiplication by the flip only permutes columns, so it leaves the entry family — and therefore
  the projective differential field — unchanged, while moving the anchor from `-P` to `-1`.

Direct Lean checks, targeted leaf builds and umbrella wiring done.  Axiom audit of every capstone
above reports only `propext`, `Classical.choice`, and `Quot.sound`.

The kernel condition is not cosmetic: exact rational linear algebra on `Fin 2` gives kernel
dimension `1` at the identity and generically, but dimension `4` at the flip `P`.  Regularity is
what puts the family in the good locus.

## Gates

- [x] exact quantum regularity convention fixed
- [x] complete strict-difference `4 x 4` classification identified
- [x] full projective functional alphabet checked to be DA
- [x] positive-unitary Hamiltonian-density cut derived
- [x] scalar freedom separated from projective field
- [x] adjacent-braid/nonregular counterexample boundary preserved
- [x] novelty rejected
- [x] classification eliminated: the Sutherland linearisation proves projective DA in every state
  dimension
- [x] exact Lean theorems, targeted leaf builds, and axiom gate
