# Finite-unit Milnor colimit

- **ID:** `deninger-finite-unit-milnor-colimit`
- **Stage:** 2-fully-proven
- **Type:** SOURCE ALGEBRA THEOREM
- **Label:** `DAC_FINITE_UNIT_MILNOR_COLIMIT`
- **Parent:** `deninger-baumslag-milnor-pro-realization`

## Statement

Let \(k\) be a field, let \(V\) be a possibly infinite-dimensional
\(k\)-vector space, and let \(\mathcal I(V)\) be the filtered poset of its
finite-dimensional subspaces.  Put
\[
 P=\Lambda_k(V),\qquad P_U=\Lambda_k(U),\qquad
 K_U=k\oplus U,\quad U^2=0.                                         \tag{1}
\]
Then:

1. \(P\) is a free, hence flat, \(P_U\)-module for every
   \(U\in\mathcal I(V)\);
2. the derived base change is discrete as a DGA:
   \[
   P\mathop{\otimes}^{\mathbb L}_{P_U}K_U
   \simeq
   P\otimes_{P_U}K_U
   \cong
   P/\langle\Lambda^{\ge2}U\rangle;                                 \tag{2}
   \]
3. with transition maps induced by inclusions \(U\subset U'\),
   \[
   \operatorname*{colim}_{U\in\mathcal I(V)}
   \left(P\mathop{\otimes}^{\mathbb L}_{P_U}K_U\right)
   \simeq k\oplus V,\qquad V^2=0.                                   \tag{3}
   \]

If \(Q_U\xrightarrow{\sim}K_U\) is any cofibrant
\(P_U\)-algebra resolution, then `(2)`--`(3)` remain true with \(Q_U\) in
place of \(K_U\).

## Proof

Choose a vector-space complement \(V=U\oplus W\).  Exterior multiplication
gives
\[
 \Lambda(V)\cong\Lambda(U)\otimes_k\Lambda(W),
\]
so \(P\) is free over \(P_U\).  Derived tensor therefore equals ordinary
tensor.  Since \(K_U=P_U/\Lambda^{\ge2}U\), base change gives the quotient in
`(2)`.

The transition \(U\subset U'\) adds relations killing every product whose
factors lie in \(U'\).  In the filtered colimit, every exterior monomial of
degree at least two vanishes: its finitely many factors span some
finite-dimensional \(U\).  No degree-zero or degree-one element is killed,
because every transition ideal is generated in degrees at least two.
Consequently the colimit is exactly the square-zero algebra \(k\oplus V\).

Filtered colimits of vector spaces are exact.  Therefore the same
calculation applies to cofibrant resolutions \(Q_U\to K_U\): flat base
change preserves each quasi-isomorphism, and filtered colimit preserves the
resulting quasi-isomorphisms.

## Application

For \(V=V_{F,\mathbb Q}\), `(3)` proves the algebraic continuous-cochain
target in `DAC_BAUMSLAG_MILNOR_PRO_REALIZATION`.  After tensoring
with \(\mathbb R\), it is
\[
 K_\ast^M(F)\otimes\mathbb R
 \cong\mathbb R\oplus V_{F,\mathbb R}.
\]
The remaining issue is geometric: prove finite-stage cochains satisfy the
relative Eilenberg--Moore comparison and commute with the pro-realization.

## Hostile audit

- Freeness uses a noncanonical complement, but flatness and `(2)` are
  canonical.
- The theorem concerns global algebraic base change.  It makes no
  stalkwise assertion and does not conflict with
  `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION`.
- It does not prove the twisted topological Eilenberg--Moore map `(4)` of the
  realization card.
- Integral exterior algebras need not be flat under arbitrary subgroup
  inclusions; the theorem is stated over a field.

**Verdict:** `FULLY PROVEN ON PAPER`.

## Lean status

### All three clauses landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerMilnorSquareZeroQuotient.lean` and
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerExteriorFreeness.lean`.  Axiom audit of every
declaration: `propext, Classical.choice, Quot.sound`.

**Clause 1 — freeness.**  `DeningerExteriorFreeness.lean`.

- `deningerZeroQuadraticForm_prod`, `deningerZeroProdIsometry` — the zero form of a product is the
  product of the zero forms, isometrically.
- `deningerExteriorProdEquiv` — **`Λ(M₁ ⊕ M₂) ≃ₐ[k] Λ(M₁) ᵍ⊗[k] Λ(M₂)`**: the exterior algebra is
  the Clifford algebra of the zero form, so mathlib's `CliffordAlgebra.prodEquiv` applies.  This is
  the card's "exterior multiplication gives `Λ(V) ≅ Λ(U) ⊗ Λ(W)`", with the Koszul signs made
  explicit by the graded tensor product.
- `deningerExteriorProdEquiv_inl`, `deningerGradedTmul_left` — the decomposition carries `Λ(M₁)`
  to the left factor, and left multiplication by the left factor carries no Koszul sign.
- `deningerExtProdTensorEquiv` — hence `Λ(M₁) ⊗_k Λ(M₂) ≃ₗ[Λ(M₁)] Λ(M₁ ⊕ M₂)`.
- `deningerExterior_free`, `deningerExteriorSubmodule_free`,
  `deningerExteriorSubmodule_free_of_field` — **clause 1**: `Λ(V)` is a free `Λ(U)`-module, for
  every subspace `U` (over a field a complement always exists).  Since `Λ(U)` is noncommutative,
  the module structure is the one induced by `Λ(U) → Λ(V)`; mathlib's `Module.Flat` is defined only
  over commutative rings, so "hence flat" is not restatable there, but freeness is the substantive
  input and gives flatness in any framework.

**Clauses 2 and 3 — base change and colimit.**  `DeningerMilnorSquareZeroQuotient.lean`.

The finite-stage algebra `P ⊗_{P_U} K_U = P/⟨Λ^{≥2}U⟩` is modelled as `RingQuot` of the relation
"the product of two vectors of `U` vanishes"; this is the correct model because `Λ(V)` is
noncommutative, so the relation ideal has to be two-sided.

- `DeningerExtSquareRel`, `DeningerExtSquareQuot` — the stage relation and its quotient.
- `deningerExtSquareQuot_universal` — **clause 2**: the stage quotient has the universal property
  of the base change `P ⊗_{P_U} K_U`, i.e. of the pushout of `K_U ← P_U → P`: an algebra map out of
  it is exactly an algebra map out of `P` killing the products of two vectors of `U`.  mathlib has
  no tensor product over a noncommutative ring, so the pushout property is the faithful statement of
  the base change, and it is what the card's proof uses.
- `deningerExtSquareStageMap` — the transition maps of the filtered system.
- `deningerExtToSquareZero`, `deningerExtSquareQuotEquiv` — **clause 3**: the total quotient is
  `k ⊕ V` with `V² = 0`, as `k`-algebras.  The quotient map and the obvious section are mutually
  inverse, because the exterior algebra is generated by its vectors and the section kills exactly
  the relations.
- `deningerExtSquareRel_finite`, `deningerRingQuotRel_finite`,
  `deningerExtSquareQuot_surjective` — **the filtered-colimit content**: every element of the total
  quotient comes from `P`, and every relation of the total quotient already holds at a finitely
  generated stage, since each relation involves only two vectors.  So no degree-zero or degree-one
  element is killed at any finite stage, and the colimit is exactly the square-zero algebra.

### Remaining

Nothing among the card's three clauses.  The closing remark — that `(2)`–`(3)` survive replacing
`K_U` by a cofibrant `P_U`-algebra resolution — is the standard consequence of the formalized
flatness together with exactness of filtered colimits; stating it in Lean would need a model
structure on differential graded algebras, which mathlib does not have.  The card's own
application (the geometric Eilenberg--Moore comparison and pro-realization) is explicitly outside
this theorem.
