# A nontrivial locally constant Weyl character at every finite place

- **ID:** `field-one-padic-weyl-character`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-spherical-weyl-multiplier-bridge`
- **Statement:** for every prime \(p\), there exists a nontrivial locally constant complex
  additive character of \(\mathbb Q_p\), trivial on \(\mathbb Z_p\) and nontrivial on \(p^{-1}\);
  its Weyl multipliers preserve compactly supported locally constant functions.

## Goal

Close the finite-place existence and preservation portion of the typed spherical-to-analytic
bridge without assuming coordinates, the trace formula, positivity, zero data, or RH.

## Theorem

Let \(p\) be prime, put
\[
  Q_p^{\mathrm{pp}}=\mathbb Q_p/\mathbb Z_p,
\]
and let \(a_p\) be the class of \(p^{-1}\).

1. \(a_p\) has exact additive order \(p\).
2. The cyclic subgroup \(\langle a_p\rangle\) is isomorphic to \(\mathbb Z/p\mathbb Z\), with
   \(1\mapsto a_p\).
3. The normalized map
   \[
     \langle a_p\rangle\longrightarrow\mathbb R/\mathbb Z,\qquad
     a_p\longmapsto 1/p
   \]
   extends to \(Q_p^{\mathrm{pp}}\).
4. Pullback gives an additive character
   \[
     \psi_p:\mathbb Q_p\longrightarrow\mathbb C^\times
   \]
   which is trivial on \(\mathbb Z_p\), nontrivial at \(p^{-1}\), and locally constant.
5. For every \(r\in\mathbb Q_p\), multiplication by \(x\mapsto\psi_p(rx)\) preserves the space
   of compactly supported locally constant complex functions. These multipliers satisfy the
   additive composition, inverse, root, and unit-scaling covariance laws.

## Proof

The relation \(p\cdot p^{-1}=1\in\mathbb Z_p\) shows \(p a_p=0\). On the other hand,
\(\lVert p^{-1}\rVert_p=p>1\), so \(p^{-1}\notin\mathbb Z_p\) and \(a_p\ne0\). Since \(p\) is
prime, the additive order of \(a_p\), a nonunit divisor of \(p\), is exactly \(p\).

The generated subgroup is therefore cyclic of cardinality \(p\), hence identified with
\(\mathbb Z/p\mathbb Z\). Send its generator to \(1/p\) modulo \(\mathbb Z\). The group
\(\mathbb R/\mathbb Z\) is divisible and therefore injective in the category of abelian groups,
so this homomorphism extends to all of \(Q_p^{\mathrm{pp}}\). Pulling back along the quotient and
then applying the circle embedding produces \(\psi_p\).

Its kernel contains \(\mathbb Z_p\). Since \(\mathbb Z_p\) is open in \(\mathbb Q_p\), every coset
has a neighborhood on which \(\psi_p\) is constant. Thus \(\psi_p\) is locally constant.
Multiplication by a locally constant function preserves local constancy; its unit modulus does
not enlarge support. The composition, inverse, root, and scaling laws follow from additivity.

## Hostile audit and exact boundary

- **No standard-character overclaim:** injectivity supplies a noncanonical extension beyond
  \(\langle a_p\rangle\). The construction fixes only depth-one normalization.
- **Not yet proved:** compatibility at every depth \(p^{-n}\), the canonical standard character,
  the restricted product over all finite places, semilocal faithfulness, and finite-place
  \(L^2\) unitarity.
- **Strongest positive survivor:** finite-place Bruhat preservation needs only local constancy;
  canonical all-depth normalization is a later assembly requirement, not a prerequisite for
  local existence.

## Gates

- [x] 0 → 1: exact quotient, character, and test-function types identified
- [x] 1 → 2: dependency-closed proof above
- [x] 2 → 3: unconditional Lean theorem, direct leaf check, and axiom audit
- [ ] 3 → 4: publication-ready integration

## Lean certificate

- **Generic module:**
  `GaloisForLFunctions.RHTower.FieldOneLocallyConstantWeylMultiplier`
- **Prime-specific module:**
  `GaloisForLFunctions.RHTower.FieldOnePadicWeylCharacter`
- **Core theorems:** `fieldOnePadicPrincipalClass_addOrderOf`,
  `fieldOnePadicUnitAddCircleCharacter_vanishes_on_integers`,
  `fieldOnePadicAddChar_ne_one`, `fieldOnePadicAddChar_isLocallyConstant`,
  `fieldOnePadicWeylMultiplier_add`, `fieldOnePadicWeylMultiplier_neg_left`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` on the order, nontriviality,
  local-constancy, and multiplier-composition theorems reports only standard Lean principles
  `propext`, `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved
  for final audit.

## Log

- 2026-07-26 — Extracted from the finite-place obstruction in C16. Formalized without
  computation and without any RH premise.
