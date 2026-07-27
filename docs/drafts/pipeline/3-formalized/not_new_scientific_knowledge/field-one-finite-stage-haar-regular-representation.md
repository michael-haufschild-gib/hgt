# Finite-stage Haar module and idele-class regular representation

- **ID:** `field-one-finite-stage-haar-regular-representation`
- **Stage:** 3-formalized
- **Type:** THEOREM / MEASURE AND HILBERT CONSTRUCTION
- **Label:** `F1-FINITE-STAGE-HAAR-L2-1`
- **Parent:** `field-one-finite-stage-module`
- **Target:** identify the finite-stage norm module with additive Haar
  scaling, prove diagonal \(S\)-unit measure invariance, and construct the
  unitary left-regular representation on idele-class Haar \(L^2\).

## Theorem

For every finite set \(S_f\) of rational finite places and every
\[
  u\in\mathbb A_S^\times
    =\mathbb R^\times\times\prod_{v\in S_f}\mathbb Q_v^\times,
\]
the distributive Haar character for multiplication on the additive group
\(\mathbb A_S\) is
\[
  \operatorname{distribHaarChar}_{\mathbb A_S}(u)
    =|u_\infty|\prod_{v\in S_f}|u_v|
    =\delta_S(u).
\]
Thus every additive Haar measure \(\mu\) obeys
\[
  \mu(uE)=\delta_S(u)\mu(E),
\]
and every diagonal rational \(S\)-unit preserves \(\mu\). The character
descends to \(C_{\mathbb Q,S}\) and equals the previously constructed
idele-class module.

The locally compact, second-countable group \(C_{\mathbb Q,S}\) has Borel
left Haar measure. Its complex \(L^2\) space carries the unitary
left-regular representation
\[
  (\lambda_S(c)f)(x)=f(c^{-1}x).
\]

## Formal proof

- `FieldOneHaarCharacterProducts.lean`: real, product, and finite dependent
  product Haar-character identities.
- `FieldOnePadicHaarScaling.lean`: residue-kernel principal-ideal identity,
  exact index \(p\), and own-prime factor \(p^{-1}\).
- `FieldOneLocalHaarModule.lean`: arbitrary-unit local identity at every
  rational adic completion.
- `FieldOneFiniteStageHaarScaling.lean`: finite-product assembly, equality
  with \(\delta_S\), quotient descent, all-idele scaling, and \(S\)-unit
  invariance.
- `FieldOneFiniteStageClassModule.lean`: continuous module on \(X_S\),
  continuous injective orbit-of-one map \(C_S\to X_S\), module
  compatibility, and equivariant scaling.
- `FieldOneFiniteStageIdeleLocusMeasure.lean`: open coordinatewise idele
  locus, open idele-class image in \(X_S\), and zero product-additive-Haar
  measure of the prequotient coordinate hyperplanes.
- `FieldOneFiniteStageIdeleClassHaarL2.lean`: Borel Haar measure,
  idele-class \(L^2\), and monoid-homomorphic unitary left translations.

## No-go closure

- **Exact killing mechanism:** Haar \(L^2(C_{\mathbb Q,S})\) is not
  definitionally \(L^2(X_S)\). The primary-source comparison uses the
  conull idele locus and a Radon--Nikodym multiplier relating additive and
  multiplicative Haar.
- **Strongest positive survivor:** local normalization, product scaling,
  diagonal invariance, group Haar \(L^2\), and the full regular unitary
  representation are unconditional Lean theorems.
- **New insight:** the remaining measure gate is the additive-orbit
  quotient/disintegration and Radon--Nikodym comparison, not the product
  formula or existence of a group representation.

## Audit

- [x] Existing repository and mathlib support searched first.
- [x] Direct cached `lake env lean <file>` checks passed for all seven leaves.
- [x] `#print axioms` for the Haar-scaling leaves reports only `propext`,
      `Classical.choice`, and `Quot.sound`.
- [x] `#print axioms` for the class-module and idele-class Haar-\(L^2\)
      leaves reports only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] No `sorry`, `admit`, custom axiom, opaque declaration, unsafe
      declaration, numerical computation, positivity premise, Xi-divisor
      premise, or RH premise.
