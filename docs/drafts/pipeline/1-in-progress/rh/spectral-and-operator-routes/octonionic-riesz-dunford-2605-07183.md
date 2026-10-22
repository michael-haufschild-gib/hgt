# Octonionic Riesz--Dunford functional calculus — full formalization ledger

- **ID:** `octonionic-riesz-dunford-2605-07183`
- **Stage:** `1-in-progress/not_new_scientific_knowledge`
- **Source:** Q. Huo, G. Ren, I. Sabadini, Z. Xu, *Octonionic Riesz--Dunford functional calculus*, arXiv:2605.07183v1 (2026), 68 pages.
- **Scope:** Formalize every lemma, proposition, theorem, and corollary in the paper that is not already present in Mathlib or this corpus, with no `sorry`, `admit`, project axiom, or unverified external premise.

## Duplication audit

- `formal_tools.py research "octonion octonionic Riesz Dunford para-linear regular inverse slice spectrum" --scan` found no octonionic development.
- Mathlib has real quaternions but no octonion type, Cayley--Dickson multiplication, alternative-algebra class, octonionic module, or slice-functional-calculus library.
- Existing corpus Cayley/resolvent modules concern different real/complex Hilbert-space operators and do not prove a paper result here.

## Source correction log

- **Lemma 8.5 proof typo:** HTML v1 line 2300 says its zero-determinant condition is “i.e. $s\notin[q]$”.  That contradicts the stated invertibility iff $s\notin[q]$ and the displayed condition `Re q = Re s`, `|Im q| = |Im s|`, which is exactly $s\in[q]$.  Formalize the mathematically consistent statement: `det(R_s-L_q)=0 ↔ s∈[q]`, hence invertible iff `s∉[q]`; do not encode the false sentence.

## Result inventory and dependency order

| Paper results | Dependency layer | Status |
| --- | --- | --- |
| Proposition 2.4; Proposition 2.10; Theorem 2.11 | Alternative octonion bimodules, real-part projection, slices and slice products | pending |
| Lemmas 2.15--2.16; Theorem 2.17; Corollary 2.18 | Slice topology, holomorphic functions, Cauchy integral | pending |
| Theorems 2.20--2.21; Lemmas 2.22, 2.24--2.25, 2.29, 2.31; Proposition 2.23; Theorem 2.27 | Octonionic bimodules and para-linear morphisms | pending |
| Theorem 3.2; Lemmas 3.3, 3.6 | Para-linear operator algebra and its product | pending |
| Lemma 4.1; Theorems 4.2--4.3; Lemma 4.4; Corollary 4.6 | Banach-module Neumann series and power-associative operators | pending |
| Lemmas 5.2, 5.4--5.6, 5.10--5.12 | Slice extensions/lifts and resolvent series | pending |
| Lemma 6.3; Theorems 6.4--6.7, 6.10--6.13 | Pull-back/push-forward spectra and topology | pending |
| Lemma 7.6; Theorems 7.7--7.8, 7.12, 7.14--7.15, 7.18 | Riesz--Dunford integral functional calculi | pending |
| Lemma 8.1; Propositions 8.2--8.3 | Power-associativity criteria for operators | pending |
| Lemmas 8.4--8.6; Theorems 8.7--8.8 | One-dimensional left-multiplication example | Lemmas 8.4--8.6 formalized, including 8.6 equations (8.7)--(8.8); Lemma 8.5's exact global invertibility classification formalized, while its displayed determinant factors remain pending; Theorems 8.7--8.8 pending |
| Proposition 9.1; Lemma 9.2; Theorems 9.4--9.6 | Spectral mapping and composition | pending |

## Completed foundation

- `HTGeometry/Octonion/Alternative.lean`: project-owned alternative-algebra API, adapted from the useful parts of `tmp/jordan/Alternative.lean` rather than copied wholesale.
- `HTGeometry/Octonion/Basic.lean`: concrete real division octonions as a corrected Cayley--Dickson doubling of Mathlib quaternions.  It includes positive-definite norm square and explicit left/right inverse identities.  Under the source multiplication convention, parameter `c = 1` is required for the new unit to square to `-1`; `c = -1` would instead be split.
- `HTGeometry/Octonion/ResolventIdentity.lean`: Lemma 8.4 equation (8.5), both pointwise and function-extensional forms.
- `HTGeometry/Octonion/Artin.lean` and `HTGeometry/Octonion/GeneratedSubalgebra.lean`: word-level Artin theorem, its real-linear/multiplicative subalgebra lift, and Lemma 8.4 equation (8.6), pointwise and subtype-operator forms.  The completed card is `pipeline/3-formalized/not_new_scientific_knowledge/octonionic-riesz-dunford-2605-07183-lemma-8-4.md`.
- `HTGeometry/Octonion/RestrictedInverse.lean` and `HTGeometry/Octonion/Conjugacy.lean`: the two-sided restricted inverse formula of Lemma 8.6 equation (8.7).  `Conjugacy.lean` proves `Q_s(q)=0 ↔ s∈[q]` for the source-faithful sphere (equal real part and imaginary norm), discharging the paper condition `s∉[q]` without any additional assumption.
- `HTGeometry/Octonion/Sylvester.lean`: Lemma 8.5's exact global real-linear classification, `Function.Bijective (R_s-L_q) ↔ s∉[q]`, and coordinate-free determinant zero locus, `LinearMap.det (R_s-L_q)=0 ↔ s∈[q]`.  Its sphere-side witness is constructive, including the antipodal case; its off-sphere direction is derived inside the appropriate Artin subalgebra.  The paper's precise determinant factorization is not yet formalized.
- `HTGeometry/Octonion/ComplexSlice.lean` and `HTGeometry/Octonion/SliceResolvent.lean`: a concrete associative complex-slice carrier, its commutativity law, and Lemma 8.6 equation (8.8).  The latter proves the exact displayed formula on every `C_J` element, including the real-parameter branch where `C_J` is not necessarily contained in the two-generator algebra; `resolventDifference_eq_sliceFormula_iff` additionally gives its unique-preimage form from the global Lemma 8.5 classification.

## Next closed target

Lemma 8.5's remaining displayed determinant calculation: establish the exact factorization of `det(R_s-L_q)` and its zero locus, without encoding the HTML typo.  The global invertibility equivalence itself is already closed in `Octonion/Sylvester.lean`.

## Verification policy

- Search corpus with `formal_tools.py research` before every reusable theorem.
- Prototype only in `/tmp` with `lake env lean`; final source checks use the same command and only targeted `lake build <module>`.
- Print theorem axioms from `/tmp`; accept only Lean's standard logical kernel axioms, never project-added axioms.
- Wire complete modules into `GaloisForLFunctions.HTGeometry` without full umbrella builds.
