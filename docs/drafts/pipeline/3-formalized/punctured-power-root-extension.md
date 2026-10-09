# Power-root lifts extend across a zero with exact ramification order

- **ID:** PUNCTURED-POWER-ROOT-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; six public declarations verified)
- **Parent:** `../1-in-progress/xi-single-mark-infinite-cover-exclusion.md`
- **Statement:** If f is analytic at a with f(a)=0, n>0, and s is holomorphic on a punctured neighborhood with s^n=f, then setting s(a)=0 gives an analytic extension. The extended root has order satisfying ord_a(f)=n ord_a(s).

## Purpose and corpus audit

This supplies the local source-lift extension in a cap chart with projection b+ζ^n. It derives the ramification-order constraint from an existing punctured lift; no divisibility assumption is needed to perform the extension.

Corpus sources: mathlib `Analysis/Complex/RemovableSingularity.lean` proves continuity plus punctured holomorphy implies analyticity; `Analysis/Analytic/Order.lean` proves `analyticOrderAt_pow` and `analyticOrderNatAt_pow`. `Bottcher/AnalyticRoot.lean` upgrades continuous roots at nonzero values. The retrieved `ComplexAffineLineSimplyConnected.lean` requires separable fibers, so does not cover this ramification point. No external sources consulted; no claim of external novelty.

## Complete paper proof

[PROVED HERE, relative to the stated corpus theorems]

For every ε>0, continuity of f at a makes |f(z)|<ε^n on a sufficiently small neighborhood. On its punctured part, |s(z)|^n=|f(z)|, hence |s(z)|<ε. Thus s tends to zero at a. Redefining s(a)=0 gives a continuous function, holomorphic off a; the corpus removable-singularity theorem makes it analytic at a.

Its n-th power agrees with f off a and at a, hence on a full neighborhood. Invariance of analytic order under local equality, followed by `analyticOrderAt_pow`, gives the exact extended-natural order identity. The natural-order form gives n dividing the finite order whenever f is not locally zero. If f is locally zero the extension is also locally zero; no finite order is claimed for that case.

## Status

The complete local classification is formalized. Global cover construction, cap atlas and uniformization remain unproved.

## Converse and exact local classification

For a nonzero analytic germ with finite order m, a holomorphic punctured n-th root exists if and only if n divides m. Necessity follows from the extension and order identity above. For sufficiency, factor f(z)=(z−a)^m u(z), with u analytic and u(a)≠0, using the corpus order-factorization theorem. On a sufficiently small disk, u is analytic and nowhere zero. `Bottcher.exists_analyticOnNhd_pow_eq` gives an analytic n-th root v there. If m=nk, then s(z)=(z−a)^k v(z) is analytic and s^n=f near a, hence supplies the required punctured lift. This is a dependency-closed paper proof of the exact local ramification classification; it is not a global covering classification.

Extension, order identity, natural-order divisibility, converse construction and exact existence criterion all pass Lean.

## Formal verification

All six public declarations now pass Lean, including `exists_punctured_power_root_iff_dvd_analyticOrderNatAt`, the exact local existence criterion. Promoted to `HTGeometry/PuncturedPowerRoot.lean`, wired to its umbrella. Production leaf build PASS, 3427 jobs, no warnings. Six-declaration axiom audit PASS, only `propext`, `Classical.choice`, `Quot.sound`; `/tmp/hgt-punctured-power-root-axioms.log`. Final direct source check PASS, exit 0, empty `/tmp/hgt-punctured-power-root-final.log`.

Index refreshed. Latest global lint FAIL on eleven unrelated unreachable modules: RHTower.PaleyWienerPoissonMajorant, ThetaCuspRatioSourceConjugation; RHTower.ThetaCuspRatioKineticLeading.JetHeads, KineticCoefficients, MinorLeading, ReflectionHeads; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No own-module or forbidden-declaration errors. Log `/tmp/hgt-punctured-power-root-lint.log`; this is a snapshot of concurrent work.

Obsolete implementation scratch removed; axiom audit and verification logs retained.
