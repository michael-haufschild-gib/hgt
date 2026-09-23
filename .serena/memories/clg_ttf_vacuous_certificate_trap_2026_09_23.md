# Certified-normalizer macros can silently return a vacuous certificate

`HTGeometry.compactGapCofactorHigherCertified%` (and `compactGapCertified%`) build a
`CompactGapNormalForm e` by running conv tactics on `Conv.mkConvGoalFor e` and then
closing every remaining goal with `goal.refl`. If the conv steps make **no progress**,
`refl` still succeeds and the macro returns `value := e` — a true but useless certificate.
The module compiles, the `_coeff_sliceN` theorem type-checks, and nothing signals failure.

Concretely found on 2026-09-23: `PolynomialODEEvenCompactGapCofactorTerm0Slice8` used
`compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm0 u w).coeff 8)`. The
higher normalizer's `norm_num` unfold list contains `evenCompactGapHeadPolynomial` and
`evenCompactGapCofactorTerm1 … Term6` but **not** `evenCompactGapCofactorTerm0`, so
nothing fired. `evenCompactGapCofactorTerm0Slice8 u w` was literally
`(evenCompactGapCofactorTerm0 u w).coeff 8`. The frontier map's claim that
"all seven degree-eight cofactor terms now have source proofs" was therefore wrong.

Symptom when assembling: `ring1` fails and the pp-truncated goal still mentions
`(evenCompactGapCofactorTerm0 u w).coeff 8`. Diagnose by
`unfold …SliceN; dsimp only [ …SliceNCertificate ]; trace_state` — if the goal is the
original coefficient expression, the certificate is vacuous.

Cheap non-vacuity check: the module's olean size. Real normalized slice modules are
tens of MB (Term0Slice8 went 0.2 MB → 64 MB after the fix). A suspiciously small olean
for a slice module means the normalization did nothing.

Fix pattern for term 0: do not normalize `(evenCompactGapCofactorTerm0 u w).coeff N`
directly. Factor first, as `PolynomialODEEvenCompactGapCofactorTerm0Slice7` does:
`Term0 = Head * (ReflectedTwelve + Correction)`, so
`coeff N = Σ_{k≤N} Head_k * (Twelve_{N-k} + Corr_{N-k})` via `evenCompactGapCoeff_mul_N`,
with `Corr_j = 0` for `j > 2` and `Twelve_j = 0` for `j > 8`; then normalize that
factored scalar with `compactGapCertified%` and an explicit `dsimp only` slice list.
This needs `evenCompactGapHeadSliceN`, which is produced by the higher normalizer
(it *does* unfold `evenCompactGapHeadPolynomial`).

General rule: any macro that ends in `refl`/`pruneSolvedGoals` after optional rewriting
must be treated as unverified until its output is inspected or consumed by a downstream
`ring1` that would fail on an unexpanded atom.
