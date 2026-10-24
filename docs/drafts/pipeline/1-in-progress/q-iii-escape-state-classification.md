# Q-III: escape states, repairing ideals, and the Kronecker curve

- **ID:** q-iii-escape-state-classification
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-2410/opus.md`, §3 Q-III and §2.1.
- **Statement:** Classify actual normalized receiver escape modules, their signed data, annihilator hulls, and indices; determine whether their generators come from the translated off-line zero hull on the Kronecker curve.

## Goal

Full answer to Q-III, unconditional Lean proofs of the answer and its corollaries,
and applications wherever they advance the research corpus. Partial structural
lemmas do not complete this goal. No use of the hgtl7 skill, numerical experiments,
new analytic assumptions, or unproved interfaces.

## Completion requirements

- [ ] Classify the actual limits from `exists_cofactorGram_limit`, including
  antipodality, pole trace, and forcing split.
- [ ] Construct their critical Wiener algebra modules and prove cyclicity.
- [ ] Establish the repairing-ideal/annihilator bridge and exact hull relation.
- [ ] Decide Kronecker-curve generation and translated-zero-hull containment.
- [ ] Establish the correct index formula, including multiplicities and possible
  infinite-dimensional cases.
- [ ] Audit the proposed exponent law and moving-translation covariance.
- [ ] Audit white-noise and golden-datum calibrations and formalize their exact
  positive conclusions.
- [ ] Formalize all resulting corollaries and relevant cross-programme applications.
- [ ] Check each new module with `lake --old env lean`, inspect transitive axioms,
  wire umbrellas without compiling them, remove own scratch artifacts.

## Approach

Search the corpus before mathlib; inspect source statements rather than relying
on report prose. Alternate precise conjectures, dependency-closed paper proofs,
Lean proofs, and revised conjectures informed by counterexamples. Preserve the
distinction between arbitrary PSD dilation kernels and actual receiver limits.

## Current evidence and conjectures

The report has been read in full. Its module construction, exponent law, and
white-noise exclusion are explicitly marked unproved. Initial search locates
the existing cofactor covariance and obstruction-hull infrastructure. Several
unrelated worktree edits predate this task and are being preserved.

1. **C1:** Every paid finitely supported convolution has zero normalized Gram
   norm along every escaping receiver subsequence. Check the exact receiver and
   convolution conventions before attempting its closure in the Wiener norm.
2. **C2:** The hull of an individual escape module is contained in the paid
   ideal hull; equality need not follow from this inclusion.
3. **C3:** The report's regular-variation scaling requires a separate proof of
   asymptotic pronic dilation, not merely the existing contraction inequality.

## Gates

- [x] 0 → 1: question and required distinctions recorded.
- [ ] 1 → 2: complete classification with no open mathematical dependency.
- [ ] 2 → 3: Lean proofs and axiom audits for every required result.

## Log

- 2026-10-25 — Read attachment and full report; began source audit and corpus searches.
