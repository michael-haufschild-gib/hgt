# Minimal higher-handle collapse — the elimination meta-theorem for the whole bucket

- **ID:** ht-c28-minimal-handle-collapse
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C28
- **Statement:** Suppose a generic-looking HT function satisfies one proposed extra finite handle (shift, integral, transform, addition, finite-state). A minimal-complexity counterexample either is genuinely exceptional or collapses, after elimination, into a forbidden nonzero differential polynomial in `f`.

## Goal
State the **elimination meta-theorem** that grades every other card: "does eliminating handle `H` force `P(f)≡0`?" Door: this IS the (A)/(B) sorting criterion — yes→BRIDGE/provable, no→genuinely new. It is the methodological keystone of the bucket.

## Door grade (hint)
**FOUNDATIONAL (meta).** Proving the general collapse lemma would convert most of C01–C30 (the function-level handles) to BRIDGE in one stroke; the residue that resists collapse is the field's genuinely-new (B)-frontier.

## Approach
Formalize differential elimination (Ritt–Kolchin characteristic sets / differential resultants) for each handle family; prove a collapse-or-exception dichotomy. The cards that provably collapse are BRIDGE; the non-collapsing residue (e.g. value-level C12/C13, iteration C03, resurgence C29) is the research frontier. Methods: 16 minimal counterexample, 19 write the fake proof, 20 name the missing lemma.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- All function-level cards C01–C11, C14–C17, C20, C25, C27, C30 (it grades them); `hypertranscendence-axis-synthesis.md` §1 (the (A)/(B) divide it formalizes).

## Log
- 2026-06-20 — created in 0-backlog from bucket C28. Graded FOUNDATIONAL — the elimination meta-theorem grading the bucket.
