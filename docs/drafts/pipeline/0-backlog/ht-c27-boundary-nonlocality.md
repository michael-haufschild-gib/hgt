# Boundary nonlocality DA/HT — no finite-local certificate separates the classes

- **ID:** ht-c27-boundary-nonlocality
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C27
- **Statement:** No finite-order contact between `f` and a DA function (matching values and derivatives to any fixed finite order at finitely many points) forces HT `f` into the DA class. The DA/HT boundary is global and identity-level, not finite-local.

## Goal
Make precise that HT is the **absence of an identity**, not a finite jet condition. Door: characterizes the DA/HT boundary as a research object (complements the identifiability card C15).

## Door grade (hint)
**BRIDGE-likely (foundational).** Provable by construction: finite-order contact constrains only finitely many jets, leaving the differential ideal free.

## Approach
Construction: given finite-order contact data with a DA function, build an HT completion sharing that contact (free differential-indeterminate tail beyond the matched order). Methods: 10 extreme cases, 16 minimal counterexample, 23 classify boundary cases.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C27; C15 (finite-sampling nonidentifiability).

## Log
- 2026-06-20 — created in 0-backlog from bucket C27.
