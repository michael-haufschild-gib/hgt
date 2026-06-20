# Singularity-skeleton nonfiniteness — no finite algebraic map of all singularities

- **ID:** ht-c10-singularity-skeleton-nonfiniteness
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C10
- **Statement:** For generic meromorphic / continuable `f ∈ HT`, the singular set is not governed by a finite algebraic skeleton (finite union of algebraic loci, finite arithmetic lattice, or finite orbit under algebraic maps), unless separately imposed.

## Goal
Block a **finite geometric handle** on the singularities. Door: tests the "no analytic pathology" caveat — HT does not force singularity wildness, so the claim is only that finite singularity geometry is generically incompatible with no-finite-handle.

## Door grade (hint)
**BRIDGE-likely, with care:** must be a *generic* statement (Gamma's regular pole lattice is a counterexample to any universal form).

## Approach
Elimination test: a finite-orbit/lattice singular set is the signature of a fixed-coefficient ODE (Fuchsian/algebraic) ⇒ a differential polynomial ⇒ BRIDGE; the generic claim is that no such finite skeleton co-exists. Attack-as-false on Γ first. Methods: 5 make it visual, 10 extreme cases, 23 classify boundary cases.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C10; C11 (monodromy), C14 (zero incidence).

## Log
- 2026-06-20 — created in 0-backlog from bucket C10.
