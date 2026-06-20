# Zero-incidence nonlaw — no finite algebraic law tying zeros of derivative orders

- **ID:** ht-c14-zero-incidence-nonlaw
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C14
- **Statement:** For generic `f ∈ HT`, the zero sets of `f, f', f'', …` satisfy no finite algebraic incidence law (no fixed algebraic rule forcing zeros of one derivative order to determine another's).

## Goal
Block a **finite geometric law** for where the derivative tower vanishes. Door: ODEs impose strong zero interlacing/multiplicity; HT removes the finite-ODE source, so generic absence is natural.

## Door grade (hint)
**BRIDGE-likely.** A finite zero-incidence law is typically the trace of a finite-order ODE (Sturm/Wronskian structure).

## Approach
Elimination test: an algebraic incidence law among zero sets implies a Wronskian/resultant identity among `f`-jets ⇒ a differential polynomial ⇒ BRIDGE. Methods: 5 make it visual, 10 extreme cases, 23 classify boundary cases.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C14; C25 (Wronskian rank), C10 (singularities).

## Log
- 2026-06-20 — created in 0-backlog from bucket C14.
