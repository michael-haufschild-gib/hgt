# Topological largeness of HT — HT is residual, finite-handle conditions are nowhere-dense

- **ID:** ht-c22-topological-largeness
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C22
- **Statement:** In a suitable function space with countably specified base field and topology, the HT functions form a residual (comeager / `G_δ`-like) set, while functions with finite algebraic-differential handles form a thin union of closed nowhere-dense conditions.

## Goal
Establish **topological typicality**: HT is the generic case, finite-handle is exceptional. Door: a Baire-category form of "constraint, not flow" — a genuinely different kind of evidence than the (A) absence proofs.

## Door grade (hint)
**Genuinely-new flavour (not a Hölder collapse).** Each candidate differential-polynomial identity `{P(f)≡0}` is a closed condition; the work is choosing the topology and handling coefficient cardinality.

## Approach
Show each `{f : P(f)≡0}` is closed nowhere-dense (a single nonzero `P` excludes a dense open set), then countable union over `P ∈ K{Y}` (needs a countable base) ⇒ complement comeager. Methods: 8 look for similar objects (Baire genericity), 11 run experiments, 18 right theorem.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C22; C23 (perturbation), C24 (random — measure analogue).

## Log
- 2026-06-20 — created in 0-backlog from bucket C22.
