# Model-theoretic orthogonality — HT generic type orthogonal to DA varieties

- **ID:** ht-c18-model-theoretic-orthogonality
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C18
- **Statement:** In a saturated differential field, the generic type of an HT function is orthogonal to finite-dimensional DA varieties and to the constant field, except for base-imposed relations.

## Goal
Upgrade "the differential ideal of relations is zero" (note §12) to a **model-theoretic orthogonality** — a structural form of "no hidden finite DA coordinates". Door: connects HT to the differential-indeterminate / wild-kernel structural framing (synthesis §2).

## Door grade (hint)
**Structural / apex-adjacent.** Stronger than the function-level BRIDGE facts; lands in differential model theory (Marker–Pillay, ω-stability of `DCF_0`). The native analogue is the orbit/quotient structure of the wild kernel.

## Approach
Show the generic HT type has trivial/`U`-rank-`ω` interaction with finite-rank DA types via the zero differential ideal; relate orthogonality to the no-relation statement. Methods: 15 strengthen, 17 change representation, 18 right theorem (orthogonality calculus in `DCF_0`).

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `hypertranscendence-axis-synthesis.md` §2 (differential indeterminate / wild kernel); `../../door/bucket-hypertranscendence.md` · C18; C19 (Galois orbit).

## Log
- 2026-06-20 — created in 0-backlog from bucket C18. Graded structural / apex-adjacent.
