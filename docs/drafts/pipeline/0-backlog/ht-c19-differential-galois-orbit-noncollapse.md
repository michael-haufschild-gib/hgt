# Differential-Galois orbit noncollapse — no finite algebraic symmetry quotient classifies f

- **ID:** ht-c19-differential-galois-orbit-noncollapse
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C19
- **Statement:** In a universal differential extension fixing `K`, the orbit of generic `f ∈ HT` under differential automorphisms does not collapse to a finite-dimensional algebraic quotient; any stabilizer visible through finite algebraic data is trivial or base-imposed.

## Goal
Block a **finite algebraic symmetry-quotient handle** classifying `f`. Door: symmetry quotients reveal hidden equations; this is the Galois-structural sibling of C18, directly adjacent to the "DSS = wild kernel free" framing.

## Door grade (hint)
**Structural / apex-adjacent.** The native instance is precisely the wild-kernel Galois structure (synthesis §2: `DSS ⟺ K free ⟺ H₂(Lie K)=0`, open). The generic-`f` statement is its model.

## Approach
Tie a finite algebraic quotient of the differential-automorphism orbit to a Picard–Vessiot finite-dim structure ⇒ contradiction with the zero differential ideal; for the native case route to the wild-kernel cohomology. Methods: 12 find an invariant, 15 strengthen, 18 right theorem.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `exponential-period-dss-cross.md`, `omega-splits-wild-kernel-freeness` (the `H_1/H_2` grading), `hypertranscendence-axis-synthesis.md` §2.
- `../../door/bucket-hypertranscendence.md` · C19; C18 (model-theoretic), C11 (monodromy).

## Log
- 2026-06-20 — created in 0-backlog from bucket C19. Graded structural / apex-adjacent.
