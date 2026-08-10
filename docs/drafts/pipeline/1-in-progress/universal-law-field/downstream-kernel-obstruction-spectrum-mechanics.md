# Downstream-kernel obstruction-spectrum mechanics

- **Programme:** Universal Law Field
- **Question type:** MECHANISM / SET OF LAWS
- **Status:** [FINITE LINEAR CORE SUBSUMED BY ULF-LHSM-1] [ROUTE-INDEPENDENT]
  [STABLE/COMPLETION EXTENSION OPEN] [NO OBJECT SEARCH]

## Mechanism question

Given a history of law-forming transformations, which local failures remain genuine after all
future transformations have acted?

The answer cannot depend only on the cokernel of each local map. A later map may kill a local
failure. The invariant is therefore prospective: local failure modulo the kernel of its entire
future tail.

## Candidate laws

1. **Prospective survival.** A defect born at stage `i` survives globally only modulo the kernel of
   the remaining composite after stage `i`.
2. **Monotone filtration.** Successive tail images give a canonical filtration of total law birth.
3. **Layer law.** Each graded layer is local failure modulo both previous attainment and future
   erasure.
4. **No backward resurrection.** Once a class is killed by a future-tail kernel, later
   postcomposition cannot restore it as the same class.
5. **Factorization relativity.** Total obstruction may be invariant while its survival-depth
   filtration changes when the history is refactorized.
6. **Completion mutation.** Algebraic stages form an exact filtration; completion inserts source
   and target homology between successive grades.

## First exact gate -- closed

For three maps `D -> E -> K -> A`, prove that the cokernel of the total composite has a canonical
two-step filtration. Identify first grade with failure in `E` modulo `im R + ker(TS)`, second grade
with failure in `K` modulo `im S + ker T`, and final grade with `coker T`. Prove the middle layer by
a short exact sequence, not a dimension count.

ULF-DKO-1 closed this gate. ULF-LHSM-1 then proved the general finite history and exact
refactorization law in Lean.

## Next gates

1. Stable-category page construction from coherent fibres/cofibres.
2. Closure-doctrine homology between adjacent grades.
3. Exact-observer preservation and nonexact-observer exchange terms.
4. Coherence for multiple independent refactorizations.
5. Nonlinear replacement using pointed fibres/torsors rather than additive quotients.
6. Intervention law: how changing one stage migrates classes between survival depths.

Routes are late countermodels only. No RH endpoint or source selector belongs in the definition.
