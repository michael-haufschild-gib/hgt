# Local-circuit two-memory capacity law

- **ID:** `local-circuit-two-memory-capacity-law`
- **Stage:** 3 -- formalized
- **Type:** exact composition / intrinsic circuit-capacity shortcut threshold
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [BROWN ALIGNMENT RATE OPEN]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/LocalCircuitTwoMemoryCapacityLaw.lean`
- **Parents:** `local-circuit-trace-capacity-law.md`,
  `static-circuit-two-memory-orthogonality-law.md`

## Exact theorem

Let a finite local gate alphabet have symmetric independence relation and dependence degree at most
`Delta`.  Quotient length-`ell` words by adjacent swaps of independent gates.  Let the resulting
trace classes index real-Hilbert target moment vectors.  Under the nested-projection and invariant
sector conditions of the two-memory law, any trace target with collision at least `a>=0` forces

\[
\langle r,q\rangle\ge
 {a\over {M+\ell-1\choose\ell}2^{\Delta\ell}}
 -\bigl(\langle u,u\rangle+\langle c,q\rangle\bigr).
\]

If the evolution returns exactly, the normalized seed is one trace target, and all target
collisions are nonnegative, the same theorem holds with `a=1`.

This is stronger than raw word counting: commuting-gate permutations are removed before the target
moment and contribute no artificial `M^ell` penalty.

## Principal declarations

- `fixedTracePreparationMoment`
- `fixedTrace_target_forces_memory_realign`
- `fixedTrace_recurrence_forces_memory_realign`

## Hostile boundary

This theorem does not prove that ordinary local-Hamiltonian dynamics suppresses the alignment.  It
proves the exact capacity-normalized implication that every successful shortcut must satisfy.  The
remaining Brown frontier is therefore a quenched, return/carrier-excised upper bound on this signed
alignment along the depth--time skeleton.  Neither heap counting alone nor conserved-memory
orthogonality supplies that rate.

The theorem also assumes the physical endpoint map is already well defined on trace classes; an
application must prove disjoint-support swaps give identical moment targets for its concrete gate
model.

## Audit

- development check: `lake env lean GaloisForLFunctions/RHTower/LocalCircuitTwoMemoryCapacityLaw.lean`;
- imported by `GaloisForLFunctions.RHTower`;
- final build: `lake build GaloisForLFunctions.RHTower.LocalCircuitTwoMemoryCapacityLaw`
  (`2626/2626`);
- both headline theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
