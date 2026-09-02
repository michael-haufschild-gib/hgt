# Integral curved Tate coherent-primitive index law

- **ID:** `ULF-ICTCPI-1`
- **Stage:** 3-formalized
- **Type:** unconditional proof-carrying completion fusion theorem
- **Status:** dependency-closed paper proof; Lean-certified

## Big-picture law

Completion must act on proofs of exactness, not only on completed vectors or truth values. At each
finite stage a boundary primitive exists. A completed boundary remains exact only when those
primitives can be chosen as one compatible inverse history. Their transition mismatch is a cocycle;
its Roos class is the obstruction to a coherent correction.

## Corpus audit

1. `SourceMarkedExFlag` retains fixed-marker survival but no boundary primitive; convergence to an
   exact state has no positive survival test and is therefore vacuous.
2. `exists_coherent_representatives_iff_mismatch_mem_range` proves the general primitive-coherence
   obstruction law, and `boundaryObstruction_eq_zero_iff` identifies it with `lim^1`.
3. `routeRTailRoos_primitive_unique` proves that the concrete diagonal mismatch has only one
   unrestricted primitive: the literal negative-tail family.
4. `routeRDiagonalTailRoosClass_eq_zero_iff_summable` says this primitive belongs to the fixed
   summable boundary ideal exactly when the global coefficient sequence is summable.
5. `preDivisorTransverseDerivedCompletionClass_eq_criticalWall` identifies this Roos class with the
   zero-independent reflection-normal transverse class.
6. `ULF-ICTFPI-1` identifies its Xi zero radical with evaluated `det C_T`, source-marked survival
   convergence, formation-completion escape, and compact recurrence descent.
7. The fixed-tail bond prepends zero and is not surjective. Its reaches keep losing new head
   coordinates, so blanket Mittag--Leffler stability is unavailable and would erase the carrier.
8. Orthogonal theta-shell replication carries the same quadratic ghost on every independent shell;
   its recovery is sequentially closable exactly on the critical line.
9. Every response factoring through bounded formation and bounded recovery on one source norm is
   sequentially closable; unbounded graph loading is the classified escape.

## Statement and proof

For `s in C`, let `P(s)` be the type of summable primitive histories `h_n` satisfying the literal
Roos equation for the critical-wall sequence at centered rate `2 Re(s)-1`.

1. `P(s)` is always subsingleton: ambient primitive rigidity forces every member to be the literal
   negative-tail family.
2. `P(s)` is inhabited iff the pre-divisor transverse Roos class vanishes.
3. On an Xi copy `q`, `P(q)` is inhabited iff the integral formation index `I(q)` vanishes.
4. The same existence is equivalent to fixed-marker convergence and compact recurrence descent.
5. On an Xi copy, `P(q)` is inhabited iff orthogonally replicated theta recovery is sequentially
   closable.
6. Any exact factorization of that shell recovery through bounded ingress and bounded egress on one
   normed completion constructs the unique member of `P(q)`.
7. Every Xi primitive fibre is inhabited iff RH.

Each clause follows by unfolding the primitive fibre, applying quotient-zero/range membership,
then using the certified Roos, integral-index, and recurrence equivalences. No new premise enters.

## Exact RH closure

The remaining source theorem is now precise: construct the literal negative-tail primitive as a
summable arithmetic history before Xi specialization, or construct a different zero-independent
primitive tower with a coefficient-faithful map to this one. After Xi base change, uniqueness makes
its image the required primitive; the theorem forces every `I(q)=0`, hence RH.

Equivalently, construct one occurrence-independent shell GNS formation whose ingress and recovery
are both bounded and whose algebraic core recovers the literal theta quadratic ghost. The bounded
factorization theorem then supplies shell closability, and clause 5 supplies the same primitive.

Producing a primitive separately after selecting `q`, proving Boolean boundary membership, or
making the entire target tower Mittag--Leffler is invalid. The first is RH-equivalent, the second
forgets the witness, and the third contradicts the target tower's strict head-loss geometry.
