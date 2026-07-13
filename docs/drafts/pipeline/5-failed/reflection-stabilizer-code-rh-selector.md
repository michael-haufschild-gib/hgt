# Reflection stabilizer-code RH selector

- **ID:** `reflection-stabilizer-code-rh-selector`
- **Stage:** 5-failed
- **Type:** `[FALSIFIED]`, `[FRINGE DETOUR]`, `[POSITIVE RESIDUE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/ReflectionStabilizerCodeBlindness.lean`
- **Consumer:** `../1-in-progress/fermionic-fe-projector-lefschetz-rh.md`

## Proposed chain

```text
completed source
  -> a reflection-stabilizer quantum code on Xi residue modes
  -> physical code space is the +1 FE sector
  -> a free reflected zero pair is removed as an error syndrome
  -> every zero is reflection fixed
  -> RH.
```

The stabilizer step does not remove a free pair. It only chooses its symmetric line. For any
coefficient type `A`, the `+1` swap-stabilized sector of `A x A` is canonically equivalent to `A`
via `a -> (a,a)`. A fixed singleton also has code space `A`. Once the ambient embedding and the
discarded syndrome are forgotten, the two orbit types are indistinguishable.

Equivalently, a free reflected pair is not an uncorrectable inconsistency. It supplies a perfectly
valid symmetric codeword and a separate anti-invariant syndrome. Declaring the latter absent is
exactly the fixed-versus-free conclusion the construction was supposed to prove.

## Positive residue

The formal survivor is the anti-invariant syndrome

```text
delta(a,b)=a-b,
delta=0  iff  (a,b) is swap stabilized.
```

A live code-theoretic chain must retain and source-annihilate the complete syndrome module before
projecting to the code space. This is precisely the fermionic boundary problem already isolated by
`ReflectionFermionBoundary`: a free orbit supplies an explicit anti-invariant vector, and RH is
equivalent to injectivity of `1+J_FE`. Stabilizer language contributes no annihilation mechanism;
it returns the same open source contraction problem.

## Two-ended verdict

The source end is unconstructed, and the proposed middle is false even for one abstract two-cycle.
The right-hand implication would become valid only after assuming the anti-invariant syndrome
module vanishes. That is the existing RH-bearing open core, not a quantum-code theorem.
