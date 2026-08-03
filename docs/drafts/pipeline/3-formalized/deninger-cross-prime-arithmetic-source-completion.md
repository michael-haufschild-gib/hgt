# Deninger cross-prime arithmetic source completion

**Stage:** 3 — formalized in Lean 4  
**Date:** 2026-08-03

Paper proof:

```text
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/
deninger-cross-prime-arithmetic-source-completion.md
```

Formal module:

```text
formal/GaloisForLFunctions/RHTower/
DeningerCalderonWittAllCrossPrimeArithmeticSourceCompletion.lean
```

## Formal content

- concrete span of all actual ordered cross-prime Calderón--Witt witnesses;
- canonical linear equivalence between finitely supported coefficients and
  that source span;
- coefficientwise embedding of the source span into the `ℓ²` packet;
- exact coordinate recovery and injectivity;
- dense range of finite arithmetic packets;
- dense range of the actual source-span embedding;
- exact vanishing of the old all-prime oriented boundary on the source span;
- uniqueness theorem: continuous observations zero on the source span are
  zero on the completion;
- corollary: every continuous extension agreeing with the old oriented
  boundary on the arithmetic core is the zero operator.

Capstones:

```text
deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan
deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_injective
deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_denseRange
deningerCalderonWittGlobalOrientedBoundary_crossPrimeSourceSpan
deningerCalderonWittCrossPrimeContinuousObservation_eq_zero_of_sourceSpan
deningerCalderonWittCrossPrimeContinuousOrientedBoundaryExtension_eq_zero
```

Direct `lake env lean` elaboration passes.  Module is wired into the
`RHTower` umbrella.  Targeted build and axiom audit are recorded in final
Route-L audit.
