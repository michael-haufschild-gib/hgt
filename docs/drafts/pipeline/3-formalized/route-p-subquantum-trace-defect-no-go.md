# Route P subquantum trace-defect no-go

- **ID:** P-ASD
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** P
- **Statement:** `[LEAN-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` Any matrix-complete Route-P boundary restriction whose total additive trace defect has eventual density strictly below the one-zero quantum `2` forces RH. Under failure of RH, every such restriction must satisfy `2N ≤ sourceBudget + defect(N)` for every repeated-copy packet size `N`.

## RH proof chain

`subquantum-density approximate Loewner restriction → no strict-right Xi copy → RH`.
This kills approximate matrix-complete transport as an independent repair of the exact Route-P restriction law. A survivor must pay at least one full zero quantum per repeated target copy, hence cannot hide the missing boundary order in a sublinear or subquantum approximation error.

## Frontier

- `[CORPUS]` `routePStrictRightZeroBaseCauchyCubicCharge_ge_two`: one strict-right copy costs at least `2`.
- `[CORPUS]` `re_trace_routePPrimitiveBurnolWindowGramMatrix_le_budget` and `routePPrimitiveBaseCauchyCubicTraceBudget_lt_quantum`: every injectively labelled primitive source packet has total trace strictly below `2`.
- `[CORPUS]` `matrix_re_trace_mono_of_frankensteinLoewnerLE`: Loewner domination controls real trace.
- `[CORPUS]` `routePMatrixCompleteBoundaryRestrictionLaw_iff_riemannHypothesis` treats exact domination only; corpus search found no approximate defect-density classification.
- `[LITERATURE]` Burnol's Nyman--Beurling lower bounds and Sonine/co-Poisson systems quantify different Hilbert-space approximation obstructions: https://arxiv.org/abs/math/0103058, https://arxiv.org/abs/math/0203120.
- `[LITERATURE]` Connes--Consani analyze positivity/trace obstructions for scaling-Hamiltonian cutoffs: https://arxiv.org/abs/1910.14368.
- `[LITERATURE]` Chuk's finite Weil matrices quantify compact-window positivity and collapsing ground-state gaps, not source-to-zero Gram Loewner transport or repeated-copy trace-defect density: https://arxiv.org/abs/2608.24827.
- `[LITERATURE]` Rodgers states a generic functorial Loewner-selector no-go schema (Zenodo 18602639), but does not contain the primitive source budget, the strict-right Cauchy-cube quantum, or this asymptotic trace-density law.

## Hostile attack

- Repeated target copies are allowed by the exact matrix-complete interface; only the primitive source labels are required injective.
- No positivity or Hermiticity of the additive error is needed: Loewner positivity of the completed difference plus its real trace cap suffices.
- The result is a route-class kill, not an RH producer: its right side is vacuous under RH because `XiRightZeroCopy` is empty.
- **Verdict:** `SURVIVES HOSTILE AUDIT`.

## Paper proof

Assume RH fails and choose one `q : XiRightZeroCopy`. For every `N`, feed the constant packet `i ↦ q` to an approximate matrix restriction. The target trace is a sum of `N` diagonal Cauchy-cube charges, each at least `2`, hence is at least `2N`. Loewner trace monotonicity bounds it by the primitive source trace plus the additive error trace. Injectivity of the primitive labels bounds the source trace by the fixed budget `B<2`; the error cap gives
`2N ≤ B + D(N)`.

If `D(N) ≤ cN` eventually for some `c<2`, choose `N` beyond that tail with `B < (2-c)N`. Then `B+D(N)<2N`, contradiction. Hence the approximate restriction excludes every strict-right Xi copy and proves RH. Conversely, under RH `XiRightZeroCopy` is empty, so `D=0`, `c=1`, and zero error realize the universally quantified restriction vacuously. No conjectural input remains.

## Gates

- [x] 0 → 1 in-progress: exact route class, corpus and primary-literature audits, hostile attack
- [x] 1 → 2 fully-proven: dependency-closed repeated-packet quantum proof
- [x] 2 → 3 formalized: `RoutePMatrixCompleteSubquantumTraceDefectNoGo.lean`; source check and targeted module build pass; axiom audit is `[propext, Classical.choice, Quot.sound]`
