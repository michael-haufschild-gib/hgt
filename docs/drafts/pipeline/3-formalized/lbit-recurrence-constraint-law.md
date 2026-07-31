# L-bit recurrence-constraint law

- **ID:** `lbit-recurrence-constraint-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/LBitRecurrenceConstraintLaw.lean`

## Exact law

For every finite \(N\)-mode l-bit Hamiltonian,
\[
  \boxed{
  \tau(J)+
  \operatorname{rank}_{\mathbb Q}L_{E_J}^{\mathrm{proj}}
  =2^N-1.}
\]

Thus every noninteracting localized spectrum has
\[
  \operatorname{rank}_{\mathbb Q}L_{E_J}^{\mathrm{proj}}
  \ge 2^N-1-N,
\]
and, when its \(N\) one-body coefficients are rationally independent, the
bound is exact:
\[
  \tau(J)=N,\qquad
  \operatorname{rank}_{\mathbb Q}L_{E_J}^{\mathrm{proj}}
  =2^N-1-N.
\]
Every full-temporal-rank localized spectrum instead has relation rank zero.
The change does not require an eigenbasis change or l-bit transport.

This sharpens the physical statement:

> Spatial localization and recurrence constraint complexity are independent.

## Formal declarations

- `lbitTemporalRank_add_relationRank`;
- `lbitNoninteracting_relationRank_lower_bound`;
- `lbitCoefficientSubspace_eq_singletonSpan`;
- `lbitNoninteracting_temporalRank_eq`;
- `lbitNoninteracting_relationRank_eq`;
- `lbitFullTemporalRank_relationRank_eq_zero`;
- `lbitFullTemporalRank_relationSpace_eq_bot`.

## Scope

The result is unconditional for finite exact l-bit fixed points. It does not
assert a microscopic Anderson/MBL dressing theorem, an infinite-volume
recurrence measure, or stability of exact rational rank under noise.

## Verification

Direct target compilation passed with:

```text
lake env lean GaloisForLFunctions/HTGeometry/LBitRecurrenceConstraintLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/LBitRecurrenceConstraintLaw.olean
```

Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Final `lake build` audit is reserved for publication audit.
