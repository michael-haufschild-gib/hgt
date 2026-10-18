# CHMD cross-route audit: terminal EDQ drift layer is always zero

Source: EulerDeletionNestedProjectionCovariance.lean:1444, namespace RHTower.DeletionResidueMartingale, historyLayer_predictableDrift_eq_reverse_tail. The exact RHS is a sum over i in range N with l<i. Therefore historyLayer n (predictableDrift (n+1))=0 for EVERY n, including primes. This is an immediate consequence of existing corpus work, not a new scientific theorem. Do not infer useful arithmetic cancellation from terminal prime support or terminal child-energy identities: at this indexing the entire reverse tail is empty.

Direct scratch proof checked with `lake --old env lean` (exit0) and #print axioms: only propext, Classical.choice, Quot.sound:

```
example (n : ℕ) : historyLayer n (predictableDrift (n+1)) = 0 := by
  rw [historyLayer_predictableDrift_eq_reverse_tail]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [if_neg (by omega : ¬ n < i)]
```

The nonempty arithmetic target needs N>l+1 and retains all simultaneous later Mobius coefficients. Existing EulerDeletionLogClockSingleQuotient.lean already reduces full drift energy to 2*norm(logClockSourceProjection N)^2+4+110/(N+1). EulerDeletionTwoLogClockRHEndpoint already receives a cofinal polylogarithmic bound on the two-logarithm signed source projection. Neither estimates the actual paired quotient. High-clock leakage and terminal cancellation do not pay the low-clock source.

Separate checkpoint audit: MobiusDivisorFiniteClockCountingCancellation defines clock energy over fixedCoreSquarefreeIndices P M: only squarefree cofactors disjoint from P. MobiusDivisorTerminalClockOrder.mobiusDivisorFiniteClockEnergy_terminal already gives current head square plus weighted omitted-prime singleton squares. Fresh checkpoint energy does not contain arbitrary earlier completed cutoffs as positive coordinates; processing their cofactors removes those coordinates.

CHMD main all-scale folded-wave bound remains OPEN. No repository Lean file changed for this applicability audit. Main card: docs/drafts/pipeline/1-in-progress/chmd-all-scale-folded-mobius-control-2026-10-18.md. Ledger: logs/chmd-all-scale-folded-mobius-1810.md. Source searches reported nonpartial results but incomplete/stale compiler metadata and unavailable semantic coverage; no exhaustive absence or external novelty claim.