# EWQ-V source-independent Krein completion no-go

- **ID:** EWQ-V-KREIN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean module:** `GaloisForLFunctions.RHTower.EulerSquarefreeWickSourceIndependentKreinCompletionNoGo`

## Result

Fix any finite auxiliary coefficient space, two coefficient channels, one prime, and one real
diagonal metric whose forward-channel weight is nonzero.  Suppose every actual Xi divisor admits
an otherwise arbitrary matrix whose paired entries are the literal centered prime character and
its inverse and which is self-adjoint for that same metric.  Then RH holds.

Lean proves more locally:

- one completion forces the exact metric ratio
  `norm(w_reverse) = norm(w_forward) * norm(chi)^2`;
- critical-line reflection reciprocates `norm(chi)`;
- the same fixed metric cannot complete both points of an off-line Xi reflection orbit;
- completion on every Xi fibre therefore implies `RiemannHypothesis`.

No positivity, purity, rank, equal-diagonal hypothesis, or restriction on auxiliary entries is
used.  This covers positive, negative, and mixed-sign diagonal Hilbert/Krein data coefficientwise,
including completed jets.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/EulerSquarefreeWickSourceIndependentKreinCompletionNoGo.lean` — PASS
- `lake build GaloisForLFunctions.RHTower.EulerSquarefreeWickSourceIndependentKreinCompletionNoGo` — PASS
- axiom audit — only `propext`, `Classical.choice`, `Quot.sound`
- module wired into `GaloisForLFunctions.RHTower`
- repository lint reaches module; overall lint remains red only on unrelated pre-existing umbrella reachability failures

