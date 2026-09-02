# Integral curved Tate coherent-primitive index law — formalization certificate

- **Paper theorem:** `ULF-ICTCPI-1`
- **Lean module:**
  `GaloisForLFunctions.RHTower.IntegralCurvedTateCoherentPrimitiveIndex`
- **Scratch check:** passed
- **Direct Lean check:** passed
- **Targeted build:** passed
- **Axiom audit:** only `propext`, `Classical.choice`, `Quot.sound`

## Certified declarations

- `PreDivisorTransverseCoherentPrimitive`
- `preDivisorTransverseCoherentPrimitive_coe_eq`
- `preDivisorTransverseCoherentPrimitive_subsingleton`
- `nonempty_preDivisorTransverseCoherentPrimitive_iff`
- `nonempty_preDivisorTransverseCoherentPrimitive_iff_index_zero`
- `deningerXiCoherentPrimitiveCompletion_fusion`
- `nonempty_preDivisorTransverseCoherentPrimitive_iff_shellReplica_closable`
- `nonempty_preDivisorTransverseCoherentPrimitive_of_bounded_shell_factorization`
- `forall_nonempty_preDivisorTransverseCoherentPrimitive_iff_riemannHypothesis`

They prove the literal summable primitive-completion fibre is always subsingleton, with its only
possible member the negative arithmetic-tail history. It is inhabited exactly when the pre-divisor
Roos class and evaluated integral formation index vanish. On Xi fibres this is also fixed-marker
convergence, compact recurrence descent, and closability of orthogonally replicated theta recovery;
any common bounded formation/recovery factorization produces the unique primitive. Universal
inhabitation is RH. No primitive is assumed.
