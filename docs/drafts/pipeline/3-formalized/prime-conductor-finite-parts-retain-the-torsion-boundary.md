# Prime conductor finite parts retain the torsion boundary

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Q1/O1](../1-in-progress/three-frontier-questions-full-solutions.md).

Let `v_m,N(n)=c_m(n)/sqrt(phi(m)n log N)` and let `P_N` be the literal
prime matrix on `1,…,N`. The exact mixed limit is

`<v_m,N,P_N v_l,N>−1_(m=l) log N`
`→ −I(m,l)/sqrt(phi(m)phi(l))−1_(m=l)[log m+tameDifferent(m)]`.

Its diagonal is `−2 log m`; each mixed prime-power edge retains the
negative torsion intersection. For a fixed finite packet the corresponding
quadratic limit is the negative torsion pairing minus
`sum a_m²[log m+tameDifferent(m)]`.

## Dependency-closed reduction

Write `lambda_l=gamma+log l+tameDifferent(l)` and
`r_l,N=P_N v_l,N−(log N−lambda_l)v_l,N`.
The proved residual norm tends to zero, while `||v_m,N||→1`.
Cauchy–Schwarz therefore makes `<v_m,N,r_l,N>→0`.

The exact harmonic Gram finite part gives
`log N <v_m,N,v_l,N>−1_(m=l) log N`
`→gamma·1_(m=l)−I(m,l)/sqrt(phi(m)phi(l))`.
Subtracting `lambda_l<v_m,N,v_l,N>` proves the stated limit.
On the diagonal, `I(m,m)/phi(m)=log m−tameDifferent(m)` cancels the tame terms.

## Lean

`SuccessorShellArithmetic/Conductor/PrimeConductorFinitePart.lean`:

- `tendsto_primeConductorPairing_finitePart`;
- `tendsto_primeConductorPairing_diagonal`;
- `tendsto_primeConductorPairing_of_ne`;
- `tendsto_primeConductorPacket_finitePart`.

Final direct `lake --old env lean` check passed. All four capstones depend
only on `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
The limit retains the full prime cutoff; identification of the complete
Gamma, pole, and successor-shell form remains open.
