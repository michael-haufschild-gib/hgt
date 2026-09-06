# Bounded chronological arithmetic repair

**Frozen target [R].** Construct real arrays a_(k,N), one bound C independent of k,N,
and full L²(0,∞) convergence e^(−t)+Σ_(k≤N)a_(k,N)h(kt)→0,
where h(t)=1/t−1/(e^t−1). The coefficients and estimates must be derived without RH.
This target is unchanged. See [interface assessment](chronological-rh-recovery-interface.md).

## Active mathematical splits

1. Arithmetic repair in increasing degree forces Möbius coefficients when all
   earlier discrete heat coefficients are cancelled exactly. The scalar bound
   |μ(k)|≤1 is available; concentration of error at t→0 is not controlled by this.
2. **[BRIDGE] Nonlinear response repair.** The already formal dyadic identity gives
   g(t)=2h(2t)−h(t)=1/(e^t+1). Joining response factors permits the recurrence
   P₀=0, P_(m+1)=g(1+P_m). Its candidate exact error is
   e^(−t)−P_m=e^(−t)g^m, hence squared L² error at most 4^(−m)/2.
   These are powers of a response, not the arithmetic dilates required by [R].
3. **Test of bounded linearization.** At q=e^(−t), g=q/(1+q).
   The square has Taylor coefficient (−1)^n(n−1), n≥1. A Lambert expansion
   Σ a_k q^k/(1−q^k) therefore forces a_p=−(p−1) at every odd prime p.
   Thus even the first square cannot have uniformly bounded exact Lambert
   coefficients. The needed cancellation may occur only after infinitely many
   nonlinear repair steps; a bounded linearization of every intermediate product
   is an invalid shortcut. Formal-series and L²-closure claims must be distinguished.
4. **[BRIDGE, under audit] Unrestricted heat density.** If F is orthogonal to
   every h(kt), its complex dilation pairing may be holomorphic with polynomial
   growth on shifted right half-planes. Integer-zero uniqueness would then force
   orthogonality to every positive real dilation, followed by Mellin completeness.
   This argument needs its analytic bounds and uniqueness theorem checked;
   it supplies no coefficient bound and is not claimed as a Lean result.

## Fake proof and exact gap

Nonlinear repair converges rapidly; replace each product by arithmetic dilates;
pass the error estimate to the resulting coefficients. The middle step has no
uniform coefficient bound, and g² exposes explicit prime growth. Neither the
geometric uniform norm nor a trace identity removes this growth.

## Status

Original target open. Work is focused on exact nonlinear recovery, its arithmetic
coefficient cost, and whether a joint limiting construction can control that cost.
No numerical evidence is used as a proof; no new RH theorem is claimed.
