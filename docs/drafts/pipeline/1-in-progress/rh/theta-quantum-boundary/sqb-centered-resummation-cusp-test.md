# SQB centered resummation: actual native cusp test

Status: deferred under the user's instruction to stop repeated source-exclusion
work and run positive occurrence conjectures. No centered-source exclusion is
claimed. Current work is in [the positive occurrence loop](sqb-positive-occurrence-conjecturing-loop.md).
RH remains unproved. The frontier map is read-only; no numerical computations.

Full chain: original Xi/modular source -> independent full-Xi occurrence in
the actual native entire operator -> real-preimage classification -> critical
line -> RH. Independent occurrence remains the hardest obstacle.

## Exact candidate and hardest test

The [audited exponential resummation](../../../3-formalized/sqb-resummed-source-mean-obstruction.md)
constructs P_s for s=rho/2+2, with native mean Gamma(s-1)!=0. Its uncentered
residual is nonzero. The remaining candidate is v=P_s-QP_s, where Q is the
actual native constant projection. Centering commutes with the actual
covariance C, and C v belongs to the actual entire graph.

Test the complete residual v-(2+mu)Cv. The existing exact covariance kernel
classification (`SelbergScatteringEntireEigenvectors.covariance_residual_zero_iff`)
implies that a zero residual gives Bv=e^(-1)v, even in its zero-vector branch,
where e=1+1/4+Im(rho)^2/4>1. This yields the original energy graph equation.
No occurrence or nonzero centered-vector premise is to be supplied.

## Direct analytical attack

1. Prove uniform original cusp decay of P_s. Nonparabolic row heights are at
   most 1/y. For Re(s)>2,

       |h_s(t)| <= t^2 (1/y)^(Re(s)-2)

   on every nonparabolic row. Their total quadratic mass is already bounded
   for y>=1/2. The parabolic row has norm y^Re(s) exp(-y), which tends to zero.
   This gives uniform decay in the original horizontal coordinate.

2. Use the actual tail tests w_n=1-chi_n, with chi_n the existing smooth
   modular cutoff at Y=n+3. Their native energy images are exactly
   A w_n=w_n+D2 chi_n. Both terms are supported above Y and uniformly bounded.
   Original cusp volume above Y is 1/Y, while w_n=1 above 2Y. Consequently
   Y integral w_n lies between 1/2 and 1.

3. Pair the putative energy equation for P_s-QP_s against w_n and multiply
   by Y. Uniform decay makes both pairings with P_s tend to zero. The constant
   component survives with coefficient (1-e) QP_s. Its original nonzero mean
   and e>1 would contradict the lower tail-mass bound.

This attacks the actual centered operator equation. It would also prove the
centered source nonzero as a consequence of a nonzero residual. Until the
full weak limit is checked, no centered-source exclusion is claimed.

- [ ] Uniform original cusp decay.
- [ ] Quantitative native cutoff-tail masses and operator pairings.
- [ ] Exact contradiction from the full-Xi residual kernel classification.
- [ ] Positive survivor, final Lean audit, umbrella and corpus wiring.
