# Growing-conductor Mertens errors have uniform logarithmic decay

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** For every `A≥0` and integer `k≥0`, one starting horizon gives

`|Σ_(n≤X) F(n mod q)Λ(n)/n − κ_q(F)log X − FP_q(F)| ≤ [2/(log Y)^k]Σ_r|F(r)|`

simultaneously for all sufficiently large `Y`, every `X≥Y`, every `q≤(log Y)^A` and every signed residue pattern `F`. Here `FP_q(F)` is the actual residue-Mertens finite part.

## Proof

[PROVED HERE] Let `L=Σ_r|F(r)|` and `R(t)=Σ_(n≤t)F(n mod q)Λ(n)−κ_q(F)t`. The [uniform cumulative source theorem](growing-conductor-prime-sources-have-uniform-logarithmic-decay.md), at exponent `k+2`, gives `|R(t)|≤Lt/(log t)^(k+2)` for every `t≥X`, because the allowed modulus range increases with `t`.

Exact Abel transport gives, for `Z≥X`,

`E(Z)−E(X)=R(Z)/Z−R(X)/X+∫_X^Z R(t)/t² dt`,

where `E` denotes the actual finite-part remainder. Its already proved pointwise limit is zero for each `q,F`. The integral is bounded by

`L∫_X^Z dt/[t(log t)^(k+2)] ≤ L/[(k+1)(log X)^(k+1)]`.

Let `Z→∞`. The resulting bound is

`|E(X)|≤L/(log X)^(k+2)+L/[(k+1)(log X)^(k+1)]≤2L/(log Y)^k`.

The finite part cancels in the exact difference identity before estimation. Pointwise convergence is used only after choosing `q,F`; its convergence horizon never enters the uniform bound.

## Formalization and scope

Lean: `GaloisForLFunctions/CriticalArithmeticCorrelationTheory/GrowingConductorMertensErrorsHaveUniformLogarithmicDecay.lean`; audit pending. This supplies a common actual arithmetic source on polynomial logarithmic conductor families. It does not yet bound the weighted sum of all eight complete-Weil residuals, capture actual negative eigenvectors, or control physical separated-bump loss.
