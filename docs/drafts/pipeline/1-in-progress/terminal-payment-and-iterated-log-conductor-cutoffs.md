# Terminal payment and iterated-log conductor cutoffs

- **Stage:** 1-in-progress.
- **Type:** CONJECTURE.
- **Wall:** Σ1d.
- **Statement:** For every nonzero compact real `C²` profile, one super-log-log clock retains logarithmic coercivity on `V_floor(exp(L/(log t)^κ))` for every `κ>1`, where `L=log N`, `t=log L`.

## Mechanism

Cap the explicit spectral clock additionally by `t log log t`; its ratio to `t`
still tends to infinity. The logarithmic floor and raw low-block budget remain valid.
In the high block, replace the unweighted near error by the terminal weighted pairing,
paying it with a fixed fraction of prime adjunction.

The remaining overlap comparison costs
`Oφ(c(1+log c)(1+log R)/L)`.
At the proposed cutoff its ratio to `t` is
`Oφ(log log t/(log t)^(κ−1))→0`.
The center has smaller linear cost, the separated quadratic cost tends to zero,
and the terminal coefficient is bounded by a polynomial in `t` divided by `L`.
All terms involving `R^j/N` vanish since `log R=o(L)`.

The existing high-gap theorem requires each error to be at most one. The conjecture
instead pays errors against the growing `log Q` gap, with `Q=floor(L^q)`.
Required new input: retain explicit costs in the overlap low/high comparison and
combine them with terminal payment before imposing the horizon inequalities.

## Exact sources

- `EveryProfileHasALogarithmicHighConductorGap.lean`: low/high packet split,
  overlap comparison, cubic lag bound and prime adjunction.
- `TerminalSupportSharpensTheWeightedNearPairing.lean`: weighted terminal pairing;
  directly checked with a clean transitive axiom audit.
- `EveryCompactProfileHasAnExplicitTailClock.lean`: checked explicit spectral clock.

The proposed cutoff exceeds `exp(L/t^ε)` for every fixed `ε>0`.
