# Physical-horizon source charge at vanishing energy

- **ID:** critical-rigidity-physical-vanishing-charge
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Lean:** `CriticalScaleArithmeticRigidity/PhysicalHorizonCharges.lean` — pending check

## Statement

For every real `t`, tolerance `ε>0`, and lower cutoff `R`, some `Q≥max(R,2)` works for every `N≥Q`: an actual harmonic-pole-neutral packet `a` satisfies

`L_Q(a)<ε`, `mean G_Q(a)=t`,

`[Σ_(n≤N) F_a(n)²/n]/log N<ε`,

`[Σ_(n≤N) |G_Q(a)(n)−t|²/n]/log N<ε`.

The same cutoff works simultaneously for all these physical horizons. The generator is the complete literal dilation generator; this statement does not replace it by the finite-horizon prime matrix or assert a complete-Weil sign.

## Proof

The proved harmonic packet upper bound is `(log N+17(1+log Q))M`. For `N≥Q≥2`, `log 2>1/2` gives `1+log Q≤3log N`, hence the normalized physical square is at most `52M`.

On prime coefficients the exact excitation gap gives `2log 2·M≤L`. Harmonic projection contracts physical square and preserves `L` and `G`. Thus projected input square divided by `log N` is at most `(26/log 2)L`.

The centered generator is the negative packet with coefficients `τ_p a_p`. Its coefficient square is at most `(log 2/2)L`, so its normalized physical square is at most `26log 2·L`.

For the normalized coherent prime coefficients `(t/B_Q)sqrt(p−1)/p`, response is `t` and energy is `t²/B_Q`. Since `B_Q→∞`, choose `Q≥max(R,2)` with

`(1+26/log 2+26log 2)t²/B_Q<ε`.

Every claimed bound follows, uniformly for `N≥Q`, after the explicit harmonic projection.

## Insight

Receiving charge can survive vanishing arithmetic energy and vanishing physically sampled input. It is not an artefact of averaging over the factorial common period. A limit based on the input energy and physical norm alone cannot recover this source output. Its cancellation in the complete signed form remains a separate problem.
