# Critical primary energy under simultaneous L² and shift limits

- **ID:** sz-critical-moving-primary-energy-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `sz-critical-moving-source-liminf-2026-10-24`, primary-energy component.
- **Statement:** Strong L² convergence preserves the critical compensated energy as a lower bound when the positive Suzuki shift also tends to zero; infinite limiting energy forces divergence.

## Exact statement

Let q_j converge strongly to q in real L², and let ω_j tend to zero through
positive values. With C_q its autocorrelation, set

`E_ω(q)=integral^+_(t>0) (C_q(0)-C_q(t)) B_ω(t)/ω`,

`E_0(q)=integral^+_(t>0) (C_q(0)-C_q(t)) K(t)`,

where `K(t)=2exp(-5t/2)/(1-exp(-2t))` for t>0.

Then `E_0(q)≤liminf_j E_(ω_j)(q_j)` in ENNReal. If E_0(q)=infinity, then
`E_(ω_j)(q_j)→infinity`. No compact support, smoothness, finite energy, or rate
of L² approximation is required.

## Dependency-closed proof

For each fixed t, `C_q(t)=<q,T_t q>`, where T_t is the physical translation
isometry. Continuity of this quadratic matrix coefficient gives pointwise
convergence of the correlations and their deficits. The exact normalized
primary kernel tends to K(t) at every t>0. Thus the nonnegative integrands
converge pointwise. Fatou gives the claimed lower bound. If its left side is
infinite, the lower limit is infinite; the upper limit is automatically at most
infinity, proving convergence in ENNReal.

This is the primary-energy part of the joint source/shift limit. The full signed
arithmetic liminf and its common-window approximation consequence remain on the
separate paper card; they are not asserted by this module.

Verdict: **BRIDGE**. No external novelty claim.

## Lean declarations

Module: `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalMovingPrimaryEnergy.lean`.

- `RHTower.continuous_autocorr_L2_source`
- `RHTower.suzukiCriticalLimitingEnergy_le_liminf_of_L2_tendsto`
- `RHTower.tendsto_suzukiCriticalCompensatedEnergy_top_of_L2_tendsto`

## Gates

- [x] Complete paper proof and existing translation/kernel inputs inspected.
- [x] Direct canonical check and all three public transitive axiom audits.

## Verification

The direct canonical check passed:

```sh
cd formal
lake --old env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalMovingPrimaryEnergy.lean
```

All three public declarations were inspected with `#print axioms`; their
transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`. No
placeholders, additional axioms, trusted-computation shortcuts, or raised proof
limits occur in the module. It is imported once by `RHTower.lean`; no umbrella
compilation was run.
