# TCD exponential-type strict-Hankel landing no-go

- **ID:** TCD-EXP-TYPE-STRICT-HANKEL-NOGO
- **Stage:** 3-formalized
- **Type:** ROUTE KILL
- **Lean:** `RHTower.completeStrictReflectedHankel_exponentialType_realRootedness_noGo`

## Closed claim

There exists an even entire `F` and positive real restriction `f` such that
`\|F(z)\| ≤ exp \|z\|`, every finite Hankel matrix of reflected even jets
`d^(2k)/dt^(2k) [f(x+t)f(x-t)]|_{t=0}` is positive definite for every real
center, yet `F` has a nonreal zero.

Witness: centered-uniform Laplace transform `F(z)=sinh(z)/z`, with
`F(iπ)=0`. Exponential tilting identifies reflected even jets with moments of
the squared gap of two independent tilted uniform variables. Its law is
atomless, so every finite moment Hankel block is positive definite.

## RH consequence

Killed chain:
`finite TCD gate → complete strict reflected-Hankel positivity + even positive
entire exponential type → real-rootedness → RH`.

Survivor: TCD needs a theta/Xi-specific source-to-divisor incidence; generic
Hankel positivity plus Xi-like parity and order-one growth cannot land RH.

## Audit

- direct `lake env lean`: pass
- targeted `lake build GaloisForLFunctions.RHTower.TCDExponentialTypeCompleteStrictReflectedHankelNoGo`: pass
- axioms: `propext`, `Classical.choice`, `Quot.sound`
- umbrella: `GaloisForLFunctions.RHTower`
- corpus + primary-literature search through 2026-08 found no combined result
