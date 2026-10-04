# PM: actual power-damped boundary moments

- **ID:** PM-power-damped-boundary-moments
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** route PM; `../1-in-progress/pm-prime-square-coupled-source.md`.
- **Statement:** The actual reciprocal source has zero boundary Mellin mass, an exact first signed logarithmic moment, and an absolutely integrable second logarithmic moment, without canonical L2 admission.

## Theorem

For `0<epsilon<1/2`, set `f(x)=A_epsilon(1/x)` and
`w(x)=x^(epsilon-2)*f(x)`. Then, over `x>1`,

`integral w(x) dx = 0`,

`integral w(x)*log x dx = -D_epsilon`,

where `D_epsilon=(1-2^epsilon)*zeta(1-epsilon)/(1-epsilon)`.
Also `integral ||f(x)||*x^(epsilon-2)*(1+log(x)^2) dx` is finite, and
`D_epsilon -> log 2` as positive damping tends to zero. All assertions concern
the literal arithmetic source. No RH or square-integrability premise is used.

## Proof

The existing integer remainder saving, real floor correction, and centered
source identity give a log-four envelope at all sufficiently large real
reciprocal arguments. Its product with the boundary weight and two logarithms
is dominated by `C/(x*log(x)^2)`. The finite head is bounded using the actual
divisor coefficients in `[0,1]`.

Write the boundary transform as the integral of `w(x)*exp(-delta*log x)`.
The admitted logarithmic majorant justifies the right difference quotient by
dominated convergence. Inversion identifies this integral with the verified
Mellin transform at `1-epsilon+delta`. Dividing its exact quotient by `delta`
and using the regularized zeta residue unit gives limit `D_epsilon`. Hence
the boundary mass is zero and the first moment is `-D_epsilon`. The residue
unit at `1-epsilon`, together with the derivative of `2^epsilon` at zero,
gives the final limit `log 2`.

## Lean certificate

Module: `PMPowerDampedMobiusBoundaryMoments.lean` (416 lines).

- Seven exported theorems and two definitions; all nine axiom reports contain
  only `propext`, `Classical.choice`, `Quot.sound`.
- Targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusBoundaryMoments:olean`
  passed; new leaf took 53 seconds, unchanged dependency reports replayed.
- Final actual-file `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusBoundaryMoments.lean`
  passed with empty output after the final edit.
- Exactly one umbrella import; no umbrella build. Formal index regenerated.
- Global lint reports twelve unrelated unreachable modules; no PM failure.
  No added axiom, proof placeholder, heartbeat override, or numerical experiment.

## Frontier effect

These moments remove the analytic moment inputs from the proposed signed
prime-convolution asymptotic at the prime-square scale. The weighted prime
transfer, its uniform tail, and finite rough inversion still need formalization.
The complete mixed-current compensation and unconditional RH remain open.
