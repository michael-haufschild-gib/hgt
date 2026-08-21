# CCM completed-head characteristic seam

- **ID:** ccm-completed-head-characteristic-seam
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `CCMActualHeadOutgoingQuantileCompletedCharacteristicSeam.lean`
- **Labels:** `[BRIDGE] [INTERNAL CANDIDATE] [NOT AN RH PROOF]`

## Goal

Turn the finite quantile cells plus terminal polar interval into one exact completed-head spectral
source, without assuming either orientation of the terminal boundary. Then connect the literal
Gamma-wall outgoing producer to this symbol on the Sonin aperture.

## Gates

- [x] 0 → 1 in-progress: corpus search and orientation obstruction audit complete
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: 25 Lean theorems, targeted source/build/axiom audit and umbrella wiring
- [ ] 3 → 4 publication-ready: external novelty audit and standalone exposition

## Theorem A — orientation-free anchored transport `[PROVED HERE]`

For arbitrary real `lo`, `hi`, anchor `s`, and `f : SoninL2`, define

`P(lo,hi,s;xi) = ∫_[lo,hi] exp(h/2)
  (cos(2*pi*h*xi)-cos(2*pi*s*xi)) dh`.

Then, for either endpoint order,

`∫_[lo,hi] exp(h/2) (E_f(s)-E_f(h)) dh
  = 2 ∫_R P(lo,hi,s;xi) |Fourier(f)(xi)|^2 dxi`.

Proof must branch on endpoint order and retain interval orientation exactly.

## Theorem B — completed-head characteristic source `[PROVED HERE]`

Let `b_N` be the quantile boundary and define terminal phase

`R_(N,T)(xi) = P(b_N,T,T;xi)`

and full phase `H_(N,T)=Q_N+R_(N,T)`. Then

`H_(N,T)(xi) = ∫_[0,T] exp(h/2) cos(2*pi*h*xi) dh
 - sum_(n<N) w_n cos(2*pi*log(n)*xi)
 - (2 exp(T/2)-(2+C_N)) cos(2*pi*T*xi)`.

This identity is orientation-free because the signed endpoint coefficient is the oriented terminal
polar mass.

## Theorem C — source landing and moment law `[PROVED HERE]`

The complete finite-cell plus terminal transport block equals

`2 ∫_R H_(N,T)(xi) |Fourier(f)(xi)|^2 dxi`.

Also `H_(N,T)(0)=0`, it is even, and

`H_(N,T)''(0) = 4*pi^2 * (sum_(n<N) w_n(log n)^2
  + (2 exp(T/2)-(2+C_N))*T^2 - ∫_[0,T] exp(h/2)h^2 dh)`.

Finally, for actual aperture data, the literal Gamma-wall outgoing producer is exactly

`2 gammaHardyPhaseRate(0)||f||^2 + higherBinet(f) + 4||f||^2
  + 2 ∫ H_(N,2a)(xi)|Fourier(f)(xi)|^2 dxi`.

Thus every finite prime--polar and terminal transport term has become one spectral source; fixed
Gamma scalar, endpoint reserve, and higher-Gamma energy remain explicit. Corpus theorem
`two_gammaHardyPhaseRate_zero_add_four_neg` proves the scalar-plus-reserve coefficient is strictly
negative, so no separate nonnegative-cost budget can close the sign.

## Hostile audit

- Do not assume `b_N ≤ T`: corpus proves this is equivalent to a completed-error threshold.
- If `T < b_N`, terminal coefficient and interval are oriented; treating either as positive is false.
- Pointwise symbol positivity is not expected and is not needed for exact Sonin source landing.
- Endpoint reserve and higher-Gamma energy remain separately nonnegative after source landing, but
  the fixed Gamma scalar makes their scalar reserve negative before higher-mode compensation.

All hostile-audit conditions are retained by theorem statements. In particular, reverse terminal
orientation is handled by interval sign reversal and never converted to positive mass.

## Lean formalization

Module: `formal/GaloisForLFunctions/RHTower/CCMActualHeadOutgoingQuantileCompletedCharacteristicSeam.lean`

Formalized results include:

- orientation-free generic anchored phase and transport theorem
- ordered-product integrability and reverse-interval transport proof
- first and second anchored phase jets with differentiation under interval integral
- terminal and completed symbols, evenness, and zero-frequency mass cancellation
- exact continuous-minus-prime-minus-endpoint characteristic formula
- exact finite-plus-terminal Sonin source landing
- terminal and global signed second-moment curvature laws
- exact actual Gamma-wall producer spectral normal form

Audit:

- targeted `lake env lean` source check passed
- targeted `lake build GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileCompletedCharacteristicSeam`
  passed; no umbrella build run
- all 25 theorem axiom audits report only `propext`, `Classical.choice`, `Quot.sound`
- forbidden-token scan empty
- wired into `GaloisForLFunctions/RHTower.lean`
- no-build lint confirms new module reachable; global lint currently fails only on unrelated
  `GaloisForLFunctions.HTGeometry.LogDerivPoissonJensen`

## Log

- 2026-08-21 — created after characteristic-transport module; exact terminal orientation obstruction
  found in `quantileBoundary_le_terminal_iff_completedError_ge_threshold`.
- 2026-08-21 — Conjectures A--C and actual producer landing closed in Lean; promoted to Stage 3.
