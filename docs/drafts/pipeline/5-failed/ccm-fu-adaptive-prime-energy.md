# CCM-FU: cutoff-dependent prime-pair order

- **ID:** CCM-FU-PE3
- **Stage:** 5-failed
- **Type:** FALSIFIED; positive survivor formalized
- **Source:** [literal prime-pair energy](../5-failed/ccm-fu-prime-pair-energy.md)
- **Goal:** produce SD1 from an actual signed contraction path, retaining the fixed arithmetic source.

## Frozen statement

Use exactly the literal `K_d(M)`, processed-prime field `F_P(d)` and retained energy `Q_P(M)` on the linked card. **PE3:** for every cutoff M, some ordering of all primes below M has `Q_(P union {p})(M) <= Q_P(M)` at every successive step. The ordering may depend on M; the source, pairing operation and factor-one energy comparison are fixed.

PE3 is a separate proposal. The increasing-order PE1/PE2 failures remain failures of their original frozen statements. Their half-prime intermediate head does not occur in every ordering and does not by itself refute PE3. Conversely, PE3 would imply SD1 by exact sum preservation and the terminal scalar energy.

## Investigation protocol

Enumerate every subset state and every path for small cutoffs through 32. Dynamic programming determines whether a complete nonincreasing path exists; retain all state energies and edge decisions. Separately test the deterministic greedy rule selecting maximal energy release, breaking ties by smaller prime, through 1024. A greedy failure alone does not refute PE3. Independently recompute decisive small witnesses from the defining channel sums at high precision. Computations guide proof ideas only.

No finite pass proves PE3. Any no-go needs an analytic proof and a nontrivial positive survivor; neither the allowed order nor the ceiling is adjusted after a failure.

## Closed analytic obstruction and positive survivor

At M=7 the only nonzero signed channels are `a=K1`, `-b=-K2`, `-c=-K3`, `-e=-K5`, `f=K6`. Analytic harmonic/logarithm and square-root sandwiches give
`0.102<=a<=0.115`, `0.139<=b<=0.145`, `0.110<=c<=0.115`, `0.060<=e<=0.065`, and `0.030<=f<=0.031`.

The final pair of signed groups, according to the last prime, is

- p=2: `a-c-e` and `-b+f`;
- p=3: `a-b-e` and `-c+f`;
- p=5: `a-b-c+f` and `-e`.

Both groups are strictly negative in every case. Thus their merger increases energy by twice their strictly positive product, whichever prime is last. PE3 fails at M=7 independently of prime order.

The nontrivial survivor is a complete order-independent last-step classification and strict total contraction despite the unavoidable last-step increase. The bounds give `-0.193<=S<=-0.163`, hence `S²<=0.037249`, whereas the original diagonal is at least `0.046325`. In particular `Q-S²>0.008`. Local monotonicity is not necessary for actual global diagonal dominance. The arbitrary-cutoff SD1 source estimate remains open.

The finite screen and independent direct audit are guidance only. Formal proof reuses existing analytic source boxes and exact sum/energy identities; no experimental values become premises.

## Lean certificates and audit

[MobiusDivisorAdaptivePrimeEnergyObstruction.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorAdaptivePrimeEnergyObstruction.lean) defines the literal signed prime merger and its two/three-step energies. `mobiusDivisor_every_order_seven_final_increase` covers all six orders directly, with no assumed stage identification. `mobiusDivisor_seven_strict_diagonal_margin` proves the positive survivor `Q(7)-S(7)^2>1/125`. The general final-group identity retains the exact signed overlap.

Two new declarations in [MobiusDivisorElevenChannelBounds.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorElevenChannelBounds.lean) supply the analytic seven-channel boxes and exact zero channels, reusing the existing private analytic estimates. Both edited/new leaf modules pass foreground `lake env lean`; only their needed oleans are produced. The new module is wired once into `RHTower.lean`. A single audit of only the ten new public theorems reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Global formal lint passes with existing file-size warnings. No large or umbrella build is run.

## Scope and remaining source obligation

PE3, allowing any cutoff-dependent order but requiring every step to contract, is refuted. The older PE1/PE2 increasing-order failures retain their original scope. An adaptive order that allows local increases while keeping every stage below the original diagonal is a different, unclassified proposal; the cutoff-seven witness does not refute it. SD1 and the required all-cutoff final linear residual remain open.

## Numerical guidance

The [full data and independent audit](../2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/README.md) enumerate all subset states through M=32 and screen the separate maximal-release greedy rule through M=1024. The first full-path failure is M=7. Greedy already fails at M=5, so greedy failure is not a certificate that no successful order exists. No finite pass is treated as an all-scale proof.
