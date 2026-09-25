# Reflected completed-theta fibre positive-definiteness hostile test

Date: 2026-08-29
Status: computation complete; diagnostic only; forbidden as input to Lean proofs

## Route question

Could S6F's rank-three determinant be completed at all orders by proving every reflected fibre

```text
g_x(t) = Phi(x+t) Phi(x-t) / Phi(x)^2
```

positive definite? Bochner would then supply a positive moment measure and every signed even local
Hankel determinant. One negative finite Gram matrix kills this completion without touching direct
D1 positivity.

## Outcome

- **Full positive-definite/Bochner completion is killed.** Every one of 142 centers in
  `0 <= x <= 137/2000` had both a negative sampled cosine-transform value and a negative
  equispaced Toeplitz section.
- Failure already occurs at six points. At seam `x=0`, spacing `1/50`, 100-digit evaluation gives
  positive minimum eigenvalues for sizes four and five but a negative minimum eigenvalue for size
  six. A broader seam search finds a robust size-six negative section near spacing `0.0435`.
- Strongest transform candidate is also at seam: normalized cosine transform about
  `-2.038e-4` near frequency `24.35`. Strongest tested Toeplitz section has size 12 and minimum
  eigenvalue about `-4.43e-4`.
- **Sharp survivor:** finite-order positive definiteness through five points. An initial 10.24
  million arbitrary 4/5-point packet search at interval endpoints, followed by 10.88 million
  packets across 17 centers, found no high-precision counterexample. Every floating-point negative
  winner was roundoff and became strictly positive at 100 digits. This is evidence, not proof.

## Route consequence

The translation-invariant Bochner/TP-infinity shortcut is terminal for the completed-theta
reflected fibre. The failure threshold is structurally informative: the five-point
reflection-even coalescence is exactly where native rank-three D1 appears, while the first observed
global failure is at six points. Thus computation redirects S6F from an all-order measure
representation to either finite-order-5 positive definiteness or direct rank-three matrix geometry.

No value, sign, threshold, or packet from this run may appear in Lean. A proof of the finite-order
survivor must be analytic and source-derived.

## Reproduction

RunPod used 128 worker processes with BLAS/OpenMP threads pinned to one per process. The production
scan and both survivor scans are recorded in `results.json`, `survivor-results.json`, and
`survivor-center-results.json`; scripts, logs, environment metadata, verifier output, and checksums
are included.
