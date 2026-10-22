# CCM-FU bounded Robin trace observer no-go

- **Stage:** Formalized in Lean 4
- **Claim:** **PROVED.** Fixed causal-depth Gamma-Schur trace carrier cannot supply CCM-FU linear compensation through uniformly bounded Robin observers.
- **Chain closed if proved:** bounded Robin trace correction → bounded/sublinear correction → rectangular Ward defect tends to `-∞` on `8n` → semibounded Ward RH connector unavailable. Positive survivor: any viable Robin trace producer must be singular/unbounded, cutoff-growing, or a non-trace-class relative trace before Gram/cofinal limit.

## Corpus facts

1. `SuzukiCausalDepthGammaSchurTraceClassCompletion`: canonical Gamma-Schur energy `K` is positive trace class; source block exact; trace ceiling fixed.
2. `RectangularSemilocalObserverTailSeparation`: `‖Tr(KB)‖ ≤ ‖K‖₁‖B‖`.
3. `SuzukiTransitionCoreLinearCompensationNoGo`: Ward semiboundedness forces correction `(8n) ≥ n/576`; bounded/sublinear corrections fail.
4. `SuzukiCanonicalSignedCompensationSaturation`: required linear correction exists algebraically, but leaves exactly RH-equivalent aligned energy; it is not an independent producer.

## Frozen conjecture

For any bounded-observer family `B : ℕ → K.H →L[ℂ] K.H`, put

`c(N) = Re Tr(K ∘ B(N))`.

Prove unconditionally:

1. Ward semiboundedness implies eventually
   `n/576 ≤ ‖K‖₁ * ‖B(8n)‖`.
2. Hence no uniformly operator-norm-bounded `B` yields a semibounded transition-core Ward defect.

## Result

Both statements are proved unconditionally in
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalDepthGammaBoundedRobinTraceNoGo.lean`:

- `eventually_linear_le_causalDepthGammaTraceNorm_mul_observerNorm_of_Ward_bddBelow`;
- `no_uniformlyBounded_causalDepthGammaTrace_WardProducer`.

The module is wired into `GaloisForLFunctions.RHTower`. Direct Lean and module-only `lake build`
pass. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Global formal lint
still reports unrelated pre-existing umbrella reachability failures; it reports no forbidden
declaration in this module.

## Falsifiers

- Existing corpus theorem already proves this exact Gamma-Schur/Robin capstone.
- Trace expression is not coefficient-faithful to fixed canonical carrier.
- Proof uses RH, zero location, computation, or an added axiom.
- Uniform trace norm secretly grows with aperture.

## Literature audit through 2026-08

- Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function* (JLMS 2023 / arXiv:2206.03682): localized Mercer trace-class and screw/RH criteria; no fixed Gamma-Schur trace-duality/scaling no-go.
- Suzuki, *Weil's quadratic form via the screw function*, v2 dated 2026-08-24 (arXiv:2606.09096): localized Weil operator is explicitly unbounded with delicate domain, and proposed cofinal spectral limit uses nonlocal first-order self-adjoint realizations. No bounded-observer trace comparison of the corpus Gamma-Schur carrier. This is consistent with, but does not state, the conjectured necessity of singular/unbounded Robin transport.
- Targeted searches for `Gamma Schur`, `Robin trace`, `bounded observer`, `transition core`, and Suzuki screw operators found no collision. Novelty claim is the source-specific CCM-FU producer-class classification, not generic trace duality.
