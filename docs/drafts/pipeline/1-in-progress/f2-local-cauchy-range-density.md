# F2 — one window determines Cauchy reflection

- **Stage:** 1-in-progress
- **Conjecture:** For every `0<Re s` and every nonempty open bounded interval `I`, actual logarithmic Cauchy averaging of `L²` inputs supported in `I` has dense range in the whole logarithmic Haar `L²` space.
- **Purpose:** Test whether restricting source compatibility to one window can evade the sharp reflection boundary. This concerns actual physical functions, beyond finite coefficient projections.

## Proposed mechanism

The Cauchy Fourier symbol decays exponentially and never vanishes. Therefore the adjoint image of any `L²` vector should extend holomorphically to a strip. Orthogonality to all averaged inputs supported in `I` forces this adjoint image to vanish on `I`. Analytic uniqueness then forces global vanishing; injectivity of the adjoint gives the zero vector.

If both averaging operators have this analytic regularity, local linear factorization extends globally: every adjoint image of `T A_s†−A_(s♯)` is analytic and vanishes on `I`. For the original conjugate-linear law `R A_s=A_(s♯)J`, instead put `S=J R` and apply `J` to the output. The local equation becomes `S A_s=A_(s♯)†`; its adjoint rows are again analytic. Thus the arbitrary-factorization classification should apply without any large-window assumption.

## Gaps

- Prove the actual Cauchy operator and its adjoint send arbitrary `L²` inputs to analytic representatives, with a uniform complex-strip estimate.
- Prove local source compatibility extends globally by that analytic uniqueness argument.
- Keep the weighted Lewis-space transfer problem and signed-form positivity separate.

## Analytic inputs located

`HTGeometry/GammaVerticalModulus` supplies exponential decay of `Γ(1/2+it)` and the bound `|Γ(z)|≤Γ(Re z)`. Applied to the two literal Cauchy-symbol factors, these give exponential decay without Stirling asymptotics. Cauchy–Schwarz then gives an absolute exponential moment for the symbol times any Fourier `L²` input. `RHTower.analyticOnNhd_expFourier'` in `ExpDecayFourierAnalytic` supplies the required strip analyticity from that moment. The source estimate and local-density deductions still need formalization.
