# CCM unit-Riesz cluster — stage-3 closure programme

- **ID:** `ccm-unit-riesz-cluster-stage3-closure`
- **Stage:** `1-in-progress` — **CLOSED 2026-08-18**
- **Type:** FORMALIZATION PROGRAMME
- **Scope:** the seven `ccm-*` cards in
  `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other`
- **Completion criterion:** every paper equation asserted by each card has a matching
  unconditional Lean theorem (no hypothesis standing in for card content), the modules are wired
  into `GaloisForLFunctions.RHTower`, and each card is moved to `3-formalized`.

## Audit of the seven cards (2026-08-18)

| card | Lean module(s) | state |
|-|-|-|
| `ccm-unit-riesz-exponential-coherent-trace` | `CCMUnitRieszExponentialCoherentTrace` | **complete** — (1)–(6) all present |
| `ccm-unit-riesz-hankel-boundary-pulse` | `CCMUnitRieszHankelBoundaryPulse` + `CCMUnitRieszCesaroCurvature` | **complete** — (1)–(11) all present |
| `ccm-unit-riesz-suzuki-green-producer-classification` | `CCMUnitRieszSuzukiGreenProducerClassification` | **complete** — RH ⟺ bounded resolvent, both directions |
| `ccm-unit-riesz-coherent-polar-sampling-no-go` | `CCMUnitRieszCoherentPolarSamplingNoGo` | gap: (13) in its generator-energy form |
| `ccm-unit-riesz-aperture-resolvent-weld` | `CCMUnitRieszApertureResolventWeld` | gap: §4 all-`epsilon` order equivalence |
| `ccm-four-unit-cesaro-curvature-wall` | `CCMUnitRieszCesaroCurvature`, `CCMUnitRieszFUCurvatureTransport` | gaps: (9),(10),(12),(13),(14),(15),(16),(17), iff form of (20)–(21) |
| `ccm-unit-riesz-completed-source-stieltjes-weld` | `CCMUnitRieszCompletedSourceWeld` | gaps: (14),(22),(23),(24),(26),(27),(28) |

## Work items

### W1 — finite-aperture reporter (`CCMUnitRieszCesaroFiniteApertureReporter.lean`)

Closes `ccm-four-unit-cesaro-curvature-wall`.

1. `unitRieszCesaroApertureKernel t u := (3/32)*(exp(-u)*R(t-u) - exp(-u/2)*P(t-u))/t^3`,
   with `P = unitRieszCesaroSlowPolynomial`, `R = unitRieszCesaroFastPolynomial`.
   Exact link `exp(t/2)/t^3 * g_t''(t-u) = -K_t(u)`.  [(10)]
2. Normalized transport `(9)`: `exp(t/2)*J_tail(t)/t^3 = -(3/64)*Q_b(t) + ∫_0^(t-b) Q_b(t-u) K_t(u) du`
   by the substitution `s = t-u` inside `unitRieszCompletedSource_eq_FUCesaroCurvature_explicitEndpoint`.
3. `(12)` strict monotonicity of `R/P` on `(0,∞)` with limits `1` and `4`, hence range `⊂ (1,4)`.
4. `(13)` sign of `K_t(u)` is the sign of `R(t-u) - exp(u/2) P(t-u)`; existence, uniqueness and
   the two-sided location `0 < wall < log 16` of the wall; `wall t → log 16`.
5. `(14)` `K_t(u) → K_∞(u)` at fixed lag.
6. `(15)`,`(16)`,`(17)` moments of `K_t` on `(0,t)` at `b = 0`, from `g_t(0)=g_t'(0)=g_t(t)=0`
   and `∫_0^t g_t > 0`.
7. `(20)`–`(21)` in iff form.

### W2 — `epsilon`-order transfer (`CCMUnitRieszApertureResolventEpsilonTransfer.lean`)

Closes `ccm-unit-riesz-aperture-resolvent-weld` §4: for each `epsilon > 0`,
`(∃C, ∀t≥0, -C exp(-(1/2-epsilon)t) ≤ U(t).re) ↔ (∃C', ∀t≥0, R_1(t) ≤ C' exp(epsilon t))`.

### W3 — generator form of the fixed sample (`CCMUnitRieszCoherentGeneratorSampling.lean`)

Closes `ccm-unit-riesz-coherent-polar-sampling-no-go` (13):
`g_(1-h,h)(1)^2 = ((q-r)/(8A)) * G(1-h,h)`.

### W4 — Stirling convolution correction (`CCMUnitRieszStirlingConvolution.lean`)

`ccm-unit-riesz-completed-source-stieltjes-weld` (14),(22),(23),(24):
`r(t) := ∫_0^t k(t-s) a(s) ds`, `r ≤ 0`, `|r(t)| ≤ 3 exp(-t)(t^2/2 + 4t)`, and the all-`epsilon`
bound `|r(t)| ≤ B_ε exp((-1/2+ε)t)`.

### W5 — the Laplace weld (`CCMUnitRieszCompletedSourceLaplaceWeld.lean`)

`ccm-unit-riesz-completed-source-stieltjes-weld` (26),(27),(28).  Route that avoids
Stieltjes–Laplace measure theory entirely:

```text
J(t) = ∫_0^t W(h) mu(t-h) dh,   W(h) = exp(-h/2) E(h),  mu(u) = 3exp(-3u/2) - (3/2)exp(-u)
```
is exactly `unitRieszCompletedSourceResponse_eq_errorIntegral`.  Then

```text
L[W](z) = 2/(z(z+1)) + (zeta'/zeta)(1+z)/(z+1/2)      (bounded-by-2(h+1) Fubini)
L[mu](z) = (3/2)(z+1/2)/((z+1)(z+3/2))
L[J](z)  = L[W](z) L[mu](z) = alpha(z) R(z)
L[r](z)  = L[k](z) L[a](z)  = alpha(z) A(z)
L[J+r](z) = alpha(z)(R+A)(z) = unitRieszPoleFilledCoefficient z.
```

The only genuinely new analytic input is `L[a](z) = A(z)`, i.e.

```text
∫_0^∞ exp(-zt) exp(-t) Σ_(n ≤ exp t) (t - log n) dt = zeta(1+z)/(1+z)^2,   Re z > 0.
```

## Log

- 2026-08-18 — audit written; three cards already complete, four work items opened.

## Closure (2026-08-18)

All seven cards are at `3-formalized/new_scientific_knowledge/other`.  Seven new modules, all
wired into `GaloisForLFunctions.RHTower`, all unconditional
(`#print axioms` = `propext, Classical.choice, Quot.sound`):

```text
RHTower/CCMUnitRieszCesaroFiniteApertureReporter.lean     W1  (four-unit Cesàro card)
RHTower/CCMUnitRieszApertureResolventEpsilonTransfer.lean W2  (aperture-resolvent card)
RHTower/CCMUnitRieszCoherentGeneratorSampling.lean        W3  (polar sampling no-go card)
RHTower/CCMUnitRieszVolterraLaplace.lean                  W5' (reusable exponential-kernel
                                                               Laplace convolution law)
RHTower/CCMUnitRieszStirlingLaplace.lean                  W4/W5
RHTower/CCMUnitRieszCompletedCurrentLaplace.lean          W5
RHTower/CCMUnitRieszCompletedSourceLaplaceWeld.lean       W5
```

### Reusable assets produced

- `integral_Ioi_expVolterra_laplace` / `integrableOn_Ioi_cexp_mul_expVolterra`: the half-line
  Laplace convolution law for a decaying exponential kernel against any measurable source of at
  most linear growth, proved by a Fubini interchange over the causal wedge with the product
  majorant `exp(-σt/2) · C(1+h)exp(-σh/2)`.  This is what makes Stieltjes--Laplace measure theory
  unnecessary whenever the kernel is a finite combination of pure exponentials.
- `integral_Ioi_cexp_neg_mul_linear` / `..._linear_shift` (complex and real): the first
  exponential moment `∫_0^∞ u e^{-wu} du = 1/w²`, obtained as the `b = 0`, `φ = 1` case of the
  convolution law rather than by an improper FTC.
- `unitRieszStirlingHead_laplace`: `L[exp(-t) Σ_{n ≤ exp t}(t - log n)](z) = ζ(1+z)/(1+z)²`.
- `unitRieszCompletedCurrent_laplace`: `L[exp(-h/2) E(h)](z) = 2/z - 2/(z+1) - LSeries Λ (1+z)/(z+1/2)`.
- `setIntegral_Ioi_of_vanishing_lt` / `integrableOn_Ioc_of_vanishing_Ioo`: the half-line split for
  atoms whose switch-on point is *closed* (the value at the switch-on point need not vanish).
