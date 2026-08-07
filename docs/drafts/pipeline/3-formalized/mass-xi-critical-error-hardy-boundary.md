# Mass–Xi critical-error Hardy boundary

- **ID:** C41
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3
- **Statement:** Completed critical-Mellin source equals explicit polar boundary plus centered error flux; polar term has exact height-independent norm and terminal flux vanishes for every mass `a>1/2`.

## Goal

Remove C39's cumulative square-root main mass and cofinal terminal Abel flux without assuming RH,
PNT square-root error, endpoint vanishing, or a bounded prime source. Identify exact surviving
source-side object whose height-uniform control would close mass-shifted spectral face.

## Gates

- [x] 0 → 1 in-progress: source-pure exact Stieltjes/Hardy-boundary attack
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: `XiMassCriticalErrorFlux`, targeted `lake build` green, standard axioms only
- [ ] 3 → 4 publication-ready: standalone paper and external novelty audit

## Conjecture loops

1. **C41.0 — Raw C39 Abel synthesis.** Attack cumulative weights through connected prime-graph
   edges and Band–Kaiser packets. **Open:** cofinal non-diagonal synthesis map still absent.
2. **C41.1 — Polar completion cancels cumulative main mass.** Replace raw prime cumulative by
   `criticalMellinCompletedError`. **Proved:** exact Stieltjes integration by parts isolates polar,
   terminal, and centered-error terms.
3. **C41.2 — Polar partial source is a Hardy boundary evaluation.** Shift physical contour by
   `-i/2` and invert Fourier transform. **Proved:** limit is `2*pi*g(-i/2)` with exact norm
   `2*pi*exp(-sigma*sqrt(a^2-1/4))`, independent of height `u`.
4. **C41.3 — Terminal flux may retain RH-strength growth.** Use corpus half-weighted prime-mass
   bound and any interior depth `1/2<d<a`. **Failed as obstruction:** completed error is at most
   `2(H+1)e^(H/2)`, Fourier profile is `O_u(e^(-dH))`, so terminal product tends to zero for every
   `a>1/2`.
5. **C41.4 — Remaining centered current is automatically bounded by PNT magnitude.** **Failed:**
   known remainder envelope remains supercritical after absolute values. Phase or a new current
   norm is still required.

## Paper proof `[PROVED HERE]`

Let

```text
F(h) = stripFourier (xiMassAnalyticTest a (sigma+i*u)) h,
E(h) = criticalMellinCompletedError h.
```

Differentiation under the integral gives

```text
F'(h) = integral_x g(x) exp(-i*h*x) (-i*x).
```

Applying finite Stieltjes integration by parts to `G(h)=F(h)-F(H)` removes earlier endpoint-zero
restriction and yields

```text
Prime(H) = Polar(H) - E(H) F(H) + integral_(0,H] E(h) F'(h) dh.
```

Evenness of `F` rewrites positive polar kernel `2 cosh(h/2) F(h)` as sum of reflected weighted
Fourier profiles. The `-i/2` contour shift identifies weighted profile as Fourier transform of
`g(x-i/2)`. Fourier inversion at zero then gives

```text
integral_(0,infinity) 2 cosh(h/2) F(h) dh = 2*pi*g(-i/2).
```

At archimedean pole, corpus square-root calculation gives exact norm

```text
2*pi*exp(-sigma*xiMassArchPoleFrequency a).
```

Next, `criticalMellinPrimeMass = primeMassHalf(exp H)` and `primeMassHalf_le` imply

```text
|E(H)| <= 2(H+1) exp(H/2).
```

Choose `d=(a+1/2)/2`. Interior contour shift gives

```text
|F(H)| <= C(a,sigma,u,d) exp(-dH).
```

Since `d-1/2>0`, polynomial-times-exponential decay proves `E(H)F(H) -> 0`. Polar partials
converge by integrability, so subtraction from finite source identity proves

```text
Prime(H) - ErrorFlux(H) -> 2*pi*g(-i/2).
```

Applying same contour shift to derivative kernel, with one extra physical moment, gives

```text
|F'(H)| <= C'(a,sigma,u,d) exp(-dH).
```

Therefore `E(H)F'(H)` is absolutely integrable on positive ray and finite currents converge to
source-defined infinite integral. Adding limits yields exact completed-source formula

```text
Prime(H) -> 2*pi*g(-i/2) + integral_(0,infinity) E(h) F'(h) dh.
```

No RH-strength input occurs.

## New knowledge

Polar completion acts as a rank-one Hardy-boundary projector: square-root prime main mass is sent
to explicit evaluation at the archimedean pole. C39 cumulative weights and terminal Abel flux are
not intrinsic obstructions. Exact surviving open object is centered completed-error current

```text
integral_(0,infinity) criticalMellinCompletedError(h) * F'(h) dh.
```

C40 Kaiser synthesis remains possible, but should target this centered current rather than raw
cumulative prime coordinates.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/XiMassCriticalErrorFlux.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Main finite identity:
  `xiMassCriticalPrimePartialSource_eq_polar_sub_terminal_add_errorFlux_height`
- Polar boundary:
  `integral_xiMassPolarInfinite_eq_archPole`
- Exact polar norm:
  `norm_integral_xiMassPolarInfinite_eq`
- Terminal extinction:
  `tendsto_xiMassCompletedError_terminal_zero`
- Cofinal reduction:
  `tendsto_xiMassPrimePartial_sub_completedErrorFlux_atTop`
- Absolute current integrability:
  `integrableOn_xiMassCompletedErrorFlux`
- Exact infinite source decomposition:
  `tendsto_xiMassCriticalPrimePartialSource_atTop`
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Log

- 2026-08-08 — exact conjecture/proof loops completed; paper proof and unconditional Lean module added
