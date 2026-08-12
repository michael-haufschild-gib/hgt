# Route-P Gamma-sewn Stokes reflected compact carrier

- **ID:** `P-G70`
- **Stage:** `1-in-progress`
- **Type:** Kummer-reflected passive response / source-native compact carrier
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN DIRECT GREEN] [EXACT MODULE BUILD GREEN] [UMBRELLA-WIRED] [FINAL AUDIT PENDING] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-subcritical-passive-response.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesReflectedCompactCarrier.lean`

## Obstruction exposed by P-G69

The centered completed Xi trace is odd, whereas the one-sided P-G69 response is not. Therefore no
coefficient identification can weld that response directly to the completed trace. This is a real
parity obstruction, not a missing estimate.

## Conjecture P-G70.A: Kummer reflection forces the correct passive pair

For physical intensity `I=b_s g_s`, pair Stokes gaps `g_s` and `-g_s`:

```text
I/(z-g_s) + I/(z+g_s)
  = -2 (b_s/g_s) z / (1-(z/g_s)^2).
```

**Verdict: proved and formalized.** Every pair is odd and anti-Herglotz in the upper half-plane.
Both one-sided subtraction constants cancel exactly. Absolute convergence follows from the P-G69
summability of `b_s/g_s`.

## Conjecture P-G70.B: reciprocal gaps form a compact positive carrier

Put weight `w_s=b_s/g_s` at both nodes `x=+1/g_s` and `x=-1/g_s`. For `0<s<1`, this defines a
finite positive atomic measure supported in

```text
[-(log 2)^(-1), (log 2)^(-1)].
```

Near zero, its Markov transform `K_s` satisfies exactly

```text
R_s^ref(z) = -z K_s(z).
```

**Verdict: proved and formalized.** Route P now has a literal source-native compact positive
carrier, not merely a finite truncation or conditional Xi-divisor measure.

## Higher universal principle

P-G69 passivity, completed-trace oddness, and Kummer symmetry are three shadows of one reflection
law: physical Euler intensity lives on a signed spectral doublet, while positivity lives in its
unsigned reciprocal-gap carrier. The centered coordinate sees the odd response; endpoint moment
geometry sees the square pushforward `y=g_s^(-2)`. Thus the next object is not this symmetric
measure itself, whose odd moments vanish, but its positive square pushforward with mass `2b_s/g_s`.

## Lean realization

Headline declarations:

- `gammaSewnMobiusApertureStokesReflectedAtom_eq_compactMarkov`;
- `summable_gammaSewnMobiusApertureStokesReflectedAtom`;
- `gammaSewnMobiusApertureStokesReflectedResponse_im_nonpos`;
- `gammaSewnMobiusApertureStokesReflectedResponse_neg`;
- `gammaSewnMobiusApertureStokesReflectedCompactCarrier_finite`;
- `ae_gammaSewnMobiusApertureStokesReflectedCompactCarrier_mem_compact`;
- `gammaSewnMobiusApertureStokesReflectedResponse_eq_neg_mul_compactMarkov`.

## Gates

- [x] exact reflected Euler-resolvent identity
- [x] absolute convergence for `0<s<1`
- [x] upper-half-plane anti-Herglotz law
- [x] exact oddness
- [x] finite positive reciprocal-gap carrier
- [x] compact support
- [x] exact local Markov representation
- [x] direct Lean check
- [x] exact module build
- [x] umbrella import wired
- [ ] square-pushforward carrier and all-degree moment formula
- [ ] critical `s=1/2` completed Gamma/polar moment equality
- [ ] full umbrella build, lint, and axiom audit

## Honest boundary

P-G70 does not identify its carrier with the completed seam moment measure and does not prove RH.
It removes carrier existence, positivity, compactness, parity, and passivity as independent
obstacles. Remaining gate is exact all-degree source moment identification after squaring reciprocal
gaps.
