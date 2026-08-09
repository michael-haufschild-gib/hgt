# Mass-shifted squared-factorial root-threshold orientation no-go

- **ID:** `mass-shifted-squared-factorial-root-threshold-orientation-no-go`
- **Stage:** 3-formalized
- **Type:** FALSIFIED / THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 exact open core
- **Statement:** Exact squared-factorial normalization, a common positive singular face, a simple
  positive adaptive root, and even an everywhere-positive full-support carrier do not orient the
  first Krein crossing; the crossing is exactly source mass balance across that adaptive root.
- **Novelty:** `[CORPUS-SYNTHESIS][NOVELTY UNVERIFIED]`

## Goal

Test whether the exact reverse-Bessel transform

```text
P^sharp_(r,c)(t) = sum_j c_j t^j / ((r+j)!)^2
```

reduces the §9.3 open core to real-root geometry, interlacing, total positivity, or positivity of
the carrier. A positive answer would orient the first omitted shifted-Xi coupling without importing
an RH-equivalent hypothesis. A negative answer must identify the strongest source observable that
survives.

## Gates

- [x] 0 → 1 in-progress: exact shifted-Xi carrier interface and hostile-model attack fixed
- [x] 1 → 2 fully-proven: finite-carrier law, atomic no-go, and full-support integral no-go proved
  on paper
- [x] 2 → 3 formalized: unconditional Lean theorems in
  `XiShiftedHankelBoundaryFactorialRootThresholdNoGo`
- [ ] 3 → 4 publication-ready: standalone novelty and parent-theory audit incomplete

## Conjecture/proof loops

### Conjecture 29 — adaptive real-root geometry orients crossing

Suppose two positive carriers have one common positive singular Hankel face and the transformed
null polynomial `P^sharp` has only a simple positive root. Conjecture: positivity plus this exact
root geometry chooses the first crossing sign.

**FAIL.** For squared-factorial moments

```text
s_k(weight,node) = (sum_i weight_i node_i^k) / (k!)^2,
```

take

```text
weight+ = (48/49, 1/49),  node+ = (3/4, 13),
weight- = (12/13, 1/13),  node- = (1/2, 7).
```

Every weight and node is strictly positive and both sequences satisfy

```text
s_0 = s_1 = s_2 = 1.
```

Thus they have the same positive size-one head, the same singular size-two face, and common kernel
`c=(-1,1)`. The exact adaptive transform is

```text
P^sharp_(2,c)(t) = (t-9)/36,
```

with one simple positive root. Yet the first crossings are

```text
R+ = 37/144 > 0,
R- = -19/72 < 0.
```

The negative carrier lies entirely below `9`; the positive carrier straddles `9`. Root location
classifies the sign regions but does not determine how source mass occupies them.

### Conjecture 30 — atomic support is the obstruction

Conjecture: a strictly positive density on all of `(0,∞)` prevents the hostile mass placement and
orients the adaptive threshold integral.

**FAIL.** For finite positive weights `w_i` and scales `a_i>0`, put

```text
rho(t) = sum_i w_i a_i^(-1) exp(-t/a_i).
```

Then `rho(t)>0` for every real `t`, and the exact Gamma integral is

```text
integral_(0,∞) t^k rho(t) dt = k! sum_i w_i a_i^k.
```

Consequently

```text
integral_(0,∞) t^r P^sharp_(r,c)(t) rho(t) dt
  = sum_j c_j (sum_i w_i a_i^(r+j))/(r+j)!.
```

Applying this identity to the already formalized factorial carriers

```text
(16/17,1/17 ; 3/4,5),
(4/5,1/5 ; 1/2,3)
```

produces everywhere-positive full-support densities with the same adaptive polynomial
`(t-9)/36` and opposite exact integrals `7/24` and `-1/12`.

## Strongest positive survivor

For every finite squared-factorial carrier, without positivity assumptions,

```text
sum_j c_j s_(r+j)
  = sum_i weight_i node_i^r P^sharp_(r,c)(node_i).
```

The open crossing is therefore not a generic positivity question. It is a source-conditioned
weighted mass-balance law across the endogenous roots of the actual null flag. Root geometry,
carrier positivity, smoothness, full support, and variation diminution can organize sign changes,
but none supplies this incidence law.

For §9.3 this changes the target to:

```text
completed Euler--Gamma source distribution
        relative to roots of its own adaptive P^sharp
        => required strict root-threshold imbalance.
```

Any successful theorem must act on the combined Lebesgue-minus-Chebyshev discrepancy, because the
same adaptive packet occurs in both source integrals. A marginal kernel theorem cannot orient it.

## No-go closure

- **Exact killing theorem/mechanism:**
  `squaredFactorialCarrierRootThresholdOrientationNoGo` and
  `fullSupportFactorialCarrierRootThresholdOrientationNoGo` exhibit opposite crossings under the
  proposed geometric and support hypotheses.
- **Strongest positive survivor:**
  `sum_mul_squaredFactorialAtomicMoment_eq_factorialCarrier` and
  `integral_factorialCarrier_mul_exponentialMixtureDensity` identify the crossing exactly as
  adaptive root-threshold mass balance.
- **New insight:** failure comes from an incidence degree of freedom—where source mass lies relative
  to endogenous roots—not from bad zeros, atomicity, lack of positivity, or lack of regularity.
- **Status:** paper proof dependency-closed and formalized unconditionally; no RH sign follows.

## Literature boundary

- Salazar, [*Strict Total Positivity from Spectral Darboux and Toeplitz Smoothing Mechanisms*
  (arXiv:2607.02778)](https://arxiv.org/abs/2607.02778), proves strict total positivity for modified
  Bessel kernels and studies Pólya-frequency smoothing. This supplies relevant variation-diminishing
  context, but no source-conditioned mass-balance theorem for an adaptive polynomial.
- Csordas and Forgács, [*Multiplier sequences and the distribution of zeros of entire functions*
  (arXiv:1505.00355)](https://arxiv.org/abs/1505.00355), studies generalized Bessel multiplier
  sequences. Such diagonal zero geometry does not constrain carrier occupation across transformed
  roots.
- The exact hostile pairs, root-threshold identity, and shifted-Xi interpretation above are
  `[CORPUS-SYNTHESIS][NOVELTY UNVERIFIED]`; no external priority claim is made.

## Lean certificate

- `formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryFactorialRootThresholdNoGo.lean`
  - `sum_mul_squaredFactorialAtomicMoment_eq_factorialCarrier`
  - `squaredFactorialPositiveCarrier_face_posSemidef`
  - `squaredFactorialCarrierNoGoKernel_ne_zero`
  - `squaredFactorialCarrierRootThresholdOrientationNoGo`
  - `integrableOn_pow_mul_exponentialMixtureDensity`
  - `integral_pow_mul_exponentialMixtureDensity`
  - `integral_factorialCarrier_mul_exponentialMixtureDensity`
  - `factorialPositiveCarrier_crossing_eq_exponentialRootThresholdIntegral`
  - `factorialNegativeCarrier_crossing_eq_exponentialRootThresholdIntegral`
  - `fullSupportFactorialCarrierRootThresholdOrientationNoGo`

## Log

- 2026-08-09 — conjecture 29 killed by exact squared-factorial two-carrier pair; carrier identity
  extracted as positive survivor.
- 2026-08-09 — conjecture 30 killed by actual full-support exponential-mixture integral theorem.
- 2026-08-09 — direct `lake env lean` and targeted `lake build
  GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryFactorialRootThresholdNoGo` passed; module wired
  into RHTower umbrella.
- 2026-08-09 — axiom audit of all carrier identities, integral laws, face theorem, and no-go
  capstones reports only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-09 — target forbidden-declaration scan and `git diff --check` are clean.
- 2026-08-09 — corpus lint is red only on seven unrelated, concurrently added unreachable
  HTGeometry modules; this module is not named by any lint error.
