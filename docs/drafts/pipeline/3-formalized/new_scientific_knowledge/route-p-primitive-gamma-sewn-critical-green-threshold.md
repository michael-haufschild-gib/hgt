# Route P primitive Gamma-sewn critical Green threshold

- **ID:** `route-p-primitive-gamma-sewn-critical-green-threshold`
- **Stage:** 3-formalized
- **Label:** `P-G190`
- **Source:** P-G189, Gamma-sewn Stokes dual current, Deninger prime-log Green inverse
- **Statement:** P-G189's complete aperture defect flux is exactly half the square of Deninger's
  Green inverse applied to the critical Gamma-sewn Euler current. One Green step retains the
  divergent prime-harmonic wall; two steps are the sharp scalar trace threshold and produce an
  order-zero continuous source functional.

## Conjecture loop and hostile pivot

P-G189 left one concrete question: is its positive flux

```text
J(p,e)=1/2 * [p log p]^-1 * p^-e * (e+1)^-2                 (1)
```

merely an arithmetic re-expression, or is it the coefficientwise Gamma--polar current demanded
by Route P?

First conjecture: the hard-edge interval is the Gamma--polar defect. P-G189 falsified it because
that interval has zero first variation.

Second conjecture: `J` is a smoothed critical Gamma-sewn Stokes current. Corpus audit exposed the
canonical, source-derived smoothing operator: Deninger's Green inverse

```text
(G a)_m = deningerFreq(m)^-1 a_m.                            (2)
```

No multiplier was fitted to `(1)`. On positive prime-power Kummer axis `(p,e)`,

```text
deningerFreq(p,e)=(e+1) log p.                               (3)
```

The conjecture survives exactly, but only at Green order two.

## Sharp Green threshold

Let `C(p,e)` be real critical Gamma-sewn first-trace coefficient. Source Stokes inversion gives

```text
C(p,e)=log p * p^(-(e+1)).                                   (4)
```

Define one- and two-Green coefficients

```text
L(p,e) = C(p,e)/deningerFreq(p,e),
Q(p,e) = (1/2) C(p,e)/deningerFreq(p,e)^2.                   (5)
```

On valuation-zero prime slice,

```text
L(p,0)=1/p.                                                   (6)
```

Euler's prime-harmonic divergence proves `L` is not summable. In contrast, Lean proves

```text
Q(p,e)=J(p,e)                                                 (7)
```

for every prime and depth, hence `Q` is summable by P-G189. Thus Green order two is not a
convenient sufficient smoothing: it is the first integral order crossing the scalar trace wall.

## Operator identity and topology upgrade

For rapid Kummer test `a`, define

```text
<Q,a> = sum_(p,e) Q(p,e) a(axis(p,e)).                        (8)
```

Lean proves the literal transpose-current identity

```text
<Q,a> = EulerDualCurrent_(s=1) ((1/2) G(G(a))).               (9)
```

The right side uses already-constructed Gamma-sewn Euler current and already-constructed Deninger
Green operator. Equation `(9)` is therefore an operator-level source identification, not a
coefficient declaration.

Because `Q` is positive and summable, the same functional satisfies the stronger bound

```text
|<Q,a>| <= (sum_(p,e) Q(p,e)) * deningerHeightSeminorm(0,a). (10)
```

Raw positive-chamber Euler current costs two source seminorm steps. Double Green smoothing does
not merely make scalar mass finite; it upgrades the critical current to an order-zero continuous
functional with no height loss.

Finally P-G189's global aperture derivative becomes

```text
[sum_(p,e) M_c(p,e)]/c -> sum_(p,e) Q(p,e),   c -> 0+.       (11)
```

So P-G188's Wold defect current is the scalar mass of the double-Green-smoothed critical
Gamma-sewn current.

## Big-picture principle

P-G188/P-G189's square-root vector singularity and Gamma-sewn critical unitization wall are two
shadows of one source principle:

```text
critical von-Mangoldt current
  -- one Green step --> prime-harmonic, still non-trace-class
  -- two Green steps --> finite Wold energy flux, order-zero functional. (12)
```

This explains why smooth scalar first-jet recovery failed. Completion lives one categorical level
earlier: vector amplitude is singular, energy current is finite, and its canonical source
primitive is `G^2`, not a bounded diagonal recovery at the divisor receiver.

P-G190 does not yet build the sign-changing matrix incidence required after physical Gamma
coorientation. P-G190 identifies the scalar producer exactly and proves its optimal trace order;
P-G188/189/190 do not short the two-variable completed residue matrix or prove RH.

## Prior-corpus and novelty audit

Internal Attack 30 (`FrankensteinCCMRoutePApertureTailFluxBridge.lean`) already identifies the same
P-G188 flux with a critical-Mellin atom tested against a scalar quadratic Green log profile.
P-G190 does not claim priority over that coefficient bridge. Its new content is:

- identification with the actual nuclear Kummer operator `deningerGreen ∘ deningerGreen`;
- proof that one Green step is exactly the divergent prime-harmonic wall;
- proof that two Green steps are the sharp integral-order trace threshold;
- exact transpose-current identity `(9)`;
- order-zero continuity bound `(10)`;
- global aperture derivative identity `(11)` in this operator language.

Primary-source audit found classical components separately: Burnol's Sonine/co-Poisson zero
realizations, Deninger's dynamical explicit-formula program, and weighted translation/defect
operator theory. Relevant sources include
[Burnol](https://arxiv.org/abs/math/0203120),
[Deninger](https://arxiv.org/abs/1807.06400), and
[Phatak--Sholapurkar](https://arxiv.org/abs/1804.08981). The audited material did not state
`(5)`--`(12)` for the primitive Euler/Burnol/Gamma-sewn current. No external priority claim is made
beyond this exact Route P synthesis.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaSewnCriticalGreenThreshold.lean
```

Capstones:

- `routePPrimitiveGammaSewnCriticalLinearGreenFlux_primeSlice`;
- `not_summable_routePPrimitiveGammaSewnCriticalLinearGreenFlux`;
- `routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_eq_defectFlux`;
- `routePPrimitiveGammaSewnCriticalGreen_traceThreshold`;
- `norm_routePPrimitiveGammaSewnCriticalQuadraticGreenPairing_le`;
- `routePPrimitiveGammaSewnCriticalQuadraticGreenPairing_eq_eulerDual_green_sq`;
- `tendsto_routePPrimitiveBurnolApertureTotalDefectMass_div_zero_quadraticGreen`.

Verification:

- `/tmp/pg190.lean`: `lake env lean /tmp/pg190.lean` passed cleanly;
- exact leaf build passed;
- `/tmp/pg190_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- targeted forbidden-declaration scan: clean;
- umbrella import wired; umbrella not built.

## Gates

- [x] prior formal corpus and failed-route audit
- [x] hard-edge conjecture falsified in P-G189
- [x] exact Gamma-sewn critical coefficient identified
- [x] one-Green prime-harmonic divergence proved
- [x] two-Green equality with complete aperture flux proved
- [x] operator transpose identity proved
- [x] zero-height-loss continuity proved
- [x] global derivative reidentified
- [x] scratch verification
- [x] exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] construct sign-changing cross-incidence compatible with physical Gamma coorientation
- [ ] short completed two-variable residue current before scalarization
- [ ] unconditional RH
