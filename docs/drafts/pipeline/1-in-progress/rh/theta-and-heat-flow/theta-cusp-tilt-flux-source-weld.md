# Theta-cusp tilt-flux source weld

Status: source construction and all-plane Xi weld Lean-formalized; independent neutral-flux sign
open. Route TTF promoted from candidate to live architecture. RH not proved.

## Corpus mismatch that opened the route

`ThetaTiltFluxCarrier.lean` required a `ThetaSource`: positive, even, continuous, and pointwise
dominated by `C_M exp(-M|x|)` for every real `M`. The frontier map still reported that no literal
arithmetic instance or global transform was available.

Later corpus modules had overtaken that report:

- `HedenmalmThetaSourceSpectrumExact.lean` proves
  `thetaCuspFourierLaplace_eq_XiC_all` on all of `C`;
- `HedenmalmThetaSourceUnconditional.lean` proves strict positivity and evenness of the literal
  theta-cusp density;
- `HedenmalmThetaKernelEnergy.lean` proves its explicit positive-half-line envelope.

The missing type-level weld was therefore a concrete hard theorem, not new infrastructure.

## Conjecture loop

### TTF-C1: all exponential moments instantiate `ThetaSource` — failed as stated

All exponential moments are only integral control. They do not imply the pointwise decay field of
`ThetaSource` for an arbitrary continuous positive function. Pivot: use the corpus's explicit
theta envelope rather than infer a false generic implication.

### TTF-C2: the explicit theta envelope has a uniform every-rate bound — proved

For `t=|x|`, the corpus gives

```text
k(x) <= U exp(9t/2) exp(-pi exp(2t)).
```

Use `exp(2t) >= 2t^2`, `pi>3`, and complete the square with `A=|M|+5`:

```text
(M+9/2)t - pi exp(2t)
  <= A t - 6t^2
  <= A^2/24.
```

Hence, globally and with an explicit constant,

```text
k(x) <= U exp((|M|+5)^2/24) exp(-M|x|).
```

Lean: `thetaCuspFullSource_le_tiltDecayConstant`.

### TTF-C3: literal bilateral Laplace transform is centered Xi — proved

Evenness changes `exp(wx)` to `exp(-wx)` under `x -> -x`. The latter is exactly the Fourier--Laplace
integrand at `-i w`. The corpus all-plane theorem and `xiCent_eq_XiC` then give

```text
bilateralLaplace thetaCuspTiltSource w = xiCent w
```

for every complex `w`, with no strip or RH premise.

Lean: `bilateralLaplace_thetaCuspTiltSource_eq_xiCent`.

### TTF-C4: positivity of the correlation norm forces nonnegative neutral flux — failed

`tiltCorrelation(a) >= 0` does not determine its derivative at `a=0`. The specialized universal
flux sign is now formally exactly RH, not an automatic consequence of source positivity. This
prevents theatre and locates the remaining producer precisely.

## New route frontier

The literal arithmetic source, connector, and RH receiver are now all formal:

```text
thetaCuspFullSource
  -> thetaCuspTiltSource
  -> bilateralLaplace = xiCent
  -> source Bezoutian = centered-Xi Bezoutian
  -> universal neutral tilt-flux nonnegativity <-> RH.
```

Current open core: prove neutral first variation nonnegative for every finite Euler-safe
exponential packet directly from the one-sided arithmetic theta correlation, before invoking its
Xi Bezoutian evaluation. Any premise definitionally equivalent to the final sign is circular.

## Formal status

Module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspTiltFluxSourceWeld.lean`.

Main declarations:

- `thetaCuspTiltDecayConstant`
- `thetaCuspFullSource_le_tiltDecayConstant`
- `thetaCuspTiltSource`
- `bilateralLaplace_thetaCuspTiltSource_eq_xiCent`
- `sourceBezoutian_thetaCuspTiltSource_eq_xiCentBezoutian`
- `riemannHypothesis_iff_thetaCuspTiltSource_sourceBezoutian_nonneg`
- `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg`

Novelty status: `[NOVELTY-PLAUSIBLE]`. Internal declaration search found separate all-shift,
all-plane transform, and abstract tilt-flux results, but no literal `ThetaSource` instance or this
cross-module weld. The mathematical estimate is elementary; significance is elimination of the
first open TTF construction gate and promotion to a live arithmetic-source architecture.

