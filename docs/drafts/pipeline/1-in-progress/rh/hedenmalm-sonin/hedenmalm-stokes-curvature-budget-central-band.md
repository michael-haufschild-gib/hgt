# Hedenmalm Stokes curvature budget: exact central-band propagation

- **ID:** `hedenmalm-stokes-curvature-budget-central-band`
- **Label:** `P-G145`
- **Stage:** `1-in-progress`
- **Type:** UNCONDITIONAL SOURCE PROPAGATION / EXACT HIGH-FREQUENCY LOCALIZATION
- **Parent:** `hedenmalm-stokes-curvature-normalized-flux-budget.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVEL CROSS-ROUTE SYNTHESIS] [NOT RH]`

## Result

P-G144 left the curvature-normalized right-strip budget

```text
Re N_F(s) <= -(Re(s)-1/2) F'(1/2),
N_F(s)=F(s)-(s-1/2)F'(1/2),
F=-xi'/xi,
```

apparently open away from the positive real ray. Existing endpoint-quartet geometry already proves
the raw sign on every exact source-produced central frequency band. Transporting that theorem to
P-G144 gives, for every `XiOffLineQuartetAccretiveBand R`,

```text
Re(s)>1/2 and |Im(s)|<=R
  -> Re F(s)<=0
  -> Re N_F(s)<=-(Re(s)-1/2)F'(1/2).                  (1)
```

The sharpened rational endpoint-curvature certificate supplies

```text
R=218/25.
```

Thus `(1)` holds unconditionally for every positive aperture on the entire band
`|Im(s)|<=218/25`, not merely on `Im(s)=0`.

Define the exterior-tail budget by restricting P-G144 to

```text
R < |Im(s)|.
```

Central-band gluing is exact:

```text
TailBudget(R) <-> RightBudget                         (2)
```

for every exact endpoint-quartet band. At `R=218/25`, P-G144 then gives

```text
TailBudget(218/25) <-> RH.                            (3)
```

## Proof mechanism

Put

```text
a=Re(s)-1/2,
b=Im(s),
z=b-a*i.
```

Endpoint-quartet accretivity gives

```text
Im xiRelativeResolventTrace(z)>=0
```

whenever `a>0` and `|b|<=R`. Its companion zero-exclusion theorem makes `XiC(z)` nonzero, so the
exact completed-flux identity applies:

```text
xiRelativeResolventTrace(z)=-i F(s).
```

Taking imaginary parts yields `Re F(s)<=0`. Since the calibrated central slope is real,

```text
Re N_F(s)=Re F(s)-(Re(s)-1/2)F'(1/2),
```

which proves `(1)`. Splitting on `R<|Im(s)|` proves `(2)`; `(3)` follows from P-G144's exact
right-budget/RH equivalence.

## Why this is progress

This is not another RH criterion. It removes an infinite two-dimensional region from the open
producer problem using unconditional source geometry. P-G144's phrase “transverse propagation”
was too broad: propagation through the full low-frequency slab is already available. Remaining
unknown is exclusively high-frequency escape of finite completed first-trace remainder.

Higher principle: central curvature calibration and endpoint quartet accretivity are two views of
the same passivity budget. Local curvature fixes allowed horizontal work; quartet self-charge
prevents transverse sign loss until frequency exceeds the source-paid band. Off-line divisor
charge can therefore hide only beyond that band. This identifies frequency escape—not local
transverse instability—as current obstruction.

## Anti-theatre audit

- No zero ordinate was numerically checked; `218/25` comes from symbolic rational endpoint bounds.
- No RH-equivalent premise proves central band; `XiOffLineQuartetAccretiveBand (218/25)` is an
  unconditional theorem.
- No positivity statement is renamed: proof transports exact relative-resolvent sign to exact
  P-G144 normalized flux.
- `(3)` remains equivalence, not proof of tail budget.
- Existing `ContinuedPrimeArchPositiveFrequencyAbove R <-> RH` is nearest parent. New content is
  exact compatibility with polar-residue cancellation and curvature normalization, showing
  P-G143/P-G144 finite remainder inherits same central-band closure.

## Formal artifacts

Module:

```text
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmStokesCurvatureBudgetCentralBand.lean
```

Theorems:

```text
seamFluxCochain_re_nonpos_of_exactOffLineQuartetBand
hedenmalmCurvatureNormalizedSeamFlux_budget_of_exactOffLineQuartetBand
hedenmalmCurvatureNormalizedSeamFlux_budget_twoHundredEighteen_twentyFifths
hedenmalmCurvatureNormalizedRightTailBudget_iff_rightBudget_of_exactOffLineQuartetBand
hedenmalmCurvatureNormalizedRightTailBudget_twoHundredEighteen_twentyFifths_iff_rh
```

## Remaining target

Prove the source-side tail estimate

```text
Re F(s)<=0
```

for `1/2<Re(s)<1` and `218/25<|Im(s)|`, or construct an equivalent coefficient-faithful passive
scattering law. Any next conjecture must control high-frequency modular-seam cancellation; local
Taylor jets, central-band quartet budgets, or positive real-ray response cannot see this tail.

## Gates

- [x] paper proof dependency closed
- [x] direct foreground Lean check
- [x] exact module build (`12815/12815`)
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [ ] umbrella build
- [ ] high-frequency tail budget / RH

## Log

- 2026-08-13 — Crossed P-G144 with exact endpoint-quartet band; proved unconditional full-slab
  budget and exact RH localization to `218/25<|Im(s)|`.
