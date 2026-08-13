# Hedenmalm--Stokes curvature-normalized flux budget

- **Label:** `P-G144`
- **Stage:** 1-in-progress
- **Type:** THEOREM / GAUGE CLASSIFICATION / SHARP REAL-RAY BUDGET / RH-EQUIVALENT TRANSVERSE WALL
- **Parents:** `P-G139`, `P-G143`, `hd3-li-gauge-shift`,
  `XiSquaredEulerRayFullResponse`, `PrimeArchThetaCumulantMinor`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/HedenmalmStokesCurvatureNormalizedFluxBudget.lean`
- **Status:** `[PROVED IN LEAN] [NEW ROUTE-P SURVIVOR] [NOT RH]`

## Result

P-G143 cancels complete first-trace principal residue. Remaining finite completed flux is

```text
F(s) = seamFluxCochain(s) = -xi'(s)/xi(s).
```

Existing HD3 work records zero-free functional-equation gauge

```text
xi_c(s) = exp(c(s-1/2)^2) xi(s).
```

P-G144 proves its exact Route-P effect:

```text
F_c(s) = F(s) - 2c(s-1/2).
```

Gauge preserves functional equation and zero set, while at every zero-free noncentral point its
real parameter can prescribe arbitrary real completed flux. Therefore divisor/reflection data
cannot imply raw P-G139 dissipativity.

Define central-slope subtraction

```text
N_F(s) = F(s) - (s-1/2)F'(1/2).
```

Lean proves exact gauge invariance `N_(F_c)=N_F` away from unchanged divisor. Theta-cusp source
fixes removed jet:

```text
F'(1/2) = -normalizedPrimeArchMoment(0) < 0.
```

Hence normalization is not fitted gauge choice: source identifies slope with strict positive
theta second-moment ratio carrying a minus sign.

On positive real Euler ray `s=1/2+x`, `x>0`, complete Xi squared-Euler response `R(u)` gives exact
finite-remainder law

```text
Re N_F(1/2+x) = x (R(0)-R(x^2)).
```

Since `R` is strictly decreasing and positive unconditionally,

```text
0 < Re N_F(1/2+x) < -x F'(1/2).
```

This simultaneously kills naive normalized dissipativity and proves its strongest replacement:
positive gauge-invariant remainder has strict theta-curvature budget on entire real right ray.

Define complex-strip budget

```text
Re N_F(s) <= -(Re(s)-1/2) F'(1/2)
```

for every zero-free `1/2 < Re(s) < 1`. Algebraically this is exactly `Re F(s)<=0`; Lean proves

```text
HedenmalmCurvatureNormalizedRightBudget
  <-> SquarefreeFirstTraceRightDissipative
  <-> RH.
```

Thus Route P open core is no longer unspecified finite-remainder sign. It is transverse extension
of strict source-proved real-ray curvature budget into complex strip.

## Heavy conjecture loop

### C0 -- raw finite completed remainder is source-dissipative

**Conjecture.** Canonical polar cancellation leaves nonpositive completed current by divisor and
functional-equation symmetry.

**Failure.** Quadratic HD3 gauge preserves both data but shifts real flux arbitrarily at every
noncentral zero-free point. This broad gauge family was already known in Li chart; P-G144 proves
exact first-trace flux action and tunability.

### C1 -- central-jet subtraction removes fake sign freedom

**Conjecture.** `N_F=F-(s-1/2)F'(1/2)` removes whole quadratic FE gauge.

**Verdict: PROVED EXACTLY.** Raw flux and central slope shift by same `-2c`, hence cancel pointwise.
Reflection orientation survives.

### C2 -- normalized finite remainder is dissipative

**Conjecture.** Gauge-invariant remainder itself satisfies `Re N_F<=0`.

**Failure, WITH SHARP POSITIVE SURVIVOR.** It is strictly positive at every positive real Euler
point. Exact value is full squared-Euler response loss `x(R(0)-R(x^2))`. It stays strictly below
theta-curvature allowance `-xF'(1/2)`.

### C3 -- curvature budget is true complex invariant

**Conjecture.** Extend real-ray inequality to full right strip.

**Verdict: EXACT RH-EQUIVALENT OPEN CORE.** Budget is algebraically canonical completed-flux
dissipativity and hence RH. Real-axis restriction is already strict/unconditional; only transverse
propagation remains.

## Universal interpretation

P-G143's polar cancellation and P-G144's gauge subtraction expose same higher principle:

```text
principal residue  -> fixed by polar completion;
linear regular jet -> fixed by theta central curvature;
transverse excess  -> only RH-bearing datum left.
```

Prior stalls were shadows of mixing these three layers. Principal residue cannot carry sign after
completion. Linear jet sign is normalization-dependent until source-calibrated. Once both are
removed, real-ray radial monotonicity proves exact budget and isolates genuinely two-dimensional
complex propagation.

## Positive survivor

Prove transverse curvature-budget propagation from theta/prime source:

```text
Re N_F(s) <= -(Re(s)-1/2) F'(1/2),
1/2 < Re(s) < 1,
zeta(s) != 0.
```

Useful stronger target: a source-built subharmonic or positive-kernel majorant whose real-axis
trace is exactly `x(R(0)-R(x^2))` and whose boundary allowance is theta curvature. Generic maximum
principle without control of horizontal boundary or poles is insufficient.

## Verification

- direct `lake env lean` module check: passed
- exact module build: passed (`12813/12813`)
- `#print axioms` headline audit: only `propext`, `Classical.choice`, `Quot.sound`
- targeted forbidden-declaration scan: clean
- umbrella import: wired; umbrella build pending

## Gates

- [x] known HD3 gauge checked before novelty claim
- [x] exact flux shift and real-point tunability
- [x] exact central-slope gauge invariant
- [x] theta-source central-slope calibration and strict sign
- [x] exact real-ray response-loss formula
- [x] strict real-ray curvature budget
- [x] complex budget equivalence to P-G139 and RH
- [x] exact module build and axiom audit
- [ ] umbrella build
- [ ] source proof of transverse complex-strip budget
- [ ] RH

## Log

- 2026-08-13 -- opened after P-G143 canceled universal first-trace residue.
- 2026-08-13 -- C0 killed by exact quadratic gauge shift; broad gauge novelty downgraded against
  existing HD3 card.
- 2026-08-13 -- C1 proved; central-slope subtraction is exact quadratic-gauge quotient.
- 2026-08-13 -- C2 falsified on real ray; strict response-loss curvature budget extracted and
  formalized.
- 2026-08-13 -- C3 identified as exact transverse RH wall.
