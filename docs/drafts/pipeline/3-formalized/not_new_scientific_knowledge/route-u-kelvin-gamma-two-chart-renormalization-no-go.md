# Route U Kelvin--Gamma two-chart renormalization no-go

- **ID:** `route-u-kelvin-gamma-two-chart-renormalization-no-go`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Status:** `[LEAN-PROVED] [HOSTILE AUDIT PASSED] [BRIDGE/ROUTE NO-GO]`
- **Parent:** `route-u-kelvin-laplace-detailed-balance`
- **Exact claim:** no scalar counterterm can simultaneously renormalize the interior Mellin chart
  and the fixed-physical boundary chart of the Kelvin Gamma commutator.

## Public sentence

Gamma phase has two incompatible Kelvin infinities: the moving interior needs no subtraction,
while the fixed physical boundary needs one full logarithm of hard-edge mass.

## Exact frontier

`[CORPUS]` `gammaHardyPhaseRate_sub_log_conductor_tendsto_zero` in
`HardyZPhaseAsymptotic.lean` proves

```text
gammaHardyPhaseRate(t) - (1/2) log(t/(2*pi)) -> 0       (t -> +infinity).
```

`[CORPUS]` `XiShiftedHardEdgePrimeGammaKelvinLaplaceDetailedBalance.lean` proves that the actual
source-matched Laplace filter cancels every heat and degree cocycle, leaving precisely

```text
gammaHardyPhaseRate(x) - gammaHardyPhaseRate(a^2/x)
```

on each Kelvin orbit.  It does not determine how this commutator behaves uniformly across the
compactified orbit space.

`[LITERATURE]` Brent, *On asymptotic approximations to the log-Gamma and Riemann-Siegel theta
functions*, arXiv:1609.03682, proves explicit log-Gamma and Riemann--Siegel theta remainder bounds.
Connes--Consani, *The Scaling Hamiltonian*, arXiv:1910.14368, and *Weil positivity and Trace
formula, the archimedean place*, arXiv:2006.13771, study the archimedean scaling action and its
cutoff boundary.  None of these sources states the Route-U Kelvin two-chart scalar-counterterm
classification below.  The asymptotic input itself is classical; priority is claimed only for the
source-specific obstruction, provisionally and subject to expert audit.

## Conjecture loop

### U-KG-INTERIOR-CONTROLS-GLOBAL

`[CONJECTURE]` The fixed log-radius limit of the Gamma commutator controls the actual hard-edge
packet globally.

**Verdict:** `[FALSIFIED]`.  Put

```text
I(a) = gammaHardyPhaseRate(a*exp(-1))
       - gammaHardyPhaseRate(a*exp(1)),
B(a) = gammaHardyPhaseRate(1) - gammaHardyPhaseRate(a^2).
```

Then `I(a)->-1`, whereas `B(a)+log(a)` has a finite limit.  Hence `B(a)->-infinity`.  The fixed
physical packet lives in a boundary layer invisible to the fixed log-radius chart.

### U-KG-ONE-SCALAR-COUNTERTERM

`[CONJECTURE]` A mass-dependent scalar `r(a)` can renormalize both charts.

**Verdict:** `[FALSIFIED]` by the exact theorem below.  This failure cannot be repaired by choosing
a different multiple of `log(a)`: it excludes every scalar function `r`, without regularity or
asymptotic assumptions.

### U-KG-COCYCLE-SHEAF

`[CONJECTURE]` The complete prime--polar correction is not a scalar reserve.  It is a chart-local
Kelvin coboundary whose logarithmic charge is zero on fixed log-radius orbits and one on the fixed
physical boundary.

`[OPEN CORE]` Derive this two-chart charge directly from the literal polar evaluation and
von-Mangoldt Fourier source, then prove its cancellation/classification for the one fixed false-RH
carrier.  The no-go theorem below proves that any scalar completion is impossible; it does not yet
construct the required non-scalar source coboundary.

## Frozen theorem

Define `I` and `B` as above.  Then

```text
not exists r : R -> R, exists L_I L_B : R,
  Tendsto (fun a => I(a) + r(a)) atTop (nhds L_I)
  and
  Tendsto (fun a => B(a) + r(a)) atTop (nhds L_B).       (KG.1)
```

This statement is premise-free and quantifies over every scalar counterterm.

## Dependency-closed paper proof

Write

```text
e(t) = gammaHardyPhaseRate(t) - (1/2) log(t/(2*pi)).
```

The corpus asymptotic gives `e(t)->0` as `t->+infinity`.

For the interior chart, both `a*exp(-1)` and `a*exp(1)` tend to `+infinity`.  Therefore

```text
I(a)
 = e(a*exp(-1)) - e(a*exp(1))
   + (1/2)[log(a*exp(-1)/(2*pi))
            - log(a*exp(1)/(2*pi))].
```

Eventually `a>0`; the logarithm laws reduce the bracket to `-2`.  Thus

```text
I(a) -> -1.                                               (KG.2)
```

For the fixed physical boundary, `a^2->+infinity`, so

```text
B(a)+log(a)
 = gammaHardyPhaseRate(1) - e(a^2)
   - (1/2)log(a^2/(2*pi)) + log(a).
```

Eventually `a>0`, and

```text
(1/2)log(a^2/(2*pi)) = log(a) - (1/2)log(2*pi).
```

Consequently

```text
B(a)+log(a)
  -> gammaHardyPhaseRate(1) + (1/2)log(2*pi).             (KG.3)
```

Assume a scalar counterterm `r` and finite limits `L_I,L_B` satisfy `(KG.1)`.  Subtract `(KG.2)`
from the first convergence.  Then

```text
r(a) -> L_I+1.                                           (KG.4)
```

Subtract `(KG.3)` from the second convergence.  Then

```text
r(a)-log(a)
  -> L_B-gammaHardyPhaseRate(1)-(1/2)log(2*pi).           (KG.5)
```

Since `log(a)->+infinity`, `(KG.5)` implies `r(a)->+infinity`, contradicting the finite limit
`(KG.4)`.  This proves `(KG.1)`.

## Hostile audit

- **Wrong before right:** `(KG.1)` does not prove RH, does not sign the complete cross capital,
  and does not control polar or prime terms.  Treating it as source completion would be theatre.
- The theorem is stronger than exclusion of `c*log(a)`: `r` is arbitrary.
- No positivity, RH, zero-density, regularity of `r`, or carrier hypothesis is used.
- The two charts are not cosmetic parameterizations.  Their Gamma commutators have different
  logarithmic valuations, zero and minus one.
- The parent asymptotic is classical, so the analytic calculation is a `[BRIDGE]`.  The Route-U
  mathematical delta is the exact terminal no-go for scalar completion after source-matched heat
  cancellation.

## Universal-shadow map

| Existing result or failure | Shadow of proposed two-chart cocycle |
|---|---|
| Kelvin anti-invariance of cross density | orientation line over each inversion orbit |
| source-matched Laplace detailed balance | heat/degree gauge disappears before chart gluing |
| finite fixed-log-radius Gamma difference | zero logarithmic charge on interior Mellin chart |
| parabolic Nyquist boundary layer | unit logarithmic charge at physical boundary |
| failure of universal cross orientation | scalar sign cannot survive a nontrivial chart cocycle |
| need for literal prime--polar completion | arithmetic source must glue charts non-scalarly |

Risky consequence: any proposed Route-U completion whose mass dependence factors through one
scalar `r(a)` must fail before divisor aggregation.  A surviving source must retain orbit/chart
dependence at the prime--polar level.

## Lean certificate

`XiShiftedHardEdgePrimeGammaKelvinTwoChartNoGo.lean` proves:

1. `routeUHardEdgeKelvinGammaInteriorChart_tendsto`, exactly `(KG.2)`;
2. `routeUHardEdgeKelvinGammaPhysicalBoundaryChart_tendsto`, exactly `(KG.3)`;
3. `not_exists_routeUHardEdgeKelvinGammaGlobalScalarRenormalization`, the premise-free theorem
   `(KG.1)` quantified over arbitrary `r : ℝ → ℝ`.

The module uses symbolic filter and logarithm laws only.  It contains no numerical evaluation,
`native_decide`, `#eval`, `#reduce`, added axiom, or unclosed proof.
