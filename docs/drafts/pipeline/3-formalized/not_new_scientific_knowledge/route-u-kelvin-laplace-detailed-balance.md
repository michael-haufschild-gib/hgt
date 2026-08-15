# Route U Kelvin--Laplace detailed balance

- **ID:** `route-u-kelvin-laplace-detailed-balance`
- **Stage:** 3-formalized
- **Type:** CONJECTURE FAILURE + EXACT POSITIVE SURVIVOR
- **Status:** `[LEAN-PROVED] [HOSTILE AUDIT PASSED] [BRIDGE]`
- **Parent:** `route-u-kelvin-mellin-critical-heat-phase`

## Exact frontier

`[CORPUS]` The actual common-degree cross density satisfies, for `a,x>0`,

```text
F_t(a^2/x)
 = -(a^2/x^2)^(2d) exp(-t*((a^2/x)^2-x^2)) F_t(x).
```

Its Jacobian-paired current with an arbitrary real weight `w` is

```text
C_t(x;w)=F_t(x)w(x)+(a^2/x^2)F_t(a^2/x)w(a^2/x).
```

`[CORPUS]` Pointwise in heat time, unit-weight modular defect changes sign at one positive orbit
time.  `[CORPUS]` Polar rational terms cancel against archimedean rational terms in the continued
critical-Mellin source, so neither may be used as an independent positive reserve.  `[CORPUS]`
Every UV-safe constant PSD two-channel form collapses to full fine-sample square; local scalar or
matrix positivity cannot orient the source.

`[LITERATURE]` Burnol's [co-Poisson/Sonine theory](https://arxiv.org/abs/math/0203120) supplies
reciprocal Mellin and Fourier geometry, not this polynomial-Gaussian hard-edge heat filter.
Connes--Consani's [semilocal Weil programme](https://arxiv.org/abs/2006.13771) locates candidate
positivity in compressed scaling/Sonin operators, while [The Scaling
Hamiltonian](https://arxiv.org/abs/1910.14368) explicitly records failure of a naive
positive-operator cutoff.  [Rodgers--Tao](https://arxiv.org/abs/1801.05914) and
[Polymath](https://arxiv.org/abs/1904.12438) study Xi heat flow through zero dynamics and effective
Riemann--Siegel approximation, not Kelvin-paired completed-source currents.  No located primary
source states the identity below.  Generic Laplace moments and inversion covariance are classical,
so priority is not claimed.

## Conjecture--failure--pivot loop

### U-HEAT-MASS-ORIENTATION

`[CONJECTURE]` Positive and negative pointwise Kelvin heat phases leave a nonzero preferred
orientation after the exact Route U heat filter is integrated.

**Verdict:** `[FALSIFIED]`.  The filter does not average the phase defect imperfectly.  Its rate
and moment order exactly cancel it orbit by orbit.

### U-GAMMA-UNIVERSAL-ORIENTATION

`[CONJECTURE]` After heat integration, strict increase of `gammaHardyPhaseRate` forces one universal
sign for every polynomial cross channel.

**Verdict:** `[FALSIFIED]`.  On the inner Cayley half, the Gamma commutator is strictly negative.
The carriers `P_+(z)=1+z` and `P_-(z)=1-z` have the same even channel and opposite odd channels, so
their cross densities and filtered Gamma currents have opposite signs.  Gamma monotonicity orients
the commutator but not the carrier polarization.

### U-KELVIN-LAPLACE-DETAILED-BALANCE

`[PAPER-PROVED CANDIDATE]` Let `a,x>0`, `P` be a real polynomial, and `w` an arbitrary real weight.
Put `d=routeUHardEdgeKelvinDegree a P`, `y=a^2/x`, `N=2d+1`, and let `F_t` be the actual Route U
Kelvin cross density.  Then

```text
integral_(0,infinity) t^(2d) exp(-a^2 t) C_t(x;w) dt
 = (2d)! F_0(x)/(a^2+x^2)^N * (w(x)-w(y)).             (DB.1)
```

In particular, the unit-weight integral is exactly zero.  For `0<x<a` and
`w=gammaHardyPhaseRate`, strict Gamma monotonicity gives

```text
sign(filtered paired Gamma current) = -sign(F_0(x)).    (DB.2)
```

The rate match is rigid.  For `lambda>0` and `x!=a`,

```text
lambda+y^2 = (a^2/x^2)(lambda+x^2)  iff  lambda=a^2.   (DB.3)
```

Thus hard-edge mass shift `a^2`, moment order `2d`, Kelvin cocycle degree `2d+1`, and inversion
Jacobian are one detailed-balance law, not independent normalizations.

Lean feedback forces the stronger exact zero classification

```text
filteredCurrent(x;w)=0
  iff F_0(x)=0 or w(x)=w(a^2/x).                           (DB.7)
```

On every strict inner orbit, Gamma monotonicity makes its commutator nonzero, hence

```text
filteredGammaCurrent(x)=0 iff F_0(x)=0.                   (DB.8)
```

Both follow immediately from `(DB.1)` because factorial and shifted denominator are strictly
positive.  They survive the same hostile scope audit and are proved exactly in Lean.

## Dependency-closed paper proof

Write `r=a^2/x^2`; then `y=a^2/x`, `y^2=r a^2`, and `F_t(x)=F_0(x)exp(-t x^2)`.  Kelvin covariance
and the Jacobian give

```text
C_t(x;w)
 = F_0(x)[exp(-t x^2)w(x)-r^N exp(-t y^2)w(y)].        (DB.4)
```

Multiplication by `t^(N-1)exp(-a^2 t)` gives a difference of two integrable Gamma densities because
`a^2+x^2>0` and `a^2+y^2>0`.  The classical identity

```text
integral_(0,infinity) t^(N-1) exp(-c t) dt=(N-1)!/c^N
```

therefore yields

```text
(N-1)! F_0(x)
 [w(x)/(a^2+x^2)^N-r^N w(y)/(a^2+y^2)^N].             (DB.5)
```

But

```text
a^2+y^2=a^2+a^4/x^2=r(a^2+x^2),                       (DB.6)
```

so the second denominator contributes exactly `r^N`; cancelling proves `(DB.1)`.  Taking `w=1`
proves exact zero.  If `0<x<a`, then `0<x<a<y`; strict monotonicity of
`gammaHardyPhaseRate` on the positive ray makes `w(x)-w(y)<0`.  Every other factor in `(DB.1)` is
strictly positive except `F_0(x)`, proving `(DB.2)`.

For a general positive rate `lambda`, direct expansion gives

```text
x^2[lambda+y^2-r(lambda+x^2)]
  =(x^2-a^2)(lambda-a^2).
```

Since `x>0` and `x!=a`, the bracket vanishes exactly when `lambda=a^2`, proving `(DB.3)`.

## Hostile audit

- `(DB.1)` concerns the heat-integrated **paired archimedean cross current**, not the complete
  Gamma--polar--prime balance and not the sign of full Route U capital.
- `(DB.2)` does not orient the current without the sign of `F_0`; `P_+` and `P_-` prove no universal
  carrier sign exists.
- Pointwise critical heat time is not contradicted.  Detailed balance says its two phases cancel
  exactly under the source-matched Laplace moment.
- No RH statement, zero-free region, divisor positivity, or completed-source domination is assumed
  or concluded.
- The only analytic input is the integer Gamma integral at positive rate; all remaining steps are
  exact algebra plus already formalized Kelvin covariance and Gamma-rate monotonicity.
- Parent-theory normalization: `XiShiftedFilteredGammaTransmutation.lean` already proves the same
  filter/degree cancellation after expansion over Xi divisor atoms.  `(DB.1)` is therefore a new
  physical-orbit localization and rigidity bridge, not a new global transmutation mechanism.

## Mathematical delta

The earlier heat phase transition is a preintegration gauge shadow.  Route U's source filter is
exactly the modular detailed-balance measure that erases heat cocycle and retains only a weight
commutator.  This identifies the irreducible cross obstruction: after heat integration, all
archimedean information is the monotone Gamma difference, while every unresolved sign lies in
carrier polarization and the prime--polar completion.

## Next discriminator

Rewrite the actual inner-orbit Gamma term in Cayley coordinate.  The degree powers should cancel to
the odd covariance of `P(z)^2` against the strictly decreasing pullback
`gammaHardyPhaseRate(a*sqrt((1-z)/(1+z)))`.  Determine whether the fixed false-RH carrier has a
source-forced stochastic order, or whether prime--polar completion can realize both signs.  A
generic polynomial sign theorem is already falsified and must not be retried.

## Gates

- [x] `U-HEAT-MASS-ORIENTATION` falsified by exact cancellation
- [x] `U-GAMMA-UNIVERSAL-ORIENTATION` falsified by `1+X` / `1-X`
- [x] detailed-balance identity dependency-closed on paper
- [x] hostile paper audit
- [x] hostile Lean feedback audit; zero classification `(DB.7)`--`(DB.8)` added
- [x] exact Lean formalization and axiom audit

## Formalization audit

- Source:
  `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgePrimeGammaKelvinLaplaceDetailedBalance.lean`
- Source length: 255 lines.
- Scratch and checked-in source pass `lake env lean <file>`.
- Exact leaf `.olean` built directly: 651672 bytes.  No `lake build`, project build, or umbrella
  build was run.
- Module wired into `formal/GaloisForLFunctions/RHTower.lean`.
- Every public theorem reports only `propext`, `Classical.choice`, and `Quot.sound` under
  `#print axioms`.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `#eval`, or `#reduce` occurs.
- Static `scripts/formal_tools.py lint` found no problem in this module and confirmed umbrella
  reachability; repository-wide lint remains red only from seven unrelated pre-existing unreachable
  modules in RHTower/HTGeometry.
