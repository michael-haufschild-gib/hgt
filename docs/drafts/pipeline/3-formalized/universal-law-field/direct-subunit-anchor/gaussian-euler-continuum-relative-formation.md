# Gaussian Euler--continuum relative formation

- **ID:** ULF-GECRF-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `1-in-progress/universal-law-field/direct-subunit-anchor/restricted-prime-gamma-toeplitz-polar-defect.md`

## Statement

Write

```text
c(n) = Lambda(n)/log n  for n>=2,
L_x(s) = sum_(n>=2) c(n) exp(-pi*x*n^2) n^(-s),
J_x(s) = sum_(n>=2) Lambda(n) exp(-pi*x*n^2) n^(-s)
```

for `x>0`.  Let the continuum heat zero-mode be

```text
M_x(s) = integral_(1,infinity) exp(-pi*x*u^2) u^(-s) du,
```

and let `A_x` be its unique entire primitive normalized by

```text
A_x'(s)=M_x(s),   A_x(2)=0.
```

On the right half-plane `H={Re(s)>0}` define

```text
h_infinity(s) = (1/2) s pi^(-s/2) Gamma(s/2),
Phi_x(s) = h_infinity(s) exp(L_x(s)+A_x(s)).            (GECRF.1)
```

Then:

1. `L_x,J_x,M_x,A_x` are entire; `Phi_x` is holomorphic and zero-free on `H`.
2. Unsquared Euler formation and continuum subtraction obey the exact current law

   ```text
   L_x'(s) = -J_x(s),
   logDeriv(Phi_x)(s)
     = logDeriv(h_infinity)(s) - J_x(s) + M_x(s).       (GECRF.2)
   ```

3. Locally uniformly on `Re(s)>1`, as `x -> 0+`,

   ```text
   L_x(s) -> canonicalLog(zeta(s)),
   J_x(s) -> -zeta'(s)/zeta(s),
   M_x(s) -> 1/(s-1),
   A_x(s) -> Log(s-1),
   Phi_x(s) -> xi(s).                                  (GECRF.3)
   ```

4. For every rectangle compactly contained in `1/2<Re(s)<1`, the boundary phase of `Phi_x` has
   winding zero for every `x>0`.  Therefore any nonzero winding of the completed Xi boundary can
   arise from this source family only through failure of compactness as `x -> 0+`.
5. On `0<Re(s)<1`, the reflected-chart transition

   ```text
   G_x(s)=Phi_x(s)/Phi_x(1-s)                           (GECRF.4)
   ```

   is holomorphic and zero-free, satisfies `G_x(1-s)=G_x(s)^(-1)`, and is unitary on
   `Re(s)=1/2`.  Thus the functional-equation action lifts through formation without creating or
   deleting information.
6. On every smooth closed contour compactly contained in `Re(s)>1`, the normalized phases
   `Phi_x/|Phi_x|` converge in `C1` to `xi/|xi|`; both chiral corona losses vanish.  Hence the
   completion defect is born only after the safe Euler chart is crossed.

No zero, divisor, zero ordinate, Euler-product branch inside the critical strip, or adjustable
normalization enters `(GECRF.1)`.

## Proof

For `n>=2`, `0<=c(n)<=1`: it is `1/k` on `n=p^k` and zero otherwise.  On every compact set of
the `s`-plane, both series are normally convergent because the Gaussian `exp(-pi*x*n^2)` dominates
every power of `n`.  Termwise differentiation is valid and multiplication by `log n` changes
`c(n)` to `Lambda(n)`, proving `L_x'=-J_x`.

For fixed `x>0`, the integral defining `M_x` is normally convergent in `s` on every compact set:
the same Gaussian dominates `u^C(1+log(u)^m)` for all bounded real parts and all derivatives.
Thus `M_x` is entire.  Since `C` is simply connected, it has a unique entire primitive with value
zero at `2`.  The factor `h_infinity` is holomorphic and nonzero on `H`: `s` is nonzero there,
`Gamma` is holomorphic and nonzero there, and the exponential power of `pi` never vanishes.
This proves the first clause and `(GECRF.2)`.

Fix a compact `K` in `Re(s)>1` and choose `sigma_0>1` below every real part in `K`.  Dominated
convergence uses respectively the summable majorants

```text
c(n)n^(-sigma_0),   Lambda(n)n^(-sigma_0),   u^(-sigma_0).
```

It gives the first three limits in `(GECRF.3)` locally uniformly.  Normalization at `2` then gives

```text
A_x(s) -> integral_2^s dw/(w-1) = Log(s-1)
```

on the simply connected half-plane `Re(s)>1`.  Exponentiating and using the canonical Euler-log
identity yields

```text
Phi_x(s) -> (1/2)s*pi^(-s/2)*Gamma(s/2)*(s-1)*zeta(s)=xi(s).
```

Finally, `Phi_x` is zero-free on the interior of every stated rectangle, so its boundary winding
is zero by the argument principle.  A nonzero limiting winding cannot be produced by locally
uniform convergence on the closed rectangle (Hurwitz, or continuity of degree).  It is therefore
necessarily completion-born loss of compactness.

All coefficients, the continuum kernel, and the basepoint are real, so uniqueness of the
normalized primitive gives `Phi_x(conj(s))=conj(Phi_x(s))`.  Both `s` and `1-s` lie in `H` on the
open strip, proving holomorphy and zero-freeness of `(GECRF.4)`.  Involution gives the reciprocal
law.  On `s=1/2+it`, `1-s=conj(s)`, so `G_x(s)=Phi_x(s)/conj(Phi_x(s))` has modulus one.

On a compact contour in `Re(s)>1`, `(GECRF.3)` and `(GECRF.2)` give uniform convergence of both
`Phi_x` and its logarithmic derivative.  The nonzero limit has a positive minimum modulus, so
normalization is smooth there and the phases converge in `C1`.  Their positive and negative
weighted Fourier energies therefore converge separately; no trace mass reaches the corona.  QED.

## Corpus fusion

- `EulerLogPrimePowerLaplace` supplies the exact unsquared Euler-log carrier and differentiation
  law in the absolute-convergence chart.
- `GaussianPrimeDiscrepancy` already identifies the differentiated atomic-minus-continuous
  Gaussian mechanism: von-Mangoldt atoms against their continuous PNT density.
- `XiThinStripExponentialEulerGaugeInvariance` proves every finite entire exponential gauge has
  zero contour charge, consistent with clause 4.
- `RPGT-C` identifies the only possible completed charge as chiral Hankel trace mass lost at the
  high-mode corona.

The new theorem constructs the previously unnamed relative formation family and its universal
metric anomaly.  It does **not** prove weak `H^(1/2)` convergence on strict-right boundaries or the
sub-unit chiral-corona bound; those are the exact remaining arithmetic steps.

The transition law `(GECRF.4)` is not itself a selector.  Functional-equation symmetry is a
static chart compatibility and does not prevent the common completed section from vanishing.

## Lean status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.GaussianEulerContinuumRelativeFormation`.  Closed capstone
`gaussianEulerContinuumRelativeFormation_closed` certifies the entire Euler, continuum, and
formation fields; exact logarithmic-current identity; all locally uniform safe-chart limits;
zero rectangle winding; `C¹` contour-phase convergence; and reflected zero-free transition law.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.GaussianEulerContinuumRelativeFormation`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module `GaloisForLFunctions.RHTower.GaussianEulerContinuumRelativeFormation` (117 constants, axiom audit clean).

| Claim | Lean declaration |
|-|-|
| (GECRF.1) `L_x`, `J_x`, `M_x`, `A_x`, `h_∞`, `Φ_x` | `gaussianEulerLog`, `gaussianVonMangoldtCurrent`, `gaussianContinuumCurrent`, `gaussianContinuumPrimitive` (`exists_gaussianContinuumPrimitive`, `gaussianContinuumPrimitive_unique`, `gaussianContinuumPrimitive_two`), `gaussianArchimedeanHalfFactor` (`_eq_gammaReal`), `gaussianEulerContinuumFormation` |
| 1. `L_x, J_x, M_x, A_x` entire; `Φ_x` holomorphic and zero-free on `Re s > 0` | `differentiable_gaussianEulerLog`, `differentiable_gaussianVonMangoldtCurrent`, `differentiable_gaussianContinuumCurrent`, `differentiable_gaussianContinuumPrimitive`, `differentiableAt_gaussianEulerContinuumFormation`, `gaussianEulerContinuumFormation_ne_zero` |
| 2. (GECRF.2) `L_x' = -J_x`; `logDeriv Φ_x = logDeriv h_∞ - J_x + M_x` | `hasDerivAt_gaussianEulerLog`, `deriv_gaussianEulerLog`, `logDeriv_gaussianEulerContinuumFormation` |
| 3. (GECRF.3) locally uniform limits on `Re s > 1` | `tendstoLocallyUniformlyOn_gaussianEulerLog`, `tendstoLocallyUniformlyOn_gaussianVonMangoldtCurrent`, `tendstoLocallyUniformlyOn_gaussianContinuumCurrent`, `tendstoLocallyUniformlyOn_gaussianContinuumPrimitive`, `tendstoLocallyUniformlyOn_gaussianEulerContinuumFormation` (`gaussianEulerContinuumFormationLimit_eq_xi`) |
| 4. rectangle winding zero for every `x > 0` | `gaussianFormationRectangleWinding_eq_zero` |
| 5. (GECRF.4) `G_x` holomorphic, zero-free, `G_x(1-s) = G_x(s)⁻¹`, unitary on `Re s = 1/2` | `differentiableAt_gaussianReflectedTransition`, `gaussianReflectedTransition_ne_zero`, `gaussianReflectedTransition_one_sub`, `norm_gaussianReflectedTransition_critical`; conjugation symmetry `gaussianEulerContinuumFormation_conj` |
| 6. `C¹` convergence of normalized phases on safe contours | `tendstoLocallyUniformlyOn_logDeriv_gaussianEulerContinuumFormation`, `tendstoLocallyUniformlyOn_gaussianNormalizedPhase`, `tendstoUniformlyOn_gaussianContourPhase_c1` |
| closed capstone | `gaussianEulerContinuumRelativeFormation_closed` |

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
