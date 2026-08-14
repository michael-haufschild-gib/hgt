# Route P critical collision-scale kernel

- **ID:** `route-p-critical-collision-scale-kernel`
- **Label:** P-G172
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE / UNIFORMITY NO-GO WITH POSITIVE SURVIVOR
- **RH status:** open
- **Computation used:** no
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/RoutePCriticalCollisionScaleKernel.lean`

## Conjecture

P-G171 proves source-native ordinate diagonalization when each unequal physical gap is fixed while
`sigma -> 1+`. A height-local packet grows with height, so its smallest gap need not stay fixed.
Test the collision scale

```text
delta_sigma - gamma = kappa (sigma - 1).
```

The exact pair parameter then becomes

```text
1 + (sigma-1) [R(a+b)+i kappa].                         (172.1)
```

Therefore both columns approach the zeta pole together. The predicted zero-order limit is the
complex Cauchy kernel

```text
R / [R(a+b)+i kappa],                                   (172.2)
```

not zero. Since `(s-1)^3 zeta''(s) -> 2`, one log-moment term should tend to

```text
2 R^3 / [R(a+b)+i kappa]^3.                             (172.3)
```

Four-term Hellinger polarization then gives an exact mesoscopic cubic kernel. For a finite cluster
with scaled offsets `kappa_i`, its limiting Gram should retain every entry at relative frequency
`kappa_j-kappa_i`.

## Higher principle

The zeta pole is not a discontinuous Kronecker projector at finite resolution. It is a resolving
Cauchy kernel whose spectral resolution is exactly `sigma-1`. Fixed gaps lie in its far field and
vanish; equal gaps lie at frequency zero; collision-scale gaps survive as a non-diagonal positive
source Gram. Pointwise dephasing cannot be interchanged with growing height windows unless one
proves an independent uniform spacing or cluster-trace estimate.

## Conjecture loop

- **C1:** Differentiate the pointed completed-Xi reporter and use its four-unit Schur complement.
  **Failed as producer:** P-G162 already proves first-order Julia slack dominates the quadratic
  graph-normal toll. Differentiation does not cancel that order mismatch.
- **C2:** Apply P-G171 entrywise to each dyadic zero window, then pass height to infinity.
  **Failed:** P-G171 is pointwise in each fixed nonzero ordinate gap. No uniformity survives gaps
  comparable to `sigma-1`.
- **C3:** blow up the gap by the same critical clock used in the Hardy node and compute the retained
  kernel. **Selected and proved:** equations `(172.1)--(172.3)`, cubic polarization, and the full
  finite collision-packet law are exact source limits.

## Closed result

Lean proves the general second-derivative residue

```text
(s-1)^3 * iteratedDeriv 2 riemannZeta s -> 2
```

from the analytic zeta residue unit. It then proves `(172.1)--(172.3)` unconditionally. The actual
finite-`sigma` Route-P Hellinger tangent Gram converges to

```text
C_R(a,b;kappa)
 = 2R^3/[R(a+b)+i kappa]^3
 - 2R^3/[R(a+2b)+i kappa]^3
 - 2R^3/[R(2a+b)+i kappa]^3
 + 2R^3/[R(2a+2b)+i kappa]^3.                           (172.4)
```

Two co-moving ordinates with offsets `kappa` and `lambda` retain `(172.4)` at frequency
`lambda-kappa`; common motion is pure gauge. Every finite packet converges to the corresponding
non-diagonal collision Gram. Lean also proves a concrete falsifier:

```text
C_1(1,1;1) != 0.
```

Thus even though the two physical ordinates are distinct for every `sigma>1`, neither their
zero-order overlap nor their cubic tangent entry tends to zero. This closes the uniform-projector
shortcut negatively and exposes the positive survivor: completed height-local trace control must
bound the exact collision Gram, with no zero-spacing hypothesis and no pre-limit deletion of
near-diagonal entries.

This does not prove the Euler--Gamma trace budget or RH. It changes the open theorem from a
diagonal trace estimate to a cluster-stable non-diagonal trace estimate.

Scratch compilation produced
`/tmp/routep-snapshot/GaloisForLFunctions/RHTower/RoutePCriticalCollisionScaleKernel.olean`.
All audited capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`; targeted
forbidden-token scan is clean. Umbrella import is wired; umbrella was not compiled.

## Gates

- [x] reporter first-order-slack collision audit
- [x] exact collision-scale pair parameter
- [x] zero-order complex Cauchy limit
- [x] second zeta-jet collision limit
- [x] cubic collision kernel and concrete nonvanishing witness
- [x] two-moving-ordinate relative-frequency law
- [x] finite collision-packet quadratic-form limit
- [x] scratch compile, forbidden-token scan, and axiom audit
- [x] umbrella import wired without umbrella build
- [ ] cluster-stable completed height-local Euler--Gamma trace estimate
- [ ] unconditional RH closure
