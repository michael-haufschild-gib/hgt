# Route P critical-boundary ordinate diagonalization

- **ID:** `route-p-critical-boundary-ordinate-diagonalization`
- **Label:** P-G171
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE / SOURCE-NATIVE ORDINATE LOCALIZATION
- **RH status:** open
- **Computation used:** no
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/RoutePCriticalBoundaryOrdinateDiagonalization.lean`

## Conjecture

Let `t=R(sigma-1)` and replace P-G170's real projective node by the moving complex node

```text
u_sigma,R(a,gamma) = R*a - 1/2 + i*gamma/(sigma-1).
```

The apparent singularity is source-faithful: multiplication by `sigma-1` in the Euler damping
turns its imaginary part into the fixed unitary phase `n^(-i*gamma)`, while its real part and
Hilbert norm are unchanged. Pairing ordinates `gamma` and `delta` gives the exact zeta argument

```text
1 + t*(a+b) + i*(delta-gamma).
```

After projective normalization, equal ordinates still see the zeta pole and converge to the Hardy
kernel `1/(a+b)`. Unequal ordinates land away from the pole, so reciprocal source normalization
kills the overlap. The same dichotomy should hold for P-G170's log-weighted tangent Gram: equal
ordinates retain the cubic Hellinger kernel and unequal ordinates vanish.

## Higher principle

Horizontal damping and vertical dephasing are not two kernels to multiply. They are real and
imaginary components of one moving Hardy node. The zeta pole itself is then a spectral projector:
its residue preserves the diagonal ordinate fibre, while the normalized regular boundary values
annihilate every off-diagonal fibre.

## Why this is new

P-G159 supplies unitary logarithmic phase for fixed complex nodes. P-G169 supplies full
half-plane projective columns. P-G170 realizes the cubic horizontal jet as an actual finite-sigma
Euler tangent. Existing `XiWardCubicIntegerHarmonicDephasing` instead introduces a separate
integer-harmonic Cesaro projector and leaves its nonlinear product with the horizontal source
unidentified. P-G171 tests and formalizes a single-source replacement: critical imaginary blow-up
puts both effects inside one exact Hermitian Euler Gram.

## Hostile checks

1. Moving node must remain in P-G169's sharp source half-plane for every `sigma>1`; no analytic
   continuation may replace a genuine `EulerPositiveL2` vector.
2. Exact finite-sigma inner product must contain `i*(delta-gamma)` with no residual
   `sigma-1` factor.
3. Off-diagonal convergence must use regularity of zeta or its second jet away from `1` together
   with the actual reciprocal-zeta source normalization; formal insertion of a Kronecker delta
   earns no credit.
4. Diagonal tangent limit must reduce to P-G170's exact source Gram, not only to an abstract cubic
   kernel.
5. Finite packet diagonalization is not yet the completed Euler--Gamma `N/4` trace estimate.

## Conjecture loop

- **C1:** multiply P-G170's horizontal kernel by the existing integer-harmonic vertical kernel.
  **Rejected:** repeats the open nonlinear-product identification and provides no one-source Gram.
- **C2:** keep a fixed imaginary Hardy node while `sigma->1`. **Failed:** Euler damping multiplies
  its phase by `sigma-1`, so all ordinates coalesce at the boundary.
- **C3:** scale imaginary displacement by `1/(sigma-1)`. **Selected:** phase stays physical, norm
  stays fixed, and pole-versus-regular boundary behavior predicts exact ordinate diagonalization.

## Closed result

The conjecture is proved unconditionally in Lean. For every `sigma>1`, positive projective depths,
and real ordinates, the moving node lies in the sharp P-G169 source half-plane and defines a
genuine full-Euler Hilbert column. Its exact pair exponent is

```text
1 + R*(a+b)*(sigma-1) + i*(delta-gamma).
```

The projectively normalized state Gram converges to `1/(a+b)` when `gamma=delta` and to zero
otherwise. The log-weighted columns are separately constructed in `EulerPositiveL2`; their exact
Gram is the second zeta jet at the displayed pair exponent divided by `zeta(sigma)`. Lean proves
the half-weighted packet's literal coordinate derivative and identifies its Hilbert tangent Gram
with the four-term complex second-jet polarization. Its critical limit is

```text
if gamma = delta then cubicLogMomentHellingerHorizontalKernel a b else 0.
```

For every finite label type and arbitrary complex coefficients, Lean also proves convergence of
the complete packet quadratic form to the exact ordinate-block projection: unequal ordinate
blocks vanish, while repeated ordinates retain their horizontal cubic Gram. Thus the separate
integer-harmonic Cesaro multiplier is unnecessary at source level; horizontal separation and
vertical dephasing are one Hermitian Euler tangent Gram.

Scratch compilation produced
`/tmp/routep-snapshot/GaloisForLFunctions/RHTower/RoutePCriticalBoundaryOrdinateDiagonalization.olean`.
All audited capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`; targeted
forbidden scan is clean. Umbrella import is wired; umbrella was not compiled.

## Gates

- [x] corpus collision and dead-route audit
- [x] Lean moving-node source and exact finite-sigma overlap
- [x] Lean zero-order diagonal/off-diagonal boundary law
- [x] Lean log-weighted source tangent and exact complex zeta-jet Gram
- [x] Lean cubic diagonal/off-diagonal boundary law
- [x] finite packet trace consequence
- [x] scratch compile, forbidden-token scan, and axiom audit
- [x] umbrella import wired without umbrella build
- [ ] completed height-local Euler--Gamma trace estimate
