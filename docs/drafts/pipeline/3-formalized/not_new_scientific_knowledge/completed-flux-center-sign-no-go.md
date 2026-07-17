# Completed-flux center-sign no-go

- **ID:** `completed-flux-center-sign-no-go`
- **Stage:** 3-formalized
- **Type:** `[PROVED] [BRIDGE] [ROUTE NO-GO]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CompletedFluxCenterSign.lean`
- **Statement:** The quadratic completed-flux coefficient and its fixed continued-prime plus
  archimedean decomposition have strictly negative real part at the critical-line center.

## Claim

The theta-cusp source gives the unconditional signs

```text
Xi(0) > 0,    Xi'(0) = 0,    Xi''(0) < 0.
```

The exact quadratic completed-flux reader is

```text
Xi'(t)^2 - Xi(t) Xi''(t)
  = -Xi(t)^2 completedFluxTaylorCoeff(linePt(t), 2).
```

At `t=0`, the left side is strictly positive and `Xi(0)^2` is strictly positive.  Hence

```text
Re completedFluxTaylorCoeff(linePt(0), 2) < 0.
```

Using the fixed coefficient decomposition gives

```text
Re (infinitePrimeFluxTaylorCoeff(linePt(0), 2)
  + archimedeanBoundaryFluxTaylorCoeff(linePt(0), 2)) < 0.
```

Therefore the functional-equation fixed point cannot supply the positive quadratic source value
which would refute RH.  Any quadratic completed-flux disproof must be genuinely off-center; center
symmetry does not merely fail to decide the sign, but forces the RH-compatible strict sign.

## Main declarations

- `completedFluxTaylorCoeff_two_center_re_neg`
- `prime_archimedean_second_coeff_center_re_neg`

## Scientific status

This is a sharp route elimination, not new scientific knowledge.  It combines the already-proved
theta-cusp center signs with the already-proved Laguerre reader.  The surviving source problem is
global: force a positive quadratic coefficient away from the center, or use a complete unshielded
source such as supercritical growth of the rectangular prime-polar negative mass.

## Gates

- [x] exact symmetric discriminator identified
- [x] unconditional paper proof
- [x] Lean formalization
- [ ] source producer for `not RiemannHypothesis`
