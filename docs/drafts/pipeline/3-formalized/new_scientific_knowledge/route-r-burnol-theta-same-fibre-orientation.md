# Route R Burnol–theta same-fibre orientation law

- **ID:** `route-r-burnol-theta-same-fibre-orientation`
- **Stage:** 3 — formalized in Lean 4
- **Route:** R
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [FRONTIER ADVANCE] [NOT RH]`
- **RH used:** no
- **Computation used:** no

## Open core attacked

For the fixed Burnol co-Poisson atom, Route R has the explicit head current

```text
J_rho = |1-rho|^(-2) - (log 2)^2 |rho|^(-2).
```

Lean already proves `J_rho > 0` throughout `1/2 < Re rho < 1`.  Therefore a source theorem giving
`J_rho <= 0` at every actual right-half Xi divisor must independently exclude such a divisor.
The missing issue is not another estimate on `J`; it is an orientation-changing source comparison.

## Conjecture / attack cycle

1. **Completed divided Xi energy supplies the missing source current.** `[PARTIAL SUCCESS]`
   `HedenmalmCompletedDividedEnergy` identifies the genuine completed first quotient
   `Q_rho = XiC/(.-alpha_rho)` with theta root energy at `-alpha_rho`.  The reflected argument
   initially leaves the physical orientation ambiguous.
2. **Theta root energy is reflection-even at a source zero.** `[PROVED]`  Source reflection gives
   `U_{-z}(-x)=-U_z(x)`.  Haar reflection and norm invariance therefore give
   `E(-z)=E(z)` without zero location, simplicity, or an assumed source dagger.
3. **Same-fibre compact boundary law.** `[PROVED]`  Substitution into the existing Plancherel
   identity and compact boundary-flux formula gives the division-free identity

   ```text
   pi * M * B_theta(q)
     = Im(alpha_q) * ‖completedXiFirstDividedL2(q.support)‖^2.
   ```

   `M>0` is fixed theta-source mass.  The divided vector is nonzero at every divisor support
   point, so this comparison is coefficient-faithful and multiplicity-safe.
4. **Can this directly prove Burnol dissipativity?** `[FAILED — ORIENTATION OPPOSITION]`  At every
   hypothetical right-half divisor, `Im(alpha_q)<0`, hence `B_theta(q)<0`; the already explicit
   Burnol current satisfies `J_rho>0`.  Lean proves their product is strictly negative.  Positive
   same-fibre transport cannot identify them with the same orientation.

## Mathematical delta

The compact-theta source no longer merely gives a different RH-equivalent sign detector.  Its
rank-two boundary current now lands on the exact same-fibre positive norm of the genuine completed
first-divided Xi vector.  Reflection ambiguity and normalization ambiguity are gone:

```text
fixed positive normalization = pi * thetaSource.mass;
retained vector              = completedXiFirstDividedL2 rho;
orientation coefficient      = (xiSpectralPoint rho).im.
```

This reduces the Route-R comparison burden from a full GNS/compact-source representation map to
one precise orientation-changing scalar handoff from the Burnol fixed-window divided atom to the
completed first-divided Xi vector.  A positive isometry or ordinary same-orientation polarization
comparison is now formally excluded as sufficient.

## Remaining theorem

Construct from pre-divisor Euler–Gamma–Stokes data a coefficient-faithful handoff which carries the
Burnol fixed-window divided current into the completed-Xi/theta same-fibre boundary port **with the
required orientation reversal**.  It must not assume `J_rho <= 0`, critical-line placement, RH,
same-fibre norm identity, or a source-dagger identity.  The new theorem supplies the completed-Xi
norm and compact boundary side unconditionally; only the Burnol-to-completed-Xi orientation
handoff remains.

## Lean

Module:

```text
formal/GaloisForLFunctions/RHTower/RouteRBurnolThetaSameFiberOrientation.lean
```

Capstones:

- `thetaRootEnergy_neg_of_zero`;
- `norm_sq_completedXiFirstDividedL2_eq_sameFiberThetaRootEnergy`;
- `thetaXiRankTwoBoundaryFlux_completedXi_sameFiber`;
- `thetaXiRankTwoBoundaryFlux_neg_of_rightHalf`;
- `burnolThetaSameFiber_orientedCurrents_opposed`.

Module is wired into `formal/GaloisForLFunctions/RHTower.lean`.

