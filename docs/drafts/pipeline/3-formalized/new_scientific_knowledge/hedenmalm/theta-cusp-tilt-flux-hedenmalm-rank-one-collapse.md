# TTF rank-one sector collapses to the Hedenmalm transverse current

Status: Lean-formalized, unconditional route compression. `[CORPUS-NEW SYNTHESIS]`. Does not
prove RH.

## Exact weld

For `a>0`, `b` real, and `w=a+b*I`, Lean proves

```text
Re(sourceBezoutian thetaCuspTiltSource w w)
  = xiTransverseEnergyCurrent(a,b)/(2a).
```

The coordinate rotation is exact:

```text
xiCent(w)  = XiC(-I*w),
xiCent'(w) = -I*XiC'(-I*w).
```

Inside `0<a<1`, the transverse current is the existing actual-source Hedenmalm current, hence

```text
Re(sourceBezoutian thetaCuspTiltSource w w)
  = thetaCuspCenterMixedFourierCurrent(a,b)/(2a).
```

Without any strip restriction, the transverse current equals the split Krein value of the pointed
theta/Xi orbit. Existing exterior-orbit positivity therefore yields

```text
1/2 <= Re(w)
  ==> 0 <= Re(sourceBezoutian thetaCuspTiltSource w w).
```

Finally `thetaCuspTiltSource_oneMode_tiltFlux_nonneg` transfers this to the literal derivative at
neutral tilt of every one-mode correlation.

## New route information

TTF's RH criterion samples modes only in `Re(w)>1/2`. Its entire one-mode sector is now proved
nonnegative on the larger closed domain `Re(w)>=1/2`. Therefore no scalar tilt trajectory, scalar
diagonal estimate, or scalar source-shape argument can close or refute TTF. The first potentially
RH-bearing information is cross-mode coherence in a packet of at least two distinct modes.

This identifies TTF's diagonal as the already-developed Hedenmalm transverse producer, while
retaining a genuinely different off-diagonal packet problem. It also transfers every existing
Hedenmalm current positivity band to the matching scalar TTF diagonal by an exact positive scale.

## Lean source

`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspTiltFluxHedenmalmWeld.lean`

Closed declarations:

```text
deriv_xiCent_eq_neg_I_mul_deriv_XiC
sourceBezoutian_thetaCuspTiltSource_self_re_eq_transverseCurrent_div
sourceBezoutian_thetaCuspTiltSource_self_re_eq_centerMixedCurrent_div
xiTransverseEnergyCurrent_eq_thetaXiHankelOrbit_kreinForm
sourceBezoutian_thetaCuspTiltSource_self_nonneg_of_half_le
thetaCuspTiltSource_oneMode_tiltFlux_nonneg
```

Verification:

- direct source check passed with `lake env lean`;
- exact target build passed with
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxHedenmalmWeld`;
- no umbrella/full build was run;
- all six `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`;
- module is wired into `RHTower.lean`.
