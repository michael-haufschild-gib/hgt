# Suzuki mixed-coordinate phase falsifier and centered Euler seam

- **ID:** `suzuki-jump-phase-obstruction-centered-euler-seam`
- **Stage:** 3-formalized
- **Type:** MIXED-COORDINATE FALSIFIER / MEROMORPHIC ORDER LAW / RH CONNECTOR
- **Scientific status:** `[SOURCE NO-GO RETRACTED] [MIXED ALGEBRA LEAN-PROVED]`
  `[CENTERED EULER LEAN-PROVED] [NOT RH]`
- **RH used:** no
- **Computation used:** no
- **Failed parent:** `../../5-failed/suzuki-scalar-jump-herglotz-phase-no-go.md`
- **Live successor:** `../../1-in-progress/suzuki-carleman-jump-euler-defect-weld.md`

## Result

> **Retraction (2026-07-22).** Phase theorem below applies to mixed expression `G_eta W-T_phys`,
> not Suzuki's physical sheet.  Physical multiplier is `iG_eta`; after canonical multiplication
> by `-i`, centered interval input is `-iT_phys` and exact one-sided coordinate is
> `eta=-i lambda/2`.  Correct normalized source flux is real and is not forced to vanish.  Scalar
> jump-Herglotz conjecture remains open.  See
> `suzuki-one-sided-coordinate-phase-normalization.md`.

For real Suzuki characteristic slopes, purely imaginary centered shifts, and purely imaginary
zero-frequency physical right-triangle values, exact two-shift algebra gives

```text
Re Phi_(alpha,beta)=0.
```

The unconditional central curvature law then gives

```text
Re Res_0 m_ext=-XiC''(0)/XiC(0)>0.
```

Since a scalar Herglotz function has nonpositive real residue at a real pole, this proves only
that mixed quotient cannot be Herglotz.  It is a coordinate falsifier, not source-phase no-go.

Define the centered Euler observable

```text
J[f](z)=z*(z*f'(z)-f(z)).
```

Lean proves, for every meromorphic germ of negative integral order `n`,

```text
ord_0 E[f]=n,
ord_0 J[f]=n+1,
z != 0 -> ord_z J[f]=n-1,
J[f+c*z]=J[f].
```

Thus a simple central pole becomes removable, linear endpoint escape is killed, and every
hypothetical nonreal Xi pole remains an exact double pole.  Because `z` is an analytic unit on
upper half-plane, one independently analytic source germ for `J[m_ext]` reduces to the existing
Euler-defect germ weld and proves RH.

## Formalization

Module:
`formal/GaloisForLFunctions/RHTower/SuzukiCarlemanJumpPhaseObstruction.lean`.

Key declarations:

```text
meromorphicOrderAt_suzukiEulerDefect_zero_eq
meromorphicOrderAt_suzukiCenteredEulerDefect_zero_eq_add_one
meromorphicOrderAt_suzukiCenteredEulerDefect_eq_sub_one
suzukiCenteredEulerDefect_add_linear
suzukiMixedCoordinateCentralSourceFlux_re_eq_zero_of_real_pureImag
suzukiMixedCoordinateCentralResidue_re_pos_of_real_pureImag
not_suzukiMixedCoordinateExteriorWeylQuotient_herglotz_of_real_pureImag_source
riemannHypothesis_of_suzukiAffineSewnExteriorWeylCenteredEulerDefect_source_germ_weld
```

Formal phase theorem takes real/pure-imaginary data in the mixed coordinate.  It must not be
instantiated as actual source sheet without `-i` triangle rephasing.  Centered Euler theorems and
prime--Gamma analytic-germ task remain valid independently.

## Gates

- [x] paper phase calculation exposed mixed-coordinate contradiction
- [x] scalar source Herglotz contradiction retracted
- [x] strongest positive survivor extracted
- [x] unconditional Lean theorem batch
- [x] direct leaf check
- [x] physical-to-normalized source phase formalized in `SuzukiCarlemanCoordinatePhase`
- [ ] analytic prime--Gamma germ `D_src=J[m_ext]`
- [ ] RH
