# Suzuki valuation-depth light coercivity law

- **Stage:** 1 — in progress
- **Type:** exact all-depth source law
- **Parent:** `../2-fully-proven/new_scientific_knowledge/suzuki-aperture-dressed-wall-light-completion.md`
- **RH used:** no
- **Computation used:** no

## Frontier

The forced negative FE light amplitude can vanish at one prime-power depth and one height.  The
live Suzuki transfer needs a uniformly available negative-light channel after valuation-depth
completion.  Finite-packet positivity and all-prime square summability do not decide whether
depthwise phase holes survive.

## Conjecture and falsifier

For `0 < R < 1`, define the normalized negative-light depth energy

```text
E_R(theta)=sum_(m>=1) R^(m-1) (1-sin(m theta)).
```

Conjecture:

```text
E_R(theta)
 =1/(1-R)-sin(theta)/(1-2R cos(theta)+R^2)
 >=R/(1-R^2),                                           (1)
```

with equality exactly at

```text
cos(theta)=2R/(1+R^2),
sin(theta)=(1-R^2)/(1+R^2).                             (2)
```

The positive-light series obtained by replacing `theta` with `-theta` has the same sharp floor.
For Suzuki's actual aperture-dressed wall field,

```text
R=p^(-1/2) r^4,  r=xiMobiusContinuousApertureDiskNode((h/2)a,p),
```

so `(1)` would prove that summing all valuation depths removes every light-cone phase hole before
the restricted-Weil/Robin transfer.

Falsifiers:

1. failure of the exact geometric-sine sum;
2. a phase below the proposed floor;
3. mismatch between actual squared depth ratio and `p^(-1/2)r^4`;
4. an RH, zero-location, or target-curvature premise entering the proof.

## Status

Paper derivation in progress.  No claim about the unresolved restricted-Weil transfer or RH.
