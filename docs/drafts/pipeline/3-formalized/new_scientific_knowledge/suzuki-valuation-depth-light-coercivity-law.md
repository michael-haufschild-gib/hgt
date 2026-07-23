# Suzuki valuation-depth light coercivity law

- **Stage:** 3 — formalized
- **Type:** universal sharp frame law / exact all-depth Suzuki source law
- **Parent:** `../2-fully-proven/new_scientific_knowledge/suzuki-aperture-dressed-wall-light-completion.md`
- **RH used:** no
- **Computation used:** no

## Result

For `0 ≤ R < 1`, define

```text
E_-(R,theta)=sum_(e>=0) R^e(1-sin((e+1)theta)),
E_+(R,theta)=sum_(e>=0) R^e(1+sin((e+1)theta)).
```

Both series have exact resolvent forms

```text
E_-(R,theta)=1/(1-R)-sin(theta)/(1-2R cos(theta)+R^2),
E_+(R,theta)=E_-(R,-theta).
```

The sharp two-sided universal frame law is

```text
R/(1-R^2) <= E_±(R,theta) <= (R+2)/(1-R^2),             (1)
E_-(R,theta)+E_+(R,theta)=2/(1-R).                       (2)
```

The lower equality for `E_-` holds exactly at

```text
cos(theta)=2R/(1+R^2),
sin(theta)=(1-R^2)/(1+R^2),                              (3)
```

and such a phase exists for every `R` in the range.  Hence one geometric-orbit coordinate can
have zero light energy, but its complete contractive orbit is uniformly coercive in both Lorentz
light directions.  Constant in `(1)` is optimal.

## Paper proof

Geometric-series summation gives the displayed resolvent formula.  Put

```text
D=1-2R cos(theta)+R^2.
```

Then

```text
E_-(R,theta)-R/(1-R^2)
 =[1+R^2-2R cos(theta)-(1-R^2)sin(theta)]/[(1-R^2)D].
```

Denominator is positive.  Numerator is nonnegative by exact two-square identity

```text
(2R-(1+R^2)cos(theta))^2
+((1-R^2)-(1+R^2)sin(theta))^2
=2(1+R^2)[1+R^2-2R cos(theta)-(1-R^2)sin(theta)].
```

This also gives equality classification.  The point in `(3)` lies on unit circle; choosing its
arccosine proves attainment.  Replacing `theta` by `-theta` proves positive-light floor.
Equation `(2)` then gives sharp ceilings.

## Actual Suzuki connector

For Suzuki aperture-dressed wall source, let

```text
r_p=xiMobiusContinuousApertureDiskNode((h/2)a,p),
R_p=p^(-1/2) r_p^4.
```

Lean proves this is exactly squared norm of actual Gamma/innovation depth ratio:

```text
normSq(suzukiCriticalApertureDepthRatio h a t p)=R_p.
```

Writing `A_p` for positive calibrated depth-zero endpoint amplitude, actual all-depth light
energies satisfy

```text
L_±(h,a,t,p)=A_p^2/2 * E_±(R_p,t log p),                 (4)
L_-(h,a,t,p)+L_+(h,a,t,p)=A_p^2/(1-R_p).                (5)
```

Both actual channels are strictly positive for every `h,a>0`, every real height, and every prime.
For each prime one height attains negative-channel floor exactly.

## Scientific verdict

This closes one real source obstruction: valuation-depth phase holes do not survive.  It does not
prove RH and does not construct missing restricted-Weil/Robin/Gamma/holonomy intertwiner.
The theorem supplies primewise coercivity; no global source-to-trace lower frame is claimed.
Therefore it cannot be used as terminal Suzuki verdict.

## Lean

- `formal/GaloisForLFunctions/HTGeometry/GeometricPhaseLightCoercivity.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiValuationDepthLightCoercivity.lean`

Direct checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/GeometricPhaseLightCoercivity.lean
lake env lean GaloisForLFunctions/RHTower/SuzukiValuationDepthLightCoercivity.lean
```
