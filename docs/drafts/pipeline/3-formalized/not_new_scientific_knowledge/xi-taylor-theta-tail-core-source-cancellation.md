# Xi Taylor theta-tail core source cancellation

- **ID:** `xi-taylor-theta-tail-core-source-cancellation`
- **Stage:** 3-formalized
- **Type:** EXACT FINITE SOURCE IDENTITY / REDUCTION
- **Scientific status:** `[BRIDGE] [NOT A PRODUCER]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCoreCancellation.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedSource.lean`
- **Parent target:**
  `../../1-in-progress/xi-taylor-theta-tail-core-density-current.md`

## Statement

For

```text
rho(x)=4T''(x),
S_d(z,x)=sum_(k=0)^d (-1)^k z^(2k)x^(2k+2)/(2k+2)!,
C_d(z,x)=sum_(k=0)^d (-1)^k(zx)^(2k)/(2k)!,
H_d(z,x)=1-(z^2+1/4)S_d(z,x),
```

the finite sections satisfy

```text
partial_x^2 S_d(z,x)=C_d(z,x),
partial_x^2 H_d(z,x)=-(z^2+1/4)C_d(z,x),                 (1)

integral rho(x)H_d(z,x)dx
 =1-4(z^2+1/4)integral T(x)C_d(z,x)dx.                  (2)
```

Writing `D_d=partial_z H_d`, the oriented core current has the exact mixed form

```text
J_(U_d)(z)
 =(1/4)integral Im(rho(x)D_d(z,x))dx
  -integral integral rho(x)T(y)
     Im(D_d(z,x)conjugate((z^2+1/4)C_d(z,y)))dxdy.       (3)
```

The finite sections also obey the completion identity

```text
z^2S_d(z,x)=1-C_(d+1)(z,x),
z^2H_d(z,x)=(z^2+1/4)C_(d+1)(z,x)-1/4.                  (4)
```

Finally, for every complex polynomial `P`,

```text
J_(z^2P)(z)
 =|z|^4 J_P(z)-2|z|^2 Im(z)|P(z)|^2.                    (5)
```

The exact canonical density also splits as

```text
rho(x)=T(x)+4 Phi(x),
Phi(x)=T''(x)-(1/4)T(x),                                  (6)
```

with `Phi` the completed even theta-cusp source.

The finite completed-source transform is exactly the canonical Taylor section:

```text
2 integral Phi(x)C_d(z,x)dx=P_(2d+1)(z),

z^2[2 integral Phi(x)H_d(z,x)dx]
 =(z^2+1/4)P_(2(d+1)+1)(z)-(1/4)P_1(0).                 (7)
```

At the upper completion boundary the raw seam is strictly favorable:

```text
U_d(i/2)=1/2,
J_(U_d)(i/2)=-(1/2)A_d(1/4)<0,                          (8)
```

where every coefficient of the raw tail polynomial `A_d` is strictly positive.

For any complex polynomial `P`, the current is also the vertical value derivative

```text
d/dy |P(x+iy)|^2=-2J_P(x+iy).                            (9)
```

## Scope

Equations `(1)`--`(9)` retain the boundary seam and separate the completion radial cost from the
cosine correlation.  Equation `(7)` proves that the completed-source channel is a feedback copy of
the unknown Taylor section, so treating it as an independently positive correction is circular.
Equation `(8)` signs the completion boundary but not the open strip.  The remaining producer is
exactly the raw `T` mixed correlation plus seam in `(3)`.  Therefore this package is a formalized
reduction, not the sublinear-current producer and not an RH proof.

## Verification

- Targeted module build passes.
- Formal lint passes with no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- The principal declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
