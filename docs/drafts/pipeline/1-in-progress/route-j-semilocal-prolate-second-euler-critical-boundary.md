# Route J semilocal prolate second-Euler critical boundary

**Status:** `[ACTIVE FRONTIER] [CONJECTURE UNDER HOSTILE ATTACK]`

## Target

Let `a_n(q)` be the positive one-prime semilocal Jacobi radius and

```text
R_k(q)
  = a_(2k)(q)a_(2k+1)(q) - a_(2k+1)(q)^2
    - a_(2k+2)(q)^2 + a_(2k+2)(q)a_(2k+3)(q).
```

Write

```text
a_n(q)=r_n+u_n q+v_n q^2+O(q^3),
K_k=[q^2]R_k(q).
```

Active conjecture:

```text
K_(n+1)/(2(n+1)) -> -32/pi.                            (C1)
```

## Published source input

Set

```text
alpha_n=(-4)^(-n)binom(2n,n),
t_n=2sqrt(2)alpha_n,
r_n=sqrt((n+1/2)(n+1)),
Y_n={}_2F_1(1,n+1/2;n+1;-1).
```

Connes--Consani--Moscovici prove the first two squared-radius coefficients. After reducing their
parity sums and using

```text
t_(n+1)=-((2n+1)/(2n+2))t_n,
```

the relative `q^2` coefficient becomes

```text
w_n
 = t_n^2[
     n+1-Y_n/2
     - ((2n+1)/(2n+2))(n-1+Y_n/2)
   ].                                                   (C2)
```

Euler's integral gives the normalized alternating-tail representation

```text
Y_n
 = (alpha_n+alpha_(n+1)+alpha_(n+2)+...)/alpha_n.
```

The alternating central-binomial ratio then gives the sharp elementary bound

```text
1/2 <= Y_n <= 1/2 + 1/(4n+4),                          (C3)
```

so `Y_n->1/2`. Equations `(C2)--(C3)` imply

```text
w_n/t_n^2 -> 2,
[q^2]a_n(q)^2 / n -> 16/pi.                            (C4)
```

The first radius coefficient satisfies

```text
u_n^2/n -> 8/pi.
```

Since

```text
v_n=([q^2]a_n(q)^2-u_n^2)/(2r_n),
```

one obtains

```text
v_n -> 4/pi.                                           (C5)
```

## Predicted critical coefficient

Expanding the four-radius residual,

```text
K_k =
  v_m r_(m+1)+u_m u_(m+1)+r_m v_(m+1)
  -(u_(m+1)^2+2r_(m+1)v_(m+1))
  -(u_(m+2)^2+2r_(m+2)v_(m+2))
  +v_(m+2)r_(m+3)+u_(m+2)u_(m+3)+r_(m+2)v_(m+3),
m=2k.                                                   (C6)
```

The six terms linear in `v` cancel after division by `m`, using `(C5)` and `r_(m+j)/m->1`.
The first jets alternate:

```text
u_(2j)<0, u_(2j+1)>0,
|u_n|/sqrt(n)->2sqrt(2/pi).
```

Thus the four quadratic terms in `(C6)` each contribute `-8/pi`, giving `(C1)`.

## Hostile checks

1. The published `q^2` anomaly coefficient is not itself new.
2. The cancellation `(C2)` must be proved from the literal published parity formula, not posited.
3. The hypergeometric limit must be proved from the alternating central-binomial tail; numerical
   evidence is inadmissible.
4. `K_n~-(32/pi)n` still does not prove all-orders uniformity or resummation.
5. Fixed-prime data remain zero in the global prime-clock quotient. Complete shell finite-support
   rigidity forbids turning `(C1)` into a global current by ordinary field completion.

## Lean target

```text
formal/GaloisForLFunctions/RHTower/
  SemilocalProlateSecondEulerCriticalJet.lean
```

Required capstones:

```text
tendsto_semilocalHypergeometricTail
tendsto_squaredJacobiRadiusSecondCoefficient_div
tendsto_jacobiRadiusSecondCoefficient
tendsto_criticalResidualSecondCoefficient_div_boundary
```

No assumptions, computations, `sorry`, `admit`, project axioms, opaque constants, or unsafe
declarations.
