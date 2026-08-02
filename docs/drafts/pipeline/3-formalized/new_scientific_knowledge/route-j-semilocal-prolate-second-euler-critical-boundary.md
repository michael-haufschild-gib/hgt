# Route J semilocal prolate second-Euler critical boundary

**Status:** `[PAPER+LEAN-PROVED]`
`[CANDIDATE SOURCE-SPECIFIC NEW SCIENTIFIC KNOWLEDGE]`

## Exact statement

Let

```text
c_n = 4^(-n) binom(2n,n),
alpha_n = (-1)^n c_n,
t_n = 2 sqrt(2) alpha_n,
r_n = sqrt((n+1/2)(n+1)).
```

For the positive one-prime semilocal Jacobi radius write

```text
a_n(q) = r_n + u_n q + v_n q^2 + O(q^3).
```

For the four-radius Route-J critical residual put

```text
R_k(q)
  = a_(2k)(q)a_(2k+1)(q) - a_(2k+1)(q)^2
    - a_(2k+2)(q)^2 + a_(2k+2)(q)a_(2k+3)(q),
K_k = [q^2]R_k(q).
```

Then

```text
K_(n+1) / (2(n+1)) -> -32/pi.                         (1)
```

Together with the first-Euler law

```text
[q]R_(n+1)(q) / sqrt(2(n+1)) -> 4 sqrt(2/pi),
```

equation (1) proves that both first and second Euler corrections become order one on

```text
q sqrt(n) asymp 1,    q^2 n asymp 1,
n asymp p^2 for q=p^(-1).                              (2)
```

This is an order-two theorem. It makes no all-orders or resummation claim.

## Published input and novelty boundary

Connes--Consani--Moscovici give the one-prime `q^2` squared-radius coefficient. In source
normalization its non-archimedean bracket is

```text
E_n
 = n+1-Y_n/2
   - ((2n+1)/(2n+2))(n-1+Y_n/2),                       (3)
Y_n = {}_2F_1(1,n+1/2;n+1;-1).
```

Their squared-radius formula and already published first anomaly are inputs. New result is exact
propagation through positive square root and then Route-J four-radius critical weld, including
sharp constant in (1).

## Alternating-tail realization

Euler's integral and central-binomial expansion identify `Y_n` with normalized conditionally
convergent tail

```text
T_n = sum_(j>=0) (-1)^j c_(n+j),
Y_n = T_n/c_n.                                         (4)
```

Define `T_n` as actual limit of finite alternating partial sums. Since `c_n` is positive,
decreasing, and tends to zero, alternating convergence gives existence. Shifting finite partial
sums and passing to unique limits gives

```text
T_n+T_(n+1)=c_n.                                       (5)
```

Put `d_n=c_n-c_(n+1)`. Central-binomial ratio gives

```text
c_(n+1)/c_n=(2n+1)/(2n+2),
d_n=c_n/(2n+2).                                        (6)
```

Sequence `d_n` is positive, decreasing, and tends to zero. Applying alternating-series remainder
inequalities to

```text
T_n-T_(n+1)=sum_(j>=0)(-1)^j d_(n+j)
```

yields

```text
0 <= T_n-T_(n+1) <= d_n.                               (7)
```

Solving (5) and (7), then dividing by `c_n>0`, proves sharp source-normalized bound

```text
1/2 <= Y_n <= 1/2 + 1/(4n+4),                          (8)
Y_n -> 1/2.                                            (9)
```

## Exact second-radius cancellation

Using `(2n+1)/(2n+2)=1-1/(2n+2)`, published bracket (3) rewrites exactly as

```text
E_n
 = 2-Y_n + (n-1+Y_n/2)/(2n+2),                        (10)
E_n -> 2.                                              (11)
```

Published relative coefficient is `t_n^2 E_n`. Since Wallis' law gives

```text
(n+1)c_n^2 -> 1/pi,    t_n^2=8c_n^2,
```

and `r_n/(n+1)->1`, absolute squared-radius coefficient `W_n=[q^2]a_n(q)^2` satisfies

```text
W_n/(n+1) -> 16/pi.                                   (12)
```

Source-forced first radius jet obeys

```text
u_n^2/(n+1) -> 8/pi.                                  (13)
```

Positive-square-root comparison

```text
a_n(q)^2
 = r_n^2 + 2r_nu_n q + (u_n^2+2r_nv_n)q^2 + O(q^3)
```

therefore gives

```text
v_n=(W_n-u_n^2)/(2r_n) -> 4/pi.                       (14)
```

## Four-radius weld

Set `m=2k`. Expanding critical residual to second order splits it into term linear in `v` and
term quadratic in `u`:

```text
K_k = L_k+Q_k,                                         (15)

L_k =
 v_m r_(m+1)+r_m v_(m+1)-2r_(m+1)v_(m+1)
 -2r_(m+2)v_(m+2)+v_(m+2)r_(m+3)+r_(m+2)v_(m+3),

Q_k =
 u_m u_(m+1)-u_(m+1)^2-u_(m+2)^2+u_(m+2)u_(m+3).
```

For each fixed shift `j`,

```text
r_(m+j)/m -> 1,    v_(m+j) -> 4/pi.
```

Thus six normalized linear contributions cancel:

```text
L_(n+1)/(2(n+1))
  -> (4/pi)(1+1-2-2+1+1)=0.                           (16)
```

First jets alternate with positive amplitude

```text
u_n=(-1)^(n+1)U_n,
U_n/sqrt(n+1) -> A=2sqrt(2)/sqrt(pi),
A^2=8/pi.                                              (17)
```

At even quartet in (15), both cross-products are negative and both squares already carry minus
sign. Consequently

```text
Q_(n+1)/(2(n+1))
  -> -A^2-A^2-A^2-A^2
   = -32/pi.                                           (18)
```

Equations (15), (16), and (18) prove (1).

## Hostile audit

1. **Published pieces are not relabelled as novelty.**  
   Source paper already contains `q^2` anomaly and squared-Jacobi-radius formulas. Equation (3)
   and input defining `W_n` are provenance, not new claims.

2. **Hypergeometric limit is not numerical evidence.**  
   Tail is constructed as genuine conditionally convergent limit. Recurrence, forward drop,
   sharp bound (8), and limit (9) are unconditional.

3. **Critical constant is not read off from anomaly.**  
   Positive-square-root transport contributes subtraction `W_n-u_n^2`; four-radius linear terms
   then cancel, while four alternating first-jet products survive. Omitting either mechanism gives
   wrong coefficient.

4. **No all-orders inference.**  
   Two matching boundary exponents motivate fixed-order law `[q^r]R_n=O(n^(r/2))`, but do not
   prove it. `q^3` coefficient and boundary-layer resummation remain open.

5. **No global-source overclaim.**  
   Fixed-prime result is zero in global source-clock quotient. Complete Boolean shell theorem in
   `source-horizon-riemann-divisor/main.tex` says every ordinary differential-field observable has
   finite shell support and arbitrary field intersections contain no infinitary ghost. Global
   Route-J carrier must be genuine pro-limit, relation-valued object, or topology-singular relative
   to canonical local norms.

6. **No self-adjoint extension selected.**  
   Equation (1) identifies source-forced local boundary layer. It does not choose either
   positive-parameter prolate parity boundary angle or prove a Sonin-corner resolvent limit.

## Novelty audit

Primary-source comparison checked Connes--Consani--Moscovici, arXiv:2310.18423 and
arXiv:2403.01247. Latter contains one-prime moment, determinant, Jacobi, and anomaly coefficients
through relevant orders. Searched sources contain no Route-J four-radius `q^2` weld, no
cancellation (16), and no `-32/pi` law. Verdict:

```text
[NOVELTY PLAUSIBLE -- PRIMARY-SOURCE SEARCH NOT EXHAUSTIVE]
```

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  SemilocalProlateSecondEulerCriticalJet.lean
```

Umbrella:

```text
formal/GaloisForLFunctions/RHTower.lean
```

Key theorem map:

```text
centralBinomAlternatingTail
tendsto_centralBinomAlternatingPartialSums
centralBinomAlternatingTail_add_succ
centralBinomAlternatingTail_sub_succ_bounds
semilocalHypergeometricTail_bounds
tendsto_semilocalHypergeometricTail
publishedSecondSquaredRadiusBracket_eq
tendsto_secondSquaredRadiusBracket
tendsto_squaredJacobiRadiusSecondCoefficient_div_succ
tendsto_jacobiRadiusJet_sq_div_succ
tendsto_jacobiRadiusSecondCoefficient
tendsto_criticalResidualSecondLinearCoefficient_div_boundary
positiveEulerBoundaryAmplitude_sq
tendsto_criticalResidualFirstJetQuadraticCoefficient_div_boundary
tendsto_criticalResidualSecondCoefficient_div_boundary
```

Direct `lake env lean` validation and exact-target module build pass. `#print axioms` on capstones
reports only `propext`, `Classical.choice`, and `Quot.sound`; no project axioms, `sorry`, `admit`,
`opaque`, `unsafe`, or computation-based proofs.
