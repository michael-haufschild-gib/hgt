# CCM unit-Riesz / completed-source Stieltjes weld

- **ID:** `ccm-unit-riesz-completed-source-stieltjes-weld`
- **Stage:** `2-fully-proven/new_scientific_knowledge`
- **Type:** EXACT SOURCE WELD / ROUTE COLLAPSE / PRODUCER REORIENTATION
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`
- **Routes:** `CCM-UR`, `CCM-FU`, with source interfaces to `G`, `HG`, `GS`, `EP`
- **Parents:** `ccm-unit-riesz-markov-virial-landau-law`,
  `ccm-fu-third-grade-cesaro-completeness`, `CriticalMellinFourCoordinateCollapseUniversalityLaw`

## Public claim

The unit-Riesz causal-complement coefficient is not a separate Möbius source after completion.
It is a positive two-exponential aperture smoothing of the literal completed critical-Mellin
Euler--Gamma Stieltjes current, plus one completely explicit source-free correction.  That
correction is strictly negative and exponentially smaller than the half-unit RH scale.

Consequently the open all-epsilon one-sided CCM-UR estimate is **equivalent**, with no loss of
exponent, to the same estimate for a positive smoothing of the completed prime-minus-polar current
used by CCM-FU.  Möbius floor algebra is one presentation of the source, not the surviving
producer coordinate.

This does not prove the estimate or RH.  It removes a false route distinction and relocates the
hard theorem to the common signed completed source before divisor continuation.

## 1. Literal completed Stieltjes current

For `t >= 0`, put

```text
E(t) = 4 sinh(t/2) - sum_(n <= exp t) Lambda(n)/sqrt(n).               (1)
```

This is locally of bounded variation and `E(0)=0`.  Its distributional Stieltjes derivative is

```text
dE(t) = 2 cosh(t/2) dt
        - sum_(n >= 2) Lambda(n)/sqrt(n) delta_(log n).                (2)
```

Define the critically weighted completed current

```text
dnu(t) = exp(-t/2) dE(t)
        = (1 + exp(-t)) dt
          - sum_(n >= 2) Lambda(n)/n delta_(log n).                    (3)
```

For `Re z > 0`, its Laplace transform is therefore

```text
R(z) = L[dnu](z)
     = 1/z + 1/(z+1) + zeta'(1+z)/zeta(1+z).                          (4)
```

This is exactly the corpus's continued critical-Mellin defect on its convergent half-plane.

## 2. Unit-Riesz transform and exact algebraic split

The proved unit-Riesz coefficient transform is

```text
C(z) = alpha(z) [ zeta(1+z)/(1+z)^2
                  + zeta'(1+z)/zeta(1+z) ],                           (5)

alpha(z) = 3/[2(z+1)(z+3/2)].                                        (6)
```

Subtracting `(4)` from the bracket gives the exact identity

```text
C(z) = alpha(z) R(z) + alpha(z) A(z),                                 (7)

A(z) = zeta(1+z)/(1+z)^2 - 1/z - 1/(z+1).                            (8)
```

The apparent singularity of `A` at zero is removable.  If

```text
G(z) = regularizedRiemannZeta(1+z)/(1+z)^2,
```

then `G(0)=1` and the pole-filled continuation is

```text
A_filled(z) = dslope G 0 z - 1/(z+1).                                (9)
```

Thus `A_filled` is analytic on `Re z > -1/2`; the only rational denominator there is `z+1`,
and divided differences preserve analyticity.  The multiplier `alpha` is analytic and zero-free
on the same half-plane.

Equation `(7)` is stronger than another common-germ observation because its second term has an
explicit causal inverse with a fixed sign.

## 3. Exact inverse Laplace correction

For `t >= 0`, let `N(t)=floor(exp t)` and define

```text
a(t) = exp(-t) [N(t)t - log(N(t)!)] - 1 - exp(-t).                    (10)
```

For `Re z > 0`, Tonelli/Fubini on the absolutely convergent positive head gives

```text
L[ exp(-t) sum_(n <= exp t) (t-log n) ](z)
  = sum_(n>=1) integral_(log n)^infinity
      exp(-(z+1)t)(t-log n) dt
  = zeta(1+z)/(1+z)^2.                                                (11)
```

Since the inverse transforms of `1/z` and `1/(z+1)` are `1` and `exp(-t)`, respectively,

```text
L[a](z)=A(z).                                                         (12)
```

The inverse transform of `alpha` is the positive kernel

```text
k(t)=3(exp(-t)-exp(-3t/2)) >= 0.                                     (13)
```

Hence the source-free correction in `(7)` is

```text
r(t)=(k*a)(t).                                                        (14)
```

## 4. New sign law for the correction

Write `x=exp t` and `N=floor x`.  Then `N <= x < N+1`, `N>=1`, and

```text
x a(t)=N log x-log(N!)-x-1.                                          (15)
```

For fixed `N`, the function `x |-> N log x-x` is nonincreasing on `[N,infinity)`.  The elementary
factorial lower bound

```text
log(N!) >= N log N-N+1                                               (16)
```

therefore gives

```text
x a(t)
 <= N log N-log(N!)-N-1
 <= -2.                                                              (17)
```

Thus

```text
a(t) <= -2 exp(-t) < 0.                                              (18)
```

For the opposite side, the right Riemann-sum comparison

```text
log(N!) <= (N+1)log(N+1)-N                                         (19)
```

and `N <= x < N+1 <= 2x`, together with
`N log((N+1)/x)<=1` and `log 2<=1`, give

```text
x a(t) >= -4-t.                                                       (20)
```

Combining `(18)` and `(20)`,

```text
-(t+4)exp(-t) <= a(t) <= -2exp(-t).                                  (21)
```

Since `k>=0`, equations `(14)` and `(21)` imply

```text
r(t) <= 0,                                                           (22)

|r(t)| <= 3 exp(-t) integral_0^t (t-s+4) ds
       = 3 exp(-t)(t^2/2+4t).                                       (23)
```

In particular, for every `epsilon>0`, there is `B_epsilon>=0` such that

```text
|r(t)| <= B_epsilon exp((-1/2+epsilon)t),  t>=0.                      (24)
```

No prime estimate enters `(18)--(24)`.

## 5. Time-domain completed-source weld

Define the completed-source unit-Riesz response by the Stieltjes convolution

```text
J(t) = integral_[0,t] k(t-s) dnu(s)
     = integral_[0,t]
         3[exp(-(t-s))-exp(-3(t-s)/2)] exp(-s/2) dE(s).               (25)
```

The locally finite signed measure in `(3)`, the exponential-order functions in `(10)` and `(13)`,
and the known polynomial bound for the unit-Riesz coefficient all have unique Laplace transforms
on a common right half-plane.  Equations `(4)`, `(7)`, `(12)`, and `(13)` therefore give

```text
I(t)=J(t)+r(t),                                                       (26)
```

where `I=d*V_h` is the existing unit-Riesz Markov--virial coefficient.  This is an identity of
locally integrable functions, hence pointwise at every continuity point and in the canonical
right-continuous representative used by the source construction.

Because `r<=0`,

```text
I(t) <= J(t).                                                         (27)
```

More importantly, `(24)` and `(26)` prove the exact producer equivalence

```text
for every epsilon>0,
  I(t) >= -C_epsilon exp((-1/2+epsilon)t) eventually

iff

for every epsilon>0,
  J(t) >= -C'_epsilon exp((-1/2+epsilon)t) eventually.                (28)
```

The reverse implication pays only the explicit negligible correction `(24)`; the forward
implication follows directly from `J=I-r>=I`.

## 6. Frontier consequence

The CCM-UR open core is no longer correctly described as requiring a uniquely Möbius
first-crossing mechanism.  Its exact surviving statement is the completed-current lower law in
`(28)`.  The same literal `E` and `dE` drive CCM-FU's third-grade cumulative source.  The two routes
use different reporters:

```text
CCM-FU: polynomially weighted cumulative/triangular smoothing of dE;
CCM-UR: positive translation-invariant two-exponential smoothing of exp(-t/2)dE.
```

Neither reporter estimate presently implies the other.  The new weld is therefore a route
collapse at the producer source, not an RH proof.  It directs subsequent work to a signed
completed-source inequality before Möbius, screw, Hankel, Pick, or ground-state scalarization.

For Route G, CCM-HG, CCM-GS, and CCM-EP, `(25)` supplies an exact comparison coordinate: any claimed
source-side positivity or boundary covariance must reproduce this signed completed-current
response, not merely the already-known common meromorphic divisor germ.

## 7. Hostile novelty and theatre audit

### Already known or already in corpus

- `[LITERATURE]` Möbius-convolution RH criteria and their Mellin transforms are classical; in
  particular Baez-Duarte's Möbius-convolution framework contains the generic smoothing mechanism.
- `[CORPUS]` The unit-Riesz Markov transform `(5)`, its noncensorship of zeta zeros, the completed
  critical-Mellin transform `(4)`, and the four-coordinate meromorphic collapse are already proved.
- `[ELEMENTARY]` Inverse Laplace transforms of rational factors and integral bounds for `log(N!)`
  are standard tools.

### Exact residue claimed here

The candidate new content is their **source-level composition**:

1. the explicit inverse correction `(10)`;
2. its strict global negative sign and two-sided exponential bound `(21)`;
3. the exact time-domain weld `(26)` to the literal completed Euler--Gamma Stieltjes current; and
4. the no-loss equivalence `(28)` of the two open producer formulations.

Targeted searches of the exact rational transform, Riesz/Möbius convolution criteria, Connes--
Consani source formulas, and current CCM literature found no statement of `(10)`, `(21)`, `(26)`,
or `(28)`.  This is not a priority proof.  Status remains `[NOVELTY UNVERIFIED]`.

### Circularity falsifiers

1. No zero list, zero-free continuation, or RH-equivalent positivity is used to derive `(26)`.
2. The prime source enters only through the literal locally finite Stieltjes current `(2)`.
3. The sign in `(21)` is source-free factorial geometry, not inferred from the desired bound.
4. Equation `(28)` does not assert either lower bound; it only proves they are the same open
   producer after an explicitly controlled correction.

Verdict: `SURVIVES PRELIMINARY ATTACK`; significant route reorientation, not RH closure.

## 8. Lean plan

Formalize a new unconditional leaf with:

- pole-filled unit-Riesz coefficient and exact factorization through
  `regularizedCriticalMellinDefect`;
- analyticity and zero-freeness of the multiplier on `Re z>-1/2`;
- analyticity of the divided-difference correction on that half-plane;
- equality with the existing coefficient formula on `Re z>0`;
- finite-floor correction `(10)` and its exact strict sign/bounds `(21)`;
- abstract positive-convolution sign and negligible-error lower-bound transfer used by `(28)`.

The measure-valued identity `(26)` may be formalized in a second leaf if current Bochner/Stieltjes
Laplace infrastructure cannot express it without importing unrelated measure theory.  No abstract
premise may be relabeled as the literal source weld.
