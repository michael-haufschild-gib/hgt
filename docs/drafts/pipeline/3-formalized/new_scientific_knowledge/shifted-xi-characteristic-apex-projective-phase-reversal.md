# Shifted-Xi characteristic-apex projective phase reversal

- **ID:** `shifted-xi-characteristic-apex-projective-phase-reversal`
- **Stage:** 3-formalized
- **Route:** U
- **Type:** THEOREM + NO-GO + POSITIVE SURVIVOR
- **Status:** `[LEAN-FORMALIZED] [UMBRELLA-WIRED] [CORPUS-NOVEL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Depends on:** characteristic-apex transport, finite orthogonal no-common-root, reciprocal-mass
  gauge equivalence, and fixed-degree shifted-Chebyshev recession.

## Exact claim

For shifted-Xi moments at mass `y>0`, write

```text
A_n(y) = P_n(y,1/y),
R_n(y) = A_n(y)/A_(n+1)(y),
alpha_n(y) = nth monic Jacobi diagonal,
beta_n(y) = nth monic Jacobi lower coefficient.
```

Whenever the degree-`n+1` denominator is nonzero in a positive block through degree `n+2`,

```text
R_n' = -2n
       + ((2n+1)/y-(2n-1)alpha_n) R_n
       - 2(n+1)beta_(n+1) R_n^2.                       (PAR.1)
```

Equivalently, the oriented projective Wronskian is

```text
A_(n+1) A_n' - A_n A_(n+1)'
 = -2n A_(n+1)^2
   + ((2n+1)/y-(2n-1)alpha_n) A_n A_(n+1)
   - 2(n+1)beta_(n+1) A_n^2.                           (PAR.2)
```

For every fixed `n>0`, on the square-mass ray `y=w^2`,

```text
R_n(w^2)/w^2 -> 4,
deriv R_n(w^2) -> 4.                                   (PAR.3)
```

At every positive-degree contact `A_n(y)=0`, the already formalized law is instead

```text
R_n'(y)=-2n<0.                                          (PAR.4)
```

Thus no globally decreasing lifted projective phase can be extracted from `R_n` by treating its
adjacent-degree poles as mere chart singularities. The actual shifted-Xi trajectory is eventually
strictly forward in the far-right chamber and strictly backward at every numerator contact.

## Paper proof

Put `a_n` for the first subleading coefficient of `P_n`. Characteristic transport gives

```text
A_n'=(a_n+n/y-2n alpha_n)A_n-2n A_(n+1),               (PAR.5)
A_(n+1)'=(a_(n+1)+(n+1)/y-2(n+1)alpha_(n+1))A_(n+1)
          -2(n+1)A_(n+2).                              (PAR.6)
```

The three-term recurrence at `1/y` and first-coefficient recurrence are

```text
A_(n+2)=(1/y-alpha_(n+1))A_(n+1)-beta_(n+1)A_n,
a_(n+1)=a_n-alpha_n.                                   (PAR.7)
```

Apply the quotient rule to `R_n=A_n/A_(n+1)` and substitute (PAR.5)--(PAR.7). The coefficient of
`R_n` reduces exactly to

```text
(a_n-a_(n+1))-1/y-2n alpha_n+2(n+1)alpha_(n+1)
  +2(n+1)(1/y-alpha_(n+1))
= (2n+1)/y-(2n-1)alpha_n,
```

proving (PAR.1). Multiplication by `A_(n+1)^2` gives (PAR.2).

For recession, normalized admission is

```text
Q_n(w,z)=w^(2n) P_n(w^2,z/w^2).
```

Hence, inside the eventual positive chamber,

```text
R_n(w^2)/w^2 = Q_n(w,1)/Q_(n+1)(w,1).                  (PAR.8)
```

Coefficientwise shifted-Xi recession gives `Q_n(w) -> Arc.amplitude_n`. Since
`Arc.amplitude_n(1)=Arc.monicScale_n` and
`Arc.monicScale_(n+1)=Arc.monicScale_n/4`, (PAR.8) tends to `4`. The normalized recurrence
coefficients satisfy

```text
w^2 alpha_n(w^2) -> 1/2,
w^4 beta_(n+1)(w^2) -> 1/16.                            (PAR.9)
```

Substitute `R_n=w^2 r_n`, (PAR.8), and (PAR.9) into (PAR.1):

```text
R_n' = -2n
       + ((2n+1)-(2n-1)w^2 alpha_n)r_n
       - 2(n+1)w^4 beta_(n+1)r_n^2

    -> -2n + ((2n+1)-(2n-1)/2)4 - 2(n+1)(1/16)16
     = 4.
```

The denominator is eventually nonzero because its normalized value tends to the strictly positive
`Arc.monicScale_(n+1)`. This closes (PAR.3). Equation (PAR.4) is the contact specialization of
(PAR.1), using adjacent-degree no-common-root.

## Hostile falsity audit and stronger survivor

1. **Conjecture:** universal contact slope extends to `R_n'<0` throughout each projective chart.
   **Verdict:** `[FALSIFIED]`. The literal shifted-Xi far-right trajectory has derivative tending
   to `4>0`.
2. **Exact why:** projective derivative is a quadratic form, not its negative constant term. Put

   ```text
   B_n=(2n+1)/y-(2n-1)alpha_n.
   ```

   Its discriminant is `B_n^2-16n(n+1)beta_(n+1)`. Under normalized arcsine recession it tends,
   after multiplication by `y^2`, to

   ```text
   (2n+3)^2/4-n(n+1)=2n+9/4>0.
   ```

   The phase form is asymptotically indefinite; positivity cannot make it globally negative.
3. **Stronger positive survivor:** `[LEAN-FORMALIZED]` the exact Riccati law and source-specific
   reversal (PAR.1)--(PAR.4). They classify the failure and show that any successful global phase
   invariant must renormalize or charge turning sectors, not merely compactify poles.

## Higher principle and revised open core

Contact orientation is a boundary value of a nonisospectral projective connection. The negative
constant term is visible only at the numerator divisor; away from it, Jacobi connection and next
edge generate an indefinite quadratic phase field. Far-right shifted-Chebyshev recession selects
the forward sector of that field. Local contacts and infinity therefore have opposite orientation.

`[OPEN CORE]`: construct a source-specific signed action that charges every transition between the
far-right forward sector and a backward numerator contact, then compare its cumulative charge with
the existing arithmetic-source/hyperbolic-reset budget on a cofinal parabolic frontier. A monotone
ratio, generic interlacing argument, or pole compactification alone is now ruled out.

## Literature audit

- Tsujimoto--Zhedanov, [Toda--Schrodinger correspondence and orthogonal
  polynomials](https://arxiv.org/abs/1404.2012), relates Toda evolution to Riccati equations for
  orthogonal-polynomial Stieltjes functions.
- Yue--Chang--Hu, [Stationary reduction based on nonisospectral deformation of orthogonal
  polynomials](https://arxiv.org/abs/2407.09875), develops nonisospectral OP flows and Lax systems.
- Delvaux--Dette, [Zeros and ratio asymptotics for matrix orthogonal
  polynomials](https://arxiv.org/abs/1108.5155), treats ratio/zero asymptotics under recurrence
  coefficient hypotheses.

These parent theories explain Riccati and ratio mechanisms. None of the inspected primary sources
states (PAR.1) for the completed-Xi moving characteristic apex, the opposite contact/far-right
orientations, or the exact limiting slope `4`. External priority remains unverified pending expert
review.

## Lean formalization

Module:

```text
formal/GaloisForLFunctions/RHTower/
XiShiftedCanonicalAdmissionCharacteristicApexProjectivePhaseReversal.lean
```

Lean proves the pole-free Wronskian identity (PAR.2), chart Riccati law (PAR.1), exact
source-coordinate gauge, fixed-degree ratio recession, coefficient recession, derivative limit
and eventual positive derivative. It also defines the Riccati discriminant and proves

```text
w^4 D_n(w^2) -> 2n+9/4
eventually 0 < D_n(w^2).
```

The module is imported by `GaloisForLFunctions.RHTower`. Direct `lake env lean` and targeted
`lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexProjectivePhaseReversal`
both pass; the targeted build completes `12013/12013` jobs. All 13 public theorem audits depend
only on `[propext, Classical.choice, Quot.sound]`. Forbidden-declaration scan is clean. Global
lint reaches this module through the umbrella; its only errors are unrelated unwired modules
elsewhere in the dirty worktree.

