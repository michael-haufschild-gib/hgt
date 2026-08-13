# Shifted-Xi radial Christoffel apex pure-top flux

- **ID:** `shifted-xi-radial-christoffel-apex-pure-top-flux`
- **Stage:** 3-formalized
- **Route:** U
- **Type:** THEOREM
- **Scientific status:** `[PROVED HERE] [CORPUS-NOVEL] [EXTERNAL NOVELTY SEARCHED] [LEAN-PROVED]`
- **Lean status:** complete in
  `RHTower/XiShiftedCanonicalAdmissionCharacteristicApexChristoffelEnergy.lean`, umbrella-wired.
  Direct `lake env lean` passes. Targeted
  `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexChristoffelEnergy`
  completes and produces an importable object. Axiom audit of all 12 public theorems reports only
  `[propext, Classical.choice, Quot.sound]`. Targeted forbidden-token scan is clean. Repository lint
  reaches the module; its nonzero exit is caused by ten unrelated unwired modules listed in lint
  output, not this theorem.

## Frozen theorem

Put

```text
A_n(y) = P_n(y, 1/y),
N_n(y) = <P_n(y), P_n(y)>_y,
q_n(y) = A_n(y)^2 / N_n(y),
F_n(y) = 2 A_(n+1)(y) A_n(y) / N_n(y),
Q_N(y) = sum_(n=0)^N q_n(y).
```

On the finite shifted-Xi positive chamber through degree `N+1`, Lean proves

```text
q_0' = y^(-1) q_0 - (1/2) F_0,

q_n' = y^(-1) q_n
       + (n-1/2) F_(n-1) - (n+1/2) F_n       (n > 0),

Q_N' = y^(-1) Q_N - (N+1/2) F_N,

(Q_N/y)' = -((N+1/2)/y) F_N
           = -((2N+1)/y) A_(N+1) A_N / N_N.
```

It also proves the exact identification

```text
Q_N(y) = K_N(1/y, 1/y),
```

where `K_N` is the finite Christoffel--Darboux kernel for the shifted-Xi moment form, and proves
`Q_N(y) > 0`. The source-derived parabolic degree horizon discharges finite positivity whenever
`routeUParabolicDegreeHorizon * (N+2)^2 <= y`.

At a degree-`N` characteristic contact `A_N(y)=0`, the whole radial Christoffel energy is
stationary:

```text
(Q_N/y)' = 0.
```

## Proof

For `n>0`, combine the already formalized skew characteristic transport and norm flow:

```text
A_n' = (a_n-n alpha_n) A_n + n beta_n A_(n-1) - n A_(n+1),
N_n' = (2a_n-(2n+1)alpha_n) N_n.
```

Differentiating `q_n=A_n^2/N_n` cancels `a_n` and gives

```text
q_n' = alpha_n q_n + n F_(n-1) - n F_n.
```

Evaluate the finite Jacobi recurrence at the moving apex:

```text
y^(-1) A_n = A_(n+1) + alpha_n A_n + beta_n A_(n-1).
```

Using `N_(n-1) beta_n = N_n`, this rewrites the diagonal term exactly as

```text
alpha_n q_n = y^(-1) q_n - (1/2)F_(n-1) - (1/2)F_n.
```

Degree zero is proved separately, not hidden in a predecessor convention. Here `A_0=1`,
`N_0=s_0`, `s_0'=-s_1`, and the degree-zero recurrence gives
`alpha_0=y^(-1)-A_1`. Therefore

```text
q_0' = alpha_0 q_0 = y^(-1)q_0-(1/2)F_0.
```

Summing includes this degree-zero half-current. Every interior half-weighted edge cancels, as does
the apparent lower boundary. Dividing by `y` cancels the homogeneous radial term. No limit,
numerical certificate, computation, RH premise, or added axiom is used.

## Conjecture / failure / pivot ledger

1. **The earlier `A_n^2/(nN_n)` energy exposes the final global wall.** `[FAILED AS FINAL FORM]`
   It correctly telescopes raw skew transport, but leaves Jacobi bulk and a lower flux.
2. **Jacobi bulk is genuine source production.** `[FAILED]` Evaluated recurrence shows it is two
   half-edge currents plus homogeneous radial transport.
3. **Unweighted norm shells alone give a closed positive-degree sum.** `[FAILED]` Omitting degree
   zero leaves exactly half the bottom edge.
4. **Include degree zero, then use radial gauge `Q_N/y`.** `[PROVED HERE]` All bulk, interior, and
   bottom terms cancel; one top adjacent-degree product remains.

## Higher principle

The prior bulk and bottom obstructions were shadows of two missing completions:

1. **projection completion:** use the full Christoffel reproducing density, including the vacuum
   degree;
2. **radial gauge completion:** divide by the characteristic scale `y`.

Under the shifted moment flow, the completed diagonal projection density obeys a degree-space
continuity law. Its covariant derivative is a Noether-type current through the truncation edge.
The Jacobi diagonal is not a source; it is the connection term that converts ordinary derivative
to this covariant boundary law.

## Exact remaining obstruction

Route U no longer needs control of a bulk sum, a lower flux, or all diagonal Jacobi coefficients.
It needs orientation of one literal observable on the intrinsic parabolic schedule:

```text
A_N(y) A_(N+1)(y).
```

Generic positive-moment theory does not fix this sign: it records where `1/y` lies relative to
adjacent orthogonal-polynomial zeros. At contact the first-order radial energy derivative vanishes,
so this energy cannot by itself orient the crossing at the contact point. Next viable pivots are:

- prove a source-specific sign of the adjacent product immediately off the frontier;
- differentiate the pure top law once more and use already proved contact transversality;
- identify the top product with a signed first Hausdorff difference, Weyl ratio, or frontier
  inertia whose shifted-Xi source orientation is already accessible.

This theorem is not RH. It removes the previous multi-term wall and isolates the remaining
orientation problem to one boundary coordinate.

## Novelty audit

Corpus search found the individual characteristic transport, norm flow, Jacobi recurrence, and
Christoffel kernel, but no moving-apex derivative of the full diagonal kernel and no radial
pure-top boundary law.

External search inspected:

- Barry Simon, [The Christoffel--Darboux Kernel](https://arxiv.org/abs/0806.1528), for projection,
  reproducing, and diagonal-kernel structure;
- Basor--Chen--Ehrhardt,
  [Painleve V and time dependent Jacobi polynomials](https://arxiv.org/abs/0905.2620), for
  time-dependent orthogonal-polynomial/Toda deformation;
- Yue--Chang--Hu,
  [Stationary reduction method based on nonisospectral deformation of orthogonal polynomials](https://arxiv.org/abs/2407.09875),
  including its 2025 v3, for nonisospectral orthogonal-polynomial flows and Lax systems.

No inspected source states the completed-Xi moving-apex law above, its exact degree-zero
half-current cancellation, or the radial reduction to one top product. External priority remains
provisional.
