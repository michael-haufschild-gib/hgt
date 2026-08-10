# Mass-shifted fourth-cumulant reserve no-go

- **ID:** `mass-shifted-fourth-cumulant-reserve-no-go`
- **Stage:** 5-failed
- **Type:** EXACT CIRCULARITY THEOREM / POSITIVE SURVIVOR
- **Source:** Route-U degree-one Cassini contact
- **RH used:** no
- **Computation used:** no
- **Lean:** `XiShiftedHankelCassiniFourthCumulantCapNoGo.lean`

## Failed conjecture

At the theta Esscher contact `N(t)=0`, the quantitative reserve

```text
t^3 K4 <= 3 A (1-e)(1-2e^2)                              (1)
```

was proposed as a source inequality strictly weaker than terminal-flux orientation.

## Exact failure

Put `y=t^2`, `m_k=Re xiShiftedReciprocalMoment(y,k)`, `A=t m_0`, and
`e=1-2y m_1/m_0`.  Contact is `m_0 m_2=m_1^2`.  Expanding the corpus definition

```text
K4=-6m_1+48y m_2-48y^2 m_3
```

and substituting contact into `(1)` cancels every lower term.  The result is exactly

```text
m_1 m_3-m_2^2 >= 0.                                     (2)
```

For null root `a=m_1/m_0=m_2/m_1`,

```text
m_1 L_y(X(X-a)^2)=m_1m_3-m_2^2.                         (3)
```

Corpus positivity gives `m_1>0`.  Therefore `(1)`, `(2)`, nonnegative theta contact flow, and
nonnegative Route-U terminal flux are equivalent.  The proposed reserve is the desired sign in
cumulant coordinates, not an independent arithmetic producer.

## Lean closure

`XiShiftedHankelCassiniFourthCumulantCapNoGo.lean` proves unconditionally:

- exact identity `(3)` on every actual flat degree-one face;
- `(1)` iff nonnegative contact flow;
- contact flow nonnegative iff terminal flux nonnegative;
- terminal flux nonnegative iff adjacent shifted minor `(2)` is nonnegative;
- capstone equivalence `(1) <-> (2)`.

Module is umbrella-wired through `RHTower.lean`.  No new axiom, computation, or RH premise occurs.

## Positive survivor

The failure localizes where new arithmetic information must enter: before cumulant compression.
The source-selected pre-compression object is the one-Euler mixed factorial amplitude

```text
Q_(r,c)(T)=sum_j c_j T^j/((r+j)!(r+j+1)!).
```

`XiShiftedHankelBoundaryFactorialEulerSourceConnection.lean` proves that actual completed-source
mass differentiation lands on this amplitude before archimedean/Chebyshev aggregation.  Remaining
source theorem must orient those two channels on `Q_(r,c)` or its determinant-line hyperedge
current.  Another scalar cap downstream of the aggregation is disallowed by this no-go.

## Status

`[FAILED EXACTLY] [POSITIVE SALVAGE FORMALIZED] [NOT RH]`.

## Log

- 2026-08-10 — derived contact reduction without computation; formalized full weak-sign
  equivalence and extracted mixed Euler source landing as positive survivor.
