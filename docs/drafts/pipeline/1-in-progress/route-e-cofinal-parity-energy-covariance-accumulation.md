# Route E cofinal signed parity--energy covariance accumulation

- **ID:** `ROUTE-E-COFINAL-PARITY-ENERGY-COVARIANCE-001`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` / `[OPEN CORE]`
- **Parent:** `rh-current-frontier-map.md`, `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **External audit:** intentionally omitted under current instruction; no priority claim permitted

## Frozen target

Let

\[
 S_y=\{p\text{ prime}:p\le y\},\qquad
 J_y(x)=\sum_{T\subseteq S_y}(-1)^{|T|}e^{-x\prod_{p\in T}p},\qquad
 Z_y(x)=\sum_{T\subseteq S_y}e^{-x\prod_{p\in T}p},
\]

and \(\psi_y=J_y/Z_y\).  Fix any aperture schedule satisfying, for all sufficiently small
\(x>0\),

\[
 (y(x)+1)x\ge 2\log(1/x).                               \tag{A0}
\]

**`COFINAL-SIGNED-COVARIANCE-ACCUMULATION`.**  For every \(\varepsilon>0\), there are
\(C_\varepsilon<\infty\) and \(x_\varepsilon>0\) such that

\[
 0<x\le x_\varepsilon
 \quad\Longrightarrow\quad
 |\psi_{y(x)}(x)|\le C_\varepsilon x^{1/2-\varepsilon}.  \tag{A1}
\]

The proof must proceed through the exact prime-insertion recurrence and retain its signed defect
forcing in the parity--energy covariance form

\[
 \Delta_{S,p}(x)=Z_S(x)Z_S(px)
 \int_x^{px}-\operatorname{Cov}_{S,t}((-1)^{|T|},E(T))\,dt. \tag{A2}
\]

No assumption equivalent to `(A1)`, no Mertens prefix bound, and no absolute-value replacement of
the signed accumulation is admissible.

## Why this target is sufficient

The positive partition satisfies \(Z_y(x)\le\sum_{n\ge1}e^{-nx}\ll x^{-1}\), so `(A1)` gives
\(|J_y(x)|\ll_\varepsilon x^{-1/2-\varepsilon}\).  The proved finite/infinite-volume bridge and
`(A0)` make the omitted tail \(O(x)\), hence the true Möbius--Laplace transform has every
strict-half bound.  Existing consumers then imply RH.

## Binding hostile gates

1. Derive the exact fully weighted Duhamel recurrence before proposing an inequality.
2. Check whether the proposed accumulation statistic is algebraically equal to the desired current.
   If so, verdict `CIRCULAR` unless an independently proved source inequality controls it.
3. Respect the alternating finite-volume jet
   \[
   \Delta'_{S,p}(0)=(p-1)2^{|S|}(-1)^{|S|+1}\prod_{q\in S}(q-1).
   \]
4. Reject termwise positivity, monotonicity, generic covariance inequalities, and MR fluctuation
   bounds unless they retain the coherent block mean.
5. No Lean work until a complete paper theorem survives these gates.

## Current status

- `[CONJECTURE]` `(A1)` is exactly the requested RH-strength cofinal bound.
- `[CORPUS]` `(A2)` and the alternating jet are unconditional Lean theorems in
  `RHTower/GibbsParityEnergyCovariance.lean`.
- `[OPEN CORE]` Find a non-circular cross-prime law controlling the signed weighted accumulation.

