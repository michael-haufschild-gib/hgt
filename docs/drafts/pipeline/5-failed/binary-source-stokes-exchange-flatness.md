# Failed route: binary source--Stokes exchange from raw clock curvature

- **ID:** `ngd-failed-binary-source-stokes-exchange-flatness`
- **Stage:** 5 — failed/retired
- **Status:** `[FALSIFIED] [PAPER COUNTERTHEOREM] [POSITIVE SURVIVOR EXTRACTED]`
  `[NOT RH] [NO LEAN WRITTEN]`

## Failed conjecture

The conjecture treated

\[
 \kappa(gh)-\kappa(g)-\kappa(h)=\kappa(g)\kappa(h),
 \qquad \kappa=\chi-1,
\]

as invariant binary curvature and proposed a source `2`-cell whose flatness would force the
critical line.

## Exact falsifier

For every positive character `chi:G->R_(>0)`, define

\[
 \ell(g)=\log(1+\kappa(g))=\log\chi(g).
\]

Then

\[
 \ell(gh)=\ell(g)+\ell(h).
\]

Equivalently, `F(X,Y)=X+Y+XY` is globally linearized on `X>-1` by `log(1+X)` and formally
linearized over `Q`. In the literal RH clock chart,

\[
 \chi_t(n)=n^t,qquad \ell_t(n)=t\log n
\]

for every real `t`, including every off-centre value. Therefore `kappa(g)kappa(h)` is the
additivity defect of one coordinate, not coordinate-free curvature. An arbitrary binary reporter
of that term would be chart-dependent and cannot found Lawspace Twistor Geometry.

Ordinary group `H^2` does not rescue it because

\[
 d_{grp}\kappa(g,h)=-\kappa(g)\kappa(h).
\]

The representative is already a coboundary for every character.

## Additional typing failures

1. The former `[Sigma(g,h)]` was not a homology class: its Hochschild boundary has product-trace
   value `1` and is nonzero.
2. “Xi top-conormal before divisor choice” mixed source and target types.
3. A conservative functor was used as though it were a normalized scalar reporter.
4. Weighted curvature used `rho` and `c_rho`, so only the unweighted product-normalized chain was
   pre-divisor.
5. Reporter flatness specialized to the desired critical-line statement and had no independent
   source proof.

## Positive survivor

The following paper theorems survive:

1. inner correction changes a trace--derivation cocycle only by a Hochschild coboundary and
   preserves its prime period;
2. product trace measures a product-normalized Hochschild boundary;
3. the raw clock coordinate obeys the exact formal-group law;
4. logarithm linearizes that law;
5. ordinary `H^2` forgets the chosen primitive.

The field-level invariant must survive source-preserving presentation equivalence and admissible
local coordinate changes. Viable candidates include holonomy conjugacy, stability type,
characteristic classes, admission failure, and the descent gerbe of exactification frames.

## Replacement conjecture

**Reparametrization-invariant exactification descent.** Construct the homotopy fibre

\[
 \operatorname{Lift}_{src}(t)=
 \operatorname{fib}_t\left(
 \operatorname{Triv}_{src}\longrightarrow
 \operatorname*{holim}_\alpha\operatorname{Triv}_\alpha
 \right),
\]

prove invariance under source-preserving presentation and law-coordinate changes, and compute at
least two nonisomorphic corpus invariants as functorial boundary maps from this one fibre. This is
a make-or-break theorem for Lawspace Twistor Geometry. It is not a Route-R selector.

## Lean boundary

No Lean was written or built. Do not formalize the failed binary conjecture. The logarithmic
linearization and inner-correction theorems may later be formalized only after the paper card is
stabilized.

## Log

- 2026-08-08 — retired after hostile audit exhibited global logarithmic linearization of every
  positive radial clock character.

