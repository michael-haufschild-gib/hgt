# Global PSD of the bare first-atom tail kernel fails

- **ID:** RH-FIRST-ATOM-GLOBAL-TAIL-PSD-ROOT-20260926
- **Stage:** 5-failed
- **Type:** FALSIFIED mechanism; full theta and RH remain open
- **Owner:** root
- **Parent:** `../1-in-progress/rh-first-atom-tail-audit-root-2026-09-26.md`
- **Statement:** The exact first-atom first-moment tail kernel is not globally PSD.

## Exact scope

Let f(x)=thetaCuspSourceTerm x 1 and
`K_f(x,y)=integral_(s>0) (x+y+2s)*f(x+s)*f(y+s)`.
There exists a real x with K_f(x,x)<0. Thus not every finite real-node matrix
of K_f is positive semidefinite. The negative diagonal is obtained toward
negative infinity. No negative direction supported only on positive nodes,
and no failure of the complete even theta kernel, is asserted here.

## Strongest positive survivor: exact normalized scale moment

Let E=integral f(x)^2. Then E>0 and

`integral exp(2x)*f(x)^2 = [75/(44*pi)]*E`.

Moreover the center energy mu=integral 2x*f(x)^2 satisfies
`mu <= [75/(44*pi)-1]*E < 0`.
The first equality is an exact invariant of the squared first-atom measure,
not a numerical estimate or a restatement of the negative sign.

## Dependency-closed paper proof

The corpus already gives integrability and the exact Wigner pair transform

`I(sigma)=integral exp((2sigma-1)x)*f(x)^2
 = Gamma(sigma+2)/(2*(2pi)^sigma)*(sigma^2-sigma+3)`

for sigma>0. At sigma=1/2 the polynomial equals 11/4; at sigma=3/2 it equals
15/4. Gamma(7/2)=(5/2)*Gamma(5/2) and the real-power multiplication law yield
I(3/2)/I(1/2)=75/(44pi). Gamma positivity gives E=I(1/2)>0.

Pointwise exp(2x)>=1+2x. Multiply by f(x)^2 and integrate using the corpus
center-weight integrability theorem. Then mu<=I(3/2)-I(1/2). Since pi>3,
75/(44pi)<1, proving mu<0 without a numerical computation.

The diagonal is exactly `D(x)=integral_(t>x) 2t*f(t)^2` by translation of a
half-line integral. Its integrand is absolutely integrable, so D(x)->mu as
x tends to negative infinity. Hence some D(x)<0. A PSD matrix has nonnegative
diagonal; the one-node matrix refutes global PSD.

## No-go closure

- **Killing mechanism:** Negative full-line center energy survives as the
  incoming diagonal limit of the bare-atom kernel.
- **Positive survivor:** Exact normalized scale moment 75/(44pi), positive
  mass formula, and the explicit signed center-energy bound above.
- **New insight:** The positive corrected Cauchy model cannot be promoted to
  global bare-atom PSD. Global completion needs source structure absent from
  the first atom. Complete theta has even-source cancellation, so this no-go
  cannot be transferred to it. Whether analytic locality carries the bare-atom
  obstruction into every positive tail remains a separate open bridge.
- **Paper status:** Dependency-closed using the existing exact Wigner pair
  integral and elementary exponential convexity.
- **Lean status:** Exact survivor and negative diagonal proof pass scratch and the named
  `ThetaFirstAtomTailCenterObstruction` build. All 13 public theorem axiom
  reports contain only `propext`, `Classical.choice`, `Quot.sound`. Leaf wired.
  Index refreshed; final `scripts/formal_tools.py lint --check-generated` passes
  with existing large-file warnings. All owned jobs exited.

## Prior research and route audit

Deep/method retrieval and direct reads located the exact Wigner Mellin,
log-weight, and center-integrability formulas. Those are prior corpus knowledge.
The new specialization is the normalized scale invariant and its bare-tail
center obstruction. No global novelty claim. The all-rank correction theorem
from C6 remains valid; its full-source remainder transfer is still unresolved.
