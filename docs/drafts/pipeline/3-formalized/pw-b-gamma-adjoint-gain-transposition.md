# PW-B original forward response and complete gain transposition

- **ID:** PW-B-GAMMA-ADJOINT-GAIN-TRANSPOSITION-2026-09-11
- **Stage:** 3-formalized
- **Status:** All33 public theorems passed final foreground Lean scratch without diagnostics. Exact source promoted and wired once; targeted leaf build passed in46s. All public names indexed; final repository formal lint passed.
- **Scope:** Complete forward current pairing, original triangular gain transposition and all original integral admissions. The full paired source adjoint is also proved; physical operator domain, Xi occurrence and independent Ward balance remain open. RH is not proved.
- **Depends on:** [complete paired response](pw-b-gamma-adjoint-paired-response.md), [original reciprocal source](pw-b-gamma-reciprocal-cutoff-source.md).

## Complete forward source

Write g_z(x)=M_z(x)/Q(x), w(x)=exp(-x-1/x)/x. The actual coordinate
source equation and literal Q derivative prove

`(g_z)'=g_z-g_(z-1)`.

The complete source bound is `|g_z(x)|<=C*(1+1/x)^p`. Monotonicity
of its inverse-power majorant controls the derivative at every y>=x.
The convex mean-value estimate therefore gives

`|g_z(x+h)-g_z(x)|<=C*(1+1/x)^r*h` for x>0,h>=0.

The original normalized forward difference

`F_z(x,h)=exp(-h)*(g_z(x+h)-g_z(x))/h`

is exactly the already admitted Frullani source response divided by Q(x).
Its full integral is the original parameter current M'_z(x)/Q(x), with
no source truncation. For every complex z,v,

`|w(x)*conj(g_z(x))*F_v(x,h)|<=C*x*exp(-x)*exp(-h)`.

This is absolutely integrable jointly. Its native h>delta cutoff tends to
the complete current pairing while retaining the entire positive x ray.

## Original gain and exact transposition

For x<y, define

`K_z,v(x,y)=w(x)*conj(g_z(x))*g_v(y)*exp(-(y-x))/(y-x)`.

For every delta>0 the following identity holds:

`integral_(x>0) integral_(h>delta) K_z,v(x,x+h) dh dx`

`= integral_(y>delta) w(y)*g_v(y)*integral_(r>a_delta(y)) exp(-r)/r*conj(g_z(1/(1/y+r))) dr dy`,

where `a_delta(y)=delta/[y*(y-delta)]`.

The bound `|K(x,x+h)|<=C*x*exp(-x)*exp(-h)/h` admits the original
cutoff rectangle. Extend it by zero on the complement of that rectangle.
The actual additive shear `(x,y)->(x,y-x)` preserves Lebesgue product
measure and transports its support exactly to `0<x<y-delta`.
Admitted Fubini gives the triangular integral on y>delta.

On each recipient interval, the injective map `r=1/x-1/y` has derivative
`-1/x^2` and image exactly `r>a_delta(y)`. The installed one-dimensional
Jacobian theorem retains this derivative. The original detailed-balance
identity then gives the displayed full-source gain equality. This step
uses the actual complete source evaluated at its transported argument.

Every positive-x original inner cutoff integral, every recipient inner
interval, every positive-cutoff reciprocal gain ray, and both outer gain
integrals are separately admitted. Reciprocal gain admission also follows
from its exact decomposition into the complete backward response and the
constant exponential tail. No identity relies on an undefined integral
being assigned zero.

## Verification and remaining proof

Leaf: `ThetaCuspHawkingParikhWilczekGammaAdjointGainTransposition.lean`.
Scratch: `/tmp/pwb-gamma-forward-response.lean`.
Key theorems:

- `pwGammaMobiusGroundQuotient_hasDerivAt`;
- `pwGammaMobiusForwardPairKernel_integrable`;
- `pwGammaMobiusForwardGainDensity_full_transposition`;
- `pwGammaMobiusForwardGainDensity_outer_admission`;
- `pwGammaMobiusForwardPairKernel_cutoff_tendsto`.

The [full paired adjoint assembly](pw-b-gamma-full-paired-adjoint.md)
retains the already proved logarithmic contact and empty incoming constant
loss when subtracting gains and losses and taking the cutoff limit. A
physical common operator domain, source-forced pairing, a different justified
Xi occurrence and independent fixed-grade Ward balance remain separate
obstacles. The corrected Gamma scalar ansatz remains excluded by its
original-current valuation.

The [deep/method search record](../1-in-progress/pw-b-gamma-forward-gain-searches.json)
retains partial coverage, including the first query's interrupted retrieval.
The proof uses actual corpus coordinate derivatives, mean-value estimates,
measure-preserving shear, Fubini and the injective Jacobian theorem. Recent
broad arXiv transport reading is assessed in the attack journal; no physical
entropy axiom or real-rooted positive-pencil premise is imported.
