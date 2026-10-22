# CCM logarithmic-cusp period--density quantization law

- **ID:** CCM-C37
- **Stage:** 3-formalized/needs-audit
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [CORPUS-NOVEL COMBINATION]`
  `[ARBITRARY COMPLETE NORMED TARGET] [BOUNDED HOLOMORPHIC LOGARITHMIC COVER CLOSED]`
  `[CLASSICAL Q-EXPANSION CORE] [EXTERNAL NOVELTY OPEN] [NOT RH] [NOT WHOLE-CCM DEATH]`
- **Source:** `docs/handover/connes.md` §§77--78; C36--C37
- **Statement:** Positive first-order thermal density on a bounded holomorphic periodic
  logarithmic cover quantizes its period by one positive integral cusp charge. In particular,
  ordinary `2π` logarithmic deck descent cannot carry any positive finite thermal density, hence
  cannot carry the exact CCM four-unit normalization.

## Goal

Decide the bounded holomorphic logarithmic universal-cover survivor explicitly left by C36. Replace
finite scalar ramification by a genuine periodic coordinate on the logarithmic plane, without any
finite-dimensional, finite-rank, or scalar-target assumption.

## Exact universal theorem

Let `E` be any complete complex normed space, let `h>0`, and let `f : C -> E` satisfy

```text
f(z+h)=f(z),
f is eventually holomorphic as Im(z)->+infinity,
f is bounded as Im(z)->+infinity.                       (C37.1)
```

Define the central-ray density

```text
Lambda_f(t)=||f(it)||^2/(1-exp(-exp(-t))).              (C37.2)
```

The periodic cusp coordinate and cusp function are

```text
q_h(z)=exp(2π i z/h),
F_h(q)=f(invQParam_h(q)),                               (C37.3)
```

with the removable value at `q=0`. Lean proves that `F_h` is analytic at zero. If
`Lambda_f(t)->ell` for any finite `ell>0`, then

```text
h=4π ord_0(F_h).                                        (C37.4)
```

Consequently no `2π`-periodic `f` satisfying `(C37.1)` can have a positive finite limit in
`(C37.2)`. In particular it cannot have the CCM limit `ell=4`.

The theorem is target-universal: it applies to Hilbert-, Hilbert--Schmidt-, operator-, Schatten-,
and other complete complex normed targets. It assumes no dimension, rank, compactness,
scalarization, RH premise, zero-free region, truncation, or numerical estimate.

## Proof `[PROVED HERE]`

Periodicity makes `(C37.3)` single-valued off `q=0`. Eventual holomorphy transfers through the
local inverse of `q_h`; eventual boundedness transfers along `invQParam_h(q)->i infinity`. The
vector-valued removable-singularity theorem therefore gives

```text
F_h is analytic at q=0.                                 (C37.5)
```

On the central ray the cusp coordinate is exact:

```text
q_h(it)=exp(-(2π/h)t).                                  (C37.6)
```

Thus `(C37.2)` is exactly C36's analytic ramification density for `F_h` at rate `q=2π/h`.
Positive finite density and `(C37.5)` let C36 apply:

```text
2(2π/h) ord_0(F_h)=1.                                  (C37.7)
```

Since `h>0`, rearrangement yields `(C37.4)`. If `h=2π`, then `(C37.4)` gives
`1=2 ord_0(F_h)`, impossible in the natural numbers. Every step is a Lean theorem.

The same construction proves a dimension-free periodic cusp gap: if `f` tends to zero at the
cusp, then

```text
f(z)=O(exp(-2π Im(z)/h)) as Im(z)->+infinity.           (C37.8)
```

## CCM consequence and remaining frontier

C37 closes the bounded norm-holomorphic logarithmic-deck escape from C36, including
infinite-dimensional targets. Do not retry a bounded holomorphic `2π`-periodic logarithmic source
as a four-unit CCM transport.

This is not RH and not death of whole CCM. The theorem deliberately does not cover an unbounded
cusp map, a map without eventual norm holomorphy, aperture-dependent/cofinal families with no
fixed periodic function, non-scalar monodromy, or closed graph topology invisible to ambient norm.
After C33--C37, the exact unresolved CCM object is no longer an ordinary analytic branch. It must
be a genuinely graph-singular source-to-Xi transport capable of proving

```text
D_Xi = closure(P_- M_(-2 Xi'/Xi)),
limsup_(u->0+) ||Q_u D_Xi||_(S2,ext)^2 /
                (4(1-exp(-u))) <= 1,                   (C37.9)
```

equivalently source-normalized Evans nonvanishing. Proving `(C37.9)`, deriving such a transport
from exact source geometry, or excluding every remaining graph-singular transport is still the
RH/CCM frontier.

Periodic scalar `q`-expansion and removable singularities are classical ingredients. Corpus search
found no prior arbitrary-complete-normed-target period--density charge law or exact CCM four-unit
connector. External literature novelty remains open and must not be advertised as settled.

## Formal declarations

Module `formal/GaloisForLFunctions/HTGeometry/PeriodicCuspBoundaryGap.lean`:

- `normedPeriodicCuspFunction`;
- `normedPeriodicCuspFunction_qParam_eq`;
- `analyticAt_normedPeriodicCuspFunction_zero`;
- `normedPeriodic_exp_decay_of_zero_at_inf`;
- `logarithmicCuspBoundaryDensity`;
- `qParam_vertical_eq_real_exp`.

Module `formal/GaloisForLFunctions/RHTower/CCM/CCMLogarithmicCuspBoundaryNoGo.lean`:

- `logarithmicCuspBoundaryDensity_eq_analyticRamifiedBoundaryDensity`;
- `period_eq_four_pi_mul_analyticOrderNatAt_of_logarithmicCuspBoundaryDensity_pos`;
- `not_tendsto_logarithmicCuspBoundaryDensity_pos_of_two_pi_periodic`;
- `ccmFourUnit_logarithmicCusp_period_eq_four_pi_mul_order`;
- `ccmFourUnit_not_two_pi_periodic_logarithmicCuspBoundary`.

## Gates

- [x] prior-research search across `HTGeometry`, `RHTower`, `HilbertMetric`, formalized cards,
  paper cards, and failed routes
- [x] dependency-closed paper proof
- [x] direct Lean checks for pure theorem and CCM connector
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] formal lint attribution audit: no finding in either C37 module; repository-wide lint fails on
  pre-existing umbrella-reachability findings in other dirty-tree modules
- [x] targeted final module build:
  `GaloisForLFunctions.RHTower.CCM.CCMLogarithmicCuspBoundaryNoGo`
- [ ] external novelty audit
- [ ] RH or whole-lane no-go

## Log

- 2026-07-23 — Proved vector-valued periodic cusp analyticity and decay, universal
  period--density quantization, `2π` logarithmic-cover exclusion, and exact CCM four-unit
  connectors.
