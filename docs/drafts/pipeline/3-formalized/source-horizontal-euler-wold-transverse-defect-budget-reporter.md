# Source-horizontal Euler--Wold transverse defect-budget reporter

- **ID:** `P-G209-TDBR`
- **Stage:** 3-formalized
- **Type:** `[LEAN-PROVED] [BRIDGE]`
- **Route:** P, after Xi-fibre conormal co-short admission
- **Exact claim:** The coefficientwise Euler--Wold compression defect plus one quarter of the
  primitive Euler budget times the admitted endpoint response is a nonzero-character reporter
  converging to exactly half the literal primitive source budget on every nonzero Xi conormal.

## Frontier

For a conormal coefficient `c`, let `A₋`, `A₊`, and `R` be the already-formalized admitted Euler,
Wold, and endpoint legs.  Let

```text
B = routePPrimitiveBaseCauchyCubicTraceBudget,
S(c) = 4 |c|²,
P(c) = (8/3)|c|² B.
```

Corpus proves `0 < B < 1`, `A₋=-M₋S`, `A₊=M₊S`, `M₊≤M₋`, and the complete linear-reporter
character

```text
L_(a,b,d) -> (8/3)|c|²(-a+b+2d).
```

Existing primitive-budget reporter `(1,-1,1)` lies in the blind plane. Complete-positive and
endpoint-dominating reporters overspend.

## Conjecture loop

### C0 — use the scalar Euler--Wold defect alone

Take `-A₋-A₊=(M₋-M₊)S`. It is nonnegative, coefficient-faithful, and tends to zero.

**Verdict:** `[FALSIFIED]` as requested producer. Its coefficient vector `(-1,-1,0)` has character
zero. The exact source defect is budget-safe but blind.

**Representation lesson:** transversality must be inserted through endpoint channel, but its
coefficient must be calibrated by actual primitive source budget rather than by a divisor or clock.

### C1 — primitive-budget midpoint reporter

Define

```text
T(c,q,N) = L_(-1,-1,B/4)(c,q,N)
           = (M₋(N)-M₊(N)) S(c) + (B/4) R(c,q,N).
```

Frozen predictions:

1. first equality is exact at every clock;
2. cofinal character is `B/2`, hence nonzero for `c != 0`;
3. `T(c,q,N) -> P(c)/2`;
4. for `c != 0`, eventually `0 < T(c,q,N) < P(c)`;
5. same statement holds for actual multiplicity-split Burnol/Gamma--Julia Xi coefficient;
6. no linear reporter can be both eventually source-budgeted and eventually dominate literal
   endpoint response.

## Hostile audit

- Coefficient `B/4` is one source constant. It is independent of `q`, copy index, aperture, and
  clock; no fitted divisor scalar occurs.
- Reporter uses existing endpoint response but its budget bound is derived from independent
  positivity of `P(c)` and an exact limit strictly inside `(0,P(c))`.
- It does not prove RH. Endpoint domination is impossible for every linearly source-budgeted
  reporter because corpus already proves `P(c)<R(c,q,N)` cofinally.
- Generic Krein shorting, BV pushforward, and semilocal Sonin theory do not contain this arithmetic
  source coefficient or Xi-fibre statement. The construction is a corpus-specific bridge, not a
  scientific-priority claim.
- Primary controls checked: Arlinskii's generic Krein-shorted conservative realizations
  (<https://arxiv.org/abs/1109.4020>), Cattaneo--Mnev's BV strong deformation retract
  (<https://arxiv.org/abs/2605.30558>), Connes--Consani's archimedean Weil/Sonin positivity
  (<https://arxiv.org/abs/2006.13771>), and semilocal prolate/Sonin stability
  (<https://arxiv.org/abs/2310.18423>). None asserts the source-specific finite defect identity,
  primitive coefficient `B/4`, actual Xi multiplicity statement, or linear firewall proved here.

## Paper proof

Put `V_N=M₋(N)-M₊(N)`. Existing coefficientwise Euler--Wold domination gives `V_N≥0`, and the
Jordan data-processing theorem identifies `V_N` with exact post-compression variation. Expanding
the admission definitions gives

```text
-A₋(c,N)-A₊(c,N)
= M₋(N)S(c)-M₊(N)S(c)
= V_N S(c).
```

Therefore C1's reporter is literally the nonnegative coefficient-faithful compression defect plus
`B/4` times endpoint response. It is not defined as `P-R` or by a fitted Xi-fibre correction.

Its cofinal character is

```text
-(-1)+(-1)+2(B/4)=B/2.
```

Since `B>0`, this is transverse. The complete reporter classification now gives

```text
T(c,q,N) -> (8/3)|c|²(B/2) = P(c)/2.                 (1)
```

If `c!=0`, positivity of `|c|²` and `B` gives `P(c)>0`, hence
`0<P(c)/2<P(c)`. Applying convergence in (1) to that open interval proves

```text
eventually 0 < T(c,q,N) < P(c).                       (2)
```

For actual Xi admission, take `c` to be the multiplicity-split completed Gamma--Julia coordinate.
Nonzero source coupling and nonzero aperture make `c!=0`, so (1)--(2) apply. The coordinate is
constant on one support fibre. Endpoint response is also copy-independent after its exact
Green--Stokes third-jet identity. Thus the reporter is constant over the fibre, and its fibre sum is
exactly analytic multiplicity times one-copy reporter.

Finally suppose any linear reporter `L` were eventually source-budgeted and eventually dominated
literal endpoint response. Existing endpoint overspend gives, cofinally,

```text
P(c) < R(c,q,N) <= L(c,q,N) <= P(c),
```

an immediate contradiction. Hence C1 constructs requested transverse source-budgeted reporter but
also proves linear reporting cannot transfer that budget to endpoint domination. ∎

## Proof obligations

- [x] exact finite defect identity;
- [x] exact character and half-budget identity;
- [x] eventual two-sided budget;
- [x] actual Xi coefficient and multiplicity statement;
- [x] universal linear endpoint-domination firewall;
- [x] exact unconditional Lean formalization.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/SourceHorizontalEulerWoldTransverseDefectBudgetReporter.lean`
- Capstone: `sourceHorizontalActualXiTransverseDefectBudgetReporter_producer`.
- Linear firewall: `not_eventually_sourceBudgeted_and_endpointDominating_linearReporter`.
- Exact source check: PASS.
- Exact leaf build: PASS (`13563/13563`).
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- Target has no forbidden declarations; global static lint reaches target and fails only on seven
  unrelated concurrently unwired modules.
- Umbrella import wired; umbrella not built.

## Verdict

`[LEAN-PROVED] [BRIDGE]`. Requested transverse source-budgeted reporter exists with actual Xi-fibre
coefficient and multiplicity fidelity. This does not close RH: every linear reporter that remains
source-budgeted is formally unable to dominate literal endpoint response cofinally. Remaining
Route-P producer must therefore be nonlinear, order-indefinite before scalarization, or use an
arithmetic source relation that annihilates endpoint excess rather than dominates it.
