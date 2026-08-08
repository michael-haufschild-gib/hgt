# Return-excised minimal-incidence-rank law

- **ID:** `return-excised-minimal-incidence-rank-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** frontier theorem / sharp incidence-normalized coarea law
- **Parent:** `../3-formalized/return-excised-replica-coarea-incidence-law.md`
- **Status:** `[LEAN-PROVED] [APPLICATION NOVELTY UNVERIFIED]`
- **Date:** 2026-08-08

## Frontier

The return-excised coarea law already bounds complete target capture by the Hilbert number of the
return-removed target image times one pair action.  That Hilbert number still counts target
directions never occupied by any surviving source sheet.  A hostile reviewer can therefore ask
whether the alleged incidence normalization is genuinely source--target relative or merely a
target-span bound with source integration attached.

The missing invariant is the smallest replica subspace which preserves every actual off-return
target incidence.  It is determined jointly by the occupied target image and the surviving source
image, and it leaves the pair action unchanged.

## Conjecturing protocol

### C0 -- target Hilbert number is the final normalization

**Verdict:** `[FALSIFIED AS SHARP]`.

Let `S_r(Z)` have dimension `h`, while all projected off-return source replicas lie on one line.
The existing law pays `h`, although one coordinate preserves every incidence.  Duplicate target
labels have been removed, but target directions invisible to the source are still charged.

**Positive survivor:** compress once more, after source-return excision, to the span actually met by
the projected source.

### C1 -- quotient source points with equal endpoints

**Verdict:** `[REJECTED]`.

Quotienting would erase fibre-sheet multiplicity.  Equal endpoints reached by distinct Hamiltonian
coefficients or distinct times must remain distinct contributions to the quenched measure and to
the pair action.

**Positive survivor:** compress only the finite-dimensional reporter space; never quotient source
space.

### C2 -- off-return minimal incidence carrier

**Verdict:** `[PAPER-PROVED SURVIVOR]`.

Let `H_r` be the replica Hilbert space, `u_r(x)=state(x)^(tensor r)`, and

```text
S = span {z^(tensor r) : z in Z},
w(x) = Proj_S u_r(x).
```

For a measurable, target-independent return set `R`, define

```text
U_R = span {w(x) : x notin R},
iota_R = dim U_R.
```

Then `U_R` is the unique least subspace preserving all off-return incidences, and the old target
rank `h=dim S` can be replaced by `iota_R <= h` without changing the off-return pair kernel.

### C3 -- improve the factor below `iota_R` universally

**Verdict:** `[FALSIFIED]`.

Take `iota_R` orthogonal source sheets with uniform mass and the same orthogonal vectors as targets.
At replica order one and threshold one, complete capture has mass one, while the pair action is
`1/iota_R`.  Hence the coefficient `iota_R` is attained exactly.  Any smaller universal factor is
false.

## Exact theorem

Let `mu` be a finite measure on `X`, `R` a measurable return set, `Z` a finite family of normalized
targets, `r>=1`, and `a>0`.  Put

```text
E_a = {x : exists z in Z, a <= |<state(x),z>|^2},
nu_R = mu restricted to R^c,
S = S_r(Z),
U_R = span {Proj_S u_r(x) : x in R^c},
iota_R = dim U_R.
```

Define the minimal off-return incidence kernel and action by

```text
k_R(x,y) = |<Proj_(U_R) u_r(x), Proj_(U_R) u_r(y)>|^2,
A_R = integral_(R^c x R^c) k_R(x,y) dmu(x)dmu(y).
```

Whenever the displayed coordinate fields are measurable and square-integrable,

```text
(a^r nu_R(E_a))^2 <= iota_R A_R,                         (MIR1)

mu(E_a) <= mu(R) + a^(-r) sqrt(iota_R A_R).              (MIR2)
```

For `x,y notin R`, projection to `U_R` equals projection to `S`.  Consequently `k_R` is exactly the
previous occupied-target pair kernel on the return-free square.  The advance is therefore a strict
normalization improvement, not a replacement by a smaller unrelated action.

Moreover,

```text
iota_R <= dim S = h_Z(r),                                (MIR3)
```

with strict inequality whenever some occupied target-replica direction is never met by a surviving
source sheet.

## Dependency-closed proof

Write `P_S` and `P_U` for the two orthogonal projections.  Every generator of `U_R` belongs to `S`,
so `U_R subset S`.  For `x notin R`, `P_S u_r(x)` is one of the spanning generators of `U_R`.
Nested orthogonal projection therefore gives

```text
P_U u_r(x) = P_U P_S u_r(x) = P_S u_r(x).              (1)
```

This proves both `(MIR3)` and equality of the old and new pair kernels on `R^c x R^c`.

The same identity proves minimality.  If a subspace `W` satisfies
`P_W u_r(x)=P_S u_r(x)` for every `x notin R`, then every generator of `U_R` belongs to `W`.
Hence `U_R subset W`.  Conversely `(1)` says that `U_R` itself preserves all such projections.
Thus `U_R` is the unique least exact off-return reporter.

Fix an orthonormal basis `b_1,...,b_iota` of `U_R` and put

```text
c_j(x)=<b_j,u_r(x)>,
C_jk=integral c_j(x)^* c_k(x) dnu_R(x).
```

Complete target capture and the replica target-span projection law imply, on `R^c`,

```text
a^r <= ||P_S u_r(x)||^2
     = ||P_U u_r(x)||^2
     = sum_j |c_j(x)|^2.                                (2)
```

Integrating `(2)` gives

```text
a^r nu_R(E_a) <= Tr C.                                  (3)
```

The covariance `C` is positive semidefinite.  Cauchy--Schwarz on its `iota_R` diagonal entries and
the inclusion of the diagonal in the full Hilbert--Schmidt sum give

```text
(Tr C)^2 <= iota_R ||C||_HS^2.                          (4)
```

Finite Fubini expansion gives the exact frame-potential identity

```text
||C||_HS^2
 = integral_(R^c x R^c)
     |sum_j c_j(x)^* c_j(y)|^2 dmu(x)dmu(y)
 = A_R.                                                  (5)
```

Equations `(3)`--`(5)` prove `(MIR1)`.  The set inclusion
`E_a subset R union (E_a intersect R^c)` pays return mass once.  Taking the nonnegative square root
of `(MIR1)` proves `(MIR2)`.

No target selector, targetwise union, source quotient, minimum spectral gap, Jacobian determinant,
random-matrix premise, or locality premise occurs.

## Information retained

1. **Fibre-sheet multiplicity.** Integration remains on `X` and `X x X`; equal endpoints from
   distinct source points remain distinct weighted sheets.
2. **Occupied endpoint image.** `S_r(Z)` is formed from actual target endpoints, not circuit labels.
3. **Source--target incidence.** `U_R` removes precisely those occupied target directions not met by
   any surviving projected source replica.
4. **Return removal.** `R` is excised before `U_R`, covariance, or pair action is formed, and `mu(R)`
   is paid once.
5. **Duplicate and exact-zero invariance.** Repeating target labels or adjoining a zero residual at
   positive replica order leaves `S`, `U_R`, `iota_R`, and `A_R` unchanged.

## Sharpness

Let `X={1,...,d}`, let `mu` be uniform, take `R` empty, and choose orthonormal states and targets
`state(j)=z_j=e_j`.  With `r=1` and `a=1`, every source point is captured,
`iota_R=d`, and

```text
A_R = sum_(j,k) d^(-2) |<e_j,e_k>|^2 = 1/d.
```

Thus both sides of `(MIR1)` equal one.  The incidence-rank coefficient is optimal even before any
asymptotic or physical specialization.

## Hostile review

1. This theorem does **not** prove decay of `A_R` for an ordinary Gaussian local-Hamiltonian
   ensemble.  It isolates the sharpest finite-dimensional normalization that can precede that
   estimate.
2. `iota_R` may equal `h_Z(r)`.  The theorem improves the old law exactly when surviving source and
   target replica images fail to occupy every target direction; it never promises such failure.
3. Algebraic span counts measure-zero source sheets.  An essential-span refinement could be smaller,
   but requires a separate measurable-field theorem.  No essential-rank claim is made here.
4. Trace--Hilbert--Schmidt and frame-potential identities are classical.  Welch and
   Benedetto--Fickus already identify tight frames as equality objects.  Novelty can lie only in the
   exact minimal-carrier composition with return excision and occupied circuit incidence.
5. Coarea terminology describes the source-sheet disintegration represented by the quenched pair
   integral.  No continuous Hausdorff coarea theorem is claimed in Lean.
6. Brown--Susskind remains open until one proves growing-replica decay of `A_R` for the stated static
   local-Hamiltonian ensemble and controls `iota_R` against circuit capacity.

## External comparison

- Welch's frame bound and Benedetto--Fickus frame-potential theorem cover the sharp finite-rank
  trace/collision inequality and its tight-frame equality case.
- Negro's coarea distribution theorem (`arXiv:2110.01441`) identifies pushforward density as the sum
  over all source fibres divided by intrinsic Jacobian; it does not perform occupied-target
  compression or return-excised minimal incidence reduction.
- Projected-ensemble frame-potential work studies subsystem-measurement ensembles and convergence to
  designs, not the least source--target carrier of a complete circuit tube.
- Oszmaniec--Kotowski--Horodecki--Hunter-Jones (`arXiv:2205.09734`) prove saturation and recurrence
  for random circuits and stochastic local-Hamiltonian dynamics, not the stated static-Hamiltonian
  incidence law.

No audited source states `(MIR1)--(MIR3)` with complete target capture, source return excision,
occupied endpoint compression, fibre-sheet retention, and the minimal-carrier theorem together.
This is separation evidence, not a priority proof; status remains `[APPLICATION NOVELTY UNVERIFIED]`.

## Lean realization

Module: `formal/GaloisForLFunctions/HTGeometry/ReturnExcisedMinimalIncidenceRankLaw.lean`.

Formalized statements include the abstract finite-coordinate bound; the return-excised incidence
span; inclusion in occupied target span; exact off-return projection preservation; least-carrier
minimality; incidence-rank comparison `(MIR3)`; exact pair-kernel and pair-action preservation;
squared capstone `(MIR1)`; scalar capstone `(MIR2)`; and duplicate-label/exact-zero invariance of
carrier and rank.

Verification on 2026-08-08: direct `lake env lean` passed; final
`lake build GaloisForLFunctions.HTGeometry.ReturnExcisedMinimalIncidenceRankLaw` passed; axiom audit
reported only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or project axiom.

No Brown--Susskind, local-Hamiltonian decay, or publication claim is authorized by this card alone.
