# Xi-selected Green--Stokes quadratic-ghost erasure

- **ID:** `xi-selected-green-stokes-quadratic-ghost-erasure`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / OPEN PRODUCER
- **Source:** `rh-current-frontier-map.md` · Route-L singular graph + integral Cartier Gamma seam
- **Statement:** Construct, before scalar RH specialization, a distinguished source differential
  whose Xi-Green-weighted boundary is the integral quadratic inversion ghost and whose genuine
  Gamma/co-Poisson readout vanishes by a non-universal Stokes law.

## Goal

For every retained Xi divisor `rho`, produce a source-derived chain and Stokes operation, preserving
divisor multiplicity, ordinary-prime provenance, and both reflection orientations, which proves
that canonical full-Laurent Gamma evaluation annihilates
`m_rho (q-1)(q^-1-1)`. At prime two this forces `Re rho = 1/2`; universally it closes RH.

Directly assuming the scalar annihilation, additive Cartier descent, a shared Gamma ghost, or
critical-line placement is circular and is not an admissible producer.

## Gates

- [x] 0 → 1 in-progress: exact source object and circular endpoint classified
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: exact unconditional Lean theorem and targeted audit
- [ ] 3 → 4 publication-ready

## Active frontier

`[CORPUS]` Full Laurent evaluation retains the quadratic ghost and factors through `I/I²` iff the
centered grade is zero. `[CORPUS]` The singular Meyer--Tate graph contains a multiplicity-faithful
Xi-Green vertical boundary with genuine Gamma/Sonin transport. `[CORPUS]` every continuous graph
reader annihilating all Meyer--Tate boundaries is zero. Hence required Stokes law must be selected,
non-universal, and source-derived.

`[OPEN CORE]` Find an unconditional pre-divisor reason that the distinguished Xi-Green chain—not
all boundaries—lies in the kernel of actual Gamma transport, without encoding its vanishing in the
definition.

## Conjecture loop

### C1 — universal graph Stokes blindness `[FALSIFIED]`

`DeningerGammaSixCofinalMeyerTateXiGreenBoundary` proves dense range: a continuous reader killing
all Meyer--Tate boundaries is zero, while prime atoms have nonzero physical transport. Required law
cannot be universal boundary blindness.

### C2 — completed Euler/Xi factor kills Gamma jump `[FALSIFIED]`

`EulerHedenmalmGammaStokesTransgression` proves Gamma Stokes jump is nonzero throughout strip.
At an Xi zero, zeta factor—not Gamma jump—vanishes.

### C3 — two-ended integration by parts kills current `[FALSIFIED]`

Hedenmalm root-flux identity equals transverse grade times strictly positive root energy. Stokes
faithfully reads horizontal displacement; it does not erase it.

### C4 — functional-equation pair kills same fibre `[FALSIFIED]`

Reflection negates current only after exchanging divisor fibres. Pair cancellation is automatic;
same-fibre neutrality remains RH-strength.

### C5 — all-cross Big-Witt compensation `[PROVED, INSUFFICIENT]`

Complete cross-pair second ghost vanishes before scalarization. Its diagonal is physical seam
energy and off-diagonal fibre is exact negative in Gamma incidence and ordinary-integer BV Green
transport. Ground readout sees both terms, so no independent theorem makes compensator invisible.

### C6 — closed theta Green--Stokes derivative kills ghost `[PROVED, NON-FAITHFUL]`

New Lean module `FrankensteinXiGreenStokesQuadraticGhostNormalForm.lean` proves:

- reflected Xi eigenvectors fold into odd/even compact-source modes;
- both folds have exact `B` exchange law;
- raw even fold differs from centered fold by one explicit `pinnedOne` ghost;
- full-Laurent Gamma ghost is canonically its scalar coefficient times `pinnedOne`;
- it lies unconditionally in `ker(A†)` because `ker(A†)=C pinnedOne`;
- this annihilation is non-faithful: ghost belongs to physical `range(A)` iff critical line;
- every scalar reporter nonzero on `pinnedOne` annihilates ghost iff critical line;
- global range admission is equivalent to RH.

This is exact Green--Stokes normal form, but not RH proof. Adjoint killing discards whole cokernel
and therefore cannot justify additive Cartier descent.

### C7 — strict-frontier local-L1 upgrade `[FALSIFIED AS GENERIC INPUT]`

Corpus proves every occupied exact Christoffel frontier wall is nonintegrable on every nontrivial
right interval. Universal local-L1 is already equivalent to absence of occupied frontiers and RH.
Theta source modes being L1 cannot transfer without a new coefficient-faithful identification;
such identification is the producer, not an analytic regularity corollary.

### C8 — literal cyclic boundary implies physical Stokes-flatness `[FALSIFIED]`

`SourceHorizontalGammaSixTameReaderTransgression` proves complete finite harmonic shell class is a
literal `t-1` boundary. Physical character is not a chain map: on every primitive `f`, its boundary
readout is `(exp(a)-1) chi_a(f)`. Opposite characters leave exact positive Beck--Chevalley
curvature `2(cosh(a)-1)`, zero exactly at `a=0`.

### C9 — Big-Witt singular-limit continuity kills common vertical class `[REDUCES TO TARGET]`

Fixed-left normalized Big-Witt rows converge algebraically to one common singular vertical vector,
while coefficient-faithful reporters read `p^(-t)`. Extension to common limit is possible exactly
at `t=0`; continuity is not independently supplied.

### C10 — off-line L2 Koszul inverse preserves strong Meyer source `[FALSIFIED]`

Half-density gauge intertwines strong Meyer flow with unitary translation. Ambient L2 coordinate is
invertible off line, but its inverse cannot preserve strong source image. Direct Neumann-series
attempt fails at all-exponential topology: weight-`k` translate seminorm grows geometrically with
rate proportional to `k`, while resolvent coefficient has one fixed decay rate. Large `k` defeats
convergence. Preservation itself forces critical-line placement.

### C11 — positive curvature cancels Laurent ghost `[PROVED, NOT ERASURE]`

New coefficient identity, preserving divisor multiplicity and ordinary-prime label:

`ghost(rho,p) = -m_rho * 2(cosh(log(p) * t_rho)-1)`.

Thus ghost is nonpositive and strictly negative off line. In theta harmonic carrier, its positive
paired-curvature vector cancels it exactly. Positivity confirms nonzero ghost; it cannot erase it.

### C12 — literal Xi-selected Green--Stokes Ward double `[PROVED, OPEN CORE SHARPENED]`

Formalized actual cyclic-boundary anomaly by evaluating both reflected physical characters on same
canonical Deninger source primitive, multiplying by exact Xi multiplicity, and retaining prime
clock. Lean proves:

`quadraticGhostVector + cyclicBoundaryAnomalyVector = 0`.

Anomaly is exactly paired curvature. Both terms lie in `ker(A†)` unconditionally, and each enters
physical `range(A)` or vanishes exactly on critical line. Global Stokes-flatness of literal selected
cyclic boundary is equivalent to RH. This is unconditional source law for full Ward double, not
standalone ghost erasure.

### C13 — pinned-Volterra relative boundary absorbs ghost `[PROVED, NON-FAITHFUL]`

Corpus rank-two boundary operator has `pinnedOne` in its range. Therefore both Xi-labelled ghost
and cyclic anomaly lie unconditionally in this relative-boundary range. This is valid homological
Faddeev--Popov-style killing, but quotient annihilates every `pinnedOne` coefficient. Off line these
same vectors do not lie in physical derivative range. Relative-boundary exactness cannot replace
coefficient-faithful Green--Stokes admission.

## No-go closure

- **Exact killing theorem/mechanism:** adjoint closed derivative kills canonical Hilbert ghost
  unconditionally; pinned-Volterra relative boundary also absorbs it unconditionally. Both kill
  every harmonic scalar and are therefore not coefficient-faithful.
- **Strongest positive survivor:** full reflection-folded source system, literal Deninger cyclic
  primitive, and rank-one Green--Stokes Ward double, formalized axiom-free. Quadratic ghost is exact
  negative of source-selected Beck--Chevalley anomaly. Any valid producer must prove physical
  character is Stokes-flat on this selected primitive, or place anomaly in physical derivative
  range; either pointwise statement is critical-line placement.
- **New insight:** quadratic inversion ghost is not diffuse Gamma curvature. It is literal Fredholm
  harmonic obstruction: `ker(A†)` is exactly its carrier, while coefficient-faithful physical
  admission is `range(A)`. Contractible/Faddeev--Popov killing attacks wrong quotient.
- **Status:** Stage 1. Unconditional full Ward-double law is formalized; coefficient-faithful
  standalone ghost killing remains open and is exactly RH-strength.

## Log

- 2026-08-16 — opened exact post-producer Green--Stokes lane.
- 2026-08-16 — completed seven hostile conjecture loops; formalized reflection-folded rank-one
  normal form, unconditional adjoint killing, and exact faithfulness/range wall.
- 2026-08-16 — completed five further cross-corpus loops; formalized exact curvature coefficient,
  literal cyclic-boundary anomaly, Xi-selected Ward double, and global RH-equivalence of physical
  Stokes-flatness.
