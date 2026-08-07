# Quenched replica incidence--covariance law

- **ID:** `quenched-replica-incidence-covariance-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** frontier theorem / incidence-normalized coarea bound
- **Parent:** `oriented-no-shortcut-without-return-law.md`
- **Status:** `[LEAN-PROVED] [APPLICATION NOVELTY UNVERIFIED]`
- **Date:** 2026-08-07

## Frontier

Raw coarea mass is exactly shortcut probability and therefore circular as an upper-bound method.
Raw observer-Jacobian pseudodeterminants are not observation invariants.  The replica--Hilbert
projection law replaces the complete target union by one projection moment, but leaves that moment
unbounded.  The missing step is a quenched bound which simultaneously retains source fibre sheets,
forgets duplicate circuit descriptions, remembers the occupied endpoint image, and deletes exact
return residuals.

## Conjecturing protocol

### C0 -- raw coarea action

**Verdict:** `[REDISCOVERED / CIRCULAR]`.  Coarea disintegrates the source probability over endpoint
fibres; it does not bound it.

### C1 -- raw growing-replica Jacobian determinant

**Verdict:** `[FALSIFIED]`.  Reporter duplication multiplies the determinant without changing the
capture event.  Physical tensor replication has the same exact metric/tube compensation.

### C2 -- occupied replica-span projection

**Verdict:** `[LEAN-PROVED BRIDGE]`.  For the return-removed occupied target image `Z`, put

```text
S_r(Z) = span {z^(tensor r) : z in Z},
q_r(x) = ||Proj_(S_r(Z)) psi(x)^(tensor r)||^2.
```

Complete target capture at fidelity threshold `a` implies `a^r <= q_r(x)`, hence
`a^r mu(E_a) <= integral q_r dmu`.  This is exact but the projection moment remains open.

### C3 -- occupied rank times worst source mode

Let `rho_r` be the quenched replica moment operator.  The elementary bound

```text
Tr(P_S rho_r) <= dim(S) ||rho_r||op
```

is true, but does not remove the hard supremum over one source mode.  It is a useful endpoint, not
the best attack invariant.

### C4 -- compressed covariance collision

**Verdict:** `[LEAN-PROVED SURVIVOR]`.  Fix an orthonormal basis `b_1,...,b_h` of `S_r(Z)`,
where `h = dim S_r(Z)`, and define the compressed quenched covariance

```text
C_ij = integral conjugate(<b_i, psi(x)^(tensor r)>)
                    * <b_j, psi(x)^(tensor r)> dmu(x),
K_(r,Z)(mu) = sum_(i,j) |C_ij|^2.
```

Then

```text
(integral q_r dmu)^2 <= h K_(r,Z)(mu),                    (QIC1)
a^(2r) mu(E_a)^2 <= h K_(r,Z)(mu).                       (QIC2)
```

`K_(r,Z)` is the squared coordinate Hilbert--Schmidt energy of the moment operator compressed to
the occupied replica image.  The Lean definition fixes one finite orthonormal basis and separately
proves that the resulting quantity depends only on the occupied replica span, not on target labels.
Equation `(QIC2)` is the incidence-normalized coarea bound: source sheets remain in every covariance
integral, while the target enters only through its occupied replica image.

## Dependency-closed paper proof

Write `u_x = psi(x)^(tensor r)`, `S = S_r(Z)`, `P = Proj_S`, and
`a_i(x) = <b_i,u_x>`.  Projection and Parseval give pointwise

```text
q_r(x) = ||P u_x||^2 = sum_i |a_i(x)|^2.                 (1)
```

After integrating and exchanging one finite sum with the integral,

```text
integral q_r dmu = sum_i integral |a_i(x)|^2 dmu(x)
                  = sum_i Re(C_ii).                      (2)
```

Cauchy--Schwarz on the `h` diagonal entries gives

```text
(sum_i Re(C_ii))^2 <= h sum_i Re(C_ii)^2
                     <= h sum_(i,j) |C_ij|^2.             (3)
```

Equations `(2)`--`(3)` prove `(QIC1)`.  The already proved complete-incidence law gives

```text
a^r mu(E_a) <= integral q_r dmu.                          (4)
```

Both sides of `(4)` are nonnegative.  Squaring `(4)` and applying `(QIC1)` proves `(QIC2)`.

No target selector, targetwise probability estimate, or circuit-label union occurs.

## Exact invariances

1. **Fibre sheets retained.**  Distinct source points with one endpoint remain distinct terms in
   every covariance integral.  Under coarea disintegration, all sheets contribute with their
   source density and inverse intrinsic Jacobian.
2. **Duplicate labels removed.**  Repeating circuit descriptions does not change `S`, hence changes
   neither `h` nor `K_(r,Z)`.
3. **Occupied endpoint image retained.**  Different occupied projective endpoints can enlarge the
   Veronese span and its compressed covariance even when label count is unchanged.
4. **Exact returns removed once.**  At `r>0`, an exact-return residual is zero; adjoining zero does
   not change `S`, `h`, or `K_(r,Z)`.
5. **Observer-coordinate duplication removed.**  `K_(r,Z)` is intrinsic to an orthonormal basis of
   the occupied subspace, not an arbitrary repeated reporter frame.

## Sharp boundary

This theorem closes the representation and complete-union problem.  It does not yet prove that
`K_(r,Z)(mu)` decays for the ordinary fixed-`q` Gaussian local-Hamiltonian ensemble.  The remaining
local-physics input is now exact and smaller: bound one compressed quenched covariance collision at
growing replica order.  A proof may exploit Pauli Hall expansion, replica cavity contraction, or a
source-only moment comparison; it may not return to minimum spectral gaps or targetwise unions.

## Novelty discipline

Finite-dimensional Parseval, Hilbert--Schmidt Cauchy--Schwarz, and the Ky Fan viewpoint are
classical.  The candidate new contribution is their selector-free composition with the
return-removed occupied Veronese image for autonomous recurrence/complexity.  Current label is
`[APPLICATION NOVELTY UNVERIFIED]`; no standalone novelty claim is authorized by this card.

## Lean target

- Module: `GaloisForLFunctions.HTGeometry.QuenchedReplicaIncidenceCovarianceLaw`
- Capstone: `quenchedReplica_incidenceCovariance_bound`
- Span extensionality: `replicaTargetIncidenceCollision_eq_of_span_eq`
- Event invariances: `completePureStateTargetCapture_duplicated` and
  `completePureStateTargetCapture_withZero`
- RHS invariances: `replicaTargetIncidenceCollision_duplicated` and
  `replicaTargetIncidenceCollision_withZero`

## Lean verification

- Direct `lake env lean` check: PASS.
- Final `lake build GaloisForLFunctions.HTGeometry.QuenchedReplicaIncidenceCovarianceLaw`: PASS,
  8657 jobs.
- Axiom audit of capstone, span extensionality, and return-removal theorems: only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Area umbrella import: wired through `GaloisForLFunctions.HTGeometry`.
- Global lint reaches the new module and reports no error in it.  Repository lint remains red on
  unrelated concurrently added, unwired `RHTower.Prolate*`, `ConstrainedProlate*`, and
  `SlepianKernelScaledFubini` modules.

## Honest frontier after proof

Representation problem named in this card is closed.  Brown--Susskind is not.  Exact next input is
a growing-replica decay theorem for `replicaTargetIncidenceCollision` under the ordinary fixed-`q`
Gaussian local-Hamiltonian law, strong enough to beat occupied shallow-circuit Hilbert growth.
