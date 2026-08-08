# Return-excised optimal-design coarea law

- **ID:** `return-excised-optimal-design-coarea-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / quenched incidence-normalized coarea law
- **Parent:** `../3-formalized/return-excised-minimal-incidence-rank-law.md`
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN OPEN]`
- **Date:** 2026-08-08

## Open core

After a target-independent measurable return set is removed, existing Lean theorems retain every
surviving source fibre sheet and the occupied replica endpoint image.  The maximal-volume endpoint
skeleton still pays `h^2` against a uniform fixed-target replica-moment ceiling, while the minimal
incidence-rank law leaves one compressed pair action whose static-local-Hamiltonian decay is open.

The new target is the strongest possible targetwise reduction: replace basis selection by an
optimal probability design on actual occupied endpoints, and pay exactly one occupied-image rank.

## Frozen conjecture

Let `C` be a nonempty finite target set, let `v_c` be its positive-order replica endpoint vectors,
and let

```text
S = span_C {v_c : c in C},     h = dim_C S > 0.
```

There are weights `lambda_c >= 0`, summing to one, such that for every observer vector `u` and
every target `c`,

```text
|<u,v_c>|^2 <= h * sum_j lambda_j |<u,v_j>|^2.             (OD1)
```

Consequently, for every finite quenched source measure `mu`, every independently fixed measurable
return set `R`, every positive fidelity threshold `a`, and every replica order `r >= 1`,

```text
a^r mu|_(R^c)(E_a)
  <= h * sum_j lambda_j
       integral_(R^c) |<state(x)^tensor r,v_j>|^2 dmu(x),   (OD2)

mu(E_a)
  <= mu(R) + h * a^(-r) * sup_j M_r(j;R).                  (OD3)
```

The weights are supported on actual occupied endpoints and depend only on their replica geometry,
not on source labels or fibre multiplicity.

## Conjecturing protocol

### C0 -- Pauli-character/Hall rank controls the coarea mass

**Verdict:** `[FALSIFIED BY CORPUS NO-GO]`.

The corpus proves that one-local Pauli words of linear length already span the full operator
algebra.  Linear Hall expansion therefore cannot control the nonlinear complete circuit tube.

**Positive survivor:** optimize the nonlinear endpoint incidence itself.

### C1 -- maximal-volume endpoint basis is dimension-optimal

**Verdict:** `[FALSIFIED]`.

Maximal volume gives coefficient moduli at most one.  Cauchy--Schwarz then pays one factor `h` for
each target and another factor `h` for the number of skeleton moments.  The loss is not sharp:
for `h` orthogonal targets, the complete event is bounded by the sum of the coordinate moments with
no first factor.

**Positive survivor:** replace one basis by a probability design whose worst leverage is `h`.

### C2 -- optimal occupied-endpoint design

**Verdict:** `[PAPER-PROVED]`; exact Lean formalization is open.

For coordinates on `S`, maximize

```text
det M(lambda),   M(lambda) = sum_c lambda_c v_c v_c^*,
```

over the probability simplex.  Spanning makes the maximum positive.  Along the feasible segment
from a maximizer `lambda` to a point mass at `c`, the matrix-determinant lemma and one-sided
maximality give

```text
v_c^* M(lambda)^(-1) v_c <= h.                            (KW)
```

Weighted Cauchy--Schwarz then proves `(OD1)`.  This is the finite Kiefer--Wolfowitz D/G-optimal
mechanism; novelty is not claimed for `(KW)` itself.

### C3 -- improve `h` universally

**Verdict:** `[FALSIFIED; SHARP]`.

Take `h` orthonormal source sheets and the same `h` orthonormal targets, with uniform source mass.
At threshold one every source point is captured.  Every target moment is `1/h`, so a universal
coefficient smaller than `h` in `(OD3)` fails.

## Dependency-closed proof

Let `M` be the optimal design matrix.  The determinant variation above proves `(KW)`.  Since `M`
is positive definite, matrix Cauchy--Schwarz gives

```text
|<u,v_c>|^2
 <= (v_c^* M^(-1) v_c) (u^* M u)
 <= h * sum_j lambda_j |<u,v_j>|^2,
```

which is `(OD1)`.  Positive-order tensor factorization turns target fidelity at least `a` into
`|<u,v_c>|^2 >= a^r`.  Integrating the pointwise complete-union inequality over the restricted
original source measure proves `(OD2)`.  The set inclusion
`E_a subset R union (E_a intersect R^c)` pays return mass once, and the weights sum to one, giving
`(OD3)`.

No source quotient occurs.  Repeated source points with the same endpoint remain separate integral
contributions.  Duplicate target labels may be assigned zero weight or have their weights merged,
so the law depends only on the occupied endpoint image.  Exact-zero residual targets have zero
leverage and may be removed.

## Hostile audit

- The theorem is finite-dimensional and finite-target.  No continuum gate-set statement is
  authorized without a compact-design extension or a proved finite net.
- It reduces the ordinary-static-Hamiltonian core to a weighted average, or uniform ceiling, of
  genuine fixed-endpoint moments.  It does not prove those moments decay.
- Kiefer--Wolfowitz optimal design is classical.  Candidate novelty is only its sharp composition
  with return-excised growing replicas, occupied quantum-circuit endpoint image, and quenched
  fibre-sheet retention.
- The factor `h` is exact, but `h` may still grow too quickly.  Circuit-image Hilbert growth and
  static-local-Hamiltonian moment decay remain independent quantitative obligations.

## Lean formalization map

Proposed module:
`GaloisForLFunctions.HTGeometry.ReturnExcisedOptimalDesignCoareaLaw`.

- `exists_finiteOptimalDesign`: formalize existence, positive definiteness, and endpoint leverage at most
  coordinate dimension for a determinant-maximizing probability design.
- `finiteDesign_matrixCauchySchwarz`: formalize exact weighted matrix Cauchy--Schwarz bridge.
- `exists_finiteOptimalDesign_pointwise`: formalize simultaneous dimension-linear control of every endpoint.
- `finiteComplexInner_replicaTargetCoordinate_endpoint`: prove occupied replica coordinates preserve
  the physical tensor inner product against every actual endpoint.
- `exists_replicaTarget_optimalDesign_pointwise`: prove one actual-endpoint design controls the complete
  replica target family with one occupied-Hilbert-number factor.
- `measure_completeTargetCapture_le_optimalDesignMoments`: formalize return-excised quenched coarea bound on
  original source measure, retaining every fibre-sheet contribution.
- `measure_completeTargetCapture_le_hilbert_mul_fixedMoment`: formalize uniform fixed-target consequence with
  factor `h`, replacing the earlier `h^2` maximal-volume loss.
- `finiteOptimalDesign_dimension_factor_sharp`: formalize that orthonormal endpoints force every universal
  probability-design coefficient to be at least `h`.

## External comparison

Kiefer and Wolfowitz's equivalence theorem supplies the classical leverage mechanism.  Quantum
optimal-design literature applies related criteria to state estimation and tomography.  The
audited recurrence, circuit-complexity, frame-potential, and static-Hamiltonian papers did not state
`(OD2)--(OD3)` for a return-excised occupied Veronese circuit image.  This is separation evidence,
not a priority claim.

## Gates

- [x] Internal corpus and failed-route audit
- [x] Exact conjecture frozen before Lean
- [x] Counterexamples to C0, C1, and coefficient below `h`
- [x] Dependency-closed paper proof fully audited
- [ ] Lean proof of optimal design existence and leverage bound
- [ ] Lean proof of replica complete-incidence and return-excision capstones
- [ ] Targeted build and axiom audit
- [ ] Umbrella wiring
