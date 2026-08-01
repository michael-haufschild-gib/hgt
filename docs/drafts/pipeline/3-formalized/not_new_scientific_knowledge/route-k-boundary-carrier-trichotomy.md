# Route K boundary-carrier trichotomy

- **ID:** ROUTE-K-BOUNDARY-CARRIER-TRICHOTOMY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[NOT NEW SCIENTIFIC KNOWLEDGE]` / route guardrail
- **Source:** `rh-current-frontier-map.md`, Route K; `xi-reciprocal-clifford-square-source-rh.md`
- **Statement:** A continuous full-domain Hausdorff boundary reporter that annihilates the cyclic
  Hedenmalm theta bulk on any completion in which ordinary `L²(R)` is dense must vanish; hence every
  nonzero Route K boundary carrier must break density, continuity/full-domainness, or bulk nullity.

## Goal

Close the remaining regular-completion escape hatch in Route K without assuming RH and identify the
strongest nontrivial architecture that survives.  This is not a proof of RH: it is a source-specific
classification of which Hilbert--Pólya completion mechanisms are still logically available.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, hostile attacks recorded below
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem(s), target module green, axiom audit clean
- [ ] 3 → 4  publication-ready: standalone paper and novelty audit

## State-of-the-art audit (2026-08-01)

Internal results already force the ordinary-`L²` theta radical to be dense, proper, nonclosed, and
sequentially nonclosable.  A jointly continuous translation-invariant `L²` metric is zero.  A
finite-rank self-adjoint dilation produces the Cauchy transform of `|XiC|²`, not unsquared Xi.  The
weight-one Clifford bulk closes to the free constant-coefficient square and supplies no arithmetic
determinant.  Finite-channel scalar-principal-symbol first-order models are pure gauge or finite
unions of arithmetic lattices.  Abstract scalar Weyl-function realization requires the Herglotz
sign that the prime--archimedean anti-Herglotz gate already proves RH-equivalent.

Primary literature reaches the same boundary.  Hedenmalm asks for, but does not construct, the
self-adjoint forms.  Connes--van Suijlekom obtain a conditional ground-state criterion.  The
Connes--Consani--Moscovici finite models retain a finite-to-Xi convergence problem.  Sierra's
self-adjoint boundary phase is selected locally from a chosen critical zero.  Boundary-triple
perturbation determinants explain how a Weyl function would produce a determinant, but do not
supply the Xi sign or a source construction.

## Heavy-conjecture ledger

### K1 — regular Hausdorff boundary cohomology

**Frozen conjecture.** There is a Hausdorff completion `B` of the ordinary `L²` theta carrier and a
continuous full-domain boundary reporter which kills all regular prime-tail/Hedenmalm bulk
primitives while retaining every Xi conormal.

**Hostile attack.** The translated theta source is cyclic in ordinary `L²`.  Any continuous reporter
which kills its linear span kills a dense set.  If `L²` has dense image in `B`, continuity and
Hausdorff separation force the reporter to vanish on all of `B`.  It therefore retains no nonzero
conormal.

**Verdict:** `FALSIFIED` for continuous full-domain reporters on dense completions.

### K2 — closed or unbounded boundary relation

**Frozen conjecture.** Replace the continuous reporter by a closed, densely defined boundary
relation whose transpose contains every Xi conormal and whose resolvent is compatible with one
self-adjoint realization.

**Hostile attack.** If the relation extends continuously across the `L²` bulk, K1 kills it.  If it is
genuinely unbounded or partial, its domain/common-resolvent invariance and nonannihilation of every
Xi conormal are precisely the existing limiting-absorption/common-domain core.  Self-adjointness
then makes a nonzero transpose eigenfunctional possible only at a real quadratic parameter; proving
that all source conormals land is already the RH-bearing step.

**Verdict:** `CIRCULAR AS AN INDEPENDENT RH PRODUCER`; survives only as an explicit successor
source-landing problem outside the retired regular-completion route.

### K3 — finite-rank or finite-channel source coupling

**Frozen conjecture.** Couple the free Clifford square to finitely many literal theta/prime channels
and identify its perturbation determinant with Xi.

**Hostile attack.** Rank-one Friedrichs coupling yields a Weyl response built from `|XiC|²`, losing
Xi phase and multiplicity orientation.  Finite-channel local first-order couplings remain gauge
equivalent to free motion or yield finitely many arithmetic eigenvalue lattices, incompatible with
Riemann--von Mangoldt growth.

**Verdict:** `FALSIFIED` in the specified finite-rank/local class.

### K4 — prime-marked singular determinant

**Frozen conjecture.** A source-defined infinite-rank singular or trace-class correction of a
Riemann--von Mangoldt skeleton has perturbation determinant exactly Xi and one fixed self-adjoint
domain.

**Hostile attack.** Existing no-go theorems do not kill this architecture.  However, self-adjointness
plus an exact Xi determinant would itself force all Xi zeros onto the real spectral axis.  No
independent source identity currently constructs the correction or proves determinant convergence.

**Verdict:** `SURVIVES OUTSIDE ROUTE K`, as the already isolated trace-class
determinant/conservativity core.  It must remain an explicit hard problem and new route, not be
relabeled as an achieved Clifford operator proof.

## Boundary-carrier collapse theorem `[PROVED HERE]`

Let `H` be the ordinary theta `L²` space, `v(a)` its translated source orbit, `j : H → B` a
continuous map with dense range into a Hausdorff topological vector space, and `q : B → Y` a
continuous linear reporter into a Hausdorff target.  If `q (j (v(a))) = 0` for every `a`, then
`q = 0`.

**Proof.** Let `L=q∘j`.  By hypothesis `L(v(a))=0` for every `a`.  Complex linearity gives
`L=0` on `span {v(a)}`.  Wiener cyclicity says this span is dense in `H`; continuity and Hausdorff
separation of `Y` therefore give `L=0` on `H`.  Thus `q` vanishes on `range j`.  That range is dense
in `B`, so continuity gives `q=0` on `B`.  This proves the collapse theorem.

For the positive survivor, take the contrapositive.  If `q≠0`, then either `range j` is not dense or
there exists `a` with `q(j(v(a)))≠0`.  Continuous linear maps are full-domain by definition.  Hence
allowing a nonzero reporter which still kills the complete cyclic orbit requires leaving this
category: the reporter must be partial/discontinuous, or the boundary carrier must cease to be a
dense completion of ordinary `L²`.  This proves the stated architecture trichotomy.  ∎

No numerical experiment is relevant to this topological implication.  Per task instruction
`No computations`, formal pre-certification is symbolic: each inference is a density/continuity or
linearity step with no analytic approximation hidden in the Lean statement.

## No-go closure

- **Exact killing theorem/mechanism:** continuity extends zero from the cyclic source span through
  ordinary `L²` and then through every dense completion.
- **Strongest positive survivor:** the three-way architecture law above; nonzero boundary data must
  be singular/partial, live beyond a dense `L²` completion, or retain a non-null source channel.
- **New insight:** the open Route K object cannot be a conventional Hausdorff completion plus
  continuous boundary quotient.  It must be an essential-boundary relation or a prime-marked
  infinite-rank determinant, and the all-zero landing/conservativity clause remains the RH-bearing
  core.
- **Status:** `[PROVED HERE] [FORMALIZED]`; generic and theta-source statements are unconditional.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/XiThetaBoundaryCarrierNoGo.lean`.

- `continuousBoundaryReporter_eq_zero_of_cyclic_denseRange` formalizes two-stage cyclic/dense
  collapse for arbitrary normed source, completion, and target spaces.
- `xiTheta_continuousBoundaryReporter_eq_zero` instantiates it with the actual completed theta
  translation orbit.
- `xiTheta_nonzero_continuousBoundaryReporter_forces_escape` formalizes the exact nonzero survivor.

`lake env lean GaloisForLFunctions/RHTower/XiThetaBoundaryCarrierNoGo.lean` passes.  Targeted
`lake build GaloisForLFunctions.RHTower.XiThetaBoundaryCarrierNoGo` passes.  `#print axioms` reports
only `propext`, `Classical.choice`, and `Quot.sound`.  Repository-wide source lint reaches this leaf
but, during the shared-workspace audit, is red only on unrelated concurrently added unwired modules.

This theorem is deliberately classified as a guardrail, not new mathematical science.  The stronger
source-specific new consequence used in Route K retirement is the independently formalized
arbitrary-Hilbert-target closed-graph theorem
`hilbertGram_l2PartialOperator_not_closable`.

## Log

- 2026-08-01 — created in 1-in-progress after internal-corpus and external-primary-source audits.
- 2026-08-01 — K1 and K3 falsified in exact scoped classes; K2 exposed as RH-bearing landing core;
  K4 retained as explicit singular determinant survivor.
- 2026-08-01 — boundary-carrier collapse and nonzero-reporter trichotomy proved on paper; promoted
  to `2-fully-proven` before Lean work.
- 2026-08-01 — generic and theta-source theorems formalized, umbrella wired, target build and axiom
  audit passed; promoted to `3-formalized/not_new_scientific_knowledge`.
