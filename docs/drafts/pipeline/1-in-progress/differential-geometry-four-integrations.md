# DifferentialGeometry: four geometric integrations

- **Started:** 2026-09-28
- **Status:** In progress; Bochner/Weil integration complete at the stated scope, three integrations still pending.
- **Objective:** Implement all four suggestions from the geometry/topology RH audit.
- **Source pin:** `qinz1yang/differential-geometry`, `7a48598d35109aa99d1cc678e2724c213cdf4ff3`.
- **Local toolchain:** Lean/mathlib 4.32.2; upstream pin uses 4.33.1.
- **Prior assessment:** `../0-backlog/differential-geometry-rh-mechanism-audit.md`.

## Requirements and completion evidence

1. **Bochner / Weil:** implement actual operator identities retaining prime coefficients,
   Gamma, compression/boundary and pole contributions; connect to the constrained source
   and existing edge-kernel rigidity. Investigate the remaining sign at first contact.
   A constant-rate toy identity or another assumed-positivity certificate alone does not
   complete this item. Record exactly which arithmetic premise remains open.
2. **Curvature / charge:** implement the geometric bulk/boundary identity and regularized
   divisor/charge machinery, including a concrete singular-limit calculation; connect it
   to the existing winding/completion interfaces. Preserve the boundary and defect terms.
   Attempt the arithmetic action comparison; topology or weak compactness alone is not
   a proof of that comparison.
3. **Poisson / Green:** integrate smooth Poisson existence with its actual regularity proof
   on compact connected boundaryless manifolds; construct the mean-zero linear Green
   inverse and discharge both inverse premises in the existing endpoint-dressing theorem.
   Do not substitute an assumed solution certificate or a finite-dimensional toy model.
4. **De Rham / periods:** integrate actual smooth exterior calculus, its cochain complex
   and pullbacks, and relevant low-degree Hurewicz results; construct adapters to local
   cohomology/period geometry with concrete manifold instances. An abstract square-zero
   complex alone does not complete this item.

For each item: source provenance, dependency-closed paper argument for new mathematics,
targeted compilation on the local toolchain, standard-axiom audit, umbrella registration,
and appropriate lint/index checks. No RH theorem may be claimed without its arithmetic
premises actually proved. Implementing research machinery is distinct from solving RH.

## Work plan

- [x] Re-read current instructions, audit, toolchain, and local consumer interfaces.
- [x] Confirm current upstream migration history and local compatibility gap.
- [x] Compute the exact upstream dependency closure for all four endpoints.
- [ ] Vendor/backport necessary sources with license/provenance and a reproducible manifest.
- [x] Implement and verify Bochner/Weil integration.
- [ ] Implement and verify curvature/charge integration.
- [ ] Implement and verify compact Poisson/Green integration.
- [ ] Implement and verify de Rham/period integration.
- [ ] Audit all four requirements against current files and build evidence.

## Decisions and constraints

- Preserve the local toolchain and unrelated worktree edits.
- Prefer a shared pinned dependency closure to duplicate incompatible manifold definitions.
- Serena symbol access rejects the ignored `formal/` tree; use exact `rg` and file edits.
- `update_plan` is not exposed in this session; this card is the persistent work tracker.
- Do not stop at the already-compiled four scratch declarations from the assessment.

## Progress log

### Initial implementation turn

Goal status active. Upstream migration commit `d697e1c9cb00b720b5493f3bf2dea17e319c374d`
is dated 2026-08-28. Shared dependency sizing and compatibility work starts before adapters.

The exact union closure is 1,284 upstream modules / 447,769 lines. Individual closures:
Bochner 200; integrated mixed tensors 314; conformal Gauss–Bonnet 295; regularized
Gauss–Bonnet 470; weak energy lower semicontinuity 363; Poisson existence 523; de Rham
33; low-degree Hurewicz 403. Every external import exists in installed Mathlib/Batteries.
The source closure scan found no proof-debt keywords in active code.

Vendored that closure under `formal/vendor/differential-geometry`, preserving namespaces,
source hashes, Apache license, applicable nested licenses and upstream NOTICE. Added a
local path dependency. `lake --old update DifferentialGeometry` succeeded; existing git
dependency revisions are unchanged in the lockfile.

First de Rham build compiled 22 upstream dependency modules and found three compatibility
sites: `Tensor/Multilinear/Bundle/Fiber`, `Bundle/TangentSpace`, and
`Tensor/Alternating/Shuffle/Derivative`. Local backport probes are in progress. No endpoint
has passed yet, and the goal remains active.

## Bochner adaptation: paper calculation to formalize

For finitely many commuting shifts `T_i`, rates `r_i(x)`, and real `f`, put
`D_i f(x)=f(T_i x)-f(x)`, `Lf=Σ_i r_i D_i f`,
`Γ(f,g)=(1/2)Σ_i r_i D_i f D_i g`, and `Γ₂(f)=(1/2)LΓ(f,f)-Γ(f,Lf)`.
Expanding both terms gives the exact identity

`Γ₂(f)(x) = (1/4)Σ_{i,j} r_i(x)r_j(x)(D_j D_i f(x))²`
` + (1/4)Σ_{i,j} r_j(x)(r_i(T_j x)-r_i(x))(D_i f(T_j x))²`
` - (1/2)Σ_{i,j} r_i(x)(r_j(T_i x)-r_j(x))D_i f(x)D_j f(T_i x)`.

Indeed `D_i(Lf)=Σ_j [r_j(x)D_iD_j f + D_i r_j·D_j f(T_i x)]`;
expanding `LΓ` and using `D_i f(T_j x)=D_i f+D_jD_i f` cancels the mixed term.
Unlike the constant-rate identity, this retains the complete rate-variation defect,
including aperture-cutoff and pole-profile ratios. Instantiation must use the literal
prime coefficients. The archimedean integral and full constrained form require their
own domain/integrability bridge; the finite identity alone does not complete item 1.

### Verified progress after the first build

`HTGeometry/JumpBochner.lean` compiles. Its unrestricted double-jump expansion and
commuting-shift square-plus-defect formula use only the standard axioms. A scratch
adapter using the literal von Mangoldt coefficients, signed logarithmic shifts,
aperture indicators and pole-profile ratios also verifies the support identity and
the pointwise transport from normalized jump energy to `ccmPrimePoleEdgeDensity`.
The integrated row identity passed. These declarations are now registered in
`RHTower/CCMPrimePoleJumpBochner.lean`, whose leaf build passed. Its dependency was
then narrowed from the kernel/recurrence endpoint to `CCMPrimePoleSchurDefect`;
verification of that import reduction and further energy identities is pending.

The tensor fibre retains its original normed structures. Canonical tensor-model
instances and bundle currying now compile in `Tensor/RSTensor/Defs.lean`.
Direct `pow_succ` replacements fixed three sign simplifications in
`Tensor/Alternating/Wedge.lean`. The full de Rham endpoint now passes:
`lake --old --log-level=error build +DifferentialGeometry.Tensor.Exterior.Cochain`
completed successfully (3,291 jobs, mostly cached). This includes actual exterior
calculus, `d² = 0`, pullback compatibility and the cochain construction.

`HTGeometry/ManifoldDeRhamCohomology.lean` now passes its leaf build. It supplies
actual forms and pullbacks in local cohomology, identity/composition laws on the
quotients, top-degree closedness and vanishing above tangent dimension. The
Poisson draft `/tmp/hgt-dg-poisson-green.lean` still awaits its upstream endpoint.

## Poisson and de Rham adapter arguments

Smooth real functions with zero Riemannian integral form a vector subspace on a
compact manifold: continuity gives integrability, and the integral is linear.
The geometric Laplacian is linear and its image has integral zero by the proved
divergence theorem. On the mean-zero subspace, upstream smooth Poisson existence
gives surjectivity and uniqueness gives injectivity. The resulting linear
equivalence has an inverse Green map; both compositions are identities. Applying
the existing endpoint-dressing theorem to this endomorphism ring discharges both
Green-inverse premises. Endpoint gains act on this normalized source space.

For de Rham, use the actual exterior derivative as the local cochain differential
and its proved square-zero theorem. Smooth pullbacks commute with it and therefore
induce local quotient-cohomology maps. An alternating `k`-form vanishes when `k`
exceeds tangent dimension because every `k`-tuple is linearly dependent. Hence all
top-degree forms are closed, and cohomology above manifold dimension is zero.
The entire de Rham adapter now compiles, including the corrected contravariant
composition order. Audited statements use only standard axioms.

For a concrete period instance, use the constant determinant two-form on `ℝ²`.
Its actual oriented rectangular integral is `ab`; small square integrals are
`t²`, giving normalized limit `1`. Rectangles `(a,1)` realize every real value,
so the generated period subgroup, its closure and its identity component are
all `ℝ`. This proves every field of the existing `PeriodGeometry` interface
without assuming either the carrier identification or the small-cell limit.
The two-form is closed by the dimension theorem. The entire scratch adapter now
passes, including the actual determinant form, its rectangular integral and all
`PeriodGeometry` fields. `HTGeometry/ModelDeRhamPeriods.lean` now passes its leaf
build. These are integrals over cells with boundary, not a
claim of nonzero de Rham cohomology on the plane.

### Further verified integration

`RHTower/CCMPrimePoleJumpBochner.lean` now proves that the normalized real and
imaginary jump energies integrate to the existing prime Schur energy. Both
orientations, cutoff indicators and pole-profile weights remain literal. The
narrowed import and complete extension passed the leaf build (12,903 jobs,
mostly cached).

The full consumer passed its scratch check, standard-axiom audit and leaf build
as `RHTower/CCMWeilJumpEnergy.lean`. It proves the unconstrained source
identity retaining the polar cross term, its constrained specialization, the
exact jump-energy deficit at zero source, and strict positivity from the exact
row bound plus existing two-prime rigidity. The row bound is still an explicit
arithmetic hypothesis. A combined import check caught a name collision with the
existing state-negation lemma; the new shift reversal is now named
`ccmPrimePoleEdgeEnergy_neg_shift`, and its leaf rebuilt successfully.

`RHTower/CCMPrimePoleJumpRates.lean` passes both its scratch check and leaf build:
actual rates at logarithmic coordinates simplify to rational expressions in the
multiplicative position.

The conformal Gauss–Bonnet dependency build has reached logarithmic-potential
distribution theory. `Analysis/InnerProductSpace/Laplacian` needed the available
name `ENat.coe_ne_top`, verified in a full-file scratch and then built. The next
failure exposed a set-predicate API rename across the closure. All 72 occurrences
in 33 modules were inspected and mechanically backported after a local Lean
name check. Every modified file carries a notice and is listed in
`formal/vendor/differential-geometry/LOCAL_CHANGES.md`. Further endpoint builds
will verify the entire affected closure.

The global lint gate was run during concurrent workspace changes. It reported
unreachable unrelated modules plus `CCMWeilJumpEnergy` created during that scan;
the current import for that module and all other new modules is present. The
authoritative gate must be rerun on the final state. No proof-debt error appeared.

`HTGeometry/RegularizedMonomialCharge.lean` passes its leaf build. Smoothness,
the exact radial derivative and the positive-radius multiplicity limit use only
standard axioms. Geometric bulk/boundary and winding connections remain pending.

The six-state negative-curvature polynomial and its strict sign for `log 2`,
`log 3` passed Lean in `/tmp/hgt-dg-six-point-bochner.lean`. The literal
cutoff-operator embedding is still pending; no actual-operator counterexample is
claimed from the finite graph alone.

## Curvature adaptation: paper calculation to formalize

For integer `m ≥ 0` and `ε ≠ 0`, set
`fε(z) = (1/2) log (|z|^(2m) + ε²)`. This is smooth on the whole plane.
Its radial flux on radius `R > 0` is
`R ∂r fε(R) = m R^(2m)/(R^(2m)+ε²)`.
The proved planar Green identity therefore gives
`∫_{|z|≤R} Δfε = 2πm R^(2m)/(R^(2m)+ε²)`.
The conformal metric has curvature-area density `−Δfε`. Its boundary curvature
integral is `2π(1 + m R^(2m)/(R^(2m)+ε²))`, so the total remains `2π`.
At each positive radius the Laplacian mass tends to `2πm` as `ε → 0`; subtracting
the formulas at two positive radii gives vanishing mass in their annulus. The
limiting mass equals `2π` times the existing winding of `z ↦ z^m`.
Thus singular concentration preserves the divisor charge but does not remove the
boundary correction or prove an arithmetic action bound. General divisor and Xi
specializations must retain their exact source hypotheses.

## Prime Bochner sign investigation

A numerical local-matrix probe found a negative direction. Reducing it to rational
values gives an exact candidate on the six multiplicative positions
`q = (1/2, 2/3, 1, 4/3, 3/2, 2)` with values `(8, −8, 6, −14, 15, 0)`.
Use aperture `a = log(21/10)`, so the literal prime indices are `2,3,4`, and evaluate
at `x = log 2`. All six positions are strictly inside the aperture. Only the rows
at `q = 2,1,2/3,1/2` enter the iterated energy at `log 2`.

Writing `l = log 2`, `m = log 3`, those jump rates are:

- `2 → (1, 2/3, 1/2)` with rates `(2l/3, 5m/9, l/2)`;
- `1 → (1/2, 2)` with rates `(3l/4, 3l/4)`;
- `2/3 → (4/3, 2)` with rates `(7l/10, 3m/5)`;
- `1/2 → (1, 3/2, 2)` with rates `(2l/3, 5m/9, l/2)`.

Expansion gives `Γ₂ = (125/3)l² − (13805/216)lm + (1696/81)m²`.
The inequalities `3l < 2m` and `5m < 8l` follow from `8 < 9` and `243 < 256`.
They bound this polynomial strictly below zero (approximately `−3.378716`).
This is a dependency-closed paper calculation. Its finite graph proof is now
Lean-verified; the embedding into the literal cutoff operator remains pending.

This concerns pointwise curvature of the prime jump generator, not the full Weil
form or RH. The positive infrastructure remains the exact square-plus-rate-defect
identity and its transport to Schur energy. Any successful curvature comparison
must account for the negative defect and the actual archimedean term; ordinary
nonnegative prime curvature cannot be silently assumed.

### Positive curvature estimate exposed by the obstruction

There is a stronger positive survivor than bookkeeping alone. For arbitrary
nonnegative finite jump rates (commuting shifts are unnecessary), write
`d(x)=Σ_i r_i(x)`, `a_i=f(T_i x)-f(x)`. Completing the two-step square gives

`Γ₂(f)(x) = (1/4)Σ_{i,j} r_i(x)r_j(T_i x)
  [f(T_j T_i x)-2f(T_i x)+f(x)]²`
` - (1/4)Σ_i r_i(x)[d(T_i x)+d(x)]a_i² + (1/2)[Lf(x)]²`.

Indeed the first two terms of `LΓ/2−Γ(f,Lf)` combine using
`b²−2ab=(b−a)²−a²`; the final term is `(Lf)²/2`.
Consequently `d(x)≤D` and `d(T_i x)≤D` give the quantitative bound
`Γ₂(f)(x)≥−D Γ(f)(x)`. For the actual prime operator the existing explicit
Schur row envelope can supply `D`, with the cutoff giving zero degree outside
the aperture. This avoids assuming nonnegative curvature and provides an
explicit lower-curvature estimate. `HTGeometry/JumpCurvatureBounds.lean` now
passes its leaf build and standard-axiom audit. It proves the exact identity and
the stronger bound `Γ₂ ≥ (Lf)²/2 − DΓ`. The literal prime-envelope specialization
also passed its scratch check and standard-axiom audit and is registered in
`RHTower/CCMPrimePoleCurvatureBounds.lean`, whose leaf build passes. Its degree bound
is proved using existing Chebyshev and reciprocal-Mangoldt estimates, so no new
arithmetic or nonnegative-curvature hypothesis is left in that estimate.

The upstream distributional logarithm and disk Green identity now compile after
the set-predicate backport. The conformal Gauss–Bonnet build progressed to module
44/295 (`Bundle/Equiv`), where `LinearEquiv.ofLinearMap` needs the local
`LinearEquiv.ofLinear` API. The replacement API was checked in a minimal scratch,
the local file was updated, and the endpoint build is continuing. The concrete mass/winding adapter has been split into a scratch
using only the already-compiled disk Green endpoint.

Both `CCMPrimePoleCurvatureBounds` and the new
`HTGeometry/RegularizedMonomialWinding.lean` now pass their leaf builds. The
latter proves the exact disk mass formula using the actual planar Green theorem
and its punctured-parameter limit equal to the existing monomial winding
integral's imaginary part. All audited statements use standard axioms.

The full logarithmic rate formula, including both cutoff decisions, passed a
scratch check and has been added to `CCMPrimePoleJumpRates`; the extended leaf
build also passes. The aperture `log(21/10)` and its exact six signed indices passed too.
An explicit smooth witness is available for the negative-curvature calculation:
`g(q)=1946−(156596/15)q+(42369/2)q²−(122059/6)q³+9258q⁴−(7998/5)q⁵`,
`f(x)=g(exp x)`. Exact rational interpolation verifies its six prescribed values;
the literal operator calculation in Lean remains pending.

`Bundle/Equiv` now compiles. The next compatibility failure in `Bundle/Section`
was the renamed local-frame coefficient API. The complete Section replacement
passed a scratch check; all seven Mathlib names were separately checked. All 93
affected uses in eight modules were inspected and backported, preserving the
upstream-owned exterior-derivative theorem names. Notices and file lists are in
`LOCAL_CHANGES.md`; the endpoint build continues from module 46/295.

The second authoritative global lint run still fails on unrelated unreachable
modules. It reports no error for any module in this integration, and no
proof-debt error. See `/tmp/hgt-dg-formal-lint-2.log` for that snapshot.

### Continued endpoint validation

`Tensor/Multilinear/Bundle/TensorProduct` now compiles after replacing its
instance-sensitive coordinate simplification with direct pointwise bilinearity
and zero proofs. The next section-permutation module exposes the same
transparency issue; a local reducibility probe is in progress. The complete
Hurewicz dependency build has also started independently of that geometry chain.

The first literal prime-curvature expansion exceeded the default heartbeat limit.
It is being split into four exact row evaluations for arbitrary functions,
followed by the small polynomial calculation. No heartbeat limit was raised,
and the finite-graph calculation is still distinguished from the unverified
literal-operator witness until this split proof passes.

The split literal prime-curvature calculation now passes its scratch check and
standard-axiom audit. `RHTower/CCMPrimePoleNegativeCurvature.lean` records the
actual aperture and rates, four exact row evaluations, an explicit smooth
polynomial-in-exp witness, the exact `Γ₂` value, and strict negativity. This
is no longer only a finite graph probe. It disproves blanket nonnegative
pointwise curvature for this prime generator; it does not disprove Weil
positivity or assert that the witness lies in a compactly supported source core.
Its positive survivor is the already-compiled quantitative lower bound in
`CCMPrimePoleCurvatureBounds`, including `(Lf)²/2`. The new leaf build is pending.

The negative-curvature leaf build and final existential axiom audit now pass.
The exact no-go and its already-formalized quantitative positive survivor are
recorded in `../5-failed/prime-jump-nonnegative-curvature.md`. The Bochner/Weil
integration meets its stated requirement: literal operator identity, actual
Schur energy transport, full prime/Gamma/pole source identity, kernel rigidity,
proved quantitative curvature estimate, and an exact test of the remaining
pointwise sign. The arithmetic row/Gamma comparison itself remains open.

The third global formal lint snapshot still fails only on unrelated unreachable
modules (18 in `/tmp/hgt-dg-formal-lint-3.log`); no integration or proof-debt error
is reported. Lexical research refresh recognizes the new negative-curvature
module and its 22 declarations (`/tmp/hgt-dg-prime-negative-index.json`). This is
source-index evidence, not a claim that all compiler metadata is current.

The geometry build reached module 69/295. Tensor products, slot permutations,
connection models, bundled covariant derivatives, and fixed-chart tensor
smoothness now compile. Remaining compatibility work includes an already-closed
simplification goal in `Bundle/PartialMfderiv/Basic`. The Hurewicz build reached
module 27/403 and exposed the renamed continuous-restriction API; all affected
uses are being audited and backported against the local Mathlib API.

The concrete singular-limit calculation is strengthened by the actual annular
integral: for `0<r≤R`, integrating the regularized Laplacian over
`closedBall 0 R \ closedBall 0 r` gives `2π(charge R−charge r)` and tends to zero.
This uses compact integrability and the set-integral difference theorem, not an
abstractly defined difference of masses. Both statements pass scratch checks
and standard-axiom audits and are added to `RegularizedMonomialWinding`; its
extended leaf build is pending. No general weak divisor-measure convergence
or arithmetic action bound is claimed.

## Arithmetic comparison attempt and exact remaining producers

Rechecked the current RW, TG, and HF frontiers against the geometry interfaces.
For TG the missing source statement is still an arithmetic decomposition
`E_base = E_residual + Tr T_D`, `E_residual ≥ 0`, or another source-derived
sub-unit bound on the integer charge. The geometric identities do not furnish it:

1. For the regularized monomial, the curvature bulk is `−2π charge` and boundary
   turning is `2π(1+charge)`. Their sum is always `2π`; the charge cancels.
   Thus normalizing the Gauss–Bonnet total does not bound the bulk defect.
   The proved disk and annulus limits retain arbitrary multiplicity `m`.
   For a Xi specialization one must control its actual regularized boundary
   flux or identify a nonnegative residual with the native prime/Gamma source.
   That arithmetic identification/bound has not been produced.
2. Weak lower semicontinuity has the wrong direction to supply the needed
   uniform upper budget. It permits singular concentration. Even after an
   integer charge is identified, a strict upper bound below one remains a
   separate source estimate. No weak-convergence certificate is being substituted
   for that estimate.
3. Compact mean-zero Poisson solvability addresses a different operator and
   domain from the arithmetic Meyer resolvent. The intended Green adapter
   discharges the inverse laws for the actual compact Laplacian. It does not
   identify that Laplacian with the arithmetic generator, construct a faithful
   Hodge completion, or prove the HF resolvent core (which the frontier identifies
   as RH-equivalent). Such an identification would need its own proof.

The anchored holomorphic passage theorem remains applicable only with its
uniform boundary-argument bound; non-holomorphic regularization does not prove
that bound or bypass the established holomorphic-passage obstruction. No new
conditional wrapper assuming any of these missing arithmetic producers was added.

`RegularizedMonomialWinding` with the actual annular integral and limit now passes
its extended leaf build. The missing vector-valued derivative chain rule was
proved from local `mfderiv_comp`, added to `Bundle/TangentSpace`, and its three
scalar-calculus uses now compile. The shared endpoint build continues through
curvature coordinates and metric tensor infrastructure.

### Scope of the row-comparison corollary

The corollary `ccmRestrictedWeilSourceQuadratic_pos_of_exact_row_bound` is
state-specific and strictly stronger than retaining the full jump term. Write
`Arch = ‖u‖² + (2 gammaHardyPhaseRate(0)−1)‖f‖²` on polar-constrained states.
The native comparison is `rowPotential ≤ Arch + jumpEnergy`; the sufficient
corollary instead assumes `rowPotential ≤ Arch`. It is not a claim that this
stronger inequality holds uniformly over all states and apertures, nor an
RH-equivalent formulation. The identity and curvature estimate preserve the
jump energy precisely because dropping it can lose essential cancellation.

A further diagnostic under audit is fixed-support aperture growth: widening the
cutoff adds jumps to points where the function vanishes; those increase row
potential and edge energy together without adding nonzero translation pairing.
The prime powers of 2 alone suggest an unbounded row contribution while the
fixed source archimedean cost stays fixed. This is not yet a formal counterexample
to a global row ceiling, and no such global ceiling is an implementation claim.
The first-contact-specific arithmetic producer remains unproved.

The follow-up deep row-comparison search returned partial results with coverage
pending and source-only candidates; none supplies the needed comparison or a
verified counterexample (`/tmp/hgt-dg-row-comparison-audit.json`). No candidate
from that search was used as a proof. The sufficient row corollary now explicitly
documents its individual-source scope.

The combined ConformalGaussBonnet/Poisson/Hurewicz closure has 1,023 upstream
modules. A bounded frontier builder (`/tmp/hgt-dg-build-batched.py`) compiles at
most two independent modules per Lake invocation. It reached 124 verified/fresh
modules; geometry metric conformal, scalar calculus, gradient, tensor regularity,
and curvature trace dependencies pass. Endpoint and adapter validation is still
in progress; these dependency counts are not endpoint completion evidence.

Full pinned endpoint validation now uses `--all` (1,284 modules; manifest endpoints
plus the sphere topology endpoint, already in that closure). It reached module
183 before a Hessian-realization proof's final `rfl` found no remaining goal.
That redundant step was removed; the Riemannian volume definition module in the
same batch passed. Build resumes with at most two independent jobs, preferring
one geometry and one topology module when both are ready. A finite 1,800-second
guard avoids repeatedly interrupting active proof compilation at ten minutes.

### Exact classical-Laplacian defect at the singular parameter

A further dependency-closed paper consequence of the same regularization is
`logFactor m 0 z = m log ‖z‖` (including the totalized value at zero).
Away from zero this function is harmonic, so its classical Laplacian vanishes
almost everywhere and its disk integral is zero. In contrast, the regularized
disk integrals tend to `2πm`. Hence the exact failure of commuting this singular
limit with the classical Laplacian integral is the previously identified winding
charge `2πm`. This is a statement about the classical Laplacian; it does not say
the distributional Laplacian of the logarithm vanishes. These exact defect
statements pass the Lean scratch check and standard-axiom audit and are promoted
to `RegularizedMonomialWinding`; the extended leaf build passed (3,627 jobs,
54 seconds for the rebuilt leaf).

The positive distributional statement is also proved: for compactly supported
`C²` test functions `φ`, `∫ logFactor m 0 * Δφ = 2πm φ(0)`. Its paper proof
substitutes `m log ‖z‖`, extracts the constant, and applies the upstream planar
logarithmic-potential identity. The scratch proof and standard-axiom audit pass.
This distinguishes the classical almost-everywhere loss from the retained
distributional point charge without asserting general weak-measure convergence.

The full dependency frontier reached 186/1,284 before the sole missing
`mvfderivWithin_comp` use in Laplacian minimum theory. The exact within-set chain
rule now has a scratch-verified backport from local `mfderivWithin_comp`.

### Dependency-sensitive build validation

Inspection of this Lake version's `Build/Common.lean` and `Build/Module.lean`
showed that `--old` falls back to source modification time when dependency hashes
change. Consequently an unchanged child could have been reused after a parent
backport. The earlier `.verified` timestamp shortcut is not sufficient evidence
for such children. The new bounded pipeline checks actual artifact timestamps
against sources and direct imports and removes only a stale target's generated
vendor `.olean` before building it. Parents finish before children start; at most
two independent targets run. This forces affected port modules to be checked
against their current imports while retaining the installed Mathlib cache.
Final adapter builds will receive the same dependency audit.

The pipeline now records artifact hashes with a recursive source/import/config
fingerprint. Previously built artifacts are accepted only after their parents
are validated and when newer than all transitive source changes and current
direct parent artifacts; old `.verified` stamps are ignored. This preserves
valid cache results without overlooking an unchanged intermediate module.

The topology rebuild exposed two newer finite-tuple APIs in affine cone boundary
proofs. Both use sites now prove the face identities locally; the general
`Fin.cases` proof passed a minimal scratch check and standard-axiom audit.
Full-file validation proceeds in the dependency pipeline.

`AffineChains` now passes its full-file build after removal of one redundant
trailing tactic. The current guarded builder is
`python3 scripts/run_guarded.py --timeout 1800 -- python3 /tmp/hgt-dg-build-pipeline.py --all`.
Its dependency-sensitive pass has reached 117/1,284; the earlier batched builder
is retired. Endpoint completion remains pending.

At 150/1,284 validated modules, the machine reported 29% free memory and only two
Lean compilers (about 2.2 GiB combined RSS). Concurrency is now three independent
targets via `HGT_DG_BUILD_JOBS=3`; the guarded command and dependency ordering are
unchanged. Each Lean compiler still uses one worker thread.

The manifest/provenance audit found all 1,284 source modules present and 72
modified modules. Every modified module carries a local-change notice and is
listed in `LOCAL_CHANGES.md` (`/tmp/hgt-dg-source-audit.json`). The stricter build
has reached 173/1,284; this is dependency progress, not an endpoint pass.

The dependency-sensitive build reached 206/1,284 before an instance-inference
failure in `OpenExcision`. Passing the already-proved comparison directly to
`quasiIso_comp` resolves it; the full-file scratch check and standard-axiom audit
pass. No assumptions changed. A separate short pass is rechecking the de Rham
endpoint's six remaining stale modules before the full pipeline resumes.

That de Rham pass succeeded: all 33 upstream modules validate against current
dependencies, and the final `Tensor.Exterior.Cochain` endpoint build completed
successfully (3,291 jobs). Full endpoint validation resumes with three workers.

`OpenExcision` then passed its normal leaf build. The full pass has reached
246/1,284, including Riemann tensor/section identities, gradient regularity,
tensor metric coordinates, and sphere homology/rank dependencies. No further
endpoint or adapter completion is claimed at this checkpoint.

At 269/1,284, `LoopTopology` exposed two more uses of the newer `Joined.map` API.
The full-file replacement maps path witnesses explicitly and unfolds `Joined`
where the local simplifier needs it. Scratch/API and standard-axiom checks pass.
The next dependency run uses two compiler jobs: measured free memory fell to
11% amid other machine activity.

`LoopTopology` passes its normal leaf build. At 273/1,284, two identical API
failures in `CubeCompactification` prompted a broader path-mapping audit. Its
full-file replacement and standard-axiom audit pass. Four additional genuine
`Joined` uses in transport continuity and selected Van Kampen objects receive
the same verified witness mapping; their full-file checks remain pending.
The sphere pre/postcomposition callbacks already take actual `Path` arguments
under the local `ZerothHomotopy.lift` API and correctly remain unchanged.

The following strict builds now pass: cube compactification, transport continuity,
basepoint group transport, sphere naturality, sphere Hurewicz map and sphere
generator; Hessian trace realization, Laplacian minimum theory, Riemannian volume
properties and connection embedding. The embedding needed one final redundant
`rfl` removed after its linear derivative evaluation rewrite; its subsequent
leaf build passed (2,833 jobs). Full validation resumes after 305/1,284 modules.
The refreshed source audit finds 77 modified files, all with notices, and the
scoped `git diff --check` passes.

At 314/1,284, relative chain functoriality required using the unassociated
projection lemma after left reassociation. Its full-file scratch check and
standard-axiom audit pass. All original hypotheses and statements are preserved.

### Concrete sphere strengthening: paper argument

The cached lexical research query `Hurewicz sphere homology degree` with `--any`
and the `DifferentialGeometry` module filter returned no declarations or freshness
metadata. Direct source inspection supplies the following dependency-closed
argument. For a unit sphere in a four-dimensional Euclidean space, the actual
excision dimension shift identifies H₂ with H₁ of the pole hyperplane sphere.
That hyperplane has dimension three. The degree-one computation identifies its
H₁ with reduced H₀ of a second pole hyperplane sphere, whose ambient dimension
two makes it path-connected; its reduced H₀ is zero. Thus H₂(S³) is trivial.
The proved simply-connectedness of S³ and degree-two Hurewicz identify π₂ with
H₂, discharging the π₂ hypothesis of degree-three Hurewicz. Finally the actual
top-dimensional sphere homology calculation identifies H₃(S³) with ℤ. Their
composition yields an additive equivalence π₃(S³) ≃ ℤ at any basepoint.
This uses the upstream chosen generator, with no new orientation normalization
claim. Lean verification of this strengthening remains pending.

The two sphere vanishing lemmas pass Lean and standard-axiom checks: H₁ vanishes
when ambient finrank is at least three, and H₂ when it is at least four. Their
proofs use the explicit pole dimension calculation, the actual sphere homology
equivalences, and path-connected reduced H₀. The full build reached 320/1,284;
`LocalCharts` needed one redundant final tactic removed. Its complete scratch
check and standard-axiom audit also pass.

`HTGeometry/SphereLowHomology.lean` is promoted and registered; its normal leaf
build passes (3,021 jobs), following both scratch and standard-axiom checks.
The Hurewicz draft now includes an H₂-triviality-to-π₂-triviality producer and a
concrete π₃(S³) ≃ ℤ equivalence; those declarations remain unverified until the
Hurewicz endpoint compiles. The source audit reports 78 changed upstream files,
all with notices, and the scoped whitespace check passes. Memory headroom briefly
recovered to 73%, permitting the independent sphere leaf check alongside the two
pipeline workers; the pipeline itself remains at two workers.

The Green draft now proves constant-scalar Laplacian linearity directly from
`gradFun_const_smul`, `divergence_g_smoothSmul`, and vanishing derivative of a
constant. That theorem passes a standalone scratch and standard-axiom audit with
only the Laplacian basic import; no compactness or connectedness is needed for
this intermediate law. This replaces the draft's dependency on the later
elliptic product formula. The full Green construction remains pending.

The continuing dependency pass exposed the stronger existing upstream theorem
`integralSphereHomology_subsingleton` in `SphereHomologyVanishing`: every positive
degree other than the sphere dimension vanishes. The earlier cached lexical
search had missed it. The two newly added specialized sphere proofs duplicate
cases of that theorem, so their local file and umbrella import are removed.
The Hurewicz draft instead applies the full upstream theorem with `n=3`, `k=2`,
and ambient space `EuclideanSpace ℝ (Fin 4)`. The paper argument and earlier
scratch evidence remain valid, but the final adapter will rely on the stronger
upstream result and its pending dependency validation.

The dependency-sensitive pass reached 368/1,284, then encountered the newer
upper-triangular matrix API in `LinearOrientation`. Four predicate sites and the
two supporting lemma names are now backported to `BlockTriangular id`,
`det_of_upperTriangular`, and `gramSchmidtOrthonormalBasis_inv_blockTriangular`.
The API probe, complete scratch check, and standard-axiom audit of the public
positive-determinant homotopy theorem all pass.

An isolated check of the Green draft's mean-zero space caught missing explicit
`(M := M)` arguments to the volume measure and a continuity projection that must
use `f.contMDiff.continuous`. Both are corrected in the draft. The revised mean-zero
smooth-function submodule and integrability proof pass Lean and standard-axiom
checks. Their hypotheses no longer require connectedness, positive dimension,
or boundarylessness; Laplacian preservation retains boundarylessness, while the
Poisson inverse retains connectedness and positive dimension. The full inverse
proof still awaits the Poisson endpoint.

Prepared `/tmp/hgt-dg-build-adapters.py` for the final affected-adapter dependency
check; it takes explicit local module names and must not overlap the upstream
builder. It requires Python 3.12 here (`/opt/homebrew/bin/python3.12`) for `tomllib`.
The read-only graph preflight succeeds. The root package has no custom compiler
options; the script verifies that before treating the new path-dependency registry
entry as irrelevant to native modules with no geometry imports. It still checks
transitive source/import timestamps and records recursive fingerprints, and
invalidates affected artifacts if another session changes sources during a run.

The exploratory union includes 4,241 native modules, driven by the arithmetic
Bochner dependencies; these do not import the modified geometry package. Their
completed earlier checks remain applicable to our unchanged mathematical code.
The only current `CCMWeilJumpEnergy` diff is its two-line scope clarification.
Final forced checking therefore targets the affected geometric adapters rather
than repeating the already-passed arithmetic branch and its unrelated live edits.
`ModelDeRhamPeriods` has four native dependencies and `RegularizedMonomialWinding`
has 28; the Poisson and Hurewicz adapters are added when promoted. The main strict
upstream pass has reached 399/1,284; its source audit now records 79 changed files,
all present and carrying notices.

The strict upstream pass reached 444/1,284 before three older-rewriter failures
in relative Mayer–Vietoris. A final reflexivity step and explicit congruences of
the original quotient/homology maps resolve all three, with a full-file scratch
pass and standard-axiom audit. No new transparency override was introduced.

While that proof was checked, the affected de Rham/period branch completed its
strict adapter audit: all 37 reachable local/upstream modules validate, including
rebuilt `ManifoldDeRhamCohomology` and `ModelDeRhamPeriods`; the final endpoint build
passed (3,486 jobs). Its certificates can be reused while the branch stays unchanged.
The Hurewicz part of requirement four remains pending, so that checkbox stays open.

At 465/1,284, the amalgamated-product identity leg needed direct application of
its existing projection theorem, avoiding an incomplete identity-homomorphism
simplification on Mathlib 4.32.2. Full-file scratch and standard-axiom checks pass;
the change is promoted. A single-worker affected-dependency audit of
`RegularizedMonomialWinding` is running before the main pipeline resumes.
