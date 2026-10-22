# DifferentialGeometry: four geometric integrations

- **Started:** 2026-09-28
- **Status:** 3-formalized; all four integrations complete at the stated scope. Upstream union and geometry checks pass; shared-worktree validation exceptions are recorded below.
- **Completed:** 2026-09-29
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
- [x] Vendor/backport necessary sources with license/provenance and a reproducible manifest.
- [x] Implement and verify Bochner/Weil integration.
- [x] Implement and verify curvature/charge integration.
- [x] Implement and verify compact Poisson/Green integration.
- [x] Implement and verify de Rham/period integration.
- [x] Audit all four requirements against current files and build evidence.

## Current checked interfaces

Paths below are relative to `formal/GaloisForLFunctions/`.

| Integration | Checked result | Remaining work or premise |
|---|---|---|
| Bochner / Weil | `RHTower/CCM/CCMPrimePoleJumpBochner.lean`, `CCMWeilJumpEnergy.lean`, `CCMPrimePoleCurvatureBounds.lean`: literal prime-jump identities, full source decomposition and quantitative defect bound. `CCMPrimePoleNegativeCurvature.lean` supplies a smooth negative-Γ₂ witness. | The native arithmetic sign comparison remains open. Both generic upstream Bochner/Weitzenböck endpoints now pass. |
| Curvature / charge | `HTGeometry/RegularizedMonomialCharge.lean`, `RegularizedMonomialWinding.lean`, `RegularizedMonomialCurvature.lean`: exact disk/annulus mass, distributional point charge, winding, actual metric bulk/boundary integrals and singular limits. | Complete at the stated scope. Generic regularized Gauss–Bonnet and weak-energy lower semicontinuity pass. No arithmetic sub-unit bound is proved. |
| Poisson / Green | `HTGeometry/CompactMeanZeroLaplacian.lean`, `CompactPoissonGreen.lean`, `CompactGreenEndpointDressing.lean`: actual smooth mean-zero Laplacian and Green inverse, both composition laws, L² reciprocity, exact Dirichlet energy/nonpositivity, and concrete endpoint dressing. | Complete at the stated scope. The full smooth Poisson producer passes; bounded, causal and mass-shifted inverses are not asserted. |
| De Rham / topology | `HTGeometry/ManifoldDeRhamCohomology.lean`, `ModelDeRhamPeriods.lean`, `GeometricHurewicz.lean`: actual exterior complex and pullbacks, concrete plane periods, low-degree Hurewicz maps/equivalences, sphere examples and H₂-based premise discharge. | Complete at the stated scope. No de Rham–singular comparison or arithmetic Hodge realization is claimed. |

Strict affected-import audits pass for de Rham/periods (37 modules), winding (40),
metric curvature (324), mean-zero Laplacian (108), compact Green/dressing (557), and Hurewicz (404). These counts
describe each import closure, not disjoint sets. Audited declarations use only
standard axioms. The complete 1,284-module upstream union and combined geometry import check now pass. Shared-worktree exceptions follow.

## Final validation and applicability

- All eight upstream endpoints and all 1,284 modules pass the strict dependency build;
  final combined endpoint build succeeds (5,463 Lake jobs). The 105 modified files carry
  notices; original hashes, import edges and all four license/NOTICE files are audited.
- The combined import probe includes all eight endpoints plus the native manifold,
  period, Hurewicz, curvature and Green adapters. All 18 final axiom audits use only
  `propext`, `Classical.choice`, `Quot.sound`.
- All eleven native geometry adapter closures retain current source/dependency
  certificates. The five arithmetic adapters retain their earlier targeted build and
  axiom evidence. A final 5,286-module closure scan checks 2,804 modules and identifies
  47 pre-existing stale roots, with 2,435 downstream modules uncertified. Eleven roots
  have sources newer than their artifacts; the others have newer dependency artifacts.
  This is not evidence of a fresh full arithmetic-closure build.
- `scripts/formal_tools.py index` succeeds and refreshes all three generated documents
  and the search database. `scripts/formal_tools.py lint --check-generated` reports zero
  proof debt, current generated files and no integration wiring error; it exits 1 for
  14 unrelated unreachable modules. These are preserved shared-worktree changes.
- Detailed declaration-level axiom results, source/configuration fingerprints and the
  complete unrelated gate findings are in
  `formal/vendor/differential-geometry/validation.json`. Provenance includes a normal
  endpoint rebuild command. Scoped whitespace checks pass.

The RH frontier remains the actual arithmetic sign/action comparison or a faithful
arithmetic geometric realization. The prime jump generator has a formal smooth
negative-Γ₂ witness and a proved quantitative defect bound. Compact geometric Poisson
solvability discharges the two Green inverse premises, but does not construct an
arithmetic or causal Green operator. Singular monomial charge, exact metric bulk/boundary
formulas and their limits preserve the boundary correction. Hurewicz supplies genuine
homotopy/homology premise discharge; de Rham–singular comparison and an arithmetic Hodge
realization remain outside this implementation.

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
`RHTower/CCM/CCMPrimePoleJumpBochner.lean`, whose leaf build passed. Its dependency was
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

### L² symmetry and energy refinement

For smooth mean-zero functions on the compact boundaryless manifold, define
`B(f,h) = ∫ f h dvol` and `D(f,h) = ∫ g(∇f,∇h) dvol`.
Both pairings are symmetric. The proved first Green identity gives
`B(f,Δh) = -D(f,h)`, hence `B(Δf,h) = B(f,Δh)` and
`B(f,Δf) ≤ 0`, since the metric makes the Dirichlet integrand nonnegative.
Once the smooth mean-zero Green inverse exists, substitute `f=Gq`, `h=Gr`
and use `ΔG=id`: `B(Gq,r)=B(q,Gr)` and
`B(Gq,q)=-D(Gq,Gq)≤0`. These are pairing symmetry and quadratic-energy laws;
no unbounded-operator self-adjointness, bounded extension or causal inverse
is inferred. This dependency-closed calculation is ready for Lean checking.
Prior lexical searches for Green reciprocity and mean-zero Green found the
existing interval Neumann and causal/arithmetic interfaces; the new adapter
uses the actual compact-manifold divergence and Poisson producers.

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

`RHTower/CCM/CCMPrimePoleJumpBochner.lean` now proves that the normalized real and
imaginary jump energies integrate to the existing prime Schur energy. Both
orientations, cutoff indicators and pole-profile weights remain literal. The
narrowed import and complete extension passed the leaf build (12,903 jobs,
mostly cached).

The full consumer passed its scratch check, standard-axiom audit and leaf build
as `RHTower/CCM/CCMWeilJumpEnergy.lean`. It proves the unconstrained source
identity retaining the polar cross term, its constrained specialization, the
exact jump-energy deficit at zero source, and strict positivity from the exact
row bound plus existing two-prime rigidity. The row bound is still an explicit
arithmetic hypothesis. A combined import check caught a name collision with the
existing state-negation lemma; the new shift reversal is now named
`ccmPrimePoleEdgeEnergy_neg_shift`, and its leaf rebuilt successfully.

`RHTower/CCM/CCMPrimePoleJumpRates.lean` passes both its scratch check and leaf build:
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
`RHTower/CCM/CCMPrimePoleCurvatureBounds.lean`, whose leaf build passes. Its degree bound
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
standard-axiom audit. `RHTower/CCM/CCMPrimePoleNegativeCurvature.lean` records the
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

Inspection of `HurewiczTwoAdditivity` and `CubeSphereGenerator` shows the actual
degree-two/three Hurewicz multiplication laws need only a topological space and
basepoint. The draft now constructs both additive homomorphisms at that generality,
using those laws directly. Simply-connectedness and π₂-triviality are scoped to
the isomorphisms that require them. This is a source-derived hypothesis reduction;
Lean validation of the whole Hurewicz draft remains pending its imports.

The affected winding/charge branch completed its strict adapter audit: all 40
reachable local/upstream modules validate, including the required Böttcher
rebuilds and the extended `RegularizedMonomialWinding`; the final endpoint build
passed (3,627 jobs). Its disk/annulus limits, classical singular defect and
positive distributional point-charge identity are checked against current
imports. The curvature-metric endpoint is still pending, so item two remains open.

The main pass reached 483/1,284 and found a redundant final `rfl` in based
Van Kampen. Its removal passes a full-file scratch check and standard-axiom audits
of pointed delooping and the fundamental-group pushout theorem. The earlier
`SelectedObjects` path-witness backport also passes its normal build.

A separate local-toolchain API probe verifies the exact `Additive` homomorphism,
`AddEquiv.ofBijective`, and subsingleton-transfer patterns used by the pending
Hurewicz adapter. This validates its algebraic packaging, not the still-pending
Hurewicz endpoint imports.

At 486/1,284, three Van Kampen amalgamated-product equalities required direct proof terms rather than simplification across carrier/group aliases. The complete scratch file and standard-axiom audit of `fundamentalGroupEquivAmalgamatedProduct` pass, and the strict two-worker pipeline has resumed. The source audit immediately before this change found all 1,284 sources and notices for all 82 then-modified files.

The strict pass reached 495/1,284, including `FundamentalGroup.Sphere`. Euler-characteristic simplification needed an explicit definitionally equal integer-sum target; full-file scratch and standard-axiom checks pass. The curvature draft now also states actual metric bulk and boundary limits along any everywhere-nonzero parameter family tending to zero; these remain uncompiled until the metric endpoint is available.

At 507/1,284, all three Euler-characteristic compatibility changes pass, as do relative homology and its maps. `CokernelHomotopy` then required the general positive-dependent-conditional simplification rule in its two degree cases; complete scratch and standard-axiom checks pass. An exhaustive homology search records analogous unmodified sites in subdivision homotopy/restriction/singular/support files; their actual builds remain pending.

The strict pass has reached 534/1,284. The cone boundary backport and all four subdivision homotopy modules pass, including all eight inspected dependent-conditional fixes. The source audit records 91 modified upstream files, with no missing sources or notices. The three remaining integration checkboxes stay open pending their endpoints and adapters.

The strict frontier has reached 568/1,284, including relative excision, punctured-sphere homology, triangle cone homotopy and cubical filling prerequisites. Monomorphism preservation for simplicial chains is now proved degreewise from existing coproduct monicity; pushout exactness uses explicit biproduct reassociation. Both complete modules pass their normal dependency builds, and the local Mathlib API probe passes.

For the strengthened curvature draft, let any parameter family ε(a) be everywhere nonzero and tend to zero along a filter. The finite-radius bulk identity equals −2π times `charge m ε(a) R`; continuity of the charge limit therefore gives −2πm. The unit-circle boundary identity similarly tends to 2π(1+m). Their sum retains 2π, so the charge cancellation persists in the singular limit. These are actual metric integrals in the drafted statements, with no metric required at the singular parameter itself. Lean validation remains pending the conformal endpoint.

Checkpoint: strict upstream frontier 602/1,284; second covariant derivatives, three-cycle realization and higher-simplex filling machinery pass. The main two-worker pipeline remains live in session 34109, entering L² pairing and tetrahedron/cube-sphere comparison. No additional endpoint checkbox is closed yet.

`ConformalGaussBonnet` passes in the strict pipeline, with all 295 dependencies validated. `HTGeometry/RegularizedMonomialCurvature.lean` is now promoted and registered after a full scratch check: arbitrary-radius actual metric bulk integral, unit-circle actual boundary integral, and both singular limits along any nonzero parameter family. All five audited declarations use only standard axioms. The boundary proof uses restricted scalar simplification before ring normalization. Its final strict local-adapter audit is queued for the next upstream-build boundary; generic regularized Gauss–Bonnet and weak-energy infrastructure remain pending.

The strict curvature-adapter audit passes all 324 reachable local/upstream modules; its final endpoint build succeeds (4,067 jobs). The main upstream run reached its 1,800-second guard at 665/1,284 and exited124 after cleaning its owned process group; unfinished targets retain pending markers and will rebuild.

`CompactMeanZeroLaplacian.lean` is promoted and registered after a full scratch pass with only the geometric Green-identities import, and a standard-axiom audit of the Laplacian endomorphism. It factors the already-checked mean-zero submodule and linear Laplacian out of the pending Poisson inverse, avoiding that heavy dependency for basic operator use. The Green draft now imports this shared operator module. Connectedness and positive dimension remain scoped to the inverse. Its strict adapter audit is running before the upstream pipeline resumes, now prioritizing the shorter Hurewicz branch ahead of Poisson.

The strict `CompactMeanZeroLaplacian` adapter audit passes all 108 reachable modules; the final endpoint build succeeds (3,669 jobs). The curvature adapter’s 324-module audit and this operator audit are both complete. The remaining Poisson inverse and low-degree Hurewicz adapters still await their upstream endpoints. Scoped diff checks pass.

Strict upstream frontier: 699/1,284. Orientation transport and manifold orientation pass after an explicit identity-tangent-map evaluation backport; the source audit now records 94 modified files, all present with notices. Degree-two Hurewicz additivity, local/chart orientation, De Giorgi foundations, whole-space Sobolev, weak derivatives, approximation and convolution pass. Main session54608 continues with Hurewicz prioritized. Remaining integration checkboxes stay open for the Poisson inverse, Hurewicz isomorphisms and outstanding generic geometry endpoints.

The Hurewicz draft now also exposes a generic homology-only criterion in degree three: for simply connected X, degree-two Hurewicz identifies π₂ with H₂; H₂=0 therefore supplies π₂=0, so degree-three Hurewicz gives π₃≅H₃. This reuses the drafted generic subsingleton-transfer lemma and introduces no new arithmetic or comparison assumption. The corollary remains uncompiled until the degree-three endpoint is ready.

The strict upstream run reached 772/1,284 and its 1,800-second guard cleaned up the owned process group. `HurewiczLowDegrees` and its full 403-module closure pass. An initial parallel adapter check was cancelled by its owned guard (exit143, no remaining process) when memory pressure spiked; the subsequent serial full scratch check passes.

`GeometricHurewicz.lean` is now promoted and registered: actual degree-two/three homomorphisms, low-degree equivalences, the generic H₂-vanishing criterion, π₂(S²)≃ℤ, and π₃(S³)≃ℤ. All four representative axiom audits use only standard axioms. Its strict local-adapter audit is running before the upstream build resumes.

The strict `GeometricHurewicz` adapter audit passes all 404 reachable modules; its final endpoint build succeeds (3,472 jobs). Together with the earlier current 37-module de Rham/period audit, this completes requirement four. The manifold exterior complex, functorial cohomology maps, concrete plane periods, Hurewicz homomorphisms/isomorphisms, sphere groups, and H₂-based premise discharge are all implemented and checked. No de Rham–singular comparison or normalized orientation-degree statement is claimed.

The upstream frontier has reached 791/1,284. To reduce repeated Lake setup while retaining strict recursive fingerprints, artifact hashes, forced stale-target rebuilds and pending markers, `/tmp/hgt-dg-build-validated-batches.py` now accepts dependency-ready batches under one Lake invocation. Current memory pressure keeps batch size at one; two-target scheduling has not been exercised. The previous builder was cancelled through its owned guard and exited143 before this replacement started. De Giorgi Poincaré, ball-extension foundations and higher Sobolev chain rules pass. Generic curvature/energy and smooth Poisson endpoints remain pending.

The two-target batch passed and observation confirmed a single Lean child under `LEAN_NUM_THREADS=1`. At frontier 794, that driver was stopped through its owned guard (exit143, process exit verified). `/tmp/hgt-dg-build-validated-waves.py` now groups up to twelve dependency-ordered modules in one Lake invocation: every stale artifact is removed before launch, Lake must rebuild missing parents before children, and successful module reports receive certificates only after their parents validate. Pending markers survive interruption. The driver also rejects concurrent source/configuration changes before certifying output. Initial wave passes chart transitions and smooth chart density, reaching 796/1,284; no extra compiler concurrency is introduced. A fresh source audit still finds 94 modified files and no missing sources/notices.

The first full twelve-module wave passed (8,800 Lake jobs), followed by ball-extension estimates, Sobolev–Poincaré and smooth Morrey estimates, reaching 813/1,284. The driver was then stopped through its owned guard (exit143, process exit verified) to address repeated whole-Mathlib loading through `External/DeGiorgi/Common.lean`.

That prelude had `import Mathlib` and no mathematical declarations. A Lean metadata probe inspected every declaration in all 75 then-checked descendants and collected the defining modules of their actual Mathlib dependencies. Lean's import graph reduces this to 30 imports, including the tactic umbrella. The standalone reduced prelude passes and loads 5,295 modules versus the 10,406-module original Mathlib closure. This is an import change only, with no new theorem assumptions or compiler-limit changes. All 303 descendants are included in dependency-sensitive validation; the 75 already-checked descendants must rebuild before their certificates can be reused. The conformal Gauss–Bonnet, de Rham and Hurewicz closures are unaffected. New main session35009 starts at 738 unaffected certificates and has already rechecked the prelude, whole-space Sobolev, foundations, weak derivatives, witnesses, approximation, translation and mollification kernels. Source audit: 95 modified files, no missing sources or notices.

All 75 previously checked Common descendants have now rebuilt successfully, with renewed certificates under the reduced imports. No additional theorem-body edit was required. The strict frontier is back at 813/1,284, including smooth Morrey estimates, and continues into the remaining analytic proofs. The first four full waves took approximately 157–173 seconds each; later waves were slower under shared resource pressure, so only the measured import-graph reduction is claimed as a stable improvement. Mathlib's tracked checkout is clean and scoped diff checks pass.

The 1,800-second guard ended session35009 at 818/1,284 with exit124 and owned-process cleanup. Session56539 resumes the same strict wave driver. The frontier has reached 856/1,284: intrinsic/chart norm equivalence, scalar resolvent and spectrum, compactness, eigenbasis, spectral gap and Poisson solvability pass. Chart Laplacian formulas, weak derivatives, difference-quotient tests, Nirenberg substitution and coercivity also pass. The smooth-regularity producer and final Poisson existence endpoint remain pending; the Green draft is not promoted yet.

At 861/1,284, `MasterInequality/CrossBounds.lean` lacked `MemLp.integrable_sq` after removing the Mathlib umbrella. The lemma exists in local `Mathlib.MeasureTheory.Function.L2Space`, and its generic API probe passes. All 16 uses across seven modules were mapped: six are the failing file or its descendants; the independent `UniformDiffQuotBoundFromDomain/DataBounds.lean` branch also lacks the lemma in a targeted parent-import probe. Both files now import `L2Space` explicitly, with no proof-body changes. Source audit: 97 modified files, all sources/notices present. Session72898 resumes the strict driver; the full cross-bounds module and subsequent smooth/manifold/chart H² regularity modules pass, reaching 865/1,284. The independent data-bounds module and full smooth Poisson endpoint remain pending.

All seven modules containing the 16 square-integrability calls now pass, including both explicitly amended modules. The build also checks the full nonsmooth Nirenberg inequality, weak-solution approximation, local Laplacian H² regularity, the H² bootstrap, multiplication rules, Ricci frame identities and the Bochner orthonormal-frame trace. Session72898 ends at its 1,800-second guard with exit124 and owned-process cleanup at 927/1,284; the same driver is resumed. An exhaustive import audit compares both original and current sources against the manifest for all 1,284 modules: no baseline mismatches and no changed internal DifferentialGeometry import edges. Thus the manifest-based dependency validation remains applicable; local import changes only affect Mathlib dependencies.

The full 200-module pointwise `WeitzenbockIdentity` closure now passes, giving four checked upstream endpoints out of eight. The strict frontier reached 963/1,284, including Sobolev smooth representatives, differentiated chart residuals, Hessian pairing identification and polarized Bochner identities. Session11462 was stopped through its owned guard (exit143, process exit verified) at a wave boundary to check the lightweight energy refinement.

The new `CompactMeanZeroLaplacian` scratch passes without warnings. Its L² symmetry and nonpositivity theorems use only standard axioms. The first Green identity gives the exact negative Dirichlet pairing; positivity comes from the actual metric. These results are promoted with no connectedness or positive-dimension assumptions. The affected 108-module adapter audit is running. The pending Green draft now derives inverse symmetry and its exact negative Dirichlet energy, but those inverse declarations are not yet compiled or promoted.

The strengthened `CompactMeanZeroLaplacian` passes its strict 108-module audit and final endpoint build (3,669 jobs). The upstream wave build resumes. Its temporary driver now supports stopping after a completed wave, so subsequent adapter checks need not interrupt an active proof compilation.

The strict frontier reaches 999/1,284 with differentiated variational identities, third-order chart regularity, canonical derived data and the derived H² interior estimate checked. Session70590 exits75 only after completing its wave; its process exit is verified. Session96059 now targets the 523-module Poisson closure alone, starting from 483 checked dependencies with serial waves of32. This finishes the actual producer before checking the Green adapter; the remaining generic geometry endpoints follow afterward. The historical source-assessment card now links this ledger instead of describing all integrations as unimplemented.

`PoissonExistence` and its complete 523-module closure pass in session96059, including arbitrary-order chart regularity, Laplacian-domain powers and the smooth-representative producer. The final endpoint build succeeds (4,412 jobs); five of eight upstream endpoints are now checked, and the union frontier is 1,039/1,284. The Green draft is now being compiled against this actual producer. Its existing endpoint-dressing consumer has 31 local dependencies, which will be included in the strict adapter audit.

The full Green scratch now passes without warnings: Laplacian bijectivity, both inverse laws, L² reciprocity, exact negative Dirichlet energy, nonpositivity, and endpoint dressing. All five representative axiom audits use only standard axioms. The dressing proof uses `LinearMap.ext` to stop extensionality at the mean-zero vector, before pointwise evaluation. The production implementation is split into geometry-only `CompactPoissonGreen.lean` and `CompactGreenEndpointDressing.lean`, keeping the clock consumer's 31-module dependency chain out of the generic inverse. Both modules are registered. Their strict combined 557-module audit is running; the final union axiom probe now also covers the production Green and Laplacian energy laws.

The production Green/dressing audit passes all 557 reachable modules and its final endpoint build (9,212 jobs). It refreshes the current local consumer dependencies before compiling the dressing adapter. Requirement three is complete: actual smooth geometric Poisson solvability produces the normalized inverse, both composition laws and endpoint dressing; reciprocity and the exact negative Dirichlet-energy law strengthen the interface. Generic inverse use imports only the geometry core. No bounded, causal, mass-shifted or arithmetic realization is claimed. The remaining upstream union build resumes at 1,039/1,284.

At union frontier 1,066/1,284, six lemmas in `Analysis/Spectral/Tensor/CovGrad/Product/Scalar.lean` fail because the scalar-product definition unexpectedly retains `CompactSpace M` and `SigmaCompactSpace M` on Lean 4.32.2. An explicit signature probe confirms those dependencies. Replacing the support proof by direct `HasCompactSupport.mono` removes them and the unnecessary `T2Space` dependency; the two evaluation lemmas omit their now-unused Hausdorff assumption. The entire corrected file and three axiom audits pass without warnings. No additional premise is introduced. The exhaustive vendored search finds no explicit positional `@scalarSmul` or `@scalarSmul_toSection_apply` uses. The promoted backport carries a source notice and `LOCAL_CHANGES` entry. Source audit: 98 modified files, no missing sources or notices. Session89939 resumes the strict union build.

For the final generated-index refresh, the required `prompt-write` skill was found at `/Users/michael/.claude/skills/prompt-write/SKILL.md`; it and its GPT/file-authoring references were read. The refresh will preserve the existing generator and instruction text, updating source-derived lookup data. The skill's sequential-thinking tool is not exposed in this session; source/schema consistency and stale-reference review will be performed directly.

The scalar-product module and its downstream covariant-gradient, lowering, trace and integration-by-parts modules pass the normal strict build. The integrated mixed-tensor Weitzenböck endpoint and its full 314-module closure pass at union frontier 1,087/1,284. This is the sixth checked upstream endpoint; regularized Gauss–Bonnet and harmonic-map weak lower semicontinuity remain. The broader positional-call search, including fully qualified names and both evaluation lemmas, finds no affected explicit `@scalarSmul` uses in either the vendored closure or the native Lean tree. The build has entered manifold area and metric projection infrastructure, reaching 1,093/1,284.

The next wave reaches 1,121/1,284 and stops on one residual definitional equality in `Geometry/Connection/SourceSectionPairing.lean`. A single `rfl` after chart-representation simplification passes the complete scratch file and a standard-axiom audit of `sourceSectionCovariantDerivative_chart`, without warnings. The promoted edit preserves every statement, hypothesis and existing compiler option. Source audit: 99 modified files, no missing sources or notices. Session14934 resumes the strict union build. Six upstream endpoints remain complete; regularized Gauss–Bonnet and weak-energy lower semicontinuity are still pending.

Direct review of the generated indexes confirms that the new Green modules and mean-zero energy declarations are absent, and older mean-zero entries have stale line references. The final refresh must update those source-derived records while preserving the existing lookup schema and the gap report's explicit distinction from a mathematical proof ledger.

The source-section backport and the downstream disk metric/conformal connection chain pass. The next wave reaches 1,152/1,284 before `DiskBoundaryAcceleration.lean` exposes a simplifier type-correctness mismatch between fibres at `U (c θ)` and `(U ∘ c) θ`. Restating the sum in the canonical fibre before applying bilinearity passes the complete scratch file and standard-axiom audit, without warnings. No assumptions or compiler settings change. The promoted source notice and compatibility entry bring the audit to 100 modified files, with no missing sources or notices. Session74961 resumes the strict union build with 132 modules still unverified.

The boundary-acceleration backport passes the normal strict build. The next complete wave also checks smooth ODE flow, geodesic existence/rescaling, exponential-map smoothness and its local diffeomorphism theorem, reaching 1,184/1,284. Session74961 continues into normal coordinates and metric pullbacks at 1,188/1,284; no additional compatibility edit has been required. The two final generic endpoints and final union audit remain open.

The strict union reaches 1,240/1,284 and stops on product-model aliases in `TwoParameterFields` and mixed composition/basepoint tangent fibres in `CurveUnitReparametrization`. Direct proof terms at three alias boundaries, deletion of one redundant reflexivity step, and explicit canonical-fibre targets resolve both files. Complete scratch compilations and six representative axiom audits pass without warnings; statements, hypotheses and compiler settings are unchanged. Both promoted backports carry source notices and compatibility entries. The strict union build resumes for the remaining 44 modules.

At 1,266/1,284, downstream curve-curvature reparametrization and disk boundary curvature expose the same composition/basepoint alias issue. Canonical-fibre targets and an explicit zero-velocity rewrite resolve both complete scratch files; both endpoint axiom audits contain only standard axioms, with no warnings. Source audit now records 104 modified files, all with notices. The source-integrity audit confirms all 1,284 original hashes against the pinned upstream checkout, no changed internal import edges, and exact preservation of all four license/NOTICE files. The installed Mathlib checkout is clean. The final 18 modules resume in the strict union build.

`RegularizedGaussBonnet` and its full 470-module closure pass at union frontier 1,272/1,284. The normal builds verify both latest curvature backports and the intervening trace-density/boundary identities. Seven of eight upstream endpoints are now checked; only harmonic-map weak energy lower semicontinuity remains, followed by the combined endpoint/adapter audit and final generated-index gate.

The frontier reaches 1,280/1,284, including quadratic energy lower semicontinuity and Euclidean gradient-column integration. `LocalChartDistance` needs the older Mathlib `setOf_riemannianEDist_lt_subset_nhds` name and explicit evaluation across the chart-derivative codomain alias. Its full scratch file, local API probe and two axiom audits pass without warnings after specifying the API probe universes. Both theorem proofs retain their original assumptions and statements. Source audit: 105 modified files, all with notices. The final four modules resume.

Final completion: the remaining local chart-distance, smooth Lipschitz, manifold
Rademacher and weak harmonic-map energy modules pass, followed by the combined
endpoint build. All eight upstream endpoints are checked. Explicit generic endpoint
imports are registered in `HTGeometry.lean`; all native modules remain registered.
The joint import/18-axiom probe passes. The generated indexes are reviewed for the new
Green/energy/Hurewicz declarations and source line references. Final lint and dependency
freshness limitations are recorded above, without claiming a clean unrelated worktree.
All four scoped implementation requirements are complete; this card moves to stage 3.
