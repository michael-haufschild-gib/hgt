# DifferentialGeometry: four geometric integrations

- **Started:** 2026-09-28
- **Status:** In progress; none of the four integrations is yet complete.
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
- [ ] Implement and verify Bochner/Weil integration.
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
