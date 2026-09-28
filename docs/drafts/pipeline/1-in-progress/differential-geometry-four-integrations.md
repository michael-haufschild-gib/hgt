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
