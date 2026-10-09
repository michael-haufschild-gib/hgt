# Lift actual critical-value paths through a terminal collision

- **ID:** ORDERED-CRITICAL-VALUE-COLLISION-PATH-LIFTING-20261009
- **Stage:** 3-formalized
- **Type:** BRIDGE; paper proof and Lean audits complete
- **Parent:** `../1-in-progress/finite-planar-polynomial-realization.md`
- **Target:** A continuous ordered critical-value path on [0,1], distinct at every time t<1, has a unique continuous parameter lift through any prescribed initial realization, including its possibly collided endpoint.

## Corpus audit

The lexical query `proper finite fiber covering endpoint path lift` returned no indexed declarations. The actual regular critical-value covering and all-fiber finiteness are already formalized. `IsCoveringMap.existsUnique_continuousMap_lifts` gives lifts over the contractible half-open interval. `ProperFiniteFiberEndpoint` gives convergence from properness, a finite limiting fiber and connected filter bases. Installed `Topology/ExtendFrom` and `Topology/Order/ExtendFrom` give continuous extension from a dense interval once the endpoint limits are supplied. No web sources used; external novelty unverified.

## Complete paper proof [PROVED HERE]

Let b:[0,1]→C^(n+1) be continuous and injective as an ordered tuple for every t<1. Fix v₀ with B(v₀)=b(0). On J=[0,1), regard b as a continuous map into the distinct-value configuration space. J is convex, hence contractible, simply connected and locally path connected. Lift b uniquely through the proved covering B:RegularParameter→Configuration, with initial point v₀. Forgetting the regular-subtype tag gives a continuous parameter curve V:J→Parameter satisfying B(V(t))=b(t).

Extend V arbitrarily to a function f on R outside J. It is continuous on J, hence on (0,1), and tends to v₀ at 0 from the right. Its image B∘f tends to b(1) at 1 from the left, since it agrees with the continuous extension of b throughout (0,1). The left-neighborhood filter at 1 has a basis of intervals (a,1). Restricting that basis to intervals inside (0,1), then mapping by f, gives a preconnected basis. The proved proper finite-fiber filter theorem yields a parameter v₁ with B(v₁)=b(1) and f→v₁ at 1 from the left. Thus both endpoint limits exist with their required images.

Extend f continuously from (0,1) to [0,1] using the inspected `extendFrom` theorem. Its endpoint-value lemmas give v₀ at 0 and v₁ at 1; its interior-value lemma retains V. The resulting continuous map v satisfies B∘v=b at every point, by the interior identity and the two endpoint identities. This constructs the closed-interval lift, with no assumed parameter curve or endpoint.

For uniqueness, any second continuous lift lies in RegularParameter for t<1, since its B-values equal the distinct tuple b(t). Its restriction to J is therefore a lift through the same covering with the same initial value, and covering uniqueness makes the restrictions equal. Continuity into the Hausdorff parameter space extends equality from dense J to its endpoint. Hence the full closed lift is unique.

## Consequence and remaining obligation

Together with the root-transport square theorem, this constructs collision limits while preserving every target loop avoiding the entire moving critical-value set. The starting polynomial and value path are explicit input data; existence of the parameter deformation is now the theorem's conclusion. Prescribed planar monodromy and finite planar completions of actual Xi pieces still require construction; this bridge does not assert either of them or RH.

- 2026-10-09 — `ProperFiniteFiberIntervalExtension.lean` passes its production leaf build (2 theorems). The actual closed-lift theorem is written and under Lean verification; its first check exposed subtype presentation issues, now corrected. Next combinatorial target and complete paper proof: `../3-formalized/tree-factorization-hurwitz-transitivity.md`. Actual critical-value exchanges and their action on meridians remain separate required geometric work.

- 2026-10-09 — actual `existsUnique_valuesWithConstant_collision_path_lift` passes production build. Both modules are wired into HTGeometry; three public axiom audits and final actual-source checks are running. The lift now reaches the collided endpoint, and uniqueness is proved on the entire closed interval.

## Final certificate

Two modules, three explicit public declarations, all production leaf builds, all standard-only public axiom audits and all final actual-source `lake env lean` checks pass. Both final logs are empty; both modules are wired into HTGeometry.

- `ProperFiniteFiberIntervalExtension.lean` — left endpoint convergence and continuous extension of a half-open lift through a finite terminal fiber.
- `OrderedCriticalValueCollisionPathLifting.lean` — `OrderedCriticalValueMap.existsUnique_valuesWithConstant_collision_path_lift` constructs the actual unique closed-interval parameter lift. Properness, finite terminal fiber and regular covering are discharged for the actual map.

Axiom log: `/tmp/hgt-collision-path-lifting-axioms.log`. Final logs: `/tmp/hgt-ProperFiniteFiberIntervalExtension-final.log` and `/tmp/hgt-OrderedCriticalValueCollisionPathLifting-final.log`. The parameter curve and its endpoint are conclusions; the ordinary input data are a value path regular before its endpoint and a starting polynomial realizing its initial tuple. No arbitrary planar monodromy or RH premise is assumed or proved. Next: `../3-formalized/tree-factorization-hurwitz-transitivity.md`.

Index refresh `/tmp/hgt-root-collision-continuation-index.log` passed; the actual declaration is present in `formal/LEAN_API.md`. Authoritative lint `/tmp/hgt-root-collision-continuation-lint.log` reports two unrelated unreachable RHTower modules (`BaezDuarteMobiusRigidity`, `CCMRiemannKernelBartaLayerBounds`), with no own-module or forbidden-declaration errors. Those modules were not modified.
