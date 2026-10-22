# HB vacuum-differentiable nonlinear detector scalarization no-go

- **ID:** HB-HC94-NONLINEAR-DETECTOR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / route-class no-go
- **Statement:** Exact nonlinear scalarization of the literal BM horizon/boundary radiative FE cocycle differentiates to a linear intertwiner; off line its first variation deletes one complete readout axis. Locally faithful scalarization exists copywise exactly on the critical line and globally exactly under RH.

## Killed RH chain

`unequal physical horizon/boundary FE gains → nonlinear detector postprocessing → one scalar Ward gain → universal cancellation → RH`.

Nonlinear postprocessing is not an independent producer when its vacuum first variation is complex-linear and retains both readouts.

## Audited frontier

- `[CORPUS]` HC89 constructs actual Green-dressed radiative source-FE cocycle and bright off-line reflected cancellation.
- `[CORPUS]` HC92 proves horizon/boundary relative cocycle is gauge invariant and gain equality iff criticality.
- `[CORPUS]` HC93 classifies all complex-linear detector scalarizations: off line they delete horizon or boundary axis.
- `[LITERATURE]` Birmingham--Mokhtari, arXiv:0709.2388, treats linear hypergeometric stability of topological AdS black holes, not nonlinear two-readout FE scalarization.
- `[LITERATURE]` Sberna et al., arXiv:2112.11168, and Yi et al., arXiv:2403.09767, treat nonlinear QNM excitation/detectability, not BM horizon/boundary FE-cocycle intertwiners.

## Paper theorem and proof

Let `Cq=diag(κH(q),κB(q))` be actual two-readout radiative cocycle and `D` any nonlinear detector into any Hausdorff complex topological module. Assume real-ray vacuum first variation

`a⁻¹ D(a x) → Lx`

with complex-linear `L`, and exact scalarization `D(Cq x)=c D(x)`. Since `Cq` is complex-linear,

`a⁻¹ D(a Cq x)=a⁻¹ D(Cq(a x))=c·a⁻¹D(a x)`.

Taking `a→0`, uniqueness of limits gives `L(Cq x)=cLx`. HC93 then yields, off line,

`L(eH)=0 ∨ L(eB)=0`.

Thus injective `L` forces `κH(q)=κB(q)`, hence `Re(q)=1/2`. On wall, identity detector supplies converse. Applying copywise—even with detector depending on `q`—gives global existence iff RH.

## Hostile verdict and positive survivor

- No continuity away from vacuum, locality, positivity, invertibility, polynomiality, or perturbative-order bound is used.
- Codomain is arbitrary Hausdorff complex topological module in linearization/axis-loss theorem.
- **Killing mechanism:** exact nonlinear scalarization survives first variation; unequal physical gains force derivative rank loss.
- **Positive survivor:** sharp first-order axis-loss law. Any off-line scalarizing detector must be vacuum-singular, have non-complex-linear first response, or erase horizon/boundary readout to first order.
- This closes complex-amplitude differentiable nonlinear detector postprocessing; real-linear/conjugate first variations remain distinct.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMRadiativeSourceFEVacuumDifferentiableNonlinearDetectorNoGo.lean`
- Final theorem: `RHTower.d4HBVacuumDifferentiableNonlinearDetectorScalarizationRouteKilled`
- Sharp survivor: `RHTower.hbXiRadiativeNonlinearDetector_firstVariation_axisLoss_of_offLine`
- Global classification: `RHTower.hbXiRadiativeGlobalVacuumDifferentiableFaithfulDetectorScalarization_iff_rh`
- Direct `lake env lean` PASS.
- Targeted build PASS: `13099/13099` jobs.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Wired into `GaloisForLFunctions/RHTower.lean`; no umbrella build run.
- Formal lint reaches module and finds no forbidden declaration; unrelated shared-worktree unreachable-module errors remain.

## Gates

- [x] 0 → 1 exact conjecture and RH chain
- [x] 1 → 2 dependency-closed paper proof and hostile audit
- [x] 2 → 3 direct Lean, targeted build, axiom audit, umbrella wire
- [ ] 3 → 4 publication-ready: not claimed
