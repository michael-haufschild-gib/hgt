# Every connected punctured-disk cover is a power or exponential cover

- **ID:** PUNCTURED-DISK-COVER-CLASSIFICATION-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `xi-image-cover-analytic-capping.md`
- **Statement:** Every covering q:Y→D* with path-connected, locally path-connected source is isomorphic over D* either to exp:{Re z<0}→D* or to z↦zⁿ:D*→D* for some n>0.

## Complete paper proof

[PROVED HERE, relative to the listed corpus results]

Restrict the corpus exponential covering to D*={0<|z|<1}. Its full inverse image L={Re z<0} is convex and simply connected. Integer translations by 2πi act freely with exactly the exponential fibers. Hence this is a quotient covering by the additive integers.

Every subgroup is nℤ for some n≥0: use cyclicity and replace a generator by its absolute value. For n>0, exp(z/n) is a surjective covering L→D* whose fibers are precisely the nℤ-orbits. Its quotient homeomorphism identifies L/nℤ with D*, and the projection becomes the nth power map. For n=0 the quotient is L itself.

The checked subgroup-cover construction realizes the based fundamental-group image of q. The checked covering-comparison theorem identifies Y with this subgroup quotient. The preceding explicit identifications give the two alternatives and exact projection identities.

## Verification and scope

- `HTGeometry/PuncturedDiskCover.lean`: twenty public declarations; production leaf build PASS, 2428 jobs.
- `HTGeometry/PuncturedDiskCoverClassification.lean`: twenty-five public declarations; production leaf build PASS, 2564 jobs.
- All forty-five declarations pass the combined axiom audit with only `propext`, `Classical.choice`, `Quot.sound`: `/tmp/hgt-peripheral-axioms.log`.
- Final direct actual-source `lake env lean` checks PASS, empty logs `/tmp/hgt-PuncturedDiskCover-final.log` and `/tmp/hgt-PuncturedDiskCoverClassification-final.log`.
- Both modules wired into `HTGeometry.lean`; index refreshed. Global lint reports seven unrelated unreachable modules, no own-module or forbidden-declaration errors; `/tmp/hgt-peripheral-lint.log`. Exact list appears on `peripheral-component-bridge.md`.

This discharges the topological model classification used by the Xi capping construction. Restriction to peripheral components and the global cap atlas remain separate obligations. Corpus searches and inspected sources are recorded on the parent card. No external novelty claim, web sources, or numerical experiments.
