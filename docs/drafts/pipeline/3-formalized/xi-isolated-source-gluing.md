# Actual isolated Xi punctures and continuous extension gluing

- **ID:** XI-ISOLATED-SOURCE-GLUING-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `xi-image-cover-analytic-capping.md`
- **Statement:** Around every point of the actual Xi source, a punctured neighborhood avoids both marked fibers. Each marked source point has a connected punctured disk mapping into its target chart. Continuous local extensions over these punctures glue globally while preserving a prescribed projection identity.

## Complete paper proof

[PROVED HERE, relative to the corpus identity principle and checked punctured-disk model]

Affine scaling and translation identify any positive-radius punctured complex disk with D*. Therefore it is open and path connected. The metric neighborhood basis shows every punctured neighborhood contains such a disk.

If either marked fiber of Xi accumulated at a finite point, the analytic identity principle would make Xi identically that marked value. This contradicts xi(0)=1/2. Thus both marked fibers are locally isolated. Intersect their punctured complements and a small inverse image of the corresponding target chart to obtain the required punctured source disk.

For the gluing theorem, let U be open and let U contain a punctured neighborhood of each omitted point a. Given a continuous map on U and a local continuous extension gₐ at each omitted point, define F to equal the original map on U and gₐ(a) at each omitted point. At points of U, continuity follows from openness. At an omitted point a, a sufficiently small punctured neighborhood lies in U and the original map agrees there with gₐ. The functions also agree at a, so they agree on a whole neighborhood; F is continuous at a. Any specified projection identity holds separately on U and at the chosen omitted-point values.

The generic gluing theorem does not assume a global extension or require separation axioms. Its local-extension inputs remain explicit. Applying those inputs to the actual selected cap charts is the next proof on the parent card.

## Verification

- `HTGeometry/PuncturedSourceDisk.lean`: five public declarations; production leaf build PASS, 2429 jobs.
- `HTGeometry/PuncturedLocalGluing.lean`: one theorem; leaf build PASS, 894 jobs.
- `RHTower/XiIsolatedMarkedPunctures.lean`: four theorems; leaf build PASS, 11123 jobs.
- All ten declarations pass the combined standard-only axiom audit, `/tmp/hgt-xi-actual-caps-axioms.log`.
- All three final actual-source checks PASS with empty logs, `/tmp/hgt-{PuncturedSourceDisk,PuncturedLocalGluing,XiIsolatedMarkedPunctures}-final.log`.
- Wired and indexed. A lexical corpus query for continuous punctured extension retrieved two local/root or obstruction results, neither this gluing statement; no absence or external novelty claim. No web sources or numerical experiments.
