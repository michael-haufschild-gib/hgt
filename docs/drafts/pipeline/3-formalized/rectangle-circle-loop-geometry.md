# Actual rectangle/circle homotopies and moving-basepoint monodromy

- **ID:** RECTANGLE-CIRCLE-LOOP-GEOMETRY-20261009
- **Stage:** 3-formalized
- **Type:** BRIDGE; external novelty unverified; corpus only
- **Parent:** `../1-in-progress/polynomial-rectangle-meridian-product.md`

## Exact results and complete paper proof

The constructed rectangular loop traverses bottom, right, top and left sides in four equal time intervals. Its coordinates on these quarters are respectively Im=−h, Re=a, Im=h and Re=−a; its image lies in the closed coordinate rectangle. The aligned positive circle has angle −3π/4+2πt and the same four strict coordinate signs for every positive radius. The installed sine/cosine sign theorems verify these signs on their exact angle intervals.

Straight interpolation between these loops retains the relevant strict coordinate sign on every quarter, hence never crosses zero for any positive a,h,r. If r≤a and r≤h, convexity keeps the whole homotopy in the same rectangle. Every intermediate path is closed, with a straight moving basepoint. The radius restriction is needed only for containment.

Periodicity reduces any real angle into [0,2π), so every circle-map point occurs on the standard positive-circle path. The explicit homotopy with angle 2πt−3πs/4 rotates its basepoint to the aligned circle, keeps every intermediate path closed and preserves avoidance of any set avoided by the original circle.

For any free loop homotopy H with H(s,0)=H(s,1), the constructed basepoint path β(s)=H(s,0) satisfies γβ≃βδ by the inspected moving-endpoint homotopy theorem. Native covering transport along β is bijective and intertwines the two loop permutations. Any intertwining equivalence preserves transpositions by transporting their two exchanged elements. It preserves full cyclicity because its permutation-group isomorphism transports every integer-power same-cycle witness. No finite-sheet hypothesis is required.

## Corpus audit

The parent records the searches and exact inspected APIs: affine path/homotopy constructions, circle periodicity and trigonometric signs, convex linear preimages, path-groupoid boundary homotopy, covering monodromy composition/bijectivity, and `Equiv.permCongrHom`. All new formulas are explicit. No external sources or numerical computations were used.

## Formal certificate — 2026-10-09

Six modules, thirty explicit public declarations: `CornerCirclePath` (7), `RectangleBoundaryPath` (8), `RectangleCircleHomotopy` (4), `CirclePathRotation` (5), `FreeLoopHomotopyMonodromy` (3), and `PermutationIntertwining` (3). All six production leaf builds, all thirty standard-only axiom reports and all six final actual-source `lake env lean` checks pass. Final logs are empty. Included in the seven-module forty-report log `/tmp/hgt-rectangle-geometry-axioms.log`; final logs are `/tmp/hgt-<Module>-final.log` with the six exact module names above. All modules are wired into the HTGeometry umbrella. Completed implementation scratches removed. Index/lint refresh follows.

Actual polynomial strip instantiation still requires small meridian radii, explicit avoidance of other critical values, and the outer-rectangle comparison. The parent records a stronger slit-avoiding comparison proved on paper but not yet formalized. No prescribed polynomial realization, actual Xi embedding, external novelty certificate or RH conclusion is claimed.

Index refresh passed (`/tmp/hgt-rectangle-geometry-index.log`). Authoritative global lint reports only the unrelated unreachable module `HTGeometry.BandKernelOperators`; no error concerns these seven modules (`/tmp/hgt-rectangle-geometry-lint.log`).

The transposition-transport API was subsequently generalized to accept the caller's `DecidableEq` instances. This is necessary for ordinary polynomial root subtypes, whose equality instance differs from a globally fixed classical instance. Its mathematical statement is unchanged. The modified module passed its production build, all three standard-only axiom reports (`/tmp/hgt-permutation-intertwining-axioms.log`) and final actual-source check; final log remains empty. The temporary implementation copy is removed.
