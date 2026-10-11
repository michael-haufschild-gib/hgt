# Finite Weil Gaussian quadratic transport

Status: FORMALIZED — 2026-10-11.

Objective: upgrade every real projected finite Weil Gaussian weak limit to
vanishing quadratic cost of an actual monotone probability coupling, for
arbitrary projection coefficients a,b and offset sequence t. Keep final
roots unconditional, including the collapsed a+b=0 projection.

Sources: local Lean corpus and installed Lean dependencies only. No web,
external papers, or numerics. Prior lexical query `tendsto integral
monotoneCoupling sq` found six roots in HTGeometry.QuadraticTransportCost.
Its direct convergence receiver requires nonnegative support, so it does
not directly apply to centered Gaussian laws. Existing projected weak
limits and FluctuationRankOneLimit covariance limits cover every a,b.

Paper route:

1. Compute the projected second moment from the two variances and their
   covariance; the existing limits give (a+b)^2/4. Gaussian target has this
   exact second moment, and both source and target moments are integrable.
2. Remove the signed-function obstruction to quadratic Scheffe convergence.
   Apply existing nonnegative Scheffe to f_n^2 and g^2. Pointwise,
   |f_n-g|^2 <= 2|f_n^2-g^2| + min(|f_n-g|^2,4g^2).
   The minimum term tends to zero and is dominated by integrable 4g^2.
   Thus almost-everywhere convergence plus second-moment convergence gives
   vanishing squared-distance integral without sign assumptions.
3. For nondegenerate Gaussian targets, absolute continuity against volume
   gives null singleton boundaries; reverse absolute continuity gives a
   strictly increasing CDF. Portmanteau and the corpus quantile Galois
   connection yield pointwise quantile convergence on (0,1).
4. Apply signed quadratic convergence to the quantile functions and transfer
   their L2 cost to the actual monotone coupling.
5. Handle the zero-variance target as Dirac zero: its quantile is zero, so
   coupling quadratic cost is exactly the source second moment.

Plan: verify APIs and projected moment identities; formalize signed
quadratic cancellation; prove Gaussian quantile convergence; compose all
projection transport roots; wire imports; native-build and axiom-audit
every declaration; run lint and record unrelated failures. This card must
survive compaction until the full route is verified.

## Historical implementation checkpoint

Five leaves authored under `formal/GaloisForLFunctions/RHTower`:
`WeilLogShiftProjectedSecondMoment`, `WeilLogShiftSignedQuadratic`,
`WeilLogShiftGaussianQuantile`, `WeilLogShiftGaussianCoupling`, and
`WeilLogShiftGaussianQuadraticLimit`. Expected 21 public declarations,
including 2 definitions; count must be verified from actual source.

The projected-second-moment leaf passed a native build with empty log.
Its Gaussian moment proof needs an explicit `X := fun x : R => x` in
`variance_eq_integral` and explicit `NNReal.coe_mk` simplification.
The API scratch passed 31 explicit witnesses. Signed-quadratic native
build is the next verification step; other three leaves remain unverified.
No new umbrella imports or final axiom audit yet.

The environment once dropped temporary logs and a process handle while
preserving sources and old dependency objects. Exact process inspection
confirmed no live Lean process before restarting the affected leaf.
Do not infer success from a lost handle. Reconstruct scratch artifacts if
`/tmp` is missing, inspect exact processes, then resume sequential builds.


## Verified closure — 2026-10-11

The full route is formalized. For every fixed real a,b and every natural
offset sequence t, the actual monotone probability coupling of the
projected finite law at k=2(r+1)^2+t(r) to its Gaussian target has quadratic
cost tending to zero. The zero-variance direction a+b=0 is included.
Two arbitrary offset sequences with the same a,b also have vanishing mutual
monotone-coupling quadratic cost. Final roots have no analytic premises.

All declarations are in namespace `RHTower`:

- `WeilLogShiftProjectedSecondMoment`: finite-law integrability; Gaussian
  square integrability and exact second moment; exact projected second
  moment in terms of variances/covariance; convergence to the Gaussian
  second moment. 5 theorems.
- `WeilLogShiftSignedQuadratic`: the pointwise minimum-remainder bound;
  signed quadratic cancellation; a quantile-transport convergence receiver
  without nonnegative-support assumptions. 3 theorems. Its moment and
  convergence premises are discharged in the final finite Weil root.
- `WeilLogShiftGaussianQuantile`: strictly increasing nondegenerate
  Gaussian CDF; CDF and quantile convergence from weak convergence;
  exact Dirac-zero quantile and quadratic coupling cost. 5 theorems.
- `WeilLogShiftGaussianCoupling`: actual probability coupling, both
  marginals, quadratic-cost integrability, cost definition/nonnegativity,
  and the exact anti-diagonal cost. 2 definitions and 4 theorems.
- `WeilLogShiftGaussianQuadraticLimit`: unconditional roots
  `tendsto_finiteWeilCanonicalGaussianQuadraticCost_zero` and
  `tendsto_finiteWeilCanonicalProjectedMutualQuadraticCost_zero`.

Native verification: all five leaves exited 0 with empty logs. Final native
scratch checked all 21 declarations and 31 explicit API witnesses; only
propext, Classical.choice, and Quot.sound occur. Metadata found no issues,
fresh dependency objects, unique names, clean whitespace, 12 direct imports,
and 9 incoming import edges. All five leaves are wired once into the
RHTower umbrella. Scoped git diff --check passed. Both final roots were
found after local Lean index refresh.

Global formal lint: 12 errors and 367 warnings outside these
five leaves; global gate remains unclean. Diagnostics are preserved in
`/tmp/hgt-gaussian-quadratic-lint.log`.

Artifacts: `/tmp/hgt-gaussian-quadratic-{api.lean,api.log,metadata.py,
metadata.json,declarations.json,incoming-imports.txt,final-audit.lean,
final-audit.log,roots-search.json,lint.log,close.py}` and one native log per
leaf. The initial prior-search artifact was lost in an environment reset;
the source findings and proof route are preserved above. No web, external
papers, or numerical experiments supplied mathematical evidence.

This establishes an explicit mean-square coupling to the Gaussian law.
No separate optimality theorem for this quadratic coupling, named W2
metric, or joint two-dimensional coupling is claimed. The overarching
research goal remains active.
