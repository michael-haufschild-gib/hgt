# Local logarithmic-mean control of nodal-weight distortion

Status: formalized for all positive distinct node families; native builds and complete axiom/API audit passed.
Date: 2026-10-10. Local corpus and installed Lean dependencies only.

Let L(x,y)=(x-y)/(log(x)-log(y)) for positive distinct x,y. The first targets are positivity, symmetry, positive homogeneity, and the comparison

L(x',y) <= L(x,y) <= (x/x') L(x',y)

when 0<x'<=x, y>0, and y differs from both x and x'.

Paper proof:
1. Strict increase of log makes its secant slope positive. Existing global `strictConcaveOn_log_Ioi` and `ConcaveOn.slope_anti` make the slope (log(y)-log(x))/(y-x) antitone in y on the positive domain excluding x. Inverting positive quantities makes L monotone in y; symmetry gives monotonicity in x. The source lemma handles points on either side of the excluded diagonal. Actual-toolchain checking corrected the initially presumed `Real` namespace: the concavity theorem is global.
2. Symmetry follows by negating numerator and denominator. For t>0, log(tx)-log(ty)=log(x)-log(y), so L(tx,ty)=tL(x,y).
3. Monotonicity gives the lower bound. Put t=x/x'>=1. Since y<=ty, L(x,y)<=L(x,ty)=tL(x',y). No diagonal is encountered at the endpoints: y!=x and ty!=x because y!=x'. This proves the upper bound.
4. Let x_i=A+i, n+1 nodes, and a_i=abs(W_log,i)/abs(W_arithmetic,i). Existing nodal-product formulas give a_i=product_(l!=i) L(x_i,x_l). For i>j, the factor L(x_i,x_j)=L(x_j,x_i) cancels between a_i and a_j. Every remaining ratio lies in [1,x_i/x_j], and there are n-1 such ratios. Thus 1<=a_i/a_j<=(x_i/x_j)^(n-1). In the corpus notation n=r+1, the exponent is exactly r. Equivalently a_j<=a_i and x_j^r a_i<=x_i^r a_j.

This exposes monotone distortion of the exact binomial arithmetic weights and a bound depending on index separation. It is stronger than comparing all weights only through global endpoint powers. All analytic input is discharged by local log concavity and elementary log identities; only positivity, distinctness, and index ordering are quantified structural conditions.

Sources read: installed Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean line67; Mathlib/Analysis/Convex/Deriv.lean line381; predecessor nodal-product and binomial formulas. Focused corpus searches found no two-variable logarithmic-mean producer; see `../0-backlog/finite-weil-local-nodal-distortion.md` for the search record.

Completed scalar leaf `WeilLogShiftLogarithmicMean.lean`: eight declarations, ending in `finiteWeilLogarithmicMean_local_comparison` at line57. Completed generic nodal leaf `WeilLogShiftLogNodalDistortion.lean`: seven declarations, including the exact raw-weight identity (line44), identification with the ratio of absolute raw weights (line60), local ratio bound (line70), and division-free monotonicity/local bound (line104). The generic statement holds for every positive injective node family, so the arithmetic grid is included without restricting the producer to that grid.

Verification: both native leaf builds exited0 with empty logs. `/tmp/hgt-lognodal-final-audit.lean` exited0, checking all 15 public declarations and 32 explicit API terms; all axioms are contained in `propext`, `Classical.choice`, `Quot.sound`. Metadata audit found no source/direct-dependency freshness, complete axiom coverage, or exact umbrella-count issue. Both directly imported Mathlib source/compiled artifacts are fresh. Exhaustive incoming imports are the umbrella and internal scalar-to-nodal chain. One owned Lean process at a time; no full/umbrella build, heartbeat change, or numerical experiment.

Formal lint `/tmp/hgt-lognodal-lint.log` exits1 only on four unrelated missing umbrella imports: `RHTower.JointAncestryLogWeightBernoulli`, `RHTower.JointAncestryLogWeightExpansion`, `RHTower.JointAncestryLogWeightPrimeSum`, `HTGeometry.QKrawtchoukCompanionTriangular`. No errors in these leaves; foreign work untouched.

The scalar API audit corrected the global namespace of `strictConcaveOn_log_Ioi`; after that correction, both mathematical leaves compiled cleanly on their first native pass. No proof weakening was needed.

Follow-up completed: `finite-weil-local-distortion-modulus.md` retains the Bernoulli error and proves an additive modulus proportional to node separation, including exact canonical raw-weight identification and the full grid bound. All 11 declarations passed native builds and axiom audit. The quadratic-start mass asymptotic still requires concentration and maximum-coefficient control.

Local index refresh exited0. Exact post-index lookup found `finiteWeilLogNodalDistortion_local_bounds` at source line104. All owned build, audit, lint, index, and search sessions are terminal.
