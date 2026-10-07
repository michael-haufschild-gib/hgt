# Product-divisor cosine repair

- **ID:** cosine-product-basepoint-repair
- **Stage:** 5-failed
- **Type:** FALSIFIED as a full three-fiber C2-P construction; one-fiber certificate remains valid
- **Parent:** cosine-basepoint-secant-repair.md; logarithmic-toric-no-asymptotic-values.md
- **Statement:** Test whether replacing the secant sum by a product divisor passes the marked 1-fiber while preserving both reflections and removable normalization.

## Final verdict, 2026-10-07

The candidate passes the stated 1-fiber test but fails the simultaneous three-fiber requirements. `CosineProductNonrealFibers.two_nonreal_cube_root_fibers` proves infinitely many genuine nonreal holomorphic points over each nontrivial cube root. The explicit marker is η=(-1-i*sqrt(3))/2; its inverse is the other marker. All constructed points have nonzero denominator after cancellation. Thus further cancellation cannot remove this obstruction.

The strongest positive survivor is the analytic two-parameter corner branch, followed by an injective discrete family of genuine fiber points. Its dependency-closed paper proof and Lean certificate are in [the formalized corner card](../3-formalized/cosine-product-corner-unfolding.md). The mechanism uses two local submersions and exact conic/exponential identities. No generic IFT novelty is claimed. This retires this candidate only; the general rational-repair classification is now pursued in [the component-rigidity card](../1-in-progress/cosine-algebraic-fiber-rigidity.md).

The sections below retain the construction and its earlier tests; their formerly open second/third-fiber questions are resolved by this verdict. C2-P and RH remain open.

## Exact candidate

Let T be the labeled cosine source, a=T(0), H(w)=T(w)-T(-w), and K(w)=(T(w)-a)*(T(-w)-a). Set

    W(w)=(H(w)+i*K(w))/(H(w)-i*K(w)),

interpreted meromorphically with cancellations. The entire divided difference b(w)=(T(w)-a)/w, filled at zero, gives coordinates after cancelling w:

    N(w)=b(w)+b(-w)-i*w*b(w)*b(-w),
    D(w)=b(w)+b(-w)+i*w*b(w)*b(-w).

**Conjecture M [FORMAL homogeneous certificate]:** this explicit repair has W(0)=1 holomorphically with nonzero derivative, both required reflections, and N(w)=D(w) implies w∈3ℤ, including common zeros. It has no nonzero projective period, infinitely many genuine regular 1-points, and no polynomial homogeneous representation. Test the other two marked fibers and every local degree before claiming a C2-P example. Differential-algebraic rigidity is not decided here.

## Paper mechanism and hostile boundary

The divided difference b is already entire. B=b(w)+b(-w) is even; P=w*b(w)*b(-w) is odd. Both commute with conjugation. Thus w↦-w swaps N,D and conjugation conjugates and swaps them, giving the two projective reflection identities. At zero N=D=2T'(0)!=0, so W is holomorphic with value 1. Its first jet is W'(0)=-i*T'(0)!=0, hence it is nonconstant and the filled 1-point is simple.

Away from a common zero, W=1 forces K=0. Existing `source_eq_fiberValue_iff` and `source_zero` place T(w)=a at `w=27*n²+3*n`, and T(-w)=a at its negative, all in 3ℤ. Every common zero of the uncancelled coordinates H±iK also has K=0 and lies on that same real lattice. Hence any further meromorphic filling cannot create a nonreal 1-point. For the already-cancelled N,D, a common zero away from zero likewise forces b(w)*b(-w)=0. No classification of their real common zeros is assumed. The stronger homogeneous lattice statement is formalized without assuming a globally reduced pair.

This prevents overgeneralizing the conic no-escape theorem: absence of finite asymptotic paths does not imply finiteness of real fibers for every polynomial projection of (T(w),T(-w)). The product K has an infinite real zero fiber. The finite-real-fiber argument on the four corners belongs to the sum projection. General Laurent polynomials have additional boundary points, which can retain a unit-circle coordinate.

## Audit and next work

- Verdict: candidate passes the homogeneous 1-fiber, infinite regular fiber, nonrationality and aperiodicity tests in Lean; the Cayley transform and cancellation mechanism are classical. Significant novelty unverified.
- No contradiction with the regular-diagonal theorem: generic diagonal value is -1 and the normalization point is a diagonal basepoint before cancellation.
- This does not cancel work on Conjecture E for the earlier secant repair. E still needs the infinite-fiber and real-fiber steps after its now-formal no-escape theorem.
- Completed formal target: entire N,D, both reflections, value and local degree at zero, exact homogeneous 1-fiber lattice containment, projective aperiodicity, infinitely many regular 1-points and nonrationality. Next attack the other cube-root fibers explicitly. Do not infer their constraints from the first fiber.
- Deep corpus query `cosine reciprocal product basepoint marked fiber`: all 20 candidate statements and all 20 source-argument statements inspected. Hits concern unrelated fiber products and co-Poisson cosine machinery; proposed tangent/reciprocal-vector ingredient is inapplicable. `partial=false`, no errors, coverage snapshot complete at the file-inventory level, compiler freshness incomplete. Rephrase targeted lexical searches before claiming absence. External novelty audit pending.

Targeted lexical query `"cosine" "basepoint"` finds the existing secant-repair module only (26 declarations, default per-module cap2), already read in full. [Bergweiler–Eremenko, linearly distributed values](https://www.math.purdue.edu/~eremenko/dvi/real.pdf), Theorem1 and its proof, classify the non-circle-image exception when three fibers are real. The present W already maps the real line into the unit circle by conjugate reciprocity, so that conclusion supplies no missing marked-fiber information; its proof also uses excluded characteristic estimates. Their [three-ray paper](https://www.math.purdue.edu/~eremenko/dvi/radial_mero_revision2.pdf), introduction and Theorems1.1–1.3, concerns three distinct rays, not three labels on the same real line. Do not transplant that classification or its growth estimates. These parent comparisons do not establish novelty of this specialization.

## Exact formal target and cancellation proof

The formal theorem is the stronger homogeneous statement `N(w)=D(w) → ∃n:ℤ, w=3*n`. It includes every common zero as well as every ordinary 1-point, so it controls any meromorphic filling without assuming that the displayed homogeneous pair is globally reduced. Indeed N-D=-2i*w*b(w)*b(-w); a zero forces w=0 or one divided difference to vanish. Multiplying the divided difference by its argument gives T(w)=a or T(-w)=a, and the existing labeled-fiber theorem applies. At zero both coordinates are nonzero and direct quotient differentiation gives W'(0)=-i*T'(0). Entirety and both coordinate-swap identities follow from the existing divided-difference proof. Global reduction and the other two marked fibers are separate claims.

## Period-return jet test [FORMAL CORE]

Write C=T'(0), p(w)=T(w)-a, q(w)=T(-w)-a and B(w)=b(w)+b(-w). A projective period τ of N,D gives the exact identity

    (p(w+τ)-q(w+τ))*w*b(w)*b(-w) + p(w+τ)*q(w+τ)*B(w) = 0.

At w=0 this forces p(τ)*q(τ)=0. Differentiating once gives

    C*(p(τ)-q(τ)) + 2*(T'(τ)*q(τ)-T'(-τ)*p(τ)) = 0.

If precisely one factor vanishes, its source derivative s must satisfy 2s=C. But the exact source fiber and jet formulas give τ or -τ = ((18n+1)^2-1)/12 and s*(18n+1)=C. Hence 18n=1, impossible in ℤ by divisibility.

If both factors vanish, divide the displayed identity by w² away from zero and fill using continuous divided differences. For s=T'(τ), t=T'(-τ) the result is C*(s+t)=2*s*t. The two source jet formulas imply n+m=0. The two source fiber formulas then give 54*n²=0, so n=0 and τ=0. This argument uses algebraic cancellation and local derivatives, including possible common basepoints; it requires no classification by size of integer solutions, positivity, or growth bounds. `CosineProductAperiodic.projective_period_eq_zero` passed direct Lean verification. The other two labeled fibers remain completely separate obligations.

## Infinite regular fiber [FORMAL]

The points x_n=fiberPoint(1,7n+1), n∈ℤ, are injective. If T(-x_n)=a, the exact fiber formula gives `(18m+1)^2+(18(7n+1)+1)^2=2`. Reduction modulo seven would make five a square, contradicting the finite-field identity x^7=x. Thus T(-x_n)≠a, x_n≠0, b(x_n)=0 and b(-x_n)≠0. Consequently N(x_n)=D(x_n)≠0 and W is holomorphic there with value one. This provides infinitely many genuine, uncancelled marked points without an integer-size argument.

There can be no polynomial pair P,Q with Q nonzero and N*Q=D*P identically: the infinite regular 1-fiber first forces P=Q. At every nonreal point N≠D, so Q vanishes there; polynomial identity then forces Q=0. This proves nonrationality projectively, retaining all basepoints.

## Anti-theatre correction

The broad statement “both reflections plus one lattice-confined fiber do not force a period” is elementary already: a rational Cayley transform of w suffices. Even requiring an infinite simple fiber does not make that general boundary new: the odd entire function sin(πw/3)/(w²-9), filled at ±3, supplies a classical Cayley example. This cycle's narrower contribution is testing the explicit rational reflected-cosine repair against the previous diagonal obstruction, including its basepoints and its exact period-return jets. Significant scientific novelty is **not established**. Do not sell this specialization as a new general rigidity obstruction. The next consequential target remains the simultaneous three-fiber condition, not polishing the one-fiber example indefinitely.

## No-go closure status

The proposed universal extension “every normalized reciprocal rational cosine repair has a nonreal 1-point” is false: the homogeneous lattice certificate excludes such a point even after filling. Positive survivor is this explicit nonrational, aperiodic repair with an infinite regular 1-fiber. No general rational-repair route or C2-P conjecture is closed here.

## Earlier consequential test — resolved by the final verdict

The other two fibers are the exact equations `(1-λ)*H+i*(1+λ)*K=0`, λ³=1, λ≠1, after retaining local cancellations. Their prescribed residue classes and simple local degrees have not been proved or disproved. Do not replace these obligations with the elementary one-fiber phenomenon.

A possible geometric producer is to classify asymptotic ends of the proper cosine-pair curve in P¹×P¹. At (∞,∞), the product repair equals -1. For a putative limiting value λ≠-1, its boundary fiber has only two possible points, each with one finite source coordinate. Connectedness would fix one boundary point, contradicting absence of finite asymptotic paths for the scalar descended cosine. The scalar no-asymptotic theorem and properness of the pair still need dependency-closed proofs and exact Lean statements; the existing `ConicInteriorLimit` machinery may supply the latter. This would address all three marked target values together, but alone would not locate their fibers on the required residue classes. Treat this as a candidate, not a completed proof or an implicit Iversen premise.

## Verification log

Three leaves: `CosineProductRepair`, `CosineProductAperiodic`, `CosineProductInfiniteFiber`. Targeted `lake build --old +GaloisForLFunctions.HTGeometry.CosineProductInfiniteFiber` passes, 3405 jobs. Five certificate/aperiodicity/infinite-fiber/nonrationality axiom checks report only `propext`, `Classical.choice`, `Quot.sound`. Each leaf is wired once into HTGeometry. Scoped whitespace checks pass. No full or umbrella build, heartbeat increase or numerical experiment.

Final direct `lake env lean <leaf>` passes separately for all three leaves, with no output or warnings. All owned jobs reached terminal exit codes. Seven owned scratch files were removed; no commit or push was made.

Global `scripts/formal_tools.py lint` exits 1 on twelve unrelated unreachable leaves: RHTower `WeilConeVonMangoldtZetaPencil`, `XiTiltRayGrowth`; HTGeometry `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`, `ModularHeightBounds`, `ModularLambdaGrowth`, `ModularThetaNormBounds`, `SchottkyDiskGrowth`, `SchottkyHalfPlaneGrowth`. None of these three product leaves is flagged. `scripts/formal_tools.py index` passes and regenerates LEAN_API, LEAN_GAPS and LEAN_OVERVIEW, reporting five changed files and zero removals. Global lint is not reported as passing.
