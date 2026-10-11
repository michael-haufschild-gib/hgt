# Local nodal distortion and the quadratic-start mass limit

Status: quadratic-start conjecture FORMALIZED; only the stronger A/n -> infinity regime remains speculative backlog.
Date: 2026-10-10. Derived from local Lean results only; no external novelty claim or numerical experiment.

The completed global comparison bounds all raw logarithmic weights between A^n and (A+n)^n times the arithmetic weights. It proves relative mass convergence when n²/A tends to zero. It discards common normalization and all information about the index of a weight.

Proved result: the same square-root constant sqrt(pi/2) holds for every k_r=2(r+1)²+t(r), with arbitrary t : Nat -> Nat. The factor-two comparison alone was insufficient; binomial concentration closes the normalization gap. A possible stronger regime A/n tending to infinity is speculative and must not be treated as established.

Formalized finite bridge: let W_i be raw logarithmic nodal weights on log(A+i), and w_i the arithmetic weights on i. Set a_i=abs(W_i)/abs(w_i). The exact product formula gives a_i as a product of logarithmic means L(A+i,A+j)=(i-j)/(log(A+i)-log(A+j)), j!=i. For i>j, the common factor L(A+i,A+j) cancels in a_i/a_j. There remain n-1 factors. Monotonicity and homogeneity of L now prove

1 <= a_i/a_j <= ((A+i)/(A+j))^(n-1),

so distortion varies slowly across nearby indices even when the global distortion stays bounded away from one. This ratio inequality is formalized for all positive injective node families, with all analytic input produced from the local corpus. Its explicit canonical raw-weight identification and additive grid modulus are now formalized as well: under A>=2(r+1)², abs(a_i/a_j-1)<=abs(i-j)/(r+1).

Completed continuation: exact binomial second moments and weighted concentration control both the sum and the maximum of the perturbed profile. Their common distortion factor cancels upon normalization. The formalized relative-error bound is sqrt((n+1)/2)/n + sqrt((n+1)G/2)/n, which tends to zero because the arithmetic mass G is asymptotic to sqrt(pi/2)*sqrt(n).

Current corpus inputs: WeilLogShiftMomentRatios exact nodal-weight ratios; WeilLogShiftNodalDistortion product formula; WeilLogShiftArithmeticBinomial exact arithmetic weights; existing Wallis mass limit. The focused HTGeometry search for "logarithmic mean" found only a Jacobi log-prefix sum and a Poisson boundary-log estimate; both statements were inspected and are unrelated to the two-variable mean here. Exhaustive identifier search in HTGeometry and installed Mathlib/Analysis found no `logarithmicMean` or `logarithmic_mean` definition.

Useful installed-source leads: `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:67`, global `strictConcaveOn_log_Ioi`; `Mathlib/Analysis/Convex/Deriv.lean:381`, `ConcaveOn.slope_anti`, which is antitone on the entire positive domain minus the fixed point, including comparisons across that point. Actual-toolchain checking corrected the initially presumed `Real` namespace. The first comparison is fully formalized in `../3-formalized/finite-weil-logarithmic-mean-distortion.md` (15 declarations, complete axiom audit). The additive modulus is fully formalized in `../3-formalized/finite-weil-local-distortion-modulus.md` (11 declarations, complete axiom audit). Concentration, maximum-coefficient control, and the unconditional quadratic-start asymptotic are fully formalized in `../3-formalized/finite-weil-quadratic-mass-concentration.md` (28 declarations, complete axiom audit). The midpoint distributional bridge is formalized in `../3-formalized/finite-weil-quadratic-binomial-law.md` (nine declarations, full axiom audit). The whole-fiber parity-conditioned binomial law is formalized in `../3-formalized/finite-weil-quadratic-parity-fiber-law.md` (23 declarations, full axiom audit). Exact adjacent optimal transport is the next paper-proved target in `../2-fully-proven/finite-weil-adjacent-nodal-transport.md`.
