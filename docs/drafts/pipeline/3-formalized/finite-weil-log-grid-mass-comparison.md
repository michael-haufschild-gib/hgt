# Log-cluster mass compared with equally spaced nodes

Status: formalized; all native builds and public-declaration axiom audits passed.
Date: 2026-10-10.
Research sources: local Lean corpus and installed Lean dependencies only. No web, external papers, numerical experiments, or external novelty claim.

Goal: replace the position-dependent canonical absolute mass by a controlled arithmetic-node reference, then carry that comparison into the unconditional actual-reader cost receiver.

Corpus audit: `nodal weight log bound` returned no declarations. `log_sub_log div` exposed existing `HTGeometry.LogarithmicSpacing`: both one-sided logarithmic difference bounds and the absolute lower-spacing bound. `WeilLogShiftMomentBarycentric` supplies reciprocal nodal products and normalization; `WeilLogShiftMassWeightedSensitivity` supplies the actual-reader existence/cost receiver. No existing comparison appeared in the exhaustive WeilLogShift source search. Installed Lagrange code contains the raw nodal-weight definition and its nonvanishing theorem. Binomial formulas are a future target, not a claim of this increment.

Notation: n=r+1, A=k+2, U=k+r+3=A+n. Arithmetic nodes are g_i=i for i in Fin(r+2); logarithmic nodes are h_i=log(A+i)-log A. W(h) is the raw nodal-weight vector, beta(h)=W(h)/||W(h)||_infinity, S(h)=sum|beta(h)|, and G_r=S(g).

Paper proof:
1. For injective h,g, nonnegative a and arbitrary real b, if a|h_i-h_j|<=b|g_i-g_j| for distinct nodes, then a/|g_i-g_j|<=b/|h_i-h_j|. Multiply the n inequalities over j!=i. The nodal product identity gives a^n|W(g)_i|<=b^n|W(h)_i|. Lean exposed that no separate sign assumption on b is needed; it was removed from the public helper and both callers.
2. Pointwise bounds A0|f_i|<=|g_i|<=B0|f_i| give the same inequalities for absolute sums and sup norms. Since nonzero nodal norms are positive and S(h)=sum|W(h)|/||W(h)||, cross multiplication yields A0 S(f)<=B0 S(g) and A0 S(g)<=B0 S(f).
3. The existing logarithmic inequalities imply A|h_i-h_j|<=|i-j|<=U|h_i-h_j|. For the upper logarithmic bound, order the two positive arguments, use log(y)-log(x)<=(y-x)/x, and x>=A. For the lower bound, use |y-x|/max(x,y)<=|log(y)-log(x)| and max(x,y)<=U.
4. Therefore A^n|W(g)_i|<=|W(h)_i|<=U^n|W(g)_i|. The normalized masses obey A^n G_r<=U^n S(h) and A^n S(h)<=U^n G_r. This gives both directions of distortion control, for every r,k, without any analytic premise.
5. The existing unconditional reader receiver supplies B>0,L>=1, actual coordinate-reader existence, and S(h)*(k+2)^2*2^r<=2B*cost1(w) for every reader under its stated width condition. Multiply this by U^n and combine with the first comparison: A^n G_r*(k+2)^2*2^r<=2U^n B*cost1(w). All constants and reader existence come from existing proved producers.

Formalized leaves: `WeilLogShiftNodalDistortion.lean` (six declarations), `WeilLogShiftArithmeticMassComparison.lean` (eight), `WeilLogShiftArithmeticCost.lean` (two). Exact mass comparison is in the second leaf at line107. Final receivers in the third leaf: `exists_finiteWeilGram_arithmetic_fiber_sensitivity` at line10 and `exists_finiteWeilGram_arithmetic_coordinate_cost` at line48. The full-fiber receiver also includes actual-reader existence.

Verification: all three native leaf compiles passed with empty logs. `/tmp/hgt-grid-final-audit.lean` checked all sixteen public declarations and thirty imported API terms; only `propext`, `Classical.choice`, and `Quot.sound`. Direct-dependency/source freshness, incoming-import scope, unique umbrella wiring, local index refresh, and exact final-receiver lookup passed. No full build, heartbeat change, numerical experiment, external source, or foreign-file repair.

Final formal lint exited1 on six unrelated missing imports: `RHTower.PaperThetaObservationContrast`, `RHTower.PaperThetaObservationEntropy`, `RHTower.PaperThetaObservationHistory`, `HTGeometry.PaperFiniteObservationEntropy`, `HTGeometry.PaperFiniteObservationLaw`, and `HTGeometry.QKrawtchoukCompanionTriangular`. No errors named these three new leaves.

Implementation note: endpoint let aliases required explicit unfolding before `exact_mod_cast`; no mathematical premise was added.

New insight: moving the cluster outward changes the normalized dual mass by an explicitly controlled distortion around one fixed arithmetic-node reference for each order. No explicit binomial value or asymptotic growth rate for that reference is claimed here. Next target: identify G_r exactly from arithmetic nodal products, then turn the comparison into explicit order growth.

Limitation: the distortion factor can grow with r when the cluster start grows only linearly. No uniform-in-order approximation is claimed.

Next corpus leads, read from local source but not yet scratch-verified for the next proof: `Mathlib/Algebra/Group/ForwardDiff.lean` contains `fwdDiff_iter_eq_sum_shift` (line147), `fwdDiff_iter_pow_eq_zero_of_lt` (line237), and `fwdDiff_iter_eq_factorial` (line252). `Nat.sum_range_choose` and `Nat.choose_le_middle` identify binomial total mass and its maximum. Candidate: with n=r+1, G_r=2^n/choose(n,n/2). The signed binomial vector annihilates lower moments by forward differences; the existing barycentric span and positive last entry should identify its normalization exactly. This formula is NOT formalized by this card.

Follow-up completed 2026-10-10: [finite-weil-arithmetic-binomial-mass.md](finite-weil-arithmetic-binomial-mass.md) identifies raw weights, normalized dual, and G_r=2^(r+1)/choose(r+1,(r+1)/2), and substitutes this exact reference into both cost receivers. All 14 declarations passed native build and axiom audit. Square-root growth and uniform distortion remain the next separate bridge.
