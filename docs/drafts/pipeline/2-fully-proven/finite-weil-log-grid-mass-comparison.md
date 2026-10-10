# Log-cluster mass compared with equally spaced nodes

Status: dependency-closed paper proof; Lean implementation next.
Date: 2026-10-10.
Research sources: local Lean corpus and installed Lean dependencies only. No web, external papers, numerical experiments, or external novelty claim.

Goal: replace the position-dependent canonical absolute mass by a controlled arithmetic-node reference, then carry that comparison into the unconditional actual-reader cost receiver.

Corpus audit: `nodal weight log bound` returned no declarations. `log_sub_log div` exposed existing `HTGeometry.LogarithmicSpacing`: both one-sided logarithmic difference bounds and the absolute lower-spacing bound. `WeilLogShiftMomentBarycentric` supplies reciprocal nodal products and normalization; `WeilLogShiftMassWeightedSensitivity` supplies the actual-reader existence/cost receiver. No existing comparison appeared in the exhaustive WeilLogShift source search. Installed Lagrange code contains the raw nodal-weight definition and its nonvanishing theorem. Binomial formulas are a future target, not a claim of this increment.

Notation: n=r+1, A=k+2, U=k+r+3=A+n. Arithmetic nodes are g_i=i for i in Fin(r+2); logarithmic nodes are h_i=log(A+i)-log A. W(h) is the raw nodal-weight vector, beta(h)=W(h)/||W(h)||_infinity, S(h)=sum|beta(h)|, and G_r=S(g).

Paper proof:
1. For injective h,g and nonnegative a,b, if a|h_i-h_j|<=b|g_i-g_j| for distinct nodes, then a/|g_i-g_j|<=b/|h_i-h_j|. Multiply the n inequalities over j!=i. The nodal product identity gives a^n|W(g)_i|<=b^n|W(h)_i|.
2. Pointwise bounds A0|f_i|<=|g_i|<=B0|f_i| give the same inequalities for absolute sums and sup norms. Since nonzero nodal norms are positive and S(h)=sum|W(h)|/||W(h)||, cross multiplication yields A0 S(f)<=B0 S(g) and A0 S(g)<=B0 S(f).
3. The existing logarithmic inequalities imply A|h_i-h_j|<=|i-j|<=U|h_i-h_j|. For the upper logarithmic bound, order the two positive arguments, use log(y)-log(x)<=(y-x)/x, and x>=A. For the lower bound, use |y-x|/max(x,y)<=|log(y)-log(x)| and max(x,y)<=U.
4. Therefore A^n|W(g)_i|<=|W(h)_i|<=U^n|W(g)_i|. The normalized masses obey A^n G_r<=U^n S(h) and A^n S(h)<=U^n G_r. This gives both directions of distortion control, for every r,k, without any analytic premise.
5. The existing unconditional reader receiver supplies B>0,L>=1, actual coordinate-reader existence, and S(h)*(k+2)^2*2^r<=2B*cost1(w) for every reader under its stated width condition. Multiply this by U^n and combine with the first comparison: A^n G_r*(k+2)^2*2^r<=2U^n B*cost1(w). All constants and reader existence come from existing proved producers.

Planned leaves: `WeilLogShiftNodalDistortion.lean`, `WeilLogShiftArithmeticMassComparison.lean`, `WeilLogShiftArithmeticCost.lean`. Verify every new public declaration via native compilation and scratch axioms, imported API signatures, direct-dependency freshness, umbrella wiring, local index, and formal lint. One owned Lean process at a time; no full build or heartbeat change.

New insight: moving the cluster outward changes the normalized dual mass by an explicitly controlled distortion around one fixed arithmetic-node reference for each order. No explicit binomial value or asymptotic growth rate for that reference is claimed here. Next target: identify G_r exactly from arithmetic nodal products, then turn the comparison into explicit order growth.
