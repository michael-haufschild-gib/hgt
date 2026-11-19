# Prescribing the fixed part of the signed charge

- **Stage** 3-formalized

Let \(F\) be a legal involution, \(S\) any subset of its squarefree fixed nonunits, and \(B(k)\) any threshold. There is another legal involution \(G\) whose squarefree fixed set through \(X\) differs from \(\{1\}\cup S\) in at most
\[
 D_B(X)=\#\{k\le X:B(k)<X\}
\]
positions, with unpaid count at most \(U_F(X)+2D_B(X)\).

Take a separated perfect completion \(P\). Restore to fixed status precisely the complete \(P\)-edges whose lower endpoint belongs to \(S\). A point of \(S\) missed this way was an upper endpoint. Its lower partner was changed from \(F\), since an \(F\)-edge could not meet an \(F\)-fixed point. A newly fixed vertex outside \(S\cup\{1\}\) is likewise the upper endpoint of a changed edge. Every discrepancy is therefore in the image under \(P\) of \(\{k\le X:B(k)<X\}\). Only deleted edges already closed by \(X\) can increase the unpaid count. They add at most two vertices per such lower endpoint.

The signed allocation can be nonlinear. Let \(h:\mathbb Z\to\mathbb Z\) satisfy \(h(0)=0\) and \(h(a+1)-h(a)\in\{0,1\}\) for every \(a\). Along the signed walk \(S_n\) on all original squarefree fixed vertices, select an entry when \(h(S_n)\ne h(S_{n-1})\). The increment of \(h(S_n)\) is then exactly the sign of that entry. Telescoping gives selected charge \(h(S_X)\) at every cutoff. Reinstating the mandatory unit if the rule discarded it costs at most one.

Start with a density-one matching whose signed crossings stay below one quarter of the prescribed diverging envelope \(w\). Choose \(B(k)\ge(k+1)^2\) so that \(w(X)\ge4(k+1)\) for \(X>B(k)\). Then \(D_B(X)\le\sqrt X\) and \(D_B(X)\le w(X)/4\). Since \(h\) is 1-Lipschitz, one resulting matching has unpaid count \(o(X)\) and its fixed and crossing charges approximate \(h(M(X))\) and \(M(X)-h(M(X))\) to error at most \(w(X)\) at every sufficiently large cutoff.

Taking \(h(a)=\max(a,0)\) separates the upward and downward parts of the actual Mertens prefix. Taking \(h(a)=\lfloor\alpha a\rfloor\) gives every constant fraction \(0\le\alpha\le1\). The two approximation errors have opposite signs.

**Lean.** `prescribe_fixed_vertices_at_all_cutoffs`, `nonlinear_allocation_of_the_mertens_prefix`, `separate_the_positive_and_negative_mertens_excursions`, and `fractional_allocation_of_the_mertens_prefix`. [Support prescription](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/PrescribingTheSquarefreeFixedVertices.lean) · [Signed allocation](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/NonlinearAllocationOfTheMertensPrefix.lean)
