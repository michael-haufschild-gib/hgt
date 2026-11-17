# Small sections on signed spline rays

**Open target.** For each integer spline ray and every ε > 0, exhibit a nonzero rational section after increasing the logarithmic radius by εm² for all sufficiently large m.

At resolution n, sample the signed spline f at log(j/n). For each prime power k = pʳ in the support window, impose the integral valuation

    floor((2/√k) Σⱼ fⱼ fⱼₖ / j).

Negative valuations permit denominators. Let d be the positive rational generator of the resulting lattice. The logarithmic radius A is twice the product of the two sampled pole degrees minus the degree-point jet pairing with its diagonal counterterm. The small sections have coordinates z ∈ ℤ satisfying |dz| ≤ exp A.

On a fixed window, rounding all finite places changes the signed degree by at most Σₖ Λ(k), independently of the mesh and the coefficients. Before rounding, the signed degree converges to the full Weil form by logarithmic quadrature, including both poles. A nonzero section exists exactly when log d ≤ A. This leaves the arithmetic comparison of the least nonzero section with the real radius.

The primal and dual logarithmic section counts have quadratic coefficients $\max(Q(a),0)$ and $\max(-Q(a),0)$. It suffices to prove one comparison for the effective divisors $e_1+e_p$. A single constant $C$ must satisfy $\log d(m(e_1+e_p)) \le A(m(e_1+e_p))+Cm^2$ at arbitrarily large $m$ for each prime $p$. Here $d$ is an integer. [Signed section limits](../3-formalized/tate-limits-of-rational-small-sections.md) · [Prime-pair criterion](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/SmallSectionsOnPrimePairs.lean)

[Conductor graph resultants](../3-formalized/acs-vertical-contact-of-signed-divisors.md) independently realize the complete prime sum on every signed spline ray as a difference of logarithmic restriction orders. The least-section estimate at the real place remains open.
