# Curvature of integral graph orders across residue blocks

**Theorem.** Let $H(M)$ intersect the full lower divisor through $M$ with one effective endpoint at $M$, and set $A_d(n)=\sum_{r<d}[H(dn+r)-dH(n)]$. For all positive moduli and $n\ge1$, $0\le\Delta^2 A_d(n)\le 2d^2/(n+1)^3$.

**Proof.** The local graph orders give $H(M)=\sum_{j\le M}\psi(\lfloor M/j\rfloor)=\log(M!)$. Put $z_{rj}=(r+j+1-d)/d$ and $t=n+1$. Successive residue blocks differ by a sum of $\log d+\log(1+z_{rj}/t)$. Reflection of both indices sends $z$ to $-z$. Thus twice the curvature sums $\log(1-z^2/(t+1)^2)-\log(1-z^2/t^2)$. Each summand lies between zero and $4/t^3$ for $t\ge2$.

**Incomplete blocks.** For a single residue, $K=\Delta^2[H(dn+r)-dH(n)]$ satisfies $\sum_j z_{rj}^2/(t+1+z_{rj})\le t(t+1)K+\sum_j z_{rj}\le\sum_j z_{rj}^2/(t+z_{rj})$. This follows by applying $1-x^{-1}\le\log x\le x-1$ to the ratio of the successive factors. The first moment isolates the quadratic-order contribution before taking absolute values.

**Lean.** `block_curvature`, `block_curvature_bounds`, `residue_curvature_bounds`. [Proof](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/EffectivityAcrossCompleteEndpointBlocks.lean)
