# Every finite cofactor detects the ordinary prime count

Write $A(N)=\pi(N)-\sum_{2\le n\le N}1/\log n$. Fix real coefficients $f(1),\ldots,f(W)$, at least one nonzero. Then RH is equivalent to

$$\forall\,1/2<b<1,\qquad \sum_{d\le\min(W,N)}f(d)A(\lfloor N/d\rfloor)=O_{b,f,W}(N^b).$$

At each zero with $\Re\rho>b\ge1/2$, the absolute count exceeds $K N^b$ at arbitrarily large integers for every $K$. Any bound on a tail would extend to all integers by increasing its constant on the finite prefix.

**Upper bound.** For $b$ strictly above the supremum of the real parts of the nontrivial zeros, $\psi(N)-N=O(N^b)$ and $\psi(N)-\vartheta(N)=O(\sqrt N)$. The partial sums of $\mathbf1_{\rm prime}(n)\log n-\mathbf1_{n\ge2}$ are therefore $O(N^b)$. Abel summation against the positive decreasing sequence $1/\log(\max(n,2))$ gives $A(N)=O(N^b)$. Sum over the finitely many dilates.

**Converse.** In the Euler half-plane let $B$ be the Dirichlet series of the increments of $A$. Termwise differentiation gives $B'=\zeta-1-Q$, where $Q(s)=\sum_p(\log p)p^{-s}$. The higher prime powers converge locally uniformly for $\Re s>1/2$, so $Q$ has the residue of $-\zeta'/\zeta$ at every right zero. At a zero of multiplicity $m$, the meromorphic continuation of $B'$ consequently has a simple pole of residue $m$.

A count bound with exponent $b$ continues $DB$ holomorphically to $\Re s>b$, where $D(s)=\sum_{d\le W}f(d)d^{-s}$. This polynomial is nonzero somewhere in the Euler half-plane by Dirichlet-series uniqueness. Division by $D$ gives a meromorphic function $G$ whose derivative agrees with the continued $B'$ throughout this connected half-plane, as meromorphic germs. A derivative of a meromorphic germ is analytic if the germ extends analytically, and has pole order at least two if the germ has a pole. This excludes every zero with $\Re\rho>b$, including zeros at which $D(\rho)=0$. Letting $b$ decrease to $1/2$ proves the converse. [Lean source](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/EveryFiniteCofactorSeesTheOrdinaryPrimeCount.lean)

The direct Lean audit checked the RH equivalence, zero exclusion and excursions. Each depends only on `propext`, `Classical.choice` and `Quot.sound`.
