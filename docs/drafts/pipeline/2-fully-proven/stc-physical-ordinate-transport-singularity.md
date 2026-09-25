# Physical-ordinate topology forces singular source-to-seam transport

- **ID:** stc-physical-ordinate-transport-singularity
- **Stage:** 2-fully-proven (paper)
- **Routes:** STC, squarefree/Sonin source comparison
- **Status:** [PROVED ON PAPER] [SOURCE GRAM COLLAPSE AND RIGGED EXTRACTOR BOUNDEDNESS FORMALIZED] [SHARP CLASSIFICATION PAPER-ONLY] [NOT AN RH PROOF]

## Actual source and target

For real \(\sigma>1\), put \(Q(s)=\zeta(s)/\zeta(2s)\). In the literal normalized signed squarefree source, define the unit vector

\[
 x_{\sigma,\gamma}(n)
 =\mu(n)\sqrt{\frac{\mu(n)^2 n^{-\sigma}}{Q(\sigma)}}\,n^{-i\gamma}
 \quad(n\geq1),
\]

with zero coordinate at \(n=0\). The extra \(\mu(n)^2\) inside the root only makes the squarefree support explicit; it is redundant where \(\mu(n)\ne0\). This is exactly the source `infiniteMobiusSignedWeightLp` acted on by the physical, unitary logarithmic phase. Fix a horizontal coordinate \(0<\beta<1\), \(\beta\ne1/2\), and let \(Y=\ell^2(\mathbb P)\). The weighted canonical FE--Schwarz seam vector is

\[
 v_{\beta,\gamma}(p)=\frac{\log p}{\sqrt p}
 \left(p^{-\beta}-p^{\beta-1}\right)p^{i\gamma}.
 \tag{1}
\]

Its squared norm is the existing `orbitwisePrimeSeamWeightedNormSq` at \(\rho=\beta+i\gamma\). It is finite for \(0<\beta<1\), positive when \(\beta\ne1/2\), and independent of \(\gamma\). The map \(\gamma\mapsto v_{\beta,\gamma}\) is norm-continuous by dominated convergence, since the squared coordinate majorant is the summable \(\gamma\)-independent seam energy.

## Theorem: no uniformly bounded all-height landing

Let \(I\subset\mathbb R\) be any interval with nonempty interior. Suppose, for each \(\sigma>1\), \(T_\sigma:\ell^2(\mathbb N)\to Y\) is bounded and linear, and

\[
 T_\sigma x_{\sigma,\gamma}\longrightarrow v_{\beta,\gamma}
 \quad\text{in }Y\quad(\sigma\downarrow1)
 \tag{2}
\]

for **every** \(\gamma\in I\). Then \(\|T_\sigma\|\to+\infty\). The same conclusion holds for any nonzero norm-continuous target family in place of (1). In particular no bounded operator on the critical boundary Hilbert completion can carry the full physical-ordinate source family to the prime-seam family.

### Proof

The source norms are one. Its phase Gram matrix is exactly

\[
 \langle x_{\sigma,\gamma},x_{\sigma,\delta}\rangle
 =\frac{Q(\sigma+i(\delta-\gamma))}{Q(\sigma)}
 \tag{3}
\]

up to the harmless convention for conjugate-linearity. The positive Euler series gives (3) on \(\Re s>1\). By the simple pole of \(\zeta\) at one, \(Q(\sigma)\to+\infty\). For \(\gamma\ne\delta\), the numerator tends to the finite value \(Q(1+i(\delta-\gamma))\): \(\zeta\) is analytic there and \(\zeta(2+2i(\delta-\gamma))\ne0\) on its absolute-convergence half-plane. No zero-free theorem on \(\Re s=1\) is needed. Hence distinct fixed physical heights become orthogonal.

Choose an interior \(\gamma_0\in I\), set \(w=v_{\beta,\gamma_0}/\|v_{\beta,\gamma_0}\|\), and by continuity choose an interval \(J\subset I\) around \(\gamma_0\) and \(c>0\) such that \(\Re\langle v_{\beta,\gamma},w\rangle\ge c\) on \(J\). For arbitrary \(m\), choose distinct \(\gamma_1,\ldots,\gamma_m\in J\). Equation (3) gives

\[
 \left\|\sum_{k=1}^{m}x_{\sigma,\gamma_k}\right\|
 \longrightarrow\sqrt m,
\]

while (2) gives

\[
 \Re\left\langle T_\sigma\sum_{k=1}^{m}x_{\sigma,\gamma_k},w\right\rangle
 \longrightarrow\sum_{k=1}^{m}\Re\langle v_{\beta,\gamma_k},w\rangle
 \ge mc.
\]

Therefore \(\liminf_{\sigma\downarrow1}\|T_\sigma\|\ge c\sqrt m\). Since \(m\) is arbitrary, the norm tends to infinity. This is a finite-packet proof; it does not require constructing a nonseparable limit space.

### Stronger support classification

The same argument gives a sharp structural law without continuity of the target family. If \(Y\) is any **separable** Hilbert space, \(\sup_{\sigma\downarrow1}\|T_\sigma\|<\infty\), and \(T_\sigma x_{\sigma,\gamma}\to y_\gamma\) for every real \(\gamma\), then \(y_\gamma=0\) except at **at most countably many** heights. To prove this, fix \(w\in Y\). For any finite list of distinct heights, the source Gram matrix tends to the identity. The finite Bessel inequality therefore gives

\[
 \sum_{k=1}^{m}|\langle y_{\gamma_k},w\rangle|^2
 \le \bigl(\limsup_{\sigma\downarrow1}\|T_\sigma\|\bigr)^2\|w\|^2.
 \tag{4}
\]

So \(\langle y_\gamma,w\rangle\ne0\) at only countably many heights. Take the union over a countable dense subset of \(Y\); it contains every height with \(y_\gamma\ne0\). The countability boundary is sharp: for any distinct \(\gamma_j\) and absolutely summable coefficients \(a_j\), the uniformly bounded functionals represented by \(\sum_j a_jx_{\sigma,\gamma_j}\) have pointwise limits supported precisely on those \(\gamma_j\) for which \(a_j\ne0\), by (3) and dominated convergence. The first-prime evaluation of (1) already contradicts (4), so this obstruction does not depend on controlling the whole prime vector.

## Exact singular transport: existence, rigidity, and sharp cost

The preceding singularity is necessary, but not a nonexistence result. Write \(y_{\sigma,\gamma}=x_{\sigma,-\gamma}\), so its physical phase is \(n^{i\gamma}\) and matches (1). For \(0<\beta<1\), \(\beta\ne1/2\), define on squarefree coordinate vectors the prime-extraction map \(D_{\sigma,\beta}:\ell^2(\mathbb N)\to\ell^2(\mathbb P)\) by

\[
 (D_{\sigma,\beta}f)(p)=m_{\sigma,\beta}(p)f(p),\qquad
 m_{\sigma,\beta}(p)=-\sqrt{Q(\sigma)}\,\log p\,
 p^{(\sigma-1)/2}\bigl(p^{-\beta}-p^{\beta-1}\bigr).
 \tag{5}
\]

Then \(D_{\sigma,\beta}y_{\sigma,\gamma}=v_{\beta,\gamma}\) **exactly for every real height**. Thus an all-height singular transport exists at each safe source level. It is bounded precisely when

\[
 1<\sigma<1+2\min(\beta,1-\beta).
 \tag{6}
\]

Indeed \(|m_{\sigma,\beta}(p)|/\sqrt{Q(\sigma)}\sim
 (\log p)p^{(\sigma-1)/2-\min(\beta,1-\beta)}\) as \(p\to\infty\). Euclid's infinitude of primes suffices for the unbounded side; no prime-counting estimate is used.

**Rigidity theorem.** If a bounded linear \(T:\ell^2(\mathbb N)\to\ell^2(\mathbb P)\) at fixed \(\sigma>1\) satisfies \(Ty_{\sigma,\gamma}=v_{\beta,\gamma}\) for all \(\gamma\) in *any nonempty open interval*, then \(T\) agrees with (5) on the entire squarefree coordinate subspace. Its behavior on nonsquarefree coordinates is unrestricted. Hence (6) is necessary for any such \(T\), and the least operator norm of an exact landing is

\[
 M_{\sigma,\beta}=\sqrt{Q(\sigma)}
 \sup_{p\in\mathbb P}\log p\,p^{(\sigma-1)/2}
 |p^{-\beta}-p^{\beta-1}|.
 \tag{7}
\]

For proof, fix an output prime \(p\). The \(p\)-coordinate of \(Ty_{\sigma,z}\) is a Dirichlet Fourier series \(\sum_n c_n n^{iz}\), where \(\sum_n|c_n|<\infty\) by Cauchy--Schwarz. More strongly, the series is holomorphic on every strip \(|\Im z|<\eta<(\sigma-1)/2\), because \(\sum_n|c_n|n^\eta<\infty\). Equality to the entire single frequency \(v_{\beta,z}(p)\) on an open real interval extends throughout that strip by the identity theorem. Cesàro averaging against \(e^{-it\log m}\) and dominated convergence recover each coefficient: it is zero unless \(m=p\), and the coefficient at \(p\) is the amplitude in (1). The squarefree source amplitude at \(p\) is \(-p^{-\sigma/2}/\sqrt{Q(\sigma)}\), forcing exactly (5). Coordinate tests give the norm lower bound (7), attained by \(D_{\sigma,\beta}\).

Let \(C_\beta=\sup_p(\log p)|p^{-\beta}-p^{\beta-1}|\), a finite positive constant. Uniform power decay of the tail for \(\sigma\) near one shows that the supremum in (7), after dividing by \(\sqrt{Q(\sigma)}\), tends to \(C_\beta\). Since \((\sigma-1)Q(\sigma)\to1/\zeta(2)\),

\[
 \sqrt{\sigma-1}\,M_{\sigma,\beta}
 \longrightarrow C_\beta/\sqrt{\zeta(2)}.
 \tag{8}
\]

The root cost is robust under **uniform-in-height** approximate landing. If \(T_\sigma\) is bounded and \(\sup_{\gamma\in\mathbb R}\|T_\sigma y_{\sigma,\gamma}-v_{\beta,\gamma}\|\to0\), then averaging each output coordinate over all heights gives its \(p\)-frequency with error at most that supremum. The same coefficient argument yields

\[
 \liminf_{\sigma\downarrow1}
 \frac{\|T_\sigma\|}{\sqrt{Q(\sigma)}}\ge C_\beta.
 \tag{9}
\]

Pointwise-in-height convergence alone gives the divergence theorem above, not (9); exchanging the critical limit with the unbounded height average would be unjustified.

### Finite zero-selected packets do not inherit this obstruction

For any finite distinct heights \(\gamma_1,\ldots,\gamma_m\) and any prescribed target vectors \(z_1,\ldots,z_m\) in a Hilbert space, there are uniformly bounded **finite-rank** maps \(S_\sigma\) for all \(\sigma\) sufficiently near one with \(S_\sigma x_{\sigma,\gamma_i}=z_i\) exactly. Their source Gram matrix tends to the identity by (3), so eventually its least eigenvalue is at least \(1/2\). Inverting that finite Gram matrix gives the interpolation map, with norm at most \(\sqrt2\) times the norm of the synthesis map \(e_i\mapsto z_i\). Therefore the all-height obstruction cannot be applied to only a finite collection of hypothetical Xi zeros. An arithmetic law must constrain how the map is selected or how it behaves across a genuinely cofinal family; arbitrary interpolation of selected zeros is nonselective.

## Critical topology: maximal graph collapse and a rigged recovery

The norm divergence in the original carrier cannot be repaired by replacing a bounded map with **one fixed closed unbounded operator**. Fix an off-centre \(\beta\), a cofinal sequence \(\sigma_j\downarrow1\), and let \(R\) be any closed complex linear relation in
\(\ell^2(\mathbb N)\oplus\ell^2(\mathbb P)\) containing
\((y_{\sigma_j,\gamma},v_{\beta,\gamma})\) for every \(j\) and every real \(\gamma\). Then its vertical fibre is the entire prime space. In fact, the **smallest** such closed relation is

\[
\boxed{\quad R_{\min}=\ell^2(\{n:\mu(n)^2=1\})\oplus\ell^2(\mathbb P).\quad}
\tag{10}
\]

For each fixed \(\gamma\), \(y_{\sigma_j,\gamma}\rightharpoonup0\): its norms equal one and each coordinate tends to zero because \(Q(\sigma_j)\to\infty\). A closed linear subspace of a Hilbert space is weakly closed, so \((0,v_{\beta,\gamma})\in R\). These target vectors span densely. Indeed, if \(w\) is orthogonal to all of them, then \(\sum_p\overline{w_p}b_\beta(p)p^{i\gamma}=0\) for every \(\gamma\), where \(b_\beta(p)=\log(p)p^{-1/2}(p^{-\beta}-p^{\beta-1})\). The coefficients are absolutely summable by Cauchy--Schwarz; Fourier averaging recovers each one, and every \(b_\beta(p)\ne0\). Thus \((0,Y)\subset R\). At any one fixed \(\sigma_j\), the source orbit \(\{y_{\sigma_j,\gamma}\}_\gamma\) spans the squarefree subspace densely, by the same absolutely summable Fourier-coefficient uniqueness argument. Subtracting arbitrary vertical outputs from the retained graph pairs and closing proves (10). Conversely every retained pair lies in the right-hand side, so it is the minimal relation. Its output is unconstrained at every source point in its domain. This is a **fixed-graph** obstruction; it does not forbid the scale-dependent maps (5).

There is a precise positive replacement. For \(a>0\), let \(H_{-a}\) be the completion of finitely supported coefficient sequences under
\(\|f\|_{-a}^2=\sum_{n\ge1}|f(n)|^2 n^{-2a}\). Equivalently the isometric \(\ell^2\) coordinate is \(\widetilde f(n)=n^{-a}f(n)\). Remove the divergent probability normalization and set

\[
 z_{\sigma,\gamma}(n)=\mu(n)n^{-\sigma/2}n^{i\gamma},\qquad
 z_{1,\gamma}(n)=\mu(n)n^{-1/2}n^{i\gamma}.
\tag{11}
\]

Then \(z_{\sigma,\gamma}\to z_{1,\gamma}\) strongly in \(H_{-a}\) as \(\sigma\downarrow1\), for every fixed \(\gamma\): \(\sum_n\mu(n)^2n^{-1-2a}<\infty\) supplies a common majorant. No such critical vector exists at \(a=0\), since \(\sum_n\mu(n)^2/n=\infty\).

Put \(\kappa=\min(\beta,1-\beta)\). For \(\beta\ne1/2\) and \(0<a<\kappa\), define the prime-coordinate maps

\[
 (B_{\sigma,\beta}f)(p)
 =-\log p\,p^{(\sigma-1)/2}
   (p^{-\beta}-p^{\beta-1})f(p),
 \qquad
 (B_{1,\beta}f)(p)
 =-\log p\,(p^{-\beta}-p^{\beta-1})f(p).
\tag{12}
\]

Here \(f\in H_{-a}\), and each map takes values in \(Y\). Whenever
\(a+(\sigma-1)/2<\kappa\), \(B_{\sigma,\beta}\) is bounded, its norm is exactly
\(\sup_p(\log p)p^{a+(\sigma-1)/2}|p^{-\beta}-p^{\beta-1}|\), and
\(B_{\sigma,\beta}z_{\sigma,\gamma}=v_{\beta,\gamma}\) **at every height**.
As \(\sigma\downarrow1\), \(B_{\sigma,\beta}\to B_{1,\beta}\) in operator norm and hence
\(B_{1,\beta}z_{1,\gamma}=v_{\beta,\gamma}\). To verify operator-norm convergence, choose \(\eta>0\) with \(a+\eta<\kappa\); when \((\sigma-1)/2<\eta\), the multiplier tails are uniformly dominated by \(2(\log p)p^{-(\kappa-a-\eta)}\to0\), and convergence is uniform on the finite head.

The window \(0<a<\kappa\) is **sharp for any bounded linear all-height landing** on \(H_{-a}\), not only for (12). If a bounded \(B:H_{-a}\to Y\) takes \(z_{1,\gamma}\) to \(v_{\beta,\gamma}\) on a nonempty real interval, the coordinate Dirichlet series is holomorphic in a strip \(|\Im\gamma|<a\). Identity continuation and Fourier coefficient recovery force \(B\) to agree with \(B_{1,\beta}\) on every squarefree coordinate. A prime basis vector then forces
\(\|B\|\ge(\log p)p^a|p^{-\beta}-p^{\beta-1}|\), which is unbounded when \(a\ge\kappa\). Thus the original graph is maximally multivalued, while the unnormalised source has a bounded critical transport after an arbitrarily small **positive** loss of coefficient regularity. The width of that loss is limited exactly by the horizontal distance \(\kappa\) from the nearer strip edge.

This recovery is **not an RH selector**. It works for every off-centre \(\beta\), independently of Xi's divisor; the multiplier itself uses \(\beta\). A proof still needs an arithmetic law that pins a source-defined transport at Xi-zero fibres and enforces a regularity or Calkin constraint strong enough to exclude off-line grades. Equations (10)--(12) identify the topology such a law must use, without providing the law.

## Interpretation and exact limit of the result

The normalized Euler source has a **discrete physical-height boundary kernel**: distinct fixed ordinates become orthogonal. The prime seam has a **continuous physical-height boundary kernel**. Matching these geometries for an entire height interval requires a singular transport. The existing fixed-\(t\) Sonin phase limit instead probes \(n^{it(\sigma-1)}\), a shrinking physical height; its all-phase diagonal is pointwise in fixed \(t\) and does not contradict this theorem. The corpus's Route-P ordinate diagonalization proves analogous orthogonality for a positive Euler source; (3) and the source-to-seam transport consequence above use the signed squarefree source and the actual STC seam.

The theorem rules out **uniformly bounded linear all-height** source-to-seam landing, while (5) constructs and classifies its exact singular replacement. That replacement works at every off-center \(\beta\), whether or not a Xi zero exists there: exact seam landing and even a chosen cofinal schedule with \(M_{\sigma(q),\beta}=o(\sqrt q)\) cannot by themselves select Xi zeros or bound the *anchored commutator's* essential norm. The source-to-seam multiplier cost and the Calkin prime-partner scale are distinct. The unresolved handoff must add an arithmetic Xi-divisor law coupling them, or use a different singular/nonlinear construction or zero-selected domain. No RH conclusion follows from (5)--(9).

## Corpus audit

- Literal normalized signed source: `InfiniteMobiusSignedChannel.lean`; physical complex phase: `MobiusCriticalComplexPhaseHardySource.lean`.
- Squarefree partition and pole normalization: `SquarefreeFixedCurrentLocalization.lean`, `SquarefreePartitionPole.lean`.
- Canonical seam and its finite off-center energy: `XiPrimeSeamCoherenceCollapse.lean`, `XiPrimeSeamReflectionEnergy.lean`, `XiPrimeSeamPairAsymptotics.lean`.
- Existing all-fixed-scaled-phase Sonin diagonal: `SoninCofinalComplexPhaseGlobalCarrier.lean`; analogous positive-Euler ordinate orthogonality: `RoutePCriticalBoundaryOrdinateDiagonalization.lean`.
- [STCPhysicalOrdinateSourceOrthogonality.lean](../../../../formal/GaloisForLFunctions/RHTower/STCPhysicalOrdinateSourceOrthogonality.lean) proves the exact source overlap and off-diagonal critical limit. Its leaf passed `lake env lean` and is wired into the RHTower umbrella without an umbrella build; the operator norm divergence and countable-support classification above remain paper-only.
- The exact multiplier, open-interval Fourier rigidity, and sharp cost (5)--(9) are paper-proved and Lean-pending. Corpus search found Fourier uniqueness and bounded diagonal-operator ingredients, but no theorem combining this literal squarefree source with the STC seam and its minimal singular cost.
- The maximal fixed-graph collapse (10) and full rigged recovery (11)--(12) are paper-proved and Lean-pending. [STCRiggedPrimeSeamBound.lean](../../../../formal/GaloisForLFunctions/RHTower/STCRiggedPrimeSeamBound.lean) already constructs the critical diagonal extractor in isometric weighted coordinates and proves its bounded-operator norm estimate for `a < min beta (1-beta)`; its leaf passed `lake env lean` and is wired into the RHTower umbrella without an umbrella build. The source-vector limit, exact source landing, rigidity and sharp failure at the threshold remain to formalise. The corpus also has generic closed-relation vertical-fibre lemmas (`CompleteResolutionCofinalConditioningLaw.lean`) and critical squarefree weak nullity at zero phase (`SquarefreeCriticalFockEscape.lean`); the source-specific, all-height prime-seam combination and sharp regularity window were not found in the partial deep search. No literature-priority claim is made.
- A broad deep corpus search returned the component source/target results, but no theorem asserting this all-height source-to-seam operator norm obstruction. The search was partial, so no external or corpus-wide priority claim is made.
