# Physical-ordinate topology forces singular source-to-seam transport

- **ID:** stc-physical-ordinate-transport-singularity
- **Stage:** 2-fully-proven (paper)
- **Routes:** STC, squarefree/Sonin source comparison
- **Status:** [PROVED ON PAPER] [LEAN PENDING] [NOT AN RH PROOF]

## Actual source and target

For real \(\sigma>1\), put \(Q(s)=\zeta(s)/\zeta(2s)\). In the literal normalized signed squarefree source, define the unit vector

\[
 x_{\sigma,\gamma}(n)
 =\mu(n)\sqrt{\frac{\mu(n)^2 n^{-\sigma}}{Q(\sigma)}}\,n^{i\gamma}
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

## Interpretation and exact limit of the result

The normalized Euler source has a **discrete physical-height boundary kernel**: distinct fixed ordinates become orthogonal. The prime seam has a **continuous physical-height boundary kernel**. Matching these geometries for an entire height interval requires a singular transport. The existing fixed-\(t\) Sonin phase limit instead probes \(n^{it(\sigma-1)}\), a shrinking physical height; its all-phase diagonal is pointwise in fixed \(t\) and does not contradict this theorem. The corpus's Route-P ordinate diagonalization proves analogous orthogonality for a positive Euler source; (3) and the source-to-seam transport consequence above use the signed squarefree source and the actual STC seam.

The theorem rules out **uniformly bounded linear all-height** source-to-seam landing. It does not rule out a singular/cofinal transport, a nonlinear construction, or a map defined only on a discrete zero-selected height set. It gives no sub-root Calkin estimate and no RH conclusion. It changes the STC handoff problem from seeking a bounded Hilbert map to controlling the rate and domain of a necessarily singular ordinate translator.

## Corpus audit

- Literal normalized signed source: `InfiniteMobiusSignedChannel.lean`; physical complex phase: `MobiusCriticalComplexPhaseHardySource.lean`.
- Squarefree partition and pole normalization: `SquarefreeFixedCurrentLocalization.lean`, `SquarefreePartitionPole.lean`.
- Canonical seam and its finite off-center energy: `XiPrimeSeamCoherenceCollapse.lean`, `XiPrimeSeamReflectionEnergy.lean`, `XiPrimeSeamPairAsymptotics.lean`.
- Existing all-fixed-scaled-phase Sonin diagonal: `SoninCofinalComplexPhaseGlobalCarrier.lean`; analogous positive-Euler ordinate orthogonality: `RoutePCriticalBoundaryOrdinateDiagonalization.lean`.
- A broad deep corpus search returned the component source/target results, but no theorem asserting this all-height source-to-seam operator norm obstruction. The search was partial, so no external or corpus-wide priority claim is made.
