# Gaussian Hilbert transverse channel-square law

- **ID:** gaussian-hilbert-transverse-channel-square-law
- **Stage:** 3-formalized
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Type:** UNIVERSAL HILBERT-METRIC PHASE LAW
- **Lean:** `GaloisForLFunctions.HilbertMetric.TransverseDegreePhase`,
  `GaloisForLFunctions.HilbertMetric.TransverseDegreeCurvature`,
  `GaloisForLFunctions.HilbertMetric.CoherentCollisionJet`
- **Paper parent:** `2-fully-proven/gaussian-hilbert-transverse-degree-phase-transition.md`

## Exact formal theorem

For any finite family of transverse channels with probabilities `p_i`, any lowering charge `B`,
and any top degree `M`, define

\[
 \Phi=B+\sum_i\bigl(1+(M-1)p_i\bigr)
       -\sum_i(M-1)^2p_i(1-p_i).
\]

Then Lean proves unconditionally

\[
 \Phi
 =B-\frac{kM(M-4)}4
   +\sum_i\left((M-1)p_i-\frac{M-2}{2}\right)^2,
 \qquad k=\#\{i\}.                                      \tag{CS}
\]

It also proves the arbitrary finite graph determinant identity.  For every real matrix `L`
representing a map from `k` top directions to finitely many orthogonal completion directions,
every natural `M>=1`, and every `t>=0`,

\[
 \det\operatorname{Gram}_{M,L}(t)
 =t^k\det\bigl(t^{M-1}I+L^{\mathsf T}L\bigr),            \tag{GD}
\]

where the degree-`M` coordinates scale by `t^(M/2)` and the one-particle coordinates by
`t^(1/2)`.

For the full symmetric top space, Lean now also proves the exact integral count

\[
 (d+1)B_{d,M}=M(M-1)\binom{d+M-1}{M},                  \tag{LC}
\]

for every `M >= 2`, and therefore, when `d>0`,

\[
 \frac{B_{d,M}}{\binom{d+M-1}{M}}=\frac{M(M-1)}{d+1}. \tag{LR}
\]

Thus the density inserted into the full-top phase theorem is connected to the actual
symmetric-power multiplicities rather than accepted as an external hypothesis.

The exact phase specialization is formalized as well:

\[
 \Phi\left(\frac{20}{17},1,5,\frac38\right)
 =-\frac5{68}<0.                                         \tag{E16}
\]

This sign is now connected to the literal determinant curvature.  With

\[
 Z_{B,k}(t)=t^B\left(t^5+\frac53t\right)^k,
\]

Lean proves

\[
 (\log Z_{B,k})''(1)=-B+\frac54k.                       \tag{DC}
\]

For the full degree-five top in base dimension sixteen, the formal count
`17 B = 20 k` therefore gives

\[
 (\log Z_{B,k})''(1)=\frac5{68}k>0.                     \tag{PC}
\]

Here `Z` is definitionally tied to `transverseDegreePartition`, whose graph determinant was
already proved in (GD); it is not a separately assumed probability model.

The scalar analytic atom needed to approach this graph determinant by coherent Gram matrices is
also formalized.  For fixed real `a,b`, put `y_epsilon=epsilon^2 a+epsilon^10 b`.  For
`q=0,1,2`, Lean proves

\[
 y_\varepsilon^q e^{y_\varepsilon}
 =\sum_{\ell=q}^{5}
   \frac{\varepsilon^{2\ell}a^\ell}{(\ell-q)!}
  +\mathbf 1_{q\le1}\varepsilon^{10}b
  +o(\varepsilon^{10}).                                \tag{CJ}
\]

These are exactly the entrywise value, first-scale-derivative, and
second-scale-derivative jets at the degree-five collision.  The little-oh conclusion is proved
from the exponential Taylor remainder and exact polynomial cancellation; it is not supplied as
a convergence hypothesis.

## Lean declarations

- `higherDegreeGraphGram_eq`
- `det_higherDegreeGraphGram`
- `transverseDegreePartition_eq`
- `transverseChannelFanoMargin_square`
- `transverseChannelFanoMargin_square_card`
- `transverseChannelFanoMargin_lower_bound`
- `transverseDegreeFanoMargin_at_phase_lt_zero_iff`
- `fullTopLoweringCharge_eq`
- `fullTopLoweringCharge_cross`
- `fullTopLoweringCharge_ratio_eq_density`
- `fullTopTransverse_phase_at_balance`
- `fifthDegree_sixteenDim_fano_margin`
- `fifthDegree_sixteenDim_superPoisson`
- `fifthDegreeBalancedPartition_eq`
- `log_fifthDegreeBalancedPartition_eq`
- `fifthDegreeBalancedPartition_log_secondDerivative_one`
- `fullTop_fifthDegreeBalanced_logCurvature`
- `fullTop_fifthDegreeBalanced_logCurvature_pos`
- `coherentCollisionExponent`
- `coherentCollision_valueJet`
- `coherentCollision_firstJet`
- `coherentCollision_secondJet`

The direct leaf check and `#print axioms` audit pass.  Every declaration above depends only on
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; there is no project axiom,
`sorry`, `admit`, `opaque`, or `unsafe` escape.

## Scientific boundary

- The graph Gram calculation, spectral factorization, Bernoulli moments, and completing a
  quadratic square are individually parent mathematics.
- The candidate new content is their exact universal organization by the lowering charge and
  top-degree phase `M(M-4)/4`, including the sharp negative degree-five crossing.
- The paper parent proves how (CS) arises from annihilation-invariant symmetric Fock subspaces,
  derives the rank-budget law, and transfers the full-top negative crossing through a coherent
  collision to distinct Gaussian point configurations.
- The exact limiting determinant curvature (DC)--(PC) and all three scalar coherent-collision
  jets (CJ) are now `[LEAN-PROVED]`.  Finite unisolvent recombination, determinant assembly, and
  strict-curvature persistence are not yet Lean-formalized.  Therefore the counterexample for
  an actual family of distinct Gaussian points remains `[PAPER-PROVED]`.
- Exact internal and external searches have not located (CS) under the Fock lowering-charge
  interpretation, its rank-budget consequence, or the Gaussian collision application.  This
  is not a proof of priority, so the novelty label remains unverified pending expert review.

## Verification log

- 2026-07-19 -- direct module check passed with `lake env lean`.
- 2026-07-19 -- axiom audit passed for the graph, channel-square, phase, and exact crossing
  declarations.
- 2026-07-19 -- direct check passed for the literal determinant-curvature connector and its
  exact positive full-top specialization.
- 2026-07-19 -- direct check passed for all three unconditional order-ten coherent-collision
  jets; finite matrix assembly remains open.
