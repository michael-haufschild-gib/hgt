# Gaussian Hilbert transverse channel-square law

- **ID:** gaussian-hilbert-transverse-channel-square-law
- **Stage:** 3-formalized
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Type:** UNIVERSAL HILBERT-METRIC PHASE LAW
- **Lean:** `GaloisForLFunctions.HilbertMetric.TransverseDegreePhase`,
  `GaloisForLFunctions.HilbertMetric.TransverseDegreeCurvature`,
  `GaloisForLFunctions.HilbertMetric.CoherentCollisionJet`,
  `GaloisForLFunctions.HilbertMetric.GramCurvaturePersistence`,
  `GaloisForLFunctions.HilbertMetric.DeterminantCurvatureJet`,
  `GaloisForLFunctions.HilbertMetric.UnisolventEvaluation`,
  `GaloisForLFunctions.HilbertMetric.PolynomialMomentCancellation`,
  `GaloisForLFunctions.HilbertMetric.PolynomialFockKernel`,
  `GaloisForLFunctions.HilbertMetric.PolynomialFockRecombination`,
  `GaloisForLFunctions.HilbertMetric.TransverseCollisionGraph`,
  `GaloisForLFunctions.HilbertMetric.DegreeFiveCollisionGraphJet`,
  `GaloisForLFunctions.HilbertMetric.DegreeFiveGaussianCurvature`
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
a convergence hypothesis.  Three further theorems prove that arbitrary finite linear
recombinations of these remainders remain little-oh of order ten; with a product index, these
are the analytic estimates for an entire recombined Gram entry.

Finally, for a finite matrix 2-jet `(A,A_1,A_2)`, define

\[
 \mathcal K(A,A_1,A_2)
 =\operatorname{tr}\!\left(A^{-1}A_2
   -A^{-1}A_1A^{-1}A_1\right).                         \tag{KJ}
\]

Lean proves that if `(A_epsilon,A_{1,epsilon},A_{2,epsilon})` converges entrywise to an
invertible limiting 2-jet, then its values of `mathcal K` converge.  In particular, strict
positive limiting log-curvature is eventually strictly positive before collision.  This
formalizes the determinant-continuity/persistence step without assuming a curvature
certificate.

The determinant differential itself is also connected, not merely named.  Lean expands the
finite determinant by permutations, differentiates each product, and defines polynomial jets
`detFirstJet(A,A_1)` and `detSecondJet(A,A_1,A_2)`.  For every entrywise twice-differentiable
matrix path with determinant nonzero near `t`, it proves

\[
 \frac{d^2}{dt^2}\log\det A(t)
 =\frac{\det A(t)\,\operatorname{detSecondJet}(A,A_1,A_2)
       -\operatorname{detFirstJet}(A,A_1)^2}
      {\det A(t)^2}.                                    \tag{DJ}
\]

Thus positivity of the compiled scalar curvature numerator is tied to the literal second
derivative of `log det`.

The collision layer is now fully assembled.  Lean constructs injective nodes unisolvent for all
monomials of total degree at most five, obtains exact delta-moment coefficients, proves the
degreewise Fock-kernel recombination identities, and transports the scalar collision jets to the
entire normalized Gram matrix 2-jet.  At degree five and base dimension sixteen the limiting
curvature is exactly

\[
  \frac5{68}\,\#\operatorname{Sym}^5(\mathbb R^{16})>0.
\]

Continuity supplies one nonzero collision scale at which both the actual coherent Gram
determinant and its literal `log det` curvature have the required signs.  A proved diagonal
gauge identity

\[
 e^{-\frac t2\lVert x_i-x_j\rVert^2}
 =e^{-\frac t2\lVert x_i\rVert^2}
  e^{t\langle x_i,x_j\rangle}
  e^{-\frac t2\lVert x_j\rVert^2}
\]

shows that the gauge adds only an affine term to `log det`; division of every point by
`sqrt 2` gives the conventional Gaussian parameterization.  The final literal theorem is

```lean
theorem exists_finiteGaussianDistanceGram_positiveLogDetCurvature :
    ∃ x : DegreeFiveIndex 16 → (Fin 16 ⊕ DegreeFiveTopIndex 16 → ℝ),
      Function.Injective x ∧
      (finiteGaussianDistanceGram x 1).det ≠ 0 ∧
      0 < deriv (deriv
        (fun t => Real.log (finiteGaussianDistanceGram x t).det)) 1
```

with `finiteGaussianDistanceGram x t i j = exp (-t * ∑ a, (x i a - x j a)^2)`.
It has no hypotheses and therefore proves that universal bandwidth log-concavity of finite
Gaussian distance determinants is false.

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
- `coherentCollision_valueJet_finset`
- `coherentCollision_firstJet_finset`
- `coherentCollision_secondJet_finset`
- `scalarLogCurvatureNumerator`
- `tendsto_scalarLogCurvatureNumerator`
- `eventually_pos_scalarLogCurvatureNumerator`
- `gramLogCurvatureJet`
- `tendsto_gramLogCurvatureJet`
- `eventually_pos_gramLogCurvatureJet`
- `detFirstJet`
- `detSecondJet`
- `hasDerivAt_matrixDet`
- `hasDerivAt_matrixDetFirstJet`
- `det_secondDerivative_eq_jet`
- `logDet_secondDerivative_eq_jet`
- `exists_injective_evaluation_basis`
- `exists_injective_nodes_delta_moments`
- `exists_injective_nodes_monomial_delta`
- `exists_gradedMonomial_unisolvent_delta`
- `recombined_innerPower_eq_diagonal`
- `degreeFiveCollisionPoint_injective`
- `exists_distinct_degreeFiveGaussianGraphJets`
- `degreeFiveSixteen_limit_curvature`
- `eventually_pos_degreeFiveSixteen_gaussianCurvature`
- `eventually_ne_degreeFiveSixteen_gaussianValueMatrix_det`
- `exists_degreeFiveSixteen_gaussianPositiveLogDetCurvature`
- `exists_distinct_degreeFiveSixteen_gaussianPositiveLogDetCurvature`
- `finiteHalfGaussianDistance_logDet_secondDerivative_eq`
- `exists_finiteGaussianDistanceGram_positiveLogDetCurvature`

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
- The exact limiting determinant curvature (DC)--(PC), all scalar coherent-collision jets (CJ),
  unisolvent nodes, polynomial moment cancellation, finite matrix assembly, scalar/matrix
  curvature persistence (KJ), determinant differentiation (DJ), local invertibility, and the
  metric diagonal gauge are `[LEAN-PROVED]`.  The actual injective Gaussian distance
  counterexample is therefore `[LEAN-PROVED]`, not merely a paper consequence.
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
  jets; finite matrix assembly was the next checkpoint and was closed later the same day.
- 2026-07-19 -- direct check passed for continuity and strict-sign persistence of the Gram
  log-curvature matrix 2-jet at every invertible limit.
- 2026-07-19 -- direct check passed for arbitrary finite linear recombination of all three jet
  remainders and for scalar curvature-numerator persistence.
- 2026-07-19 -- direct check passed for the first and second determinant jets and the literal
  second-derivative formula for `log det` under local invertibility.
- 2026-07-19 -- `#print axioms` passed for every collision, persistence, and determinant-jet
  declaration listed above; only `propext`, `Classical.choice`, and `Quot.sound` occur.
- 2026-07-19 -- direct checks passed for the full collision/metric module and the Hilbert-metric
  umbrella.  `#print axioms` for the final Gaussian distance theorem and each major connector
  reports only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-19 -- final targeted audit `lake build GaloisForLFunctions.HilbertMetric` completed
  successfully.  Generated indexes were refreshed.  Repository-wide lint has no Hilbert-metric
  proof-debt or wiring error; it remains red only because the unrelated RHTower modules
  `AnisotropicPhaseRecurrence` and `ProjectiveWeightedCoherence` are unreachable from the
  RHTower umbrella in the shared worktree.
