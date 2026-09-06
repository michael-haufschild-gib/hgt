# Multiplication preserves recovery geometry that the heat trace forgets

**Status:** paper proof. No new Lean module yet. Inputs: the formal physical homogeneous norms, attained positive gaps, actual cusp quotient, and graded Hilbert completion. Weighted-shift identities and their hyponormality interpretation are classical; novelty of this physically selected example is unestablished.

## Construction and bound

Write e_k=[u^k c] and δ_k=‖e_k‖ in the graded quotient norm, with k indexing weight k+1. The physical mode is u=c(1−(a−e)²)/4. On the sparse unit section, 0≤c≤1 and |a−e|≤1, so 0≤u≤1/4.

Multiplication by u raises homogeneous weight by one and preserves the available algebra A. If R is a normalized residual with missing coefficient one at weight k+1, then uR is a normalized residual at weight k+2. Pointwise multiplication gives ‖uR‖_physical≤‖R‖_physical/4. Apply this to an attained minimizing residual to obtain

`0<δ_(k+1)≤δ_k/4`.

Multiplication by u therefore induces an actual endomorphism U on B/A. In the physically normalized Hilbert basis b_k=e_k/δ_k,

`U b_k=w_k b_(k+1)`, `w_k=δ_(k+1)/δ_k`, `0<w_k≤1/4`.

For any finite vector x=Σx_k b_k, orthogonality gives ‖Ux‖²=Σw_k²|x_k|²≤‖x‖²/16. Density and completeness extend U uniquely to a bounded operator on the same Hilbert completion, with norm at most 1/4. On the basis, the physical flow satisfies T_q U=q U T_q; continuity extends this identity everywhere.

## A quantity sensitive to the recovery costs

The heat operator is diagonal with entries q^(k+1), so its trace does not retain the individual δ_k. The pair (T_q,U) also retains their successive ratios. Define the self-commutator K=U*U−UU*. Directly on the orthonormal basis,

`K b_0=w_0² b_0`,
`K b_k=(w_k²−w_(k−1)²)b_k` for k≥1.

In particular K≠0, so the multiplication operator is not normal. Positivity of K is equivalent to nondecreasing w_k, hence to log-convexity δ_k²≤δ_(k−1)δ_(k+1) for k≥1. This positivity is an open question here, not an assumption. No Riemannian-curvature interpretation is claimed.

The moments of the weighted shift U are γ_n=(δ_n/δ_0)². For the complexified shift, the classical Berger-measure criterion says subnormality would require these numbers to be moments of a probability measure on [0,1/16]. Whether such a measure exists remains open. This asks a concrete operator-theoretic question about optimal uniform recovery errors.

## Comparison and next proof

[Benhida–Curto–Exner, Geometrically regular weighted shifts, arXiv:2309.05888v2, §1.1](https://arxiv.org/pdf/2309.05888) defines positive weighted shifts, their product moments, the Berger-measure criterion, and the monotone-weight characterization of hyponormality. Their studied weights are sqrt((p^n+N)/(p^n+D)); no identification with our recovery ratios is known. The corpus's HTGeometry/WeightedShiftEnergy proves generic bilateral lattice energy bounds; it is not yet the required unilateral operator on our actual quotient.

First formalize the physical u bound, multiplication on homogeneous spaces, and δ_(k+1)≤δ_k/4. Then construct the bounded multiplication operator and exact weight/commutator formulas. Test log-convexity or the moment condition only after establishing this bridge; any numerical exploration is guidance, must run on the designated Runpod, and cannot enter Lean proofs.
